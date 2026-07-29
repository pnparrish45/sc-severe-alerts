#!/usr/bin/env python3
"""
SC Severe Weather Bot  v2
=========================
Watches five things at once:

  1. Hail >= 1.00"  ANYWHERE in South Carolina
  2. CONFIRMED tornado touchdowns within 30 mi of 29201 (Columbia)
  3. Any confirmed severe weather within 30 mi of 29201
  4. Wind >= 70 mph within 30 mi of 29201
  (ZIP-level watch rule removed at user request)

Data sources (ALL FREE, ZERO API KEYS):

  api.weather.gov          NWS warnings w/ hail size, wind gust, tornado tags
  mesonet.agron.iastate.edu  NWS Local Storm Reports (the "confirmed" feed)
  spc.noaa.gov             SPC preliminary hail/wind/tornado reports
  mrms.ncep.noaa.gov       MRMS MESH radar hail grid (optional)
  api.zippopotam.us        ZIP code -> lat/lon (one time, then cached)

The only credential anywhere in this file is your own email address in
USER_AGENT, which NOAA asks for as a courtesy contact.
"""

import argparse
import csv
import gzip
import io
import json
import math
import os
import smtplib
import sys
import time
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path

import requests

# ============================================================================
# CONFIG
# ============================================================================

USER_AGENT = "sc-severe-bot/2.0 (your.email@example.com)"   # <-- EDIT THIS

# --- Thresholds -------------------------------------------------------------
HAIL_THRESHOLD_IN = 1.00        # statewide hail trigger
MESH_THRESHOLD_IN = 1.25        # radar estimate runs hot; keep above the above
WIND_THRESHOLD_MPH = 70.0       # wind trigger inside the radius

# --- Geography --------------------------------------------------------------
CENTER_ZIP = "29201"
RADIUS_MILES = 30.0
WATCH_ZIPS = []          # ZIP-level rule disabled. Add ZIPs here to re-enable.

# Fallback centroids if the ZIP lookup service is unreachable.
ZIP_FALLBACK = {
    "29201": (33.990, -81.030),
    "29204": (34.045, -81.005),
    "29205": (33.987, -81.010),
    "29206": (34.048, -80.955),
}

# South Carolina bounding box (MESH grid clip only)
SC_LAT_MIN, SC_LAT_MAX = 31.95, 35.25
SC_LON_MIN, SC_LON_MAX = -83.40, -78.45

# --- Which warnings count as "major" ---------------------------------------
MAJOR_EVENTS = {
    "Tornado Warning",
    "Severe Thunderstorm Warning",
    "Extreme Wind Warning",
    "Flash Flood Warning",
    "Hurricane Warning",
    "Tropical Storm Warning",
    "High Wind Warning",
    "Ice Storm Warning",
    "Blizzard Warning",
    "Snow Squall Warning",
    "Dust Storm Warning",
}

# SPC publishes wind reports in KNOTS. Flip to "MPH" only if that ever changes.
SPC_WIND_UNIT = "KTS"

# --- Plumbing ---------------------------------------------------------------
STATE_FILE = Path(os.environ.get("HAIL_STATE_FILE", "hail_state.json"))

# Which rules this invocation checks. Set by --rules at startup.
# Run the whole set every 30 min, and just "tornado" every 10 min.
ALL_RULES = ("hail", "tornado", "wind", "severe")
RULES = set(ALL_RULES)


def rule_on(name):
    return name in RULES
ZIP_CACHE_FILE = Path("zip_cache.json")
DEDUP_HOURS = 6
LSR_LOOKBACK_HOURS = 3

NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "")
SMTP_HOST = os.environ.get("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(os.environ.get("SMTP_PORT", "587"))
SMTP_USER = os.environ.get("SMTP_USER", "")
SMTP_PASS = os.environ.get("SMTP_PASS", "")
EMAIL_TO = os.environ.get("EMAIL_TO", "")
ENABLE_MESH = os.environ.get("ENABLE_MESH", "0") == "1"

NWS_ALERTS_URL = "https://api.weather.gov/alerts/active"
IEM_LSR_URL = "https://mesonet.agron.iastate.edu/geojson/lsr.geojson"
SPC_REPORTS = {
    "hail": ["https://www.spc.noaa.gov/climo/reports/today_hail.csv",
             "https://www.spc.noaa.gov/climo/reports/yesterday_hail.csv"],
    "wind": ["https://www.spc.noaa.gov/climo/reports/today_wind.csv",
             "https://www.spc.noaa.gov/climo/reports/yesterday_wind.csv"],
    "torn": ["https://www.spc.noaa.gov/climo/reports/today_torn.csv",
             "https://www.spc.noaa.gov/climo/reports/yesterday_torn.csv"],
}
MESH_LATEST_URL = ("https://mrms.ncep.noaa.gov/2D/MESH_Max_60min/"
                   "MRMS_MESH_Max_60min.latest.grib2.gz")
ZIP_LOOKUP_URL = "https://api.zippopotam.us/us/{zip}"

UA = {"User-Agent": USER_AGENT}
GEOJSON_HEADERS = {**UA, "Accept": "application/geo+json"}

KTS_TO_MPH = 1.15078


# ============================================================================
# Geometry  (pure Python, no GIS libraries needed)
# ============================================================================

def haversine_miles(lat1, lon1, lat2, lon2):
    """Great-circle distance between two points, in miles."""
    R = 3958.8
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * R * math.asin(math.sqrt(a))


def point_in_ring(lat, lon, ring):
    """Ray-casting test. `ring` is a list of [lon, lat] pairs."""
    inside = False
    n = len(ring)
    for i in range(n):
        x1, y1 = ring[i][0], ring[i][1]
        x2, y2 = ring[(i + 1) % n][0], ring[(i + 1) % n][1]
        if (y1 > lat) != (y2 > lat):
            xint = (x2 - x1) * (lat - y1) / (y2 - y1 + 1e-15) + x1
            if lon < xint:
                inside = not inside
    return inside


def iter_rings(geometry):
    """Yield every outer ring from a GeoJSON Polygon or MultiPolygon."""
    if not geometry:
        return
    gtype = geometry.get("type")
    coords = geometry.get("coordinates") or []
    if gtype == "Polygon":
        for ring in coords:
            yield ring
    elif gtype == "MultiPolygon":
        for poly in coords:
            for ring in poly:
                yield ring


def polygon_contains(geometry, lat, lon):
    return any(point_in_ring(lat, lon, ring) for ring in iter_rings(geometry))


def polygon_within_miles(geometry, lat, lon, miles):
    """
    True if the polygon contains the point, or any vertex is within `miles`.
    Not mathematically perfect (a huge polygon's *edge* could pass closer than
    any vertex) but warning polygons have dense vertices, so it's fine at 30 mi.
    """
    if polygon_contains(geometry, lat, lon):
        return True
    for ring in iter_rings(geometry):
        for pt in ring:
            if haversine_miles(lat, lon, pt[1], pt[0]) <= miles:
                return True
    return False


# ============================================================================
# ZIP centroids
# ============================================================================

def resolve_zips(zips):
    cache = {}
    if ZIP_CACHE_FILE.exists():
        try:
            cache = json.loads(ZIP_CACHE_FILE.read_text())
        except json.JSONDecodeError:
            cache = {}

    changed = False
    for z in zips:
        if z in cache:
            continue
        try:
            r = requests.get(ZIP_LOOKUP_URL.format(zip=z), headers=UA, timeout=20)
            r.raise_for_status()
            place = r.json()["places"][0]
            cache[z] = [float(place["latitude"]), float(place["longitude"])]
            changed = True
        except Exception as e:
            print(f"  [ZIP {z} lookup failed ({e}); using fallback]", file=sys.stderr)
            cache[z] = list(ZIP_FALLBACK.get(z, (33.99, -81.03)))
            changed = True

    if changed:
        ZIP_CACHE_FILE.write_text(json.dumps(cache, indent=2))
    return {z: tuple(cache[z]) for z in zips}


# ============================================================================
# State / dedup
# ============================================================================

def load_state():
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except json.JSONDecodeError:
            pass
    return {"seen": {}}


def save_state(state):
    cutoff = datetime.now(timezone.utc) - timedelta(hours=DEDUP_HOURS * 4)
    state["seen"] = {k: v for k, v in state["seen"].items()
                     if datetime.fromisoformat(v) > cutoff}
    STATE_FILE.write_text(json.dumps(state, indent=2))


def already_sent(state, key):
    ts = state["seen"].get(key)
    if not ts:
        return False
    return (datetime.now(timezone.utc) - datetime.fromisoformat(ts)) < \
        timedelta(hours=DEDUP_HOURS)


def mark_sent(state, key):
    state["seen"][key] = datetime.now(timezone.utc).isoformat()


# ============================================================================
# Notification
# ============================================================================

def notify(title, body, priority="high"):
    print(f"\n=== ALERT ===\n{title}\n{body}\n", flush=True)

    if NTFY_TOPIC:
        try:
            requests.post(
                f"https://ntfy.sh/{NTFY_TOPIC}",
                data=body.encode("utf-8"),
                headers={"Title": title, "Priority": priority,
                         "Tags": "cloud_with_lightning_and_rain"},
                timeout=15,
            )
        except Exception as e:
            print(f"  [ntfy failed: {e}]", file=sys.stderr)

    if EMAIL_TO and SMTP_USER and SMTP_PASS:
        try:
            msg = EmailMessage()
            msg["Subject"] = title
            msg["From"] = SMTP_USER
            msg["To"] = EMAIL_TO
            msg.set_content(body)
            with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=30) as s:
                s.starttls()
                s.login(SMTP_USER, SMTP_PASS)
                s.send_message(msg)
        except Exception as e:
            print(f"  [email failed: {e}]", file=sys.stderr)


def maps_link(lat, lon):
    return f"https://www.google.com/maps?q={lat:.4f},{lon:.4f}"


# ============================================================================
# Parsing helpers
# ============================================================================

def first(param_dict, name):
    v = (param_dict or {}).get(name)
    if isinstance(v, list):
        return v[0] if v else None
    return v


def num(text):
    """Pull the first number out of strings like '1.75', '70 MPH', 'E60'."""
    if text is None:
        return None
    keep, seen_digit = [], False
    for c in str(text):
        if c.isdigit() or (c == "." and seen_digit):
            keep.append(c)
            seen_digit = True
        elif seen_digit:
            break
    try:
        return float("".join(keep))
    except ValueError:
        return None


def to_mph(magnitude, unit):
    m = num(magnitude)
    if m is None:
        return None
    u = (unit or "").upper()
    if "KT" in u or "KNOT" in u:
        return m * KTS_TO_MPH
    return m


# ============================================================================
# SOURCE 1 — NWS active warnings
# ============================================================================

def check_nws(state, zips):
    center = zips[CENTER_ZIP]

    r = requests.get(NWS_ALERTS_URL, params={"area": "SC", "status": "actual"},
                     headers=GEOJSON_HEADERS, timeout=30)
    r.raise_for_status()

    for feature in r.json().get("features", []):
        p = feature.get("properties", {}) or {}
        geom = feature.get("geometry")
        params = p.get("parameters", {}) or {}
        event = p.get("event", "")
        alert_id = p.get("id", "")

        hail_in = num(first(params, "maxHailSize"))
        gust_mph = num(first(params, "maxWindGust"))       # NWS tags this in MPH
        torn_detect = (first(params, "tornadoDetection") or "").upper()
        torn_damage = (first(params, "tornadoDamageThreat") or "").upper()
        tstm_damage = (first(params, "thunderstormDamageThreat") or "").upper()

        near_center = geom and polygon_within_miles(
            geom, center[0], center[1], RADIUS_MILES)
        hit_zips = [z for z in WATCH_ZIPS
                    if geom and z in zips and polygon_contains(geom, *zips[z])]
        # County/zone-only products have no polygon; fall back to areaDesc text
        if geom is None:
            near_center = "Richland" in (p.get("areaDesc") or "")

        reasons = []
        prio = "high"

        # 1. statewide hail
        if rule_on("hail") and hail_in and hail_in >= HAIL_THRESHOLD_IN:
            reasons.append(f'Hail {hail_in:.2f}" (statewide rule)')

        # 2. tornado — OBSERVED means a spotter/radar confirmed it on the ground
        if rule_on("tornado") and event == "Tornado Warning" and near_center:
            if torn_detect == "OBSERVED" or torn_damage:
                reasons.append(f"CONFIRMED TORNADO within {RADIUS_MILES:.0f} mi")
                prio = "urgent"
            else:
                reasons.append(f"Tornado Warning (radar indicated) "
                               f"within {RADIUS_MILES:.0f} mi")
                prio = "urgent"

        # 3. any severe warning inside the radius
        if rule_on("severe") and near_center and event in MAJOR_EVENTS \
                and not reasons:
            reasons.append(f"{event} within {RADIUS_MILES:.0f} mi of {CENTER_ZIP}")

        # 4. wind threshold inside the radius
        if rule_on("wind") and near_center and gust_mph \
                and gust_mph >= WIND_THRESHOLD_MPH:
            reasons.append(f"Wind gusts to {gust_mph:.0f} mph "
                           f"within {RADIUS_MILES:.0f} mi")
            prio = "urgent"

        # 5. (optional) anything major over WATCH_ZIPS — empty by default
        if hit_zips and event in MAJOR_EVENTS:
            reasons.append(f"{event} covering {', '.join(hit_zips)}")

        if not reasons:
            continue

        key = f"nws:{alert_id}"
        if already_sent(state, key):
            continue

        detail = []
        if hail_in:
            detail.append(f'hail {hail_in:.2f}"')
        if gust_mph:
            detail.append(f"gusts {gust_mph:.0f} mph")
        if torn_detect:
            detail.append(f"tornado {torn_detect.lower()}")
        if tstm_damage:
            detail.append(f"damage threat {tstm_damage}")

        title = f"⚠️ {event}"
        if prio == "urgent":
            title = f"🌪️ {event} — ACT NOW"

        body = (
            f"{chr(10).join('• ' + x for x in reasons)}\n\n"
            f"{', '.join(detail) if detail else ''}\n"
            f"Areas: {p.get('areaDesc')}\n"
            f"Until: {p.get('expires')}\n"
            f"Issued by: {p.get('senderName', '')}\n\n"
            f"{(p.get('description') or '')[:600]}"
        )
        notify(title, body, priority=prio)
        mark_sent(state, key)


# ============================================================================
# SOURCE 2 — NWS Local Storm Reports via IEM  (this is "CONFIRMED")
# ============================================================================

def check_lsr(state, zips):
    """
    Local Storm Reports are what an NWS office publishes after a spotter,
    law enforcement, or damage survey confirms something actually happened.
    This is the difference between "a tornado is possible" and "a tornado hit."
    """
    center = zips[CENTER_ZIP]

    r = requests.get(IEM_LSR_URL,
                     params={"states": "SC", "hours": LSR_LOOKBACK_HOURS},
                     headers=UA, timeout=30)
    r.raise_for_status()

    for f in r.json().get("features", []):
        p = f.get("properties", {}) or {}
        geom = f.get("geometry") or {}
        coords = geom.get("coordinates") or []
        if len(coords) < 2:
            continue
        lon, lat = float(coords[0]), float(coords[1])

        typetext = str(p.get("typetext") or p.get("type_text") or "").upper()
        code = str(p.get("type") or "").upper()
        unit = str(p.get("unit") or p.get("magnitude_unit") or "").upper()
        magnitude = p.get("magnitude")
        city = p.get("city") or ""
        county = p.get("county") or ""
        remark = p.get("remark") or p.get("remarks") or ""
        valid = p.get("valid") or ""
        source = p.get("source") or ""

        dist = haversine_miles(center[0], center[1], lat, lon)
        in_radius = dist <= RADIUS_MILES

        is_tornado = "TORNADO" in typetext or "WATERSPOUT" in typetext or code == "T"
        is_hail = "HAIL" in typetext or code == "H"
        is_wind = "WND" in typetext or "WIND" in typetext or "DOWNBURST" in typetext
        is_flood = "FLOOD" in typetext
        is_severe = is_tornado or is_hail or is_wind or is_flood

        reasons, prio = [], "high"

        if is_hail and rule_on("hail"):
            size = num(magnitude)
            if size and size >= HAIL_THRESHOLD_IN:
                reasons.append(f'CONFIRMED {size:.2f}" hail (statewide rule)')

        if is_tornado and in_radius and rule_on("tornado"):
            reasons.append(f"CONFIRMED TORNADO — {dist:.0f} mi from {CENTER_ZIP}")
            prio = "urgent"

        if is_wind and in_radius and rule_on("wind"):
            mph = to_mph(magnitude, unit)
            if mph and mph >= WIND_THRESHOLD_MPH:
                reasons.append(f"CONFIRMED {mph:.0f} mph wind — {dist:.0f} mi away")
                prio = "urgent"

        if is_severe and in_radius and rule_on("severe") and not reasons:
            reasons.append(f"Confirmed severe weather ({typetext.title()}) "
                           f"— {dist:.0f} mi away")

        if not reasons:
            continue

        key = f"lsr:{valid}:{lat:.3f}:{lon:.3f}:{code}:{magnitude}"
        if already_sent(state, key):
            continue

        mag_str = ""
        if magnitude not in (None, "", 0):
            mag_str = f"Magnitude: {magnitude} {unit}\n"

        title = f"✅ {typetext.title()} confirmed"
        if prio == "urgent":
            title = f"🌪️ {typetext.title()} CONFIRMED — {dist:.0f} mi"

        body = (
            f"{chr(10).join('• ' + x for x in reasons)}\n\n"
            f"Where: {city}, {county} County SC\n"
            f"{mag_str}"
            f"Time: {valid}\n"
            f"Reported by: {source}\n"
            f"{remark}\n\n"
            f"{maps_link(lat, lon)}\n"
            f"Source: NWS Local Storm Report"
        )
        notify(title, body, priority=prio)
        mark_sent(state, key)


# ============================================================================
# SOURCE 3 — SPC preliminary reports
# ============================================================================

def check_spc(state, zips):
    center = zips[CENTER_ZIP]

    wanted = {"hail": "hail", "wind": "wind", "torn": "tornado"}
    for kind, urls in SPC_REPORTS.items():
        if not rule_on(wanted[kind]):
            continue
        for url in urls:
            try:
                r = requests.get(url, headers=UA, timeout=30)
                r.raise_for_status()
            except Exception as e:
                print(f"  [SPC {kind} fetch failed: {e}]", file=sys.stderr)
                continue

            for row in csv.DictReader(io.StringIO(r.text)):
                if (row.get("State") or "").strip().upper() != "SC":
                    continue
                try:
                    lat = float(row["Lat"])
                    lon = float(row["Lon"])
                except (ValueError, TypeError, KeyError):
                    continue

                dist = haversine_miles(center[0], center[1], lat, lon)
                in_radius = dist <= RADIUS_MILES
                loc = (row.get("Location") or "").strip()
                county = (row.get("County") or "").strip()
                when = row.get("Time", "")
                comments = (row.get("Comments") or "").strip()

                reasons, prio, label = [], "high", ""

                if kind == "hail":
                    size = num(row.get("Size"))
                    if size is None:
                        continue
                    size /= 100.0                       # hundredths of an inch
                    label = f'{size:.2f}" hail'
                    if size >= HAIL_THRESHOLD_IN:
                        reasons.append(f'Reported {size:.2f}" hail (statewide)')

                elif kind == "wind":
                    raw = row.get("Speed")
                    if raw and raw.strip().upper() not in ("UNK", ""):
                        mph = to_mph(raw, SPC_WIND_UNIT)
                        label = f"{mph:.0f} mph wind" if mph else "wind damage"
                        if mph and mph >= WIND_THRESHOLD_MPH and in_radius:
                            reasons.append(f"Reported {mph:.0f} mph wind "
                                           f"— {dist:.0f} mi away")
                            prio = "urgent"
                    else:
                        label = "wind damage"
                    if in_radius and not reasons:
                        reasons.append(f"Reported wind damage — {dist:.0f} mi away")

                elif kind == "torn":
                    label = "TORNADO"
                    if in_radius:
                        reasons.append(f"TORNADO REPORT — {dist:.0f} mi "
                                       f"from {CENTER_ZIP}")
                        prio = "urgent"

                if not reasons:
                    continue

                key = f"spc:{kind}:{when}:{lat}:{lon}"
                if already_sent(state, key):
                    continue

                title = f"📍 SPC report: {label}"
                if prio == "urgent":
                    title = f"🌪️ SPC: {label} — {dist:.0f} mi"

                body = (
                    f"{chr(10).join('• ' + x for x in reasons)}\n\n"
                    f"{loc}, {county} County SC\n"
                    f"Time: {when} UTC\n"
                    f"{comments}\n\n"
                    f"{maps_link(lat, lon)}\n"
                    f"Source: SPC preliminary storm report"
                )
                notify(title, body, priority=prio)
                mark_sent(state, key)


# ============================================================================
# SOURCE 4 — MRMS MESH radar hail grid  (optional)
# ============================================================================

def check_mesh(state, zips):
    try:
        import numpy as np
        import pygrib
    except ImportError:
        print("  [MESH skipped: pip install pygrib numpy]", file=sys.stderr)
        return

    import tempfile
    center = zips[CENTER_ZIP]

    r = requests.get(MESH_LATEST_URL, headers=UA, timeout=120)
    r.raise_for_status()
    raw = gzip.decompress(r.content)

    with tempfile.NamedTemporaryFile(suffix=".grib2", delete=False) as f:
        f.write(raw)
        tmp = f.name

    try:
        grbs = pygrib.open(tmp)
        grb = grbs[1]
        vals = np.array(grb.values, dtype=float)
        lat1 = float(grb.latitudeOfFirstGridPointInDegrees)
        lon1 = float(grb.longitudeOfFirstGridPointInDegrees)
        di = float(grb.iDirectionIncrementInDegrees)
        dj = float(grb.jDirectionIncrementInDegrees)
        grbs.close()

        if lon1 > 180:
            lon1 -= 360.0

        r0, r1 = sorted([int(round((lat1 - SC_LAT_MAX) / dj)),
                         int(round((lat1 - SC_LAT_MIN) / dj))])
        c0, c1 = sorted([int(round((SC_LON_MIN - lon1) / di)),
                         int(round((SC_LON_MAX - lon1) / di))])
        r0, c0 = max(r0, 0), max(c0, 0)
        r1 = min(r1, vals.shape[0] - 1)
        c1 = min(c1, vals.shape[1] - 1)

        sub = np.where(vals[r0:r1 + 1, c0:c1 + 1] < 0, 0.0,
                       vals[r0:r1 + 1, c0:c1 + 1]) / 25.4

        hits = np.argwhere(sub >= MESH_THRESHOLD_IN)
        if hits.size == 0:
            return

        buckets = {}
        for ri, ci in hits:
            lat = lat1 - (r0 + ri) * dj
            lon = lon1 + (c0 + ci) * di
            size = float(sub[ri, ci])
            bk = (round(lat, 1), round(lon, 1))
            if size > buckets.get(bk, (0.0,))[0]:
                buckets[bk] = (size, lat, lon)

        for (blat, blon), (size, lat, lon) in sorted(buckets.items(),
                                                     key=lambda kv: -kv[1][0]):
            key = f"mesh:{blat}:{blon}"
            if already_sent(state, key):
                continue
            dist = haversine_miles(center[0], center[1], lat, lon)
            notify(
                f'🧊 {size:.2f}" MESH radar estimate',
                f'Radar-estimated max hail: {size:.2f}"\n'
                f"{dist:.0f} mi from {CENTER_ZIP}\n"
                f"{lat:.3f}, {lon:.3f}\n{maps_link(lat, lon)}\n\n"
                f"MRMS MESH 60-min max. ESTIMATE, not a confirmed report.",
                priority="default",
            )
            mark_sent(state, key)
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


# ============================================================================
# Main
# ============================================================================

def run_once():
    state = load_state()
    zips = resolve_zips([CENTER_ZIP] + WATCH_ZIPS)
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    print(f"[{stamp}] checking...", flush=True)

    for name, fn in (("NWS", check_nws), ("LSR", check_lsr), ("SPC", check_spc)):
        try:
            fn(state, zips)
        except Exception as e:
            print(f"  [{name} error: {e}]", file=sys.stderr)

    if ENABLE_MESH and rule_on("hail"):
        try:
            check_mesh(state, zips)
        except Exception as e:
            print(f"  [MESH error: {e}]", file=sys.stderr)

    save_state(state)


def main():
    ap = argparse.ArgumentParser(description="SC severe weather alert bot")
    ap.add_argument("--rules", default="all",
                    help='comma list: hail,tornado,wind,severe (or "all"). '
                         'Each rule set keeps its own dedup file.')
    ap.add_argument("--loop", action="store_true")
    ap.add_argument("--interval", type=int, default=120)
    ap.add_argument("--test", action="store_true")
    ap.add_argument("--show-zips", action="store_true",
                    help="print resolved ZIP centroids and exit")
    args = ap.parse_args()

    global RULES, STATE_FILE
    if args.rules.strip().lower() in ("all", ""):
        RULES = set(ALL_RULES)
        slug = "all"
    else:
        RULES = {r.strip().lower() for r in args.rules.split(",") if r.strip()}
        bad = RULES - set(ALL_RULES)
        if bad:
            ap.error(f"unknown rule(s): {', '.join(sorted(bad))}. "
                     f"Valid: {', '.join(ALL_RULES)}")
        slug = "-".join(sorted(RULES))

    # Separate dedup file per rule set, so the 10-min tornado job and the
    # 30-min full job never overwrite each other's state.
    if not os.environ.get("HAIL_STATE_FILE"):
        STATE_FILE = Path(f"state_{slug}.json")
    print(f"rules: {slug}   state: {STATE_FILE}")

    if args.test:
        notify("Test", "SC severe weather bot notifications are working.")
        return
    if args.show_zips:
        for z, (la, lo) in resolve_zips([CENTER_ZIP] + WATCH_ZIPS).items():
            print(f"{z}: {la:.5f}, {lo:.5f}  {maps_link(la, lo)}")
        return

    if args.loop:
        while True:
            run_once()
            time.sleep(args.interval)
    else:
        run_once()


if __name__ == "__main__":
    main()
