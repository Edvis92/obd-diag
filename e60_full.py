"""
BMW E60 diagnostics for K+DCAN cables (K-line, cars built before 03/2007).
READ-ONLY: finds control units, identifies them and reads fault memory, then
shows what each fault means using the built-in BMW fault database.
It never codes, clears, flashes or writes anything to the car.

Setup:   pip install pyserial
Run:     python e60_full.py     (needs e60_data.db in the same folder)
"""
import json
import math
import os
import queue
import re
import sqlite3
import sys
import threading
import time
import tkinter as tk
import webbrowser
from tkinter import messagebox, ttk
from urllib.parse import quote_plus

import serial
from serial.tools import list_ports

BAUD = 10400
TESTER = 0xF1
DEMO = "Demo (no car)"
AUTO = "Auto (show every variant that knows this code)"

ADDR_NAMES = {
    0x00: "Body gateway (KGM/ZGM)", 0x01: "Airbag (ACSM/MRS)", 0x02: "Steering column switch (SZL)",
    0x05: "Driver door", 0x06: "Passenger door", 0x12: "Engine (DME/DDE)", 0x16: "Active steering (AFS)",
    0x17: "Fuel pump module (EKP)", 0x18: "Gearbox (EGS)", 0x20: "Tyre pressure (RDC)",
    0x21: "Cruise control (ACC)", 0x22: "Adaptive light (ALC)", 0x23: "Roll stabilisation (ARS)",
    0x29: "Stability control (DSC)", 0x40: "Car access (CAS)", 0x41: "Alarm (DWA)",
    0x60: "Instrument cluster (KOMBI)", 0x63: "Navigation / MMI (CCC)", 0x64: "Park distance (PDC)",
    0x70: "Light module (LM)", 0x72: "Body base module (KBM)", 0x73: "Central info display (CID)",
    0x78: "Climate (IHKA)",
}
QUICK = [0x00, 0x01, 0x02, 0x05, 0x06, 0x12, 0x18, 0x29, 0x40, 0x60, 0x64, 0x70, 0x72, 0x78]

NRC = {
    0x10: "general reject", 0x11: "service not supported", 0x12: "sub-function not supported",
    0x22: "conditions not correct", 0x31: "request out of range", 0x33: "security access denied",
    0x78: "response pending",
}

# Standard OBD-II live values: pid -> (label, unit, decoder, decimals)
LIVE = {
    0x0C: ("Engine speed", "rpm", lambda d: (d[0] * 256 + d[1]) / 4, 0),
    0x0D: ("Vehicle speed", "km/h", lambda d: d[0], 0),
    0x05: ("Coolant temperature", "°C", lambda d: d[0] - 40, 0),
    0x0F: ("Intake air temperature", "°C", lambda d: d[0] - 40, 0),
    0x04: ("Engine load", "%", lambda d: d[0] * 100 / 255, 0),
    0x11: ("Throttle position", "%", lambda d: d[0] * 100 / 255, 0),
    0x10: ("Air flow (MAF)", "g/s", lambda d: (d[0] * 256 + d[1]) / 100, 1),
    0x0B: ("Intake pressure", "kPa", lambda d: d[0], 0),
    0x06: ("Short-term fuel trim", "%", lambda d: (d[0] - 128) * 100 / 128, 1),
    0x07: ("Long-term fuel trim", "%", lambda d: (d[0] - 128) * 100 / 128, 1),
    0x0E: ("Ignition timing", "°", lambda d: d[0] / 2 - 64, 1),
    0x42: ("Battery voltage", "V", lambda d: (d[0] * 256 + d[1]) / 1000, 2),
}

# ---------------------------------------------------------------------------
# Rough German -> English helper for fault texts that BMW only ships in German.
# It translates known words and word parts; anything unknown stays German.
# ---------------------------------------------------------------------------
WORDS = {  # whole words only
    "vor": "before", "nach": "after", "und": "and", "oder": "or", "mit": "with",
    "ohne": "without", "bei": "at", "von": "from", "fuer": "for", "ueber": "above",
    "nicht": "not", "kein": "no", "keine": "no", "zu": "too", "ist": "is",
    "links": "left", "rechts": "right", "hinten": "rear", "vorne": "front",
    "aus": "off", "ein": "on", "aktiv": "active", "fehler": "fault", "fehlt": "missing",
    "defekt": "defective", "falsch": "wrong", "falsche": "wrong", "hoch": "high",
    "niedrig": "low", "wegen": "due to", "gegen": "to", "masse": "ground",
    "plus": "positive", "intern": "internal", "interne": "internal", "interner": "internal",
    "botschaft": "message", "nachricht": "message", "telegramm": "message",
    "signal": "signal", "bereich": "range", "zustand": "state", "typ": "type",
    "sendet": "sends", "empfangen": "received", "erkannt": "detected",
    "begrenzt": "limited", "vorhanden": "present", "werden": "are", "wurde": "was",
    "konnte": "could", "mehrere": "several", "anzahl": "number", "alterung": "ageing", "test": "test",
}

STEMS = [  # parts of words, matched inside longer words (longest first is applied)
    ("abgasrueckfuehr", "EGR"), ("abgasrückführ", "EGR"), ("abgastemperatur", "exhaust temperature "),
    ("abgasgegendruck", "exhaust back pressure "), ("abgasklappe", "exhaust flap "), ("abgas", "exhaust gas "),
    ("ansauglufttemperatur", "intake air temperature "), ("ansaugluft", "intake air "),
    ("ladelufttemperatur", "charge air temperature "), ("ladedruck", "boost pressure "),
    ("umgebungsdruck", "ambient pressure "), ("umgebungstemperatur", "ambient temperature "),
    ("kuehlmitteltemperatur", "coolant temperature "), ("kuehlmittel", "coolant "),
    ("oeltemperatur", "oil temperature "), ("oelqualitaet", "oil quality "), ("oelniveau", "oil level "),
    ("oeldruck", "oil pressure "), ("raildruck", "rail pressure "), ("hochdruck", "high pressure "),
    ("niederdruck", "low pressure "), ("kraftstoffpumpe", "fuel pump "), ("kraftstoff", "fuel "),
    ("lambdasondenbeheizung", "oxygen sensor heater "), ("lambdasondenheizung", "oxygen sensor heater "),
    ("lambdasonde", "oxygen sensor "), ("katalysator", "catalyst "), ("partikelfilter", "particulate filter "),
    ("stickoxid", "NOx "), ("luftmassenmesser", "mass air flow sensor "), ("luftmasse", "air mass "),
    ("drosselklappen", "throttle valve "), ("drosselklappe", "throttle valve "), ("drallklappen", "swirl flap "),
    ("kurbelwellen", "crankshaft "), ("kurbelwelle", "crankshaft "), ("nockenwellen", "camshaft "),
    ("nockenwelle", "camshaft "), ("einspritzventil", "injection valve "), ("einspritzung", "injection "),
    ("injektoren", "injectors "), ("injektor", "injector "), ("gluehkerze", "glow plug "),
    ("gluehsteuergeraet", "glow control unit "), ("glühsteuergerät", "glow control unit "),
    ("zuendspule", "ignition coil "), ("zündspule", "ignition coil "), ("zuendung", "ignition "),
    ("zündung", "ignition "), ("verbrennungsaussetzer", "misfire "), ("aussetzererkennung", "misfire detection "),
    ("aussetzerkennung", "misfire detection "), ("zylindergleichstellung", "cylinder balancing "),
    ("zylinder", "cylinder "), ("laufruheregler", "smooth running control "),
    ("nullmengenadaption", "zero fuel quantity adaptation "), ("gemischadaption", "mixture adaptation "),
    ("adaption", "adaptation "), ("trimmregelung", "trim control "), ("regelabweichung", "control deviation "),
    ("regelung", "control "), ("ansteuerspannung", "drive voltage "), ("ansteuerung", "control "),
    ("steuergeraet", "control unit "), ("steuergerät", "control unit "), ("steuerung", "control "),
    ("ueberwachung", "monitoring "), ("überwachung", "monitoring "), ("plausibilitaet", "plausibility "),
    ("plausibilität", "plausibility "), ("unplausibel", "implausible "), ("kurzschluss", "short circuit "),
    ("leitungsunterbrechung", "open circuit "), ("unterbrechung", "open circuit "), ("leitung", "wiring "),
    ("versorgungsspannung", "supply voltage "), ("speisespannung", "supply voltage "),
    ("spannungsversorgung", "power supply "), ("batteriespannung", "battery voltage "),
    ("unterspannung", "undervoltage "), ("ueberspannung", "overvoltage "), ("spannung", "voltage "),
    ("batterie", "battery "), ("bordnetz", "on-board electrical system "), ("generator", "alternator "),
    ("stromregelung", "current control "), ("pumpstrom", "pump current "), ("elektrischer", "electrical "),
    ("elektrische", "electrical "), ("elektrisch", "electrical "), ("elektroluefter", "electric fan "),
    ("elektrolüfter", "electric fan "), ("sensor", "sensor "), ("geber", "sensor "), ("fuehler", "sensor "),
    ("steller", "actuator "), ("stellmotor", "servo motor "), ("ventil", "valve "), ("relais", "relay "),
    ("heizung", "heater "), ("zuheizer", "auxiliary heater "), ("temperatur", "temperature "),
    ("druck", "pressure "), ("drehzahl", "speed "), ("drehmoment", "torque "), ("drehrate", "yaw rate "),
    ("geschwindigkeit", "speed "), ("fahrzeug", "vehicle "), ("raddrehzahl", "wheel speed "),
    ("lenkwinkel", "steering angle "), ("lenkradwinkel", "steering wheel angle "), ("lenkrad", "steering wheel "),
    ("fahrpedal", "accelerator pedal "), ("bremslicht", "brake light "), ("bremse", "brake "),
    ("getriebedaten", "transmission data "), ("getriebe", "transmission "), ("kupplung", "clutch "),
    ("motorlager", "engine mount "), ("motor", "engine "), ("modul", "module "), ("schalter", "switch "),
    ("schnittstelle", "interface "), ("kommunikation", "communication "), ("bedienung", "operation "),
    ("diagnoserückmeldung", "diagnostic feedback "), ("diagnosemodus", "diagnostic mode "),
    ("diagnose", "diagnosis "), ("selbsttest", "self-test "), ("codierung", "coding "),
    ("inbetriebnahme", "commissioning "), ("abschaltung", "shutdown "), ("ausfall", "failure "),
    ("ausgang", "output "), ("auswertung", "evaluation "), ("funktion", "function "), ("riemen", "belt "),
    ("verdichter", "compressor "), ("turbine", "turbine "), ("bypassklappe", "bypass flap "),
    ("bypassventil", "bypass valve "), ("kontrollleuchte", "warning lamp "), ("kuehlerjalousie", "radiator shutter "),
    ("klimaleistung", "A/C power "), ("klemme", "terminal "), ("hauptrelais", "main relay "),
    ("anlasssperr", "starter lockout "), ("starter", "starter "), ("potenziometer", "potentiometer "),
    ("potentiometer", "potentiometer "), ("hallimpulse", "Hall pulses "), ("bezugsmarke", "reference mark "),
    ("mengenregel", "quantity control "), ("mengengeregelt", "quantity controlled "),
    ("druckgeregelt", "pressure controlled "), ("sicherung", "fuse "), ("pumpe", "pump "),
    ("luefter", "fan "), ("lüfter", "fan "), ("lager", "mount "), ("licht", "light "),
    ("energiesparmode", "energy saving mode "), ("energieverbrauchsmessung", "energy consumption measurement "),
    ("fehlerort", "fault location "), ("fehlerhaft", "faulty "), ("unbekannter", "unknown "),
    ("ungueltig", "invalid "), ("mechanischer", "mechanical "), ("thermischer", "thermal "),
    ("virtuelle", "virtual "), ("fahrgeschwindigkeitssignal", "vehicle speed signal "),
    ("multifunktionslenkrad", "multifunction steering wheel "), ("anschlag", "stop "),
    ("unterbrechung", "open circuit "), ("oel", "oil "), ("öl", "oil "), ("luft", "air "),
    ("niere", "kidney grille "), ("intelligenter", "intelligent "), ("magnet", "solenoid "), ("busfehler", "bus fault "), ("analogwerterfassung", "analog value acquisition "), ("notluft", "emergency air "),
]
_TRANS = str.maketrans({"ä": "ae", "ö": "oe", "ü": "ue", "ß": "ss", "Ä": "ae", "Ö": "oe", "Ü": "ue"})
_STEMS_SORTED = sorted(((k.translate(_TRANS), v) for k, v in STEMS), key=lambda p: -len(p[0]))


def _split_compound(low):
    """Left-to-right scan: longest known word part at each position."""
    i, parts, covered = 0, [], 0
    while i < len(low):
        for stem, en in _STEMS_SORTED:
            if low.startswith(stem, i):
                parts.append(en)
                i += len(stem)
                covered += len(stem)
                break
        else:
            parts.append(low[i])
            i += 1
    if covered < 0.6 * len(low):
        return None
    return "".join(parts)


def rough_english(text):
    """Very rough word-by-word English for BMW's German fault texts."""
    import re
    out = []
    for tok in re.split(r"([^A-Za-zÄÖÜäöüß]+)", text):
        low = tok.lower().translate(_TRANS)
        if not low.isalpha():
            out.append(tok)
        elif low in WORDS:
            out.append(WORDS[low])
        elif len(low) >= 5:
            got = _split_compound(low)
            out.append(re.sub(r"\s+", " ", got).strip() if got else tok)
        else:
            out.append(tok)
    s = re.sub(r"\s+", " ", "".join(out)).strip()
    return s[:1].upper() + s[1:] if s else s



def hx(b):
    return " ".join(f"{x:02X}" for x in b)


def wait(seconds):
    end = time.perf_counter() + seconds
    while time.perf_counter() < end:
        pass


def app_dir():
    base = sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__)
    return os.path.dirname(base)


def resource(name):
    for base in (getattr(sys, "_MEIPASS", None), app_dir()):
        if base:
            p = os.path.join(base, name)
            if os.path.exists(p):
                return p
    return None


def data_path():
    return resource("e60_data.db")


def clean(text, raw):
    return re.sub(rf"^\s*{raw}\s*[-:]?\s*", "", text or "", flags=re.I).strip()


class FaultDB:
    """Fault descriptions for the BMW E60, from the bundled e60_data.db."""

    def __init__(self):
        self.lock = threading.Lock()
        self.con = None
        path = data_path()
        if path:
            try:
                self.con = sqlite3.connect(f"file:{path}?mode=ro", uri=True, check_same_thread=False)
            except Exception:
                self.con = None

    def q(self, sql, args=()):
        if not self.con:
            return []
        with self.lock:
            return self.con.execute(sql, args).fetchall()

    def addresses(self):
        return [(a, n) for a, n, _ in self.q("select addr, min(name), count(*) from ecu group by addr order by addr")]

    def variants(self, addr):
        return self.q("select sgbd, name from ecu where addr=? order by sgbd", (addr,))

    def one(self, sgbd, code):
        rows = self.q("select de, en from dtc where sgbd=? and code=?", (sgbd, code))
        return rows[0] if rows else None

    def many(self, addr, code):
        """All different meanings of this code across the variants at this address."""
        rows = self.q(
            "select e.sgbd, d.de, d.en from dtc d join ecu e on e.sgbd=d.sgbd where e.addr=? and d.code=?",
            (addr, code),
        )
        groups = {}
        for sg, de, en in rows:
            key = clean(en or de, code)
            groups.setdefault(key, [de, en, []])[2].append(sg)
        return sorted(groups.values(), key=lambda g: -len(g[2]))

    def by_hwnr(self, addr, numbers):
        found = set()
        for n in numbers:
            for (sg,) in self.q("select h.sgbd from hwnr h join ecu e on e.sgbd=h.sgbd where h.hwnr=? and e.addr=?", (n, addr)):
                found.add(sg)
        return found


def describe(de, en, raw):
    """-> (english text, is_rough_translation, original german or '')"""
    if en:
        return clean(en, raw), False, ""
    german = clean(de, raw)
    rough = rough_english(german)
    if rough.lower() == german.lower():  # nothing to translate (e.g. technical names)
        return german, False, ""
    return rough, True, german


class FakeSerial:
    """Pretends to be a car so you can try the program without one."""

    PRESENT = {
        0x00: b"DEMO KGM 0000001", 0x12: b"DEMO DME 0000002", 0x18: b"DEMO EGS 0000003",
        0x29: b"DEMO DSC 0000004", 0x40: b"DEMO CAS 0000005", 0x60: b"DEMO KOMBI 000006",
        0x78: b"DEMO IHKA 0000007",
    }
    FAULTS = {
        0x12: [(0x27, 0x12, 0x2F), (0x27, 0x18, 0x2F), (0x27, 0x45, 0x2F)],
        0x29: [(0x5D, 0x8C, 0x2F)],
        0x40: [(0x93, 0x04, 0x2F)],
    }

    def __init__(self):
        self.buf = bytearray()
        self.break_condition = False

    def reset_input_buffer(self):
        self.buf = bytearray()

    def flush(self):
        pass

    def close(self):
        pass

    def read(self, n):
        if not self.buf:
            time.sleep(0.01)
            return b""
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def reply(self, module, data):
        msg = [0x80 | len(data), TESTER, module] + list(data)
        msg.append(sum(msg) & 0xFF)
        self.buf += bytes(msg)

    LIVE_PIDS = [0x04, 0x05, 0x06, 0x07, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x42]

    @classmethod
    def mask(cls, base):
        pids = set(cls.LIVE_PIDS) | {0x20, 0x40}
        m = sum(1 << (31 - (p - base - 1)) for p in pids if base < p <= base + 32)
        return list(m.to_bytes(4, "big"))

    @classmethod
    def live_value(cls, pid):
        import math
        t = time.time()
        if pid in (0x00, 0x20, 0x40):
            return cls.mask(pid)
        rpm = int((820 + 120 * math.sin(t * 1.3) + 40 * math.sin(t * 5)) * 4)
        volts = int(13900 + 120 * math.sin(t))
        return {
            0x04: [int((22 + 3 * math.sin(t)) * 2.55)], 0x05: [88 + 40], 0x06: [130], 0x07: [125],
            0x0B: [35], 0x0C: [rpm >> 8, rpm & 255], 0x0D: [0], 0x0E: [148], 0x0F: [24 + 40],
            0x10: [1, 0x40], 0x11: [int(14 * 2.55)], 0x42: [volts >> 8, volts & 255],
        }.get(pid, [0])

    def write(self, msg):
        time.sleep(0.02)
        self.buf += msg  # echo, like a real K-line cable
        n = msg[0] & 0x3F
        module, data = msg[1], list(msg[3:3 + n])
        if module not in self.PRESENT or not data:
            return
        if data[0] == 0x81:
            self.reply(module, [0xC1, 0xEF, 0x8F])
        elif data[0] == 0x82:
            self.reply(module, [0xC2])
        elif data[:2] == [0x1A, 0x80]:
            self.reply(module, [0x5A, 0x80] + list(self.PRESENT[module]))
        elif data[0] == 0x01 and len(data) > 1 and module == 0x12:
            self.reply(module, [0x41, data[1]] + self.live_value(data[1]))
        elif data[0] == 0x18:
            faults = self.FAULTS.get(module, [])
            body = [x for f in faults for x in f]
            self.reply(module, [0x58, len(faults)] + body)
        else:
            self.reply(module, [0x7F, data[0], 0x11])


class KLine:
    def __init__(self, port, log):
        self.log = log
        self.pending = bytearray()
        self.last_ok = None
        self.last_fail = None
        if port == DEMO:
            self.ser = FakeSerial()
        else:
            self.ser = serial.Serial(port, BAUD, bytesize=8, parity="N", stopbits=1, timeout=0.2)

    def close(self):
        try:
            self.ser.close()
        except Exception:
            pass

    @staticmethod
    def frame(target, data, functional=False):
        n = len(data)
        base = 0xC0 if functional else 0x80
        hdr = [base | n, target, TESTER] if n <= 63 else [base, target, TESTER, n]
        msg = hdr + list(data)
        msg.append(sum(msg) & 0xFF)
        return bytes(msg)

    def get(self, n, timeout):
        out = bytearray()
        while self.pending and len(out) < n:
            out.append(self.pending.pop(0))
        end = time.time() + timeout
        while len(out) < n and time.time() < end:
            out += self.ser.read(n - len(out))
        return bytes(out)

    def send(self, msg):
        self.ser.reset_input_buffer()
        self.pending = bytearray()
        self.ser.write(msg)
        self.ser.flush()
        self.log("TX " + hx(msg))
        echo = self.get(len(msg), 0.3)  # K-line cables normally echo what we send
        if echo != msg:
            self.pending = bytearray(echo)  # no echo: this is already (part of) a reply

    def recv(self, timeout=1.5):
        h = self.get(1, timeout)
        if not h:
            return None
        rest = self.get(2, 0.3)
        if len(rest) < 2:
            self.log("RX incomplete header: " + hx(h + rest))
            return None
        n = h[0] & 0x3F
        extra = b""
        if n == 0:
            extra = self.get(1, 0.3)
            if not extra:
                return None
            n = extra[0]
        data = self.get(n, 0.5)
        cs = self.get(1, 0.3)
        raw = h + rest + extra + data + cs
        self.log("RX " + hx(raw))
        if len(data) < n or not cs:
            self.log("   (incomplete reply)")
            return None
        if (sum(raw[:-1]) & 0xFF) != cs[0]:
            self.log("   (checksum mismatch)")
        return data

    def request(self, target, data, timeout=1.5, functional=False):
        r = self._request(target, data, timeout, functional)
        if r is None:
            self.last_fail = time.time()
        else:
            self.last_ok = time.time()
        return r

    def _request(self, target, data, timeout=1.5, functional=False):
        self.send(self.frame(target, data, functional))
        for _ in range(20):
            r = self.recv(timeout)
            if r is None:
                return None
            if len(r) >= 3 and r[0] == 0x7F and r[2] == 0x78:
                self.log("   (module busy, waiting)")
                continue
            return r
        return None

    def start(self, target, functional=False):
        """Fast init (25 ms low / 25 ms high), then StartCommunication."""
        self.ser.reset_input_buffer()
        self.ser.break_condition = True
        wait(0.025)
        self.ser.break_condition = False
        wait(0.025)
        r = self.request(target, [0x81], timeout=1.0, functional=functional)
        return bool(r) and r[0] == 0xC1

    def stop(self, target, functional=False):
        try:
            self.request(target, [0x82], timeout=0.5, functional=functional)
        except Exception:
            pass


def ascii_part(b):
    return "".join(chr(x) if 32 <= x < 127 else "." for x in b)


PALETTES = {
    "dark": dict(
        BG="#14151a", PANEL="#1d1f26", FIELD="#2a2d37", FG="#e6e8ee", MUTED="#8b90a0", ACCENT="#1c69d4",
        CARD="#181a20", LOGBG="#0f1014", BTN="#2f323d", BTN_HOVER="#3b3f4d", STRONG="#ffffff",
        GOOD="#4cd964", BAD="#ff6b6b", WARN="#ffb454", HEADBLUE="#6aa9ff", BODY="#4b5263",
        GLASS="#9fb4d0", WHEEL="#262830", TRACK="#2c2f3a",
    ),
    "light": dict(
        BG="#ffffff", PANEL="#f1f3f8", FIELD="#ffffff", FG="#1c1f26", MUTED="#6b7280", ACCENT="#1c69d4",
        CARD="#ffffff", LOGBG="#fbfbfd", BTN="#e3e7ee", BTN_HOVER="#d3d9e4", STRONG="#101218",
        GOOD="#1a9b3c", BAD="#d13b3b", WARN="#e8912d", HEADBLUE="#1c69d4", BODY="#8793a8",
        GLASS="#cfdced", WHEEL="#c9ced8", TRACK="#dde2ea",
    ),
}
THEME = "dark"


def set_theme(name):
    """Switches the colour palette (call before any window is built)."""
    global THEME
    THEME = name if name in PALETTES else "dark"
    globals().update(PALETTES[THEME])


set_theme("dark")


def draw_car(c, ox=0, oy=0):
    """A simple side-view sedan drawing (front of the car on the right)."""

    def P(*pts):
        return [v + (ox if i % 2 == 0 else oy) for i, v in enumerate(pts)]

    c.create_polygon(
        P(8, 66, 8, 50, 40, 44, 70, 40, 96, 16, 172, 16, 204, 40, 244, 46, 256, 58, 252, 66),
        fill=BODY, outline="",
    )
    c.create_polygon(P(80, 38, 100, 20, 170, 20, 194, 38), fill=GLASS, outline="")
    c.create_line(P(134, 20, 134, 38), fill=BODY, width=3)
    c.create_line(P(12, 56, 250, 56), fill=ACCENT, width=2)
    c.create_rectangle(P(8, 48, 14, 54), fill="#d9463e", outline="")
    c.create_rectangle(P(246, 48, 255, 54), fill="#f4f1dd", outline="")
    for cx in (60, 204):
        c.create_oval(P(cx - 18, 50, cx + 18, 86), fill=BG, outline="")
        c.create_oval(P(cx - 15, 53, cx + 15, 83), fill=WHEEL, outline=MUTED, width=2)
        c.create_oval(P(cx - 6, 62, cx + 6, 74), fill=MUTED, outline="")


class Gauge:
    """A round gauge drawn on a canvas; the arc changes colour in warning zones."""

    def __init__(self, parent, label, unit, lo, hi, decimals=0, warn=None, danger=None, low_warn=None, low_danger=None):
        self.lo, self.hi, self.dec = lo, hi, decimals
        self.warn, self.danger, self.low_warn, self.low_danger = warn, danger, low_warn, low_danger
        self.shown = "—"
        self.unit = unit
        c = self.c = tk.Canvas(parent, width=200, height=190, bg=PANEL, highlightthickness=0)
        cx, cy, r = 100, 95, 70
        self.box = (cx - r, cy - r, cx + r, cy + r)
        c.create_arc(*self.box, start=225, extent=-270, style="arc", width=14, outline=TRACK)
        for i in range(11):
            a = math.radians(225 - 27 * i)
            c.create_line(cx + 80 * math.cos(a), cy - 80 * math.sin(a),
                          cx + 86 * math.cos(a), cy - 86 * math.sin(a), fill=MUTED)
        self.arc = c.create_arc(*self.box, start=225, extent=-0.1, style="arc", width=14, outline=ACCENT)
        self.value = c.create_text(cx, cy - 2, text="—", fill=STRONG, font=("Segoe UI", 24, "bold"))
        c.create_text(cx, cy + 26, text=unit, fill=MUTED, font=("Segoe UI", 10))
        c.create_text(cx - 32, cy + 70, text=f"{lo:g}", fill=MUTED, font=("Segoe UI", 8))
        c.create_text(cx + 32, cy + 70, text=f"{hi:g}", fill=MUTED, font=("Segoe UI", 8))
        c.create_text(cx, 178, text=label.upper(), fill=MUTED, font=("Segoe UI", 8, "bold"))

    def color(self, v):
        if (self.danger is not None and v >= self.danger) or (self.low_danger is not None and v <= self.low_danger):
            return BAD
        if (self.warn is not None and v >= self.warn) or (self.low_warn is not None and v <= self.low_warn):
            return WARN
        return ACCENT

    def set(self, v):
        if v is None:
            self.shown = "n/a"
            self.c.itemconfig(self.value, text="n/a")
            self.c.itemconfig(self.arc, extent=-0.1, outline=ACCENT)
            return
        frac = min(1.0, max(0.0, (v - self.lo) / (self.hi - self.lo)))
        self.shown = f"{v:.{self.dec}f}"
        self.c.itemconfig(self.arc, extent=-max(0.1, 270 * frac), outline=self.color(v))
        self.c.itemconfig(self.value, text=self.shown)

    def reset(self):
        self.shown = "—"
        self.c.itemconfig(self.value, text="—")
        self.c.itemconfig(self.arc, extent=-0.1, outline=ACCENT)


class Tip:
    """A small hover hint for a button."""

    def __init__(self, widget, text):
        self.w, self.text, self.tw = widget, text, None
        widget.bind("<Enter>", self.show, add="+")
        widget.bind("<Leave>", self.hide, add="+")
        widget.bind("<ButtonPress>", self.hide, add="+")

    def show(self, _e=None):
        if self.tw:
            return
        x = self.w.winfo_rootx() + 10
        y = self.w.winfo_rooty() + self.w.winfo_height() + 6
        self.tw = tk.Toplevel(self.w)
        self.tw.wm_overrideredirect(True)
        self.tw.wm_geometry(f"+{x}+{y}")
        tk.Label(self.tw, text=self.text, bg=CARD, fg=FG, relief="solid", borderwidth=1,
                 padx=8, pady=4, font=("Segoe UI", 9)).pack()

    def hide(self, _e=None):
        if self.tw:
            self.tw.destroy()
            self.tw = None


# pid -> (label, unit, lowest, highest, decimals, warning zones) for the round gauges
GAUGES = {
    0x0C: ("Engine speed", "rpm", 0, 7000, 0, dict(warn=5500, danger=6500)),
    0x0D: ("Vehicle speed", "km/h", 0, 240, 0, {}),
    0x05: ("Coolant temperature", "°C", 40, 130, 0, dict(warn=105, danger=115)),
    0x42: ("Battery voltage", "V", 10, 16, 1, dict(low_warn=12.0, low_danger=11.5, warn=15.0, danger=15.5)),
}


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.settings_path = os.path.join(os.path.expanduser("~"), "e60_settings.json")
        self.settings = self.read_settings()
        set_theme(self.settings.get("theme", "dark"))
        self.title("BMW E60 diagnostics (read-only)")
        self.geometry("1080x840")
        self.minsize(1020, 660)
        try:
            self.iconbitmap(resource("e60_icon.ico"))
        except Exception:
            pass
        self.restart = False
        self.k = None
        self.busy = False
        self.cancel = False
        self.cable_found = False
        self.ticks = 0
        self.last_faults = []
        self.q = queue.Queue()
        self.db = FaultDB()
        self.logfile = os.path.join(os.path.expanduser("~"), "e60_log.txt")
        self.style_ui()

        # ---- header: title, status lights, car picture ----
        head = tk.Frame(self, bg=BG)
        head.pack(fill="x")
        left = tk.Frame(head, bg=BG)
        left.pack(side="left", padx=22, pady=14)
        tk.Label(left, text="BMW E60", font=("Segoe UI", 26, "bold"), fg=STRONG, bg=BG).pack(anchor="w")
        tk.Label(left, text="K-line diagnostics  ·  read-only", font=("Segoe UI", 11), fg=MUTED, bg=BG).pack(anchor="w")
        self.art = tk.Canvas(head, width=290, height=100, bg=BG, highlightthickness=0)
        self.art.pack(side="right", padx=16)
        self.show_art()
        mid = tk.Frame(head, bg=BG)
        mid.pack(side="left", fill="both", expand=True, padx=26)
        lights = tk.Frame(mid, bg=BG)
        lights.pack(anchor="w", pady=(24, 0))
        self.lights = {}
        for key, text in (("cable", "Cable"), ("port", "Port"), ("car", "Car")):
            f = tk.Frame(lights, bg=BG)
            f.pack(side="left", padx=(0, 22))
            dot = tk.Canvas(f, width=14, height=14, bg=BG, highlightthickness=0)
            oval = dot.create_oval(2, 2, 12, 12, fill=MUTED, outline="")
            dot.pack(side="left")
            lbl = tk.Label(f, text=text, font=("Segoe UI", 11), fg=FG, bg=BG)
            lbl.pack(side="left", padx=(7, 0))
            self.lights[key] = (dot, oval, lbl)
        self.next_step = tk.Label(mid, text="", anchor="w", justify="left", wraplength=420,
                                  font=("Segoe UI", 11), fg=MUTED, bg=BG)
        self.next_step.pack(anchor="w", pady=(10, 0))

        # ---- bottom bar ----
        bar = tk.Frame(self, bg=BG)
        bar.pack(side="bottom", fill="x")
        self.status = tk.StringVar(value="Port closed")
        tk.Label(bar, textvariable=self.status, anchor="w", bg=BG, fg=MUTED, padx=16, pady=7,
                 font=("Segoe UI", 10)).pack(side="left")
        b = ttk.Button(bar, text="Light theme" if THEME == "dark" else "Dark theme", style="Small.TButton", command=self.toggle_theme)
        b.pack(side="right", padx=(0, 14), pady=4)
        Tip(b, "Switch between the dark and the light look (the program restarts its window)")
        b = ttk.Button(bar, text="Look up online", style="Small.TButton", command=self.lookup)
        b.pack(side="right", padx=6, pady=4)
        Tip(b, "Search the web for the faults you read last")
        b = ttk.Button(bar, text="Copy this tab", style="Small.TButton", command=self.copy)
        b.pack(side="right", padx=6, pady=4)
        Tip(b, "Copy the text of the tab you are looking at")

        # ---- connection ----
        ctl = ttk.Frame(self, padding=(16, 14, 16, 0))
        ctl.pack(fill="x")
        ttk.Label(ctl, text="PORT", style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        self.port = ttk.Combobox(ctl, width=16, state="readonly")
        self.port.grid(row=1, column=0)
        b = ttk.Button(ctl, text="↻", width=3, command=self.refresh)
        b.grid(row=1, column=1, padx=4)
        Tip(b, "Look for the cable again")
        self.btn = ttk.Button(ctl, text="Open port", style="Accent.TButton", command=self.toggle)
        self.btn.grid(row=1, column=2, padx=(4, 0))
        Tip(self.btn, "Connect to the cable. Do this first.")

        sel = ttk.Frame(self, padding=(16, 10, 16, 0))
        sel.pack(fill="x")
        ttk.Label(sel, text="MODULE", style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(sel, text="VARIANT  (pick the one for your engine / car)", style="Muted.TLabel").grid(row=0, column=1, sticky="w", padx=(14, 0))
        self.mod = ttk.Combobox(sel, width=34, state="readonly")
        self.mod.grid(row=1, column=0)
        self.var = ttk.Combobox(sel, width=58, state="readonly")
        self.var.grid(row=1, column=1, padx=(14, 0), sticky="we")
        sel.columnconfigure(1, weight=1)
        self.mod.bind("<<ComboboxSelected>>", lambda e: self.on_module())
        self.var.bind("<<ComboboxSelected>>", lambda e: self.remember())
        self.port.bind("<<ComboboxSelected>>", lambda e: self.remember())
        addrs = self.db.addresses()
        if not addrs:
            addrs = [(a, ADDR_NAMES.get(a, "Module")) for a in QUICK]
        self.mod["values"] = [f"{a:02X}  {ADDR_NAMES.get(a, n or 'Module')[:40]}" for a, n in addrs]
        saved_mod = self.settings.get("module")
        self.mod.set(saved_mod if saved_mod in self.mod["values"] else "12  " + ADDR_NAMES[0x12])
        self.fill_variants()

        # ---- action buttons, in groups ----
        acts = ttk.Frame(self, padding=(16, 14, 16, 6))
        acts.pack(fill="x")

        def group(col, title, buttons):
            ttk.Label(acts, text=title, style="Muted.TLabel").grid(row=0, column=col, sticky="w")
            f = ttk.Frame(acts)
            f.grid(row=1, column=col, sticky="w", padx=(0, 26))
            for text, style, cmd, tip in buttons:
                bt = ttk.Button(f, text=text, style=style, command=cmd)
                bt.pack(side="left", padx=(0, 8))
                Tip(bt, tip)

        group(0, "CHECK THE CAR", [
            ("✓ Health check", "Accent.TButton", lambda: self.run(self.health, scan=True),
             "Ask the main modules and read every fault memory. Start here."),
            ("Quick scan", "TButton", lambda: self.run(self.scan_quick, scan=True),
             "Ask the 14 most likely modules which ones are in the car"),
            ("Full scan", "TButton", lambda: self.run(self.scan_full, scan=True),
             "Ask all known modules (takes a couple of minutes)"),
        ])
        group(1, "ONE MODULE", [
            ("Identify", "TButton", lambda: self.run(self.ident),
             "Read the identification of the module chosen above"),
            ("Read faults", "Accent.TButton", lambda: self.run(self.faults),
             "Read the fault memory of the module chosen above"),
            ("▶ Live data", "Accent.TButton", lambda: self.run(self.live, scan=True),
             "Show engine values live: speed, temperatures, battery voltage"),
        ])
        group(2, "", [("■ Stop", "Danger.TButton", self.stop_scan, "Stop the running scan or live data")])

        # ---- tabs ----
        self.tabs = ttk.Notebook(self)
        self.tabs.pack(fill="both", expand=True, padx=16, pady=(6, 8))
        self.tab_over = ttk.Frame(self.tabs, padding=16)
        self.tab_res = ttk.Frame(self.tabs)
        self.tab_live = ttk.Frame(self.tabs, padding=14)
        self.tab_log = ttk.Frame(self.tabs)
        self.tabs.add(self.tab_over, text="  Overview  ")
        self.tabs.add(self.tab_res, text="  Results  ")
        self.tabs.add(self.tab_live, text="  Live data  ")
        self.tabs.add(self.tab_log, text="  Technical log  ")

        # overview: one card per module
        self.over_title = tk.Label(self.tab_over, text="Car health", anchor="w", font=("Segoe UI", 20, "bold"), fg=STRONG, bg=PANEL)
        self.over_title.pack(fill="x")
        self.over_sub = tk.Label(
            self.tab_over, anchor="w", justify="left", font=("Segoe UI", 11), fg=MUTED, bg=PANEL,
            text="Press ✓ Health check to ask the car's modules and read every fault memory.\n"
                 "Each module becomes a card: green means no faults, orange means faults. Click a card for details.",
        )
        self.over_sub.pack(fill="x", pady=(2, 0))
        self.over_grid = tk.Frame(self.tab_over, bg=PANEL)
        self.over_grid.pack(fill="both", expand=True, pady=(12, 0))
        for c in range(3):
            self.over_grid.columnconfigure(c, weight=1, uniform="over")

        # live data: round gauges + value cards
        self.live_info = tk.Label(
            self.tab_live, text="Press ▶ Live data to read the engine computer. Press ■ Stop to end.",
            anchor="w", bg=PANEL, fg=MUTED, font=("Segoe UI", 11),
        )
        self.live_info.pack(fill="x")
        self.gauge_row = tk.Frame(self.tab_live, bg=PANEL)
        self.gauge_row.pack(fill="x", pady=(8, 4))
        self.gauges = {}
        for pid, (label, unit, lo, hi, dec, zones) in GAUGES.items():
            self.gauges[pid] = Gauge(self.gauge_row, label, unit, lo, hi, dec, **zones)
        self.live_grid = tk.Frame(self.tab_live, bg=PANEL)
        self.live_grid.pack(fill="both", expand=True, pady=(4, 0))
        for c in range(3):
            self.live_grid.columnconfigure(c, weight=1, uniform="live")
        self.live_vals = {}
        for pid, (label, unit, _f, _d) in LIVE.items():
            if pid in GAUGES:
                continue
            card = tk.Frame(self.live_grid, bg=CARD, padx=16, pady=10)
            tk.Label(card, text=label.upper(), font=("Segoe UI", 8, "bold"), fg=MUTED, bg=CARD).pack(anchor="w")
            v = tk.StringVar(value="—")
            tk.Label(card, textvariable=v, font=("Segoe UI", 24, "bold"), fg=STRONG, bg=CARD).pack(anchor="w")
            tk.Label(card, text=unit, font=("Segoe UI", 9), fg=MUTED, bg=CARD).pack(anchor="w")
            self.live_vals[pid] = (v, card)
        self.live_init(list(LIVE), None)

        # results: readable fault cards
        self.res = tk.Text(
            self.tab_res, font=("Segoe UI", 11), state="disabled", bg=CARD, fg=FG, relief="flat",
            padx=20, pady=14, wrap="word", cursor="arrow", spacing1=2, spacing3=2,
        )
        rsb = ttk.Scrollbar(self.tab_res, command=self.res.yview)
        self.res.config(yscrollcommand=rsb.set)
        rsb.pack(side="right", fill="y")
        self.res.pack(side="left", fill="both", expand=True)
        r = self.res
        r.tag_config("h1", font=("Segoe UI", 17, "bold"), foreground=STRONG, spacing1=2, spacing3=2)
        r.tag_config("sub", font=("Segoe UI", 10), foreground=MUTED, spacing3=8)
        r.tag_config("chip", font=("Consolas", 12, "bold"), foreground="#14151a", background=WARN, spacing1=16)
        r.tag_config("meaning", font=("Segoe UI", 12, "bold"), foreground=STRONG, spacing1=16)
        r.tag_config("orig", font=("Segoe UI", 10), foreground=MUTED, lmargin1=18, lmargin2=18, spacing3=2)
        r.tag_config("item", font=("Segoe UI", 11), foreground=FG, lmargin1=18, lmargin2=34, spacing3=2)
        r.tag_config("ok", font=("Segoe UI", 13, "bold"), foreground=GOOD, spacing1=10)
        r.tag_config("bad", font=("Segoe UI", 11, "bold"), foreground=BAD, spacing1=6)
        r.tag_config("good", font=("Segoe UI", 12, "bold"), foreground=GOOD)
        r.tag_config("body", font=("Segoe UI", 11), foreground=FG, spacing3=4)
        r.tag_config("hint", font=("Segoe UI", 10), foreground=MUTED, spacing1=14)

        # technical log
        self.text = tk.Text(
            self.tab_log, font=("Consolas", 9), state="disabled", bg=LOGBG, fg=FG,
            relief="flat", padx=10, pady=8, wrap="word", insertbackground=FG,
        )
        sb = ttk.Scrollbar(self.tab_log, command=self.text.yview)
        self.text.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.text.pack(side="left", fill="both", expand=True)
        self.text.tag_config("tx", foreground=MUTED)
        self.text.tag_config("rx", foreground=GOOD)
        self.text.tag_config("head", foreground=HEADBLUE, font=("Consolas", 9, "bold"))
        self.text.tag_config("good", foreground=GOOD, font=("Consolas", 9, "bold"))
        self.text.tag_config("bad", foreground=BAD)
        self.text.tag_config("fault", foreground=WARN, font=("Consolas", 9, "bold"))

        self.refresh()
        self.render_welcome()
        self.log(f"Technical log, also saved to {self.logfile}")
        if not self.db.con:
            self.log("ERROR: fault database e60_data.db not found - only fault numbers will be shown.")
        self.after(100, self.drain)
        self.tick()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def style_ui(self):
        self.configure(bg=PANEL)
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure(".", background=PANEL, foreground=FG, fieldbackground=FIELD, font=("Segoe UI", 10))
        st.configure("TFrame", background=PANEL)
        st.configure("TLabel", background=PANEL, foreground=FG)
        st.configure("Muted.TLabel", foreground=MUTED, font=("Segoe UI", 8, "bold"))
        st.configure("TButton", background=BTN, foreground=FG, padding=(14, 8), borderwidth=0, focuscolor=PANEL, font=("Segoe UI", 10))
        st.map("TButton", background=[("active", BTN_HOVER)])
        st.configure("Small.TButton", background=BTN, foreground=FG, padding=(10, 4), borderwidth=0, focuscolor=BG, font=("Segoe UI", 9))
        st.map("Small.TButton", background=[("active", BTN_HOVER)])
        st.configure("Accent.TButton", background=ACCENT, foreground="white")
        st.map("Accent.TButton", background=[("active", "#2a7de8")])
        st.configure("Danger.TButton", background="#b4443e", foreground="white")
        st.map("Danger.TButton", background=[("active", "#cf544d")])
        st.configure("TCombobox", fieldbackground=FIELD, background=BTN, foreground=FG, arrowcolor=FG, padding=5)
        st.map("TCombobox", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", FG)])
        st.configure("Vertical.TScrollbar", background=BTN, troughcolor=PANEL, arrowcolor=FG)
        st.configure("TNotebook", background=PANEL, borderwidth=0)
        st.configure("TNotebook.Tab", background=BTN, foreground=MUTED, padding=(18, 9), borderwidth=0, font=("Segoe UI", 10, "bold"))
        st.map("TNotebook.Tab", background=[("selected", ACCENT)], foreground=[("selected", "white")])
        self.option_add("*TCombobox*Listbox.background", FIELD)
        self.option_add("*TCombobox*Listbox.foreground", FG)

    def show_art(self):
        """Shows e60.png from the program's folder if you put one there, else a drawing."""
        try:
            img = tk.PhotoImage(file=os.path.join(app_dir(), "e60.png"))
            f = max(-(-img.width() // 280), -(-img.height() // 100), 1)
            self.photo = img.subsample(f)
            self.art.create_image(145, 50, image=self.photo)
        except Exception:
            draw_car(self.art, 16, 6)

    # ---- status lights ----
    def set_light(self, key, color, text):
        dot, oval, lbl = self.lights[key]
        dot.itemconfig(oval, fill=color)
        lbl.config(text=text)

    def tick(self):
        """Twice a second: refresh the status lights; every 2 seconds look for the cable."""
        self.ticks += 1
        if self.ticks % 4 == 1:
            try:
                real = [p.device for p in list_ports.comports()]
            except Exception:
                real = []
            self.cable_found = bool(real)
            values = real + [DEMO]
            if list(self.port["values"]) != values:
                self.port["values"] = values
                if self.port.get() not in values:
                    self.port.set(values[0])
        self.update_lights()
        self.after(500, self.tick)

    def update_lights(self):
        demo = self.port.get() == DEMO
        cable_ok = self.cable_found or demo
        opened = self.k is not None
        now = time.time()
        ok = getattr(self.k, "last_ok", None) if opened else None
        fail = getattr(self.k, "last_fail", None) if opened else None
        self.set_light("cable", GOOD if cable_ok else BAD, "Cable found" if cable_ok else "No cable found")
        self.set_light("port", GOOD if opened else MUTED, "Port open" if opened else "Port closed")
        if not opened:
            self.set_light("car", MUTED, "Car")
        elif ok and now - ok < 30:
            self.set_light("car", GOOD, "Car answering")
        elif fail:
            self.set_light("car", BAD, "Car not answering")
        else:
            self.set_light("car", WARN, "Car not asked yet")
        if not cable_ok:
            step = "Plug the cable into the PC."
        elif not opened:
            step = "Choose the port and press Open port."
        elif ok and now - ok < 30:
            step = "Connected to the car. Press ✓ Health check, or pick a module and press Read faults."
        elif fail:
            step = "The car is not answering. Is the ignition on, and the cable switch on K-line?"
        else:
            step = "Port is open. Press ✓ Health check."
        self.next_step.config(text=step)

    def toggle_theme(self):
        self.settings["theme"] = "light" if THEME == "dark" else "dark"
        self.restart = True
        self.on_close()

    # ---- logging (thread safe) ----
    def log(self, s):
        self.q.put(f"{time.strftime('%H:%M:%S')}  {s}")

    @staticmethod
    def tag_for(line):
        body = line[10:].strip()
        if body.startswith(("TX", "DE:")):
            return "tx"
        if body.startswith("RX"):
            return "rx"
        if body.startswith("---"):
            return "head"
        if body.startswith("FAULT"):
            return "fault"
        if body.startswith("EN:"):
            return "desc"
        if ">>>" in body:
            return "good"
        if body.startswith(("ERROR", "No answer", "No reply", "Module refused", "Unexpected")):
            return "bad"
        return ""

    def drain(self):
        lines = []
        while not self.q.empty():
            item = self.q.get()
            if isinstance(item, tuple):
                if item[0] == "status":
                    self.status.set(item[1])
                elif item[0] == "variant":
                    self.set_variant(item[1])
                    self.remember()
                elif item[0] == "live":
                    self.live_set(item[1], item[2])
                elif item[0] == "live_init":
                    self.live_init(item[1], item[2])
                    self.tabs.select(self.tab_live)
                elif item[0] == "health":
                    self.render_health(item[1], item[2], item[3], item[4])
                    self.tabs.select(self.tab_over)
                elif item[0] == "live_state":
                    self.live_info.config(text=item[1])
                elif item[0] == "show":
                    try:
                        self.render(item[1], item[2])
                    except Exception as e:
                        self.text.config(state="normal")
                        self.text.insert("end", f"ERROR drawing results: {e}\n")
                        self.text.config(state="disabled")
            else:
                lines.append(item)
        if lines:
            self.text.config(state="normal")
            for line in lines:
                tag = self.tag_for(line)
                self.text.insert("end", line + "\n", (tag,) if tag else ())
            self.text.see("end")
            self.text.config(state="disabled")
            try:
                with open(self.logfile, "a", encoding="utf-8") as f:
                    f.write("\n".join(lines) + "\n")
            except Exception:
                pass
        self.after(100, self.drain)

    def live_text(self):
        lines = []
        for pid, (label, unit, _f, _d) in LIVE.items():
            val = self.gauges[pid].shown if pid in self.gauges else self.live_vals[pid][0].get()
            lines.append(f"{label}: {val} {unit}")
        return "\n".join(lines)

    def copy(self):
        cur = str(self.tabs.select())
        if cur == str(self.tab_live):
            txt = self.live_text()
        elif cur == str(self.tab_log):
            txt = self.text.get("1.0", "end")
        elif cur == str(self.tab_over):
            txt = getattr(self, "health_text", "") or self.over_title["text"]
        else:
            txt = self.res.get("1.0", "end")
        self.clipboard_clear()
        self.clipboard_append(txt)

    # ---- port / selection ----
    def refresh(self):
        ports = [p.device for p in list_ports.comports()] + [DEMO]
        self.port["values"] = ports
        if not self.port.get():
            saved = self.settings.get("port")
            self.port.set(saved if saved in ports else ports[0])

    def toggle(self):
        if self.k:
            self.k.close()
            self.k = None
            self.btn.config(text="Open port")
            self.status.set("Port closed")
            self.log("Port closed")
            return
        try:
            self.k = KLine(self.port.get(), self.log)
        except Exception as e:
            messagebox.showerror("Cannot open port", str(e))
            return
        self.btn.config(text="Close port")
        self.status.set(f"Port {self.port.get()} open  ·  ready")
        self.log(f"Port {self.port.get()} open at {BAUD} baud")

    def target(self):
        try:
            return int(self.mod.get().split()[0], 16)
        except Exception:
            raise ValueError("Pick a module from the Module list.")

    def fill_variants(self):
        try:
            addr = self.target()
        except ValueError:
            return
        vs = self.db.variants(addr)
        values = [AUTO] + [f"{sg}  -  {rough_english(name)}" for sg, name in vs]
        self.var["values"] = values
        saved = self.settings.get("variants", {}).get(f"{addr:02X}")
        pick = next((v for v in values if saved and v.startswith(saved + "  -  ")), None)
        self.var.set(pick or (values[1] if len(vs) == 1 else AUTO))

    def on_module(self):
        self.fill_variants()
        self.remember()

    def read_settings(self):
        try:
            with open(self.settings_path, encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def remember(self):
        """Saves port, module and the variant chosen for each module."""
        self.settings["port"] = self.port.get()
        self.settings["module"] = self.mod.get()
        try:
            key = f"{self.target():02X}"
            variants = self.settings.setdefault("variants", {})
            sg = self.current_sgbd()
            if sg:
                variants[key] = sg
            else:
                variants.pop(key, None)
        except ValueError:
            pass
        try:
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(self.settings, f, indent=1)
        except Exception:
            pass

    def guess_variant(self, addr, codes):
        """Variants at this address that know every one of these fault codes."""
        sets = []
        for code in codes:
            rows = self.db.q(
                "select e.sgbd from dtc d join ecu e on e.sgbd=d.sgbd where e.addr=? and d.code=?", (addr, code))
            if rows:
                sets.append({r[0] for r in rows})
        return set.intersection(*sets) if sets else set()

    def set_variant(self, sgbd):
        for v in self.var["values"]:
            if v.startswith(sgbd + "  -  "):
                self.var.set(v)
                return

    def current_sgbd(self):
        v = self.var.get()
        return None if (not v or v.startswith("Auto")) else v.split()[0]

    def addr_name(self, a):
        return ADDR_NAMES.get(a) or next((n for x, n in self.db.addresses() if x == a), "Module")

    def stop_scan(self):
        self.cancel = True

    def run(self, fn, scan=False):
        if not self.k:
            return messagebox.showinfo("Port closed", "Press Open port first.")
        if self.busy:
            return
        try:
            ctx = None if scan else (self.target(), self.current_sgbd(), self.mod.get())
        except ValueError as e:
            return messagebox.showinfo("Module", str(e))
        self.busy = True
        self.cancel = False

        def work():
            self.q.put(("status", "Working…"))
            try:
                fn(ctx)
            except Exception as e:
                self.log(f"ERROR: {e}")
            finally:
                self.busy = False
                self.q.put(("status", "Ready"))

        threading.Thread(target=work, daemon=True).start()

    # ---- actions ----
    def show(self, kind, payload):
        self.q.put(("show", kind, payload))

    def scan_quick(self, ctx):
        self.scan(QUICK)

    def scan_full(self, ctx):
        self.scan([a for a, _ in self.db.addresses()] or QUICK)

    def scan(self, addrs):
        total = len(addrs)
        self.log(f"--- Scan: asking {total} modules to answer ---")
        found = []
        self.show("scan", dict(found=[], done=False, total=total, tried=0))
        for i, a in enumerate(addrs, 1):
            if self.cancel:
                self.log("Scan stopped.")
                return self.show("scan", dict(found=list(found), done=True, stopped=True, total=total, tried=i - 1))
            self.q.put(("status", f"Scanning {a:02X} {self.addr_name(a)} ({i} of {total}) …"))
            if self.k.start(a):
                found.append((a, self.addr_name(a)))
                self.log(f">>> {a:02X}  {self.addr_name(a)}  ANSWERED")
                self.k.stop(a)
                self.show("scan", dict(found=list(found), done=False, total=total, tried=i))
            time.sleep(0.3)
        self.log("--- Scan done ---")
        self.show("scan", dict(found=found, done=True, total=total, tried=total))

    def no_answer(self, name):
        self.log("No answer from module (see TX/RX lines above)")
        self.show("message", dict(
            title=name, level="bad",
            text="This module did not answer.\nCheck that the cable is plugged in at both ends, the ignition is on, "
                 "and that your car has this module. The Technical log tab shows what was sent.",
        ))

    def ident(self, ctx):
        t, sgbd, name = ctx
        self.log(f"--- Identify module {t:02X} ---")
        if not self.k.start(t):
            return self.no_answer(name)
        r = self.k.request(t, [0x1A, 0x80])
        if r and r[0] == 0x5A:
            text = ascii_part(r[2:])
            self.log("Identification text: " + text)
            hexs = "".join(f"{x:02X}" for x in r[2:])
            nums = set(re.findall(r"\d{7}", text)) | set(re.findall(r"(?=(\d{7}))", hexs))
            match = self.db.by_hwnr(t, nums)
            sg = next(iter(match)) if len(match) == 1 else None
            if sg:
                self.log(f"Part number matches variant {sg} - selected it for you.")
                self.q.put(("variant", sg))
            self.show("ident", dict(module=name, text=text, match=sg))
        else:
            self.show("message", dict(title=name, level="bad", text=self.explain(r)))
        self.k.stop(t)

    def faults(self, ctx):
        t, sgbd, name = ctx
        self.log(f"--- Fault memory of module {name} ---")
        if not self.k.start(t):
            return self.no_answer(name)
        r = self.k.request(t, [0x18, 0x00, 0xFF, 0x00])
        if r and r[0] == 0x58:
            body = r[2:]
            codes = [(f"{body[i]:02X}{body[i + 1]:02X}", body[i + 2]) for i in range(0, len(body) - 2, 3)]
            detected, candidates = None, []
            if not sgbd and codes:
                common = self.guess_variant(t, [c for c, _ in codes])
                if len(common) == 1:
                    detected = sgbd = next(iter(common))
                    self.log(f"Only variant {detected} knows all of these fault codes - selected it.")
                    self.q.put(("variant", detected))
                elif 1 < len(common) < len(self.db.variants(t)):
                    candidates = sorted(common)
            items = [self.explain_code(t, sgbd, raw, st) for raw, st in codes]
            self.last_faults = [(name, it["code"]) for it in items]
            path = self.save_report(name, sgbd, items)
            self.show("faults", dict(module=name, sgbd=sgbd, items=items, path=path,
                                     detected=detected, candidates=candidates, ncodes=len(codes)))
        else:
            self.show("message", dict(title=name, level="bad", text=self.explain(r)))
        self.k.stop(t)

    def explain_code(self, addr, sgbd, raw, st):
        """Looks up one fault code; returns a dict used by the result cards and the report."""
        self.log(f"FAULT {raw}  status {st:02X}")
        item = {"code": raw, "st": st, "groups": [], "note": "", "more": 0}
        if not self.db.con:
            item["note"] = "No fault database loaded."
            return item
        if sgbd:
            row = self.db.one(sgbd, raw)
            if not row:
                item["note"] = "Not in the database for this variant. Is the variant right?"
                return item
            en, rough, de = describe(row[0], row[1], raw)
            item["groups"].append({"en": en, "rough": rough, "de": de, "variants": ""})
            return item
        groups = self.db.many(addr, raw)
        if not groups:
            item["note"] = "Not found in any variant of this module."
            return item
        for de, en, sgs in groups[:4]:
            en_t, rough, de_t = describe(de, en, raw)
            who = ", ".join(sgs[:3]) + (f" +{len(sgs) - 3} more" if len(sgs) > 3 else "")
            item["groups"].append({"en": en_t, "rough": rough, "de": de_t, "variants": who})
        item["more"] = max(0, len(groups) - 4)
        return item

    @staticmethod
    def item_text(it):
        if not it["groups"]:
            return it["note"]
        return " / ".join(g["en"] + (f"  [DE: {g['de']}]" if g["de"] else "") for g in it["groups"][:2])

    def save_report(self, module, sgbd, items):
        folder = os.path.join(os.path.expanduser("~"), "Documents")
        if not os.path.isdir(folder):
            folder = os.path.expanduser("~")
        path = os.path.join(folder, "E60_fault_report.txt")
        try:
            with open(path, "a", encoding="utf-8") as f:
                f.write(f"\n=== {time.strftime('%Y-%m-%d %H:%M')}  {module}  variant: {sgbd or 'auto'} ===\n")
                if not items:
                    f.write("No stored faults\n")
                for it in items:
                    f.write(f"{it['code']}  {self.item_text(it)}\n")
            return path
        except Exception as e:
            self.log(f"ERROR: could not save report: {e}")
            return None

    # ---- health check ----
    def report_path(self):
        folder = os.path.join(os.path.expanduser("~"), "Documents")
        if not os.path.isdir(folder):
            folder = os.path.expanduser("~")
        return os.path.join(folder, "E60_fault_report.txt")

    def health(self, ctx):
        addrs = QUICK
        total = len(addrs)
        self.log("--- Health check ---")
        results = []
        self.q.put(("health", [], False, total, 0))
        for i, a in enumerate(addrs, 1):
            if self.cancel:
                self.log("Health check stopped.")
                self.q.put(("health", list(results), True, total, i - 1))
                break
            self.q.put(("status", f"Health check: {a:02X} {self.addr_name(a)} ({i} of {total}) …"))
            if self.k.start(a):
                entry = {"addr": a, "name": self.addr_name(a), "state": "answered", "count": 0}
                r = self.k.request(a, [0x18, 0x00, 0xFF, 0x00])
                if r and r[0] == 0x58:
                    body = r[2:]
                    n = sum(1 for j in range(0, len(body) - 2, 3) if body[j] or body[j + 1])
                    entry.update(state="faults" if n else "ok", count=n)
                self.k.stop(a)
                results.append(entry)
                self.log(f">>> {a:02X}  {entry['name']}  {entry['state']} ({entry['count']})")
                self.q.put(("health", list(results), False, total, i))
            time.sleep(0.3)
        else:
            self.q.put(("health", results, True, total, total))
        try:
            with open(self.report_path(), "a", encoding="utf-8") as f:
                f.write(f"\n=== {time.strftime('%Y-%m-%d %H:%M')}  Health check ===\n")
                for e in results:
                    f.write(f"{e['addr']:02X}  {e['name']}: " + (f"{e['count']} fault(s)" if e["state"] == "faults" else
                            "no faults" if e["state"] == "ok" else "answered") + "\n")
                if not results:
                    f.write("No module answered\n")
        except Exception as e:
            self.log(f"ERROR: could not save report: {e}")

    def render_health(self, results, done, total, tried):
        for w in self.over_grid.winfo_children():
            w.destroy()
        answered = len(results)
        faulty = sum(1 for r in results if r["state"] == "faults")
        if not done:
            title, color = f"Checking the car …  {tried} of {total}", STRONG
            sub = "Modules appear below as they answer."
        elif not answered:
            title, color = "No module answered", BAD
            sub = "Check that the ignition is on, the cable is plugged in at both ends and its switch is on K-line."
        elif not faulty:
            title, color = f"✓ All good: {answered} modules answered, no faults", GOOD
            sub = "Click a card to see more about that module."
        else:
            title = f"{faulty} of {answered} modules report faults"
            color = WARN
            sub = "Click an orange card to see what the faults mean."
        self.over_title.config(text=title, fg=color)
        self.over_sub.config(text=sub)
        lines = [title]
        for i, r in enumerate(results):
            self.health_card(i, r)
            lines.append(f"{r['addr']:02X}  {r['name']}: " + (f"{r['count']} fault(s)" if r["state"] == "faults"
                         else "no faults" if r["state"] == "ok" else "answered"))
        self.health_text = "\n".join(lines)

    def health_card(self, i, r):
        color = {"ok": GOOD, "faults": WARN}.get(r["state"], MUTED)
        status = {"ok": "✓  No faults", "faults": f"⚠  {r['count']} fault{'s' if r['count'] != 1 else ''}"}.get(r["state"], "Answered")
        card = tk.Frame(self.over_grid, bg=CARD, cursor="hand2")
        bar = tk.Frame(card, bg=color, width=6)
        bar.pack(side="left", fill="y")
        body = tk.Frame(card, bg=CARD, padx=14, pady=12)
        body.pack(side="left", fill="both", expand=True)
        tk.Label(body, text=r["name"], font=("Segoe UI", 12, "bold"), fg=STRONG, bg=CARD, anchor="w").pack(fill="x")
        tk.Label(body, text=f"Address {r['addr']:02X}", font=("Segoe UI", 9), fg=MUTED, bg=CARD, anchor="w").pack(fill="x")
        tk.Label(body, text=status, font=("Segoe UI", 13, "bold"), fg=color, bg=CARD, anchor="w").pack(fill="x", pady=(6, 0))
        card.grid(row=i // 3, column=i % 3, padx=6, pady=6, sticky="nsew")
        for w in (card, bar, body, *body.winfo_children()):
            w.bind("<Button-1>", lambda e, a=r["addr"]: self.open_module(a))

    def open_module(self, addr):
        """Clicking a card: choose that module and read its faults."""
        if self.busy:
            return
        for v in self.mod["values"]:
            if v.startswith(f"{addr:02X}  "):
                self.mod.set(v)
                self.on_module()
                break
        self.run(self.faults)

    # ---- live data ----
    def live_init(self, pids, text):
        for g in self.gauges.values():
            g.c.grid_forget()
            g.reset()
        for v, card in self.live_vals.values():
            card.grid_forget()
            v.set("—")
        for i, pid in enumerate(p for p in GAUGES if p in pids):
            self.gauges[pid].c.grid(row=0, column=i, padx=6, pady=4)
        for i, pid in enumerate(p for p in LIVE if p in pids and p not in GAUGES):
            self.live_vals[pid][1].grid(row=i // 3, column=i % 3, padx=6, pady=6, sticky="nsew")
        if text:
            self.live_info.config(text=text)

    def live_set(self, pid, value):
        if pid in self.gauges:
            self.gauges[pid].set(value)
        else:
            self.live_vals[pid][0].set("n/a" if value is None else f"{value:.{LIVE[pid][3]}f}")

    def read_pid(self, t, pid, functional):
        r = self.k.request(t, [0x01, pid], timeout=0.8, functional=functional)
        if r and len(r) >= 2 and r[0] == 0x41 and r[1] == pid:
            return list(r[2:])
        return None

    def discover_pids(self, t, functional):
        """Asks which standard live values the engine computer offers."""
        supported, base = set(), 0x00
        while base <= 0x40:
            d = self.read_pid(t, base, functional)
            if not d or len(d) < 4:
                break
            for i in range(32):
                if d[i // 8] & (0x80 >> (i % 8)):
                    supported.add(base + i + 1)
            if (base + 0x20) not in supported:
                break
            base += 0x20
        return supported

    def live_connect(self):
        """Tries the engine computer directly, then the standard OBD-II address."""
        k = self.k
        if k.start(0x12) and self.read_pid(0x12, 0x00, False) is not None:
            return 0x12, False
        k.stop(0x12)
        time.sleep(0.5)
        if k.start(0x33, functional=True) and self.read_pid(0x33, 0x00, True) is not None:
            return 0x33, True
        k.stop(0x33, functional=True)
        return None

    def live(self, ctx):
        self.log("--- Live data ---")
        self.q.put(("status", "Connecting to the engine computer …"))
        conn = self.live_connect()
        if not conn:
            return self.show("message", dict(
                title="Live data", level="bad",
                text="The engine computer did not answer the standard live-data requests.\n"
                     "Check the cable and ignition, and that this car's engine computer supports standard "
                     "OBD-II over the K-line. The Technical log tab shows what was sent.",
            ))
        t, functional = conn
        supported = self.discover_pids(t, functional)
        pids = [p for p in LIVE if p in supported] or list(LIVE)
        how = "directly" if not functional else "through the standard OBD-II address"
        self.q.put(("live_init", pids, f"Reading the engine computer {how}. About one update per second. Press Stop to end."))
        self.q.put(("status", "Live data running …"))
        orig = self.k.log
        self.k.log = lambda s: None  # don't flood the technical log
        bad_cycles = 0
        try:
            while not self.cancel and bad_cycles < 3:
                got = 0
                for p in pids:
                    if self.cancel:
                        break
                    d = self.read_pid(t, p, functional)
                    val = None
                    if d:
                        try:
                            val = LIVE[p][2](d)
                            got += 1
                        except Exception:
                            val = None
                    self.q.put(("live", p, val))
                bad_cycles = bad_cycles + 1 if got == 0 and not self.cancel else 0
        finally:
            self.k.log = orig
            self.k.stop(t, functional)
            self.q.put(("live_state", "Connection lost. Press Live data to try again." if bad_cycles >= 3
                        else "Stopped. Press Live data to start again."))

    # ---- result cards ----
    def res_clear(self):
        self.res.config(state="normal")
        self.res.delete("1.0", "end")
        self.res.config(state="disabled")

    def res_add(self, text, *tags):
        self.res.config(state="normal")
        self.res.insert("end", text, tags)
        self.res.config(state="disabled")

    def render(self, kind, payload):
        getattr(self, "render_" + kind)(payload)
        self.tabs.select(self.tab_res)

    def render_welcome(self):
        self.res_clear()
        self.res_add("Welcome\n", "h1")
        self.res_add("Read the fault memory of your BMW E60 and see what each fault means.\n", "sub")
        for i, s in enumerate([
            "Plug the cable into the car and the PC, and turn the ignition on.",
            "Choose the port above and press Open port.",
            "Press Quick scan to see which modules answer.",
            "Pick a module and your variant, then press Read faults.",
            "Press Live data to watch engine values such as speed, temperatures and battery voltage.",
        ], 1):
            self.res_add(f"{i}.  {s}\n", "item")
        self.res_add("\nNo car handy? Choose 'Demo (no car)' as the port to try the program.\n", "hint")
        if not self.db.con:
            self.res_add("\nThe fault database (e60_data.db) was not found, so only fault numbers can be shown.\n", "bad")

    def render_message(self, p):
        self.res_clear()
        self.res_add(p["title"] + "\n", "h1")
        self.res_add(p["text"] + "\n", "bad" if p.get("level") == "bad" else "body")

    def render_scan(self, p):
        self.res_clear()
        self.res_add("Modules\n", "h1")
        if p["done"]:
            state = "Scan stopped" if p.get("stopped") else "Scan complete"
        else:
            state = f"Scanning…  {p['tried']} of {p['total']}"
        self.res_add(f"{state}   ·   {len(p['found'])} answered\n", "sub")
        for a, name in p["found"]:
            self.res_add("●  ", "good")
            self.res_add(f"{a:02X}    {name}\n", "body")
        if p["done"] and p["found"]:
            self.res_add("\nChoose a module in the Module list above and press Read faults.\n", "hint")
        elif p["done"]:
            self.res_add(
                "\nNothing answered. Check that the cable is plugged in at both ends, the ignition is on, "
                "the cable switch is on K-line and the right port is open.\n", "bad")

    def render_ident(self, p):
        self.res_clear()
        self.res_add("Identification\n", "h1")
        self.res_add(p["module"] + "\n", "sub")
        self.res_add(p["text"] + "\n", "meaning")
        if p.get("match"):
            self.res_add(f"\nThe part number matches variant {p['match']}. It has been selected for you.\n", "good")
        else:
            self.res_add("\nThis text helps to tell which variant your control unit is.\n", "hint")

    def render_faults(self, p):
        self.res_clear()
        items = p["items"]
        n = len(items)
        self.res_add(p["module"] + "\n", "h1")
        if p["sgbd"]:
            variant = f"Variant: {p['sgbd']}"
            if p.get("detected"):
                variant += f" (detected from your {p['ncodes']} fault code{'s' if p['ncodes'] != 1 else ''})"
        else:
            variant = "Variant: not chosen, showing every possibility"
        self.res_add(f"{variant}   ·   {n} fault{'s' if n != 1 else ''} stored\n", "sub")
        if not n:
            self.res_add("✓  No stored faults\n", "ok")
        for it in items:
            self.res_add(f" {it['code']} ", "chip")
            groups = it["groups"]
            if not groups:
                self.res_add("   " + it["note"] + "\n", "meaning")
            elif len(groups) == 1:
                g = groups[0]
                self.res_add("   " + g["en"] + "\n", "meaning")
                if g["de"]:
                    self.res_add(f"German original: {g['de']}   ·   translated automatically\n", "orig")
                if g["variants"]:
                    self.res_add(f"Variants: {g['variants']}\n", "orig")
            else:
                self.res_add("   Meaning depends on the variant\n", "meaning")
                for g in groups:
                    mark = "  (translated automatically)" if g["rough"] else ""
                    self.res_add(f"•  {g['en']}{mark}   [{g['variants']}]\n", "item")
                if it["more"]:
                    self.res_add(f"…and {it['more']} more possibilities\n", "orig")
        if p.get("path"):
            self.res_add(f"\nSaved to {p['path']}\n", "hint")
        if p.get("candidates"):
            self.res_add("These variants know all of your codes: " + ", ".join(p["candidates"])
                         + ". Pick yours in the Variant list for one clear answer.\n", "hint")
        elif any(len(it["groups"]) > 1 for it in items):
            self.res_add("Pick your variant in the Variant list and press Read faults again for one clear answer.\n", "hint")

    def lookup(self):
        if not self.last_faults:
            return messagebox.showinfo("Nothing to look up", "Press Read faults first.")
        for name, raw in self.last_faults[:5]:
            module = name.split(" ", 1)[-1]
            q = quote_plus(f"BMW E60 {module} fault code {raw}")
            webbrowser.open_new_tab("https://www.google.com/search?q=" + q)

    def explain(self, r):
        if r is None:
            msg = "The module did not reply to the request."
        elif r[0] == 0x7F and len(r) >= 3:
            msg = f"The module refused the request: {NRC.get(r[2], hex(r[2]))}."
        else:
            msg = "Unexpected reply: " + hx(r)
        self.log(msg)
        return msg

    def on_close(self):
        self.remember()
        if self.k:
            self.k.close()
        self.destroy()


def main():
    while True:
        app = App()
        app.mainloop()
        if not app.restart:
            break


if __name__ == "__main__":
    main()
