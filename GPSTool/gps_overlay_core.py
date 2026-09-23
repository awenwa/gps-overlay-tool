# -*- coding: utf-8 -*-
"""
GPS 轨迹视频叠加核心引擎（通用版 v2）
把运动轨迹的实时数据（速度/配速/里程/海拔/坡度/心率/踏频/功率/时间/位置等）叠加到任意视频上。

主要能力：
  - Track        : 解析 GPX / FIT / TCX / XML（含可选心率、踏频、功率通道），按时间插值查询
  - probe_video  : 读取视频时长/分辨率/旋转/音轨，并推断拍摄开始时刻（文件名 → 容器时间）
  - HudStyle     : 显示样式（简洁 / 经典 / 圆形仪表盘 / 方形仪表盘）+ 可选数值字段 + 位置
  - build_hud    : 生成某一时刻的 HUD 图像（数据面板 + 轨迹图）
  - process_video: 完整流水线（并行生成 HUD 帧序列 → ffmpeg 合成 → 输出成片）
  - estimate_output_seconds : 输出耗时预估

命令行（无界面时可用，也用于自测）：
  python gps_overlay_core.py --track a.fit --video b.mp4 --start "2026-09-14 07:51:45" \
         --outdir out --quality 中 --style 圆形仪表盘 --fields 日期,时间,速度 --range 0,10
"""
from __future__ import annotations

import bisect
import datetime
import json
import math
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time

from PIL import Image, ImageChops, ImageDraw, ImageFont

# Windows 下调用 ffmpeg/ffprobe 时不弹出控制台黑窗
_NO_WINDOW = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0


# ---------------------------------------------------------------- 运行环境
def is_frozen() -> bool:
    """是否运行在 PyInstaller 打包出的可执行程序中"""
    return bool(getattr(sys, "frozen", False))


def resource_dir() -> str:
    """只读资源目录（内置 ffmpeg 等）。
    打包后指向程序解包目录；源码运行时指向本文件所在目录。"""
    if is_frozen():
        return getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(sys.executable)))
    return os.path.dirname(os.path.abspath(__file__))


def app_dir() -> str:
    """可写目录（settings.json / layouts.json 等）。
    打包后指向 exe 所在目录；源码运行时指向本文件所在目录。"""
    if is_frozen():
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


class _NullWriter:
    """无控制台环境下的空输出流（windowed exe 中 sys.stdout 为 None）"""
    encoding = "utf-8"

    def write(self, s):
        return len(s)

    def flush(self):
        pass

    def isatty(self):
        return False

    def fileno(self):
        raise OSError("该程序没有控制台输出")


def ensure_console_streams():
    """无控制台运行时把标准流置为空流，避免写 stdout 报错"""
    for name in ("stdout", "stderr"):
        if getattr(sys, name, None) is None:
            try:
                setattr(sys, name, _NullWriter())
            except Exception:
                pass

# ---------------------------------------------------------------- 基础工具
FONT_DIRS = [r"C:/Windows/Fonts/", "/System/Library/Fonts/", "/usr/share/fonts/truetype/"]
_CJK_CANDIDATES = ["msyh.ttc", "msyhbd.ttc", "simhei.ttf", "NotoSansCJK-Regular.ttc",
                   "PingFang.ttc", "DejaVuSans.ttf"]
_NUM_CANDIDATES = ["bahnschrift.ttf", "segoeui.ttf", "arial.ttf", "DejaVuSans-Bold.ttf"]
_FONT_CACHE: dict = {}
_FONT_PICK: dict = {}


def _pick(kind: str) -> str:
    if kind in _FONT_PICK:
        return _FONT_PICK[kind]
    cands = _CJK_CANDIDATES if kind == "cjk" else _NUM_CANDIDATES
    for d in FONT_DIRS:
        if not os.path.isdir(d):
            continue
        for c in cands:
            if os.path.exists(d + c):
                _FONT_PICK[kind] = d + c
                return d + c
    _FONT_PICK[kind] = cands[-1]
    return cands[-1]


def font(kind: str, size: int):
    """kind: cjk(中文正文) / cjkb(中文粗体) / num(数字仪表)"""
    key = (kind, size)
    if key not in _FONT_CACHE:
        if kind == "cjkb":
            path = _pick("cjk")
            for alt in ("msyhbd.ttc", "simhei.ttf"):
                for d in FONT_DIRS:
                    if os.path.exists(d + alt):
                        path = d + alt
                        break
                else:
                    continue
                break
        else:
            path = _pick(kind)
        try:
            _FONT_CACHE[key] = ImageFont.truetype(path, size)
        except Exception:
            _FONT_CACHE[key] = ImageFont.load_default()
    return _FONT_CACHE[key]


def fmt_hms(sec: float) -> str:
    sec = max(0, int(sec))
    return "%02d:%02d:%02d" % (sec // 3600, sec % 3600 // 60, sec % 60)


def fmt_pace(speed_kmh: float, unit_km: bool = True) -> str:
    """速度 → 配速（每公里用时）"""
    if not speed_kmh or speed_kmh < 0.3:
        return "--'--\""
    sec = 3600.0 / speed_kmh
    if sec > 3600:
        return "--'--\""
    return "%d'%02d\"" % (int(sec // 60), int(sec % 60))


def parse_hhmmss(s: str) -> float:
    """'01:02:03' -> 3723 秒"""
    p = [float(x) for x in re.split(r"[:：]", s.strip()) if x != ""]
    while len(p) < 3:
        p.insert(0, 0.0)
    return p[0] * 3600 + p[1] * 60 + p[2]


# ================================================================ FIT 解析
_FIT_EPOCH = 631065600          # 1989-12-31T00:00:00Z 的 Unix 时间
# base_type(低 5 位) -> (size, struct char, invalid 值)
_FIT_BASE = {
    0: (1, "B", 0xFF), 1: (1, "b", 0x7F), 2: (1, "B", 0xFF),
    3: (2, "h", 0x7FFF), 4: (2, "H", 0xFFFF),
    5: (4, "i", 0x7FFFFFFF), 6: (4, "I", 0xFFFFFFFF),
    7: (1, "s", 0x00), 8: (4, "f", None), 9: (8, "d", None),
    10: (1, "B", 0x00), 11: (2, "H", 0x0000), 12: (4, "I", 0x00000000),
    13: (1, "B", 0xFF), 14: (8, "q", 0x7FFFFFFFFFFFFFFF),
    15: (8, "Q", 0xFFFFFFFFFFFFFFFF), 16: (8, "Q", 0x0000000000000000),
}
_FIT_RECORD_MSG = 20            # record


def _fit_base(t: int):
    """取 base_type（字节低 5 位为类型，bit7 为端序能力标志）"""
    return _FIT_BASE.get(t & 0x1F)


def parse_fit(path: str) -> dict:
    """最小可用 FIT 解析：抽取 record 消息里的定位/海拔/心率/踏频/功率/距离/速度。
    返回 dict(ts=[], lat=[], lon=[], ele=[], hr=[]|None, cadence=[]|None, power=[]|None)"""
    data = open(path, "rb").read()
    if len(data) < 14:
        raise ValueError("FIT 文件过短")
    hdr_size = data[0]
    if data[8:12] != b".FIT":
        raise ValueError("不是有效的 FIT 文件（缺少 .FIT 标识）")
    data_size = struct.unpack("<I", data[4:8])[0]
    pos, end = hdr_size, min(hdr_size + data_size, len(data))

    defs: dict = {}
    out = dict(ts=[], lat=[], lon=[], ele=[], hr=[], cadence=[], power=[])
    last_ts = None
    seen_hr = seen_cad = seen_pw = False
    while pos < end:
        hdr = data[pos]
        pos += 1
        if hdr & 0x80:                                   # 压缩时间戳记录
            local = (hdr >> 5) & 0x03
            off = hdr & 0x1F
            ts = (last_ts or 0) + off
            d = defs.get(local)
            if d is None:
                continue
        else:
            local = hdr & 0x0F
            if hdr & 0x40:                               # 定义消息
                if pos + 5 > end:
                    break
                arch = data[pos + 1]
                gmsg = struct.unpack(("<H" if arch == 0 else ">H"), data[pos + 2:pos + 4])[0]
                nf = data[pos + 4]
                pos += 5
                fields, sizes = [], []
                for _ in range(nf):
                    fnum, fsize, ftype = data[pos], data[pos + 1], data[pos + 2]
                    pos += 3
                    fields.append((fnum, fsize, ftype))
                    sizes.append(fsize)
                if hdr & 0x20:                           # 开发者字段定义
                    if pos >= end:
                        break
                    ndev = data[pos]
                    pos += 1
                    for _ in range(ndev):
                        # 开发者字段定义 = 字段号(1) 大小(1) 开发者数据索引(1)
                        # 第三字节不是基础类型；这里只关心它占的数据长度
                        dsize = data[pos + 1]
                        fields.append((-1 - len(sizes), dsize, 0))   # 负号占位，val() 不会查询
                        sizes.append(dsize)
                        pos += 3
                defs[local] = dict(arch=arch, gmsg=gmsg, fields=fields, sizes=sizes)
                continue
            d = defs.get(local)
            if d is None:
                break
            ts = None
        size = sum(d["sizes"])
        if pos + size > end:
            break
        raw = {}
        off_b = 0
        for fnum, fsize, ftype in d["fields"]:
            raw[fnum] = (data[pos + off_b:pos + off_b + fsize], ftype, d["arch"])
            off_b += fsize
        pos += size

        if d["gmsg"] != _FIT_RECORD_MSG:
            continue

        def val(fnum, scale=1.0, offset=0.0):
            it = raw.get(fnum)
            if it is None:
                return None
            b, ftype, arch = it
            info = _fit_base(ftype)
            if info is None:
                return None
            sz, ch, inv = info
            if len(b) != sz or ch == "s":
                return None
            try:
                v = struct.unpack(("<" if arch == 0 else ">") + ch, b)[0]
            except Exception:
                return None
            if inv is not None and v == inv:
                return None
            return v / float(scale) - offset

        t_raw = None
        it = raw.get(253)
        if it is not None:
            info = _fit_base(it[1])
            if info:
                sz, ch, inv = info
                if sz == len(it[0]) and ch != "s":
                    try:
                        t_raw = struct.unpack(("<" if it[2] == 0 else ">") + ch, it[0])[0]
                    except Exception:
                        t_raw = None
        if t_raw is None:
            t_raw = ts                                   # 来自压缩时间戳记录
        if t_raw is None:
            continue
        if last_ts is not None and t_raw < last_ts - 0x7FFFFFFF:
            t_raw += 0x100000000                         # uint32 回绕
        last_ts = t_raw

        lat = val(0)
        lon = val(1)
        lat = lat * (180.0 / 2147483648.0) if lat is not None else None
        lon = lon * (180.0 / 2147483648.0) if lon is not None else None
        if lat is not None and lon is not None and (abs(lat) > 90 or abs(lon) > 180):
            lat = lon = None
        ele = val(78)
        if ele is None:
            ele = val(2, scale=5.0, offset=500.0)        # altitude: 原始/5 - 500
        hr = val(3)
        cad = val(4)
        pw = val(7)

        out["ts"].append(float(t_raw + _FIT_EPOCH))
        out["lat"].append(lat)
        out["lon"].append(lon)
        out["ele"].append(ele)
        out["hr"].append(int(hr) if hr else None)
        out["cadence"].append(int(cad) if cad else None)
        out["power"].append(int(pw) if pw else None)
        seen_hr = seen_hr or (hr is not None)
        seen_cad = seen_cad or (cad is not None)
        seen_pw = seen_pw or (pw is not None)

    if len(out["ts"]) < 2:
        raise ValueError("FIT 中没有解析到足够的 record 记录（需要含时间戳的数据点）")
    for k, keep in (("hr", seen_hr), ("cadence", seen_cad), ("power", seen_pw)):
        if not keep:
            out[k] = None
    if not any(v is not None for v in out["lat"]):
        out["lat"] = out["lon"] = None
        out["ele"] = out["ele"] if any(v is not None for v in out["ele"]) else None
    return out


# ================================================================ XML 轨迹（GPX / TCX / 其它）
_TIME_FMTS = ["%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S.%f",
              "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S"]


def _parse_xml_time(s: str) -> float:
    s = s.strip()
    tz = datetime.timezone.utc if s.endswith("Z") else None
    s2 = s[:-1] + "+00:00" if s.endswith("Z") else s
    try:                                        # 带时区偏移
        return datetime.datetime.fromisoformat(s2).timestamp()
    except Exception:
        pass
    for f in _TIME_FMTS:
        try:
            dt = datetime.datetime.strptime(s, f)
            return dt.replace(tzinfo=tz).timestamp()
        except Exception:
            continue
    raise ValueError("无法解析时间: " + s)


def _f(txt):
    try:
        return float(txt)
    except Exception:
        return None


def parse_xml_track(text: str) -> dict:
    """解析 GPX / TCX / 其它含轨迹点的 XML（容错正则）"""
    pts = []
    # TCX: <Trackpoint>…</Trackpoint>
    for m in re.finditer(r"<Trackpoint\b[^>]*>(.*?)</Trackpoint>", text, re.S | re.I):
        pts.append(("tcx", m.group(1), ""))
    # GPX: <trkpt lat lon>…</trkpt>
    for m in re.finditer(r"<trkpt\b([^>]*?)(?:/>|>(.*?)</trkpt>)", text, re.S | re.I):
        pts.append(("gpx", m.group(2) or "", m.group(1) or ""))
    # 其它：<point lon lat> 或 <location lat= lon=>
    if not pts:
        for m in re.finditer(r"<(?:wpt|point|location|geo:point)\b([^>]*?)(?:/>|>(.*?)</(?:wpt|point|location|geo:point)>)",
                             text, re.S | re.I):
            pts.append(("gpx", m.group(2) or "", m.group(1) or ""))
    if not pts:
        raise ValueError("文件中没有解析到轨迹点（支持 GPX / TCX / 通用 XML）")

    out = dict(ts=[], lat=[], lon=[], ele=[], hr=[], cadence=[], power=[])

    def num(body, *pats):
        for p in pats:
            m = re.search(p, body, re.S | re.I)
            if m:
                v = _f(m.group(1))
                if v is not None:
                    return v
        return None

    def txt(body, *pats):
        for p in pats:
            m = re.search(p, body, re.S | re.I)
            if m:
                return m.group(1).strip()
        return None

    for kind, body, attrs in pts:
        tm = txt(body, r"<time>([^<]+)</time>", r"<Time>([^<]+)</Time>",
                 r"<timestamp>([^<]+)</timestamp>")
        if tm is None:
            continue
        if kind == "gpx":
            lat = num(attrs, r'lat="([-\d.eE+]+)"')
            lon = num(attrs, r'lon="([-\d.eE+]+)"')
            if lat is None:
                lat = num(body, r"<LatitudeDegrees>([-\d.eE+]+)<", r"<lat>([-\d.eE+]+)<")
            if lon is None:
                lon = num(body, r"<LongitudeDegrees>([-\d.eE+]+)<", r"<lon>([-\d.eE+]+)<")
        else:
            lat = num(body, r"<LatitudeDegrees>([-\d.eE+]+)<")
            lon = num(body, r"<LongitudeDegrees>([-\d.eE+]+)<")
        ele = num(body, r"<ele>([-\d.eE+]+)</ele>", r"<AltitudeMeters>([-\d.eE+]+)<",
                  r"<gpxtpx:ele>([-\d.eE+]+)<", r"<height>([-\d.eE+]+)<")
        hr = num(body, r"<HeartRateBpm>\s*<Value>(\d+)</Value>", r"<gpxtpx:hr>(\d+)<",
                 r"<hr>(\d+)<", r"<heartrate>(\d+)<")
        cad = num(body, r"<Cadence>(\d+)<", r"<gpxtpx:cad>(\d+)<", r"<cadence>(\d+)<",
                  r"<RunCadence>(\d+)<")
        pw = num(body, r"<Watts>([\d.]+)<", r"<ns3:Watts>([\d.]+)<", r"<gpxtpx:power>([\d.]+)<",
                 r"<power>([\d.]+)<")
        try:
            tv = _parse_xml_time(tm)
        except Exception:
            tv = None
        if tv is None:
            continue
        out["ts"].append(tv)
        out["lat"].append(lat)
        out["lon"].append(lon)
        out["ele"].append(ele)
        out["hr"].append(int(hr) if hr else None)
        out["cadence"].append(int(cad) if cad else None)
        out["power"].append(int(pw) if pw else None)
    if len(out["ts"]) < 2:
        raise ValueError("XML 中没有解析到足够的带时间轨迹点")
    for k in ("hr", "cadence", "power"):
        if not any(v for v in out[k]):
            out[k] = None
    if not any(v is not None for v in out["lat"]):
        out["lat"] = out["lon"] = None
    if not any(v is not None for v in out["ele"]):
        out["ele"] = None
    return out


def _fill_missing(arr):
    """None 值前后填充，便于插值"""
    if arr is None:
        return None
    out = list(arr)
    last = None
    for i, v in enumerate(out):
        if v is None:
            out[i] = last
        else:
            last = v
    last = None
    for i in range(len(out) - 1, -1, -1):
        if out[i] is None:
            out[i] = last
        else:
            last = out[i]
    return [float(v) if v is not None else 0.0 for v in out]


# ================================================================ 轨迹
class Track:
    """运动轨迹：按时间插值查询速度/坡度/距离/海拔/坐标/心率/踏频/功率"""

    def __init__(self, ts, lat, lon, ele, hr=None, cadence=None, power=None,
                 tz_hours=8.0, name=""):
        self.name = name
        self.tz = datetime.timezone(datetime.timedelta(hours=tz_hours))
        n = len(ts)
        order = sorted(range(n), key=lambda i: ts[i])
        # FIT 等格式中部分记录可能没有定位（GPS 未就绪、暂停段、只记心率的点）：
        # 只要有两个以上带定位的点，就只保留带定位的点；否则按无定位轨迹处理
        if lat is not None and lon is not None:
            with_pos = [i for i in order if lat[i] is not None and lon[i] is not None]
            if len(with_pos) >= 2:
                order = with_pos
            else:
                lat = lon = None
        self.has_pos = lat is not None and lon is not None
        self.ts = [float(ts[i]) for i in order]
        self.has_ele = ele is not None and any(e is not None for e in ele)
        self.lat = [float(lat[i]) if self.has_pos else 0.0 for i in order]
        self.lon = [float(lon[i]) if self.has_pos else 0.0 for i in order]
        self.ele = _fill_missing([ele[i] for i in order]) if self.has_ele \
            else [0.0] * len(self.ts)
        self.hr = _fill_missing([hr[i] for i in order]) if hr else None
        self.cadence = _fill_missing([cadence[i] for i in order]) if cadence else None
        self.power = _fill_missing([power[i] for i in order]) if power else None
        # 累计距离（>200m 的相邻跳跃视为异常点，忽略）
        self.dist = [0.0]
        for i in range(1, len(self.ts)):
            d = haversine(self.lat[i - 1], self.lon[i - 1], self.lat[i], self.lon[i]) if self.has_pos else 0.0
            self.dist.append(self.dist[-1] + (d if d < 200 else 0.0))
        self.gaps = [(self.ts[i - 1], self.ts[i]) for i in range(1, len(self.ts))
                     if self.ts[i] - self.ts[i - 1] > 10]
        self._slope = None

    # ---- 解析 ----
    @staticmethod
    def from_file(path: str, tz_hours: float = 8.0) -> "Track":
        ext = os.path.splitext(path)[1].lower()
        name = os.path.splitext(os.path.basename(path))[0]
        if ext == ".fit":
            d = parse_fit(path)
        elif ext in (".gpx", ".tcx", ".xml", ".kml", ".txt", ".json"):
            try:
                text = open(path, encoding="utf-8", errors="ignore").read()
            except Exception as e:
                raise ValueError("无法读取文件：%s" % e)
            head = text[:4096]
            if "Trackpoint" in head or "<TrainingCenterDatabase" in head:
                d = parse_xml_track(text)
            elif "<trkpt" in text or "<gpx" in head:
                d = parse_xml_track(text)
            else:
                try:
                    d = parse_xml_track(text)
                except Exception:
                    raise ValueError("无法识别的轨迹文件格式（支持 GPX / TCX / XML / FIT）")
        else:
            head = open(path, "rb").read(12)
            if head[8:12] == b".FIT":
                d = parse_fit(path)
            else:
                d = parse_xml_track(open(path, encoding="utf-8", errors="ignore").read())
        if len(d["ts"]) < 2:
            raise ValueError("轨迹点不足（至少需要 2 个带时间的点）")
        return Track(d["ts"], d["lat"], d["lon"], d["ele"], d.get("hr"), d.get("cadence"),
                     d.get("power"), tz_hours, name)

    from_gpx = from_file                                  # 兼容旧调用

    # ---- 查询 ----
    @property
    def start(self):
        return self.ts[0]

    @property
    def end(self):
        return self.ts[-1]

    @property
    def total_dist(self):
        return self.dist[-1]

    @property
    def channels(self):
        return [k for k, v in (("hr", self.hr), ("cadence", self.cadence),
                               ("power", self.power)) if v]

    def _in_gap(self, t):
        for g0, g1 in self.gaps:
            if g0 < t < g1:
                return True
        return False

    def _locate(self, t):
        t = min(max(t, self.ts[0]), self.ts[-1])
        i = bisect.bisect_right(self.ts, t) - 1
        if i >= len(self.ts) - 1:
            return len(self.ts) - 2, 1.0
        return i, (t - self.ts[i]) / max(self.ts[i + 1] - self.ts[i], 1e-9)

    def interp(self, t, arr):
        if arr is None:
            return None
        if self._in_gap(t):
            i = bisect.bisect_right(self.ts, t) - 1
            return arr[max(i, 0)]
        i, f = self._locate(t)
        return arr[i] + (arr[i + 1] - arr[i]) * f

    def speed(self, t, win=2.5) -> float:
        """m/s（中心差分平滑，抑制 GPS 抖动）"""
        t0 = min(max(t - win, self.ts[0]), self.ts[-1])
        t1 = min(max(t + win, self.ts[0]), self.ts[-1])
        if t1 - t0 < 0.5 or self._in_gap(t):
            return 0.0
        return (self.interp(t1, self.dist) - self.interp(t0, self.dist)) / (t1 - t0)

    def slope_series(self, win=15.0):
        """坡度 %：±win 秒窗口的海拔差 / 水平距离，再 3 点平滑"""
        if self._slope is None:
            n = len(self.ts)
            raw = []
            if not self.has_ele:
                self._slope = [0.0] * n
                return self._slope
            for i in range(n):
                a = bisect.bisect_left(self.ts, self.ts[i] - win)
                b = bisect.bisect_right(self.ts, self.ts[i] + win) - 1
                dd = self.dist[b] - self.dist[a]
                raw.append((self.ele[b] - self.ele[a]) / dd * 100.0 if dd > 5 else 0.0)
            sm = raw[:]
            for i in range(1, n - 1):
                sm[i] = (raw[i - 1] + 2 * raw[i] + raw[i + 1]) / 4.0
            if n > 2:
                sm[0], sm[-1] = sm[1], sm[-2]
            self._slope = sm
        return self._slope

    def slope(self, t) -> float:
        return self.interp(t, self.slope_series())

    def index_at(self, t) -> int:
        return max(0, min(len(self.ts) - 1, bisect.bisect_right(self.ts, t) - 1))

    def max_speed_kmh(self) -> float:
        return max((self.speed(t) for t in self.ts), default=0.0) * 3.6

    def cumulative_max_speed(self, t) -> float:
        """截至 t 的最高速度 km/h"""
        mx, tt = 0.0, self.ts[0]
        while tt <= t:
            mx = max(mx, self.speed(tt))
            tt += 1.0
        return mx * 3.6

    def sample(self, t) -> dict:
        return dict(
            t=t, speed=self.speed(t) * 3.6, dist=self.interp(t, self.dist),
            ele=self.interp(t, self.ele), lat=self.interp(t, self.lat),
            lon=self.interp(t, self.lon), slope=self.slope(t), idx=self.index_at(t),
            hr=self.interp(t, self.hr), cadence=self.interp(t, self.cadence),
            power=self.interp(t, self.power),
            local=datetime.datetime.fromtimestamp(t, self.tz),
            elapsed=t - self.ts[0], total=self.total_dist, has_pos=self.has_pos)

    def summary(self) -> str:
        a = datetime.datetime.fromtimestamp(self.ts[0], self.tz)
        b = datetime.datetime.fromtimestamp(self.ts[-1], self.tz)
        ch = ("· 含 " + "/".join({"hr": "心率", "cadence": "踏频", "power": "功率"}[k]
                                for k in self.channels)) if self.channels else ""
        km = ("%.2f km" % (self.total_dist / 1000.0)) if self.has_pos else "无定位数据"
        return ("%d 个点 · %s · %s → %s · 用时 %s %s" %
                (len(self.ts), km, a.strftime("%m-%d %H:%M:%S"), b.strftime("%H:%M:%S"),
                 fmt_hms(self.ts[-1] - self.ts[0]), ch))


def haversine(lat1, lon1, lat2, lon2) -> float:
    R = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    h = math.sin((p2 - p1) / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lon2 - lon1) / 2) ** 2
    return 2 * R * math.asin(math.sqrt(h))


# ---------------------------------------------------------------- 心率（可选 CSV，兼容旧用法）
class HeartRate:
    """可选心率数据：CSV/TXT，每行含时间与心率两列。
    时间列支持：ISO、'YYYY-MM-DD HH:MM:SS'、'HH:MM:SS'、秒数(自轨迹起点)。"""

    def __init__(self, times, bpm):
        self.t = times
        self.v = bpm

    @staticmethod
    def from_file(path: str, track: Track = None) -> "HeartRate":
        times, bpm = [], []
        for line in open(path, encoding="utf-8", errors="ignore"):
            line = line.strip().replace(";", ",").replace("\t", ",")
            if not line:
                continue
            parts = [p.strip() for p in line.split(",") if p.strip() != ""]
            if len(parts) < 2:
                continue
            t_str, h_str = parts[0], parts[-1]
            try:
                hr = float(re.sub(r"[^\d.]", "", h_str))
            except ValueError:
                continue                      # 表头行
            try:
                if re.fullmatch(r"\d+(\.\d+)?", t_str) and track and float(t_str) < 1e6:
                    tv = track.start + float(t_str)       # 相对秒
                elif re.fullmatch(r"\d{1,2}:\d{2}(:\d{2})?", t_str) and track:
                    base = datetime.datetime.fromtimestamp(track.start, track.tz)
                    h, m, s = (list(map(float, t_str.split(":"))) + [0, 0])[:3]
                    tv = base.replace(hour=int(h), minute=int(m), second=int(s), microsecond=0).timestamp()
                else:
                    tv = _parse_xml_time(t_str)
            except Exception:
                continue
            times.append(tv)
            bpm.append(hr)
        if len(times) < 2:
            raise ValueError("心率文件解析失败：需要至少两行『时间,心率』数据")
        order = sorted(range(len(times)), key=lambda i: times[i])
        return HeartRate([times[i] for i in order], [bpm[i] for i in order])

    def at(self, t):
        t = min(max(t, self.t[0]), self.t[-1])
        i = bisect.bisect_right(self.t, t) - 1
        if i >= len(self.t) - 1:
            return self.v[-1]
        f = (t - self.t[i]) / max(self.t[i + 1] - self.t[i], 1e-9)
        return self.v[i] + (self.v[i + 1] - self.v[i]) * f


# ---------------------------------------------------------------- 视频探测
class VideoInfo:
    def __init__(self, path, duration, width, height, fps, rotation, has_audio, creation_utc):
        self.path = path
        self.duration = duration
        self.width = width
        self.height = height
        self.fps = fps
        self.rotation = rotation
        self.has_audio = has_audio
        self.creation_utc = creation_utc

    @property
    def disp_size(self):
        """显示方向（考虑旋转元数据）"""
        if abs(self.rotation) % 180 == 90:
            return self.height, self.width
        return self.width, self.height

    def __repr__(self):
        w, h = self.disp_size
        return "%s %dx%d %.2fs" % (os.path.basename(self.path), w, h, self.duration)


def _ffprobe_json(ffprobe: str, path: str) -> dict:
    out = subprocess.run([ffprobe, "-v", "error", "-print_format", "json",
                          "-show_format", "-show_streams", path],
                         capture_output=True, text=True, encoding="utf-8", errors="ignore",
                         creationflags=_NO_WINDOW)
    if out.returncode != 0:
        raise RuntimeError("ffprobe 读取失败: %s\n%s" % (path, out.stderr.strip()[:400]))
    return json.loads(out.stdout or "{}")


def probe_video(ffprobe: str, path: str) -> VideoInfo:
    j = _ffprobe_json(ffprobe, path)
    v = next((s for s in j.get("streams", []) if s.get("codec_type") == "video"), None)
    if v is None:
        raise RuntimeError("文件中没有视频轨: " + os.path.basename(path))
    dur = float(j.get("format", {}).get("duration") or v.get("duration") or 0)
    rot = 0
    for sd in v.get("side_data_list", []) or []:
        if "rotation" in sd:
            rot = int(sd["rotation"])
    if not rot and v.get("tags", {}).get("rotate"):
        rot = int(v["tags"]["rotate"])
    fps = 0.0
    try:
        num, den = str(v.get("avg_frame_rate", "0/1")).split("/")
        fps = float(num) / float(den) if float(den) else 0.0
    except Exception:
        pass
    if not fps:
        try:
            num, den = str(v.get("r_frame_rate", "0/1")).split("/")
            fps = float(num) / float(den) if float(den) else 0.0
        except Exception:
            fps = 30.0
    ctime = (j.get("format", {}).get("tags", {}) or {}).get("creation_time")
    creation = None
    if ctime:
        try:
            creation = datetime.datetime.fromisoformat(ctime.replace("Z", "+00:00")).timestamp()
        except Exception:
            creation = None
    has_audio = any(s.get("codec_type") == "audio" for s in j.get("streams", []))
    return VideoInfo(path, dur, int(v.get("width", 0)), int(v.get("height", 0)), fps, rot, has_audio, creation)


# 文件名中常见的拍摄时间写法
_NAME_PATTERNS = [
    r"(20\d{2})(\d{2})(\d{2})[_\-T ]?(\d{2})(\d{2})(\d{2})",       # VID_20260914_075145 / PXL_…
    r"(20\d{2})-(\d{2})-(\d{2})[ _T](\d{2})[:\-](\d{2})[:\-](\d{2})",
]


def start_time_from_name(path: str, tz_hours=8.0):
    name = os.path.basename(path)
    for pat in _NAME_PATTERNS:
        m = re.search(pat, name)
        if m:
            y, mo, d, h, mi, s = (int(x) for x in m.groups())
            try:
                return datetime.datetime(y, mo, d, h, mi, s,
                                         tzinfo=datetime.timezone(datetime.timedelta(hours=tz_hours))).timestamp()
            except ValueError:
                continue
    return None


def detect_start_time(info: VideoInfo, tz_hours=8.0, trust_container=True):
    """返回 (起点时间戳 或 None, 来源说明)"""
    t_name = start_time_from_name(info.path, tz_hours)
    if t_name is not None:
        return t_name, "文件名"
    if trust_container and info.creation_utc:
        return info.creation_utc - info.duration, "容器时间(录制结束时刻-时长)"
    return None, "未识别，请手工填写"


# ================================================================ 数值字段
# id -> (显示名, 单位, 字体档)
FIELD_META = {
    "date":    ("日期",    "",     "mid"),
    "time":    ("时间",    "",     "mid"),
    "geo":     ("地理位置", "",     "small"),
    "total":   ("总里程",  "km",   "num"),
    "dist":    ("当前里程", "km",   "num"),
    "elapsed": ("用时",    "",     "mid"),
    "speed":   ("速度",    "km/h", "num"),
    "ele":     ("海拔",    "m",    "num"),
    "slope":   ("坡度",    "%",    "num"),
    "pace":    ("配速",    "/km",  "mid"),
    "step":    ("步频",    "spm",  "num"),
    "hr":      ("心率",    "bpm",  "num"),
    "cadence": ("踏频",    "rpm",  "num"),
    "power":   ("功率",    "W",    "num"),
}
FIELD_ORDER = ["date", "time", "total", "dist", "elapsed", "speed", "ele", "slope",
               "pace", "step", "hr", "power", "cadence", "geo"]
# 固定在第一行 / 最后一行的字段
FIRST_ROW_FIELDS = ("date", "time")
LAST_ROW_FIELDS = ("geo",)
# 不画标题（只显示数值）的字段
NO_LABEL_FIELDS = {"date", "time"}
# 该字段依赖的轨迹通道（None = 总是可用）
FIELD_NEEDS = {"hr": "hr", "cadence": "cadence", "power": "power", "step": "cadence"}
# 主显指标优先级（取第一个被选中的）
PRIMARY_ORDER = ["speed", "pace", "power", "hr", "dist", "total", "ele"]
# 需要额外宽度的字段（跨两列）——地理位置现在固定独占最后一行
FIELD_WIDE = {"geo": True}


def pick_dial_field(st: "HudStyle", fields) -> str | None:
    """仪表盘 / 主显区显示的指标：默认速度，运动形式为跑步时用配速"""
    fs = [f for f in fields if f in FIELD_META]
    want = st.get("dial_field")
    if want in fs:
        return want
    for f in ("speed", "pace"):
        if f in fs:
            return f
    for f in PRIMARY_ORDER:
        if f in fs:
            return f
    return None


def panel_field_rows(st: "HudStyle", fields, cols: int):
    """数值面板排版：第一行 日期+时间；最后一行 地理位置（独占整行）；其余按顺序每行 cols 个"""
    fs = [f for f in fields if f in FIELD_META]
    head = [f for f in FIRST_ROW_FIELDS if f in fs]
    tail = [f for f in LAST_ROW_FIELDS if f in fs]
    body = [f for f in fs if f not in head and f not in tail]
    rows = []
    if head:
        rows.append(head)
    for i in range(0, len(body), max(1, cols)):
        rows.append(body[i:i + max(1, cols)])
    if tail:
        rows.append(tail)
    return rows
# 默认模板
TEMPLATES = {
    "跑步": ["date", "time", "geo", "total", "dist", "elapsed", "pace", "step", "hr"],
    "徒步": ["date", "time", "geo", "total", "dist", "elapsed", "speed", "ele", "slope", "hr"],
    "登山": ["date", "time", "geo", "total", "dist", "elapsed", "ele", "slope", "hr"],
    "骑行": ["date", "time", "geo", "total", "dist", "elapsed", "speed", "slope", "cadence", "power"],
    "驾驶": ["date", "time", "geo", "total", "dist", "elapsed", "speed", "slope", "ele"],
}
TEMPLATE_ORDER = ["跑步", "徒步", "登山", "骑行", "驾驶"]

# 显示样式（方形仪表盘已按需求移除，新增 4 种仪表盘）
STYLES = ["简洁", "经典", "圆形仪表盘", "光环仪表", "半环仪表", "点环仪表", "横条仪表"]
STYLE_ID = {"简洁": "simple", "经典": "classic", "圆形仪表盘": "gauge",
            "光环仪表": "halo", "半环仪表": "semi", "点环仪表": "dots", "横条仪表": "bar"}
STYLE_CN = {v: k for k, v in STYLE_ID.items()}
DIAL_STYLES = {"gauge", "halo", "semi", "dots", "bar"}

# 位置（8 向）
POSITIONS = ["上", "下", "左", "右", "左上角", "右上角", "左下角", "右下角"]
POS_ID = {"上": "top", "下": "bottom", "左": "left", "右": "right",
          "左上角": "top-left", "右上角": "top-right",
          "左下角": "bottom-left", "右下角": "bottom-right"}
POS_CN = {v: k for k, v in POS_ID.items()}

# 画质档位
QUALITY = {"高": dict(crf=20, preset="fast"),
           "中": dict(crf=23, preset="veryfast"),
           "低": dict(crf=27, preset="ultrafast")}
QUALITY_ORDER = ["高", "中", "低"]
HEIGHTS_UI = {"原始分辨率": "orig", "2160 (4K)": 2160, "1440 (2K)": 1440,
              "1080 (全高清)": 1080, "720 (高清)": 720}

# 以 2160px 宽画面为设计基准
DESIGN_W = 2160.0
PANEL_W_WIDE = 1660
PANEL_W_SIDE = 1120
MAP_BOX = (380, 820)


def field_value(fid: str, D: dict, decimals=1) -> str:
    """取字段的显示文本（缺少数据的通道返回 '--'）"""
    if fid == "date":
        return D["local"].strftime("%Y-%m-%d")
    if fid == "time":
        return D["local"].strftime("%H:%M:%S")
    if fid == "geo":
        return ("%.5f, %.5f" % (D["lat"], D["lon"])) if D.get("has_pos") else "--"
    if fid == "total":
        return "%.2f" % (D["total"] / 1000.0)
    if fid == "dist":
        return "%.2f" % (D["dist"] / 1000.0)
    if fid == "elapsed":
        return fmt_hms(D["elapsed"])
    if fid == "speed":
        return "%.1f" % D["speed"]
    if fid == "ele":
        return "%.0f" % D["ele"]
    if fid == "slope":
        s = D["slope"]
        return ("%+.1f" % s) if abs(s) >= 0.05 else "0.0"
    if fid == "pace":
        return fmt_pace(D["speed"])
    if fid == "step":
        return "%d" % round(D["cadence"]) if D.get("cadence") else "--"
    if fid == "hr":
        return "%d" % round(D["hr"]) if D.get("hr") else "--"
    if fid == "cadence":
        return "%d" % round(D["cadence"]) if D.get("cadence") else "--"
    if fid == "power":
        return "%d" % round(D["power"]) if D.get("power") else "--"
    return "--"


def field_ok(fid: str, track: "Track") -> bool:
    """该字段当前轨迹是否有数据"""
    need = FIELD_NEEDS.get(fid)
    if need is None:
        return True
    return bool(getattr(track, need, None))


def available_fields(track: "Track") -> list:
    return [f for f in FIELD_ORDER if field_ok(f, track)]


# ---------------------------------------------------------------- 样式
DEFAULT_STYLE = {
    "style": "gauge",                 # simple / classic / gauge / halo / semi / dots / bar
    "title": "GPS 运动轨迹",
    "accent": [70, 225, 135],
    "refresh_fps": 10,                # HUD 刷新率（自动）
    "speed_max": 50,                  # 仪表量程（自动）
    "units": {"speed": "km/h", "distance": "km", "elevation": "m"},
    "fields": ["date", "time", "geo", "total", "dist", "elapsed", "speed", "slope"],
    # 仪表盘主显指标：speed（速度）/ pace（配速）；为空时自动取第一个可用指标
    "dial_field": "speed",
    # 数据面板：opacity 0-100（百分比，整体透明），sx/sy 宽高缩放（1.0 = 100%，可单独调整），rel=[x,y] 为预览施动的相对位置
    "panel": {"pos": "bottom", "margin": 90, "opacity": 60,
              "sx": 1.0, "sy": 1.0, "rel": None},
    # 轨迹图：全景图（sx/sy）与放大图（zsx/zsy）透明度共用，位置与缩放互相独立
    "map": {"enabled": True, "pos": "top-right", "margin": 88, "opacity": 60,
            "sx": 1.0, "sy": 1.0, "rel": None,
            "zoom_enabled": True, "pos_zoom": "top-left", "zoom_rel": None,
            "zsx": 1.0, "zsy": 1.0},
}


def auto_refresh_fps(duration: float) -> int:
    """按视频时长自动设置 HUD 刷新率"""
    if duration <= 240:
        return 10
    if duration <= 600:
        return 6
    return 4


def auto_speed_max(track: "Track") -> int:
    """按轨迹最高速度自动设置仪表量程（用 99.5 分位，避免 GPS 跳点拉高量程）"""
    sp = sorted(track.speed(t) for t in track.ts)
    if not sp:
        return 50
    mx = sp[min(len(sp) - 1, int(len(sp) * 0.995))] * 3.6
    for step in (20, 30, 40, 50, 60, 80, 100, 120, 150, 200):
        if mx <= step * 0.92:
            return step
    return int(math.ceil(mx / 20.0) * 20)


class HudStyle:
    def __init__(self, d: dict | None = None):
        self.d = json.loads(json.dumps(DEFAULT_STYLE))
        if d:
            self.update(d)

    def update(self, d: dict):
        for k, v in d.items():
            if isinstance(v, dict) and isinstance(self.d.get(k), dict):
                self.d[k].update(v)
            else:
                self.d[k] = v
        return self

    def get(self, key, default=None):
        return self.d.get(key, default)

    def __getitem__(self, k):
        return self.d[k]

    @staticmethod
    def load(path):
        return HudStyle(json.load(open(path, encoding="utf-8")))

    def save(self, path):
        json.dump(self.d, open(path, "w", encoding="utf-8"), ensure_ascii=False, indent=2)


def _rgba(rgb, alpha=None):
    if alpha is None:
        return tuple(rgb)
    return (rgb[0], rgb[1], rgb[2], alpha)


# ================================================================ HUD 绘制
PAD = 54
HEAD_H = 100
ROW_H = {"simple": 122, "classic": 152, "gauge": 122, "halo": 122, "semi": 122,
         "dots": 122, "bar": 122}
DIAL_AREA = 620                # 仪表盘区（宽×高）
SIMPLE_PRIMARY_H = 300


def panel_layout(st: "HudStyle", fields, W: int):
    """设计基准下计算面板布局。
    返回 dict(w, h, dial=(cx,cy,R)|None, cells=[(fid,x,y,w,h)], primary=(y0,y1)|None)
    排版规则：第一行 日期+时间；最后一行 地理位置（独占整行）；其余按顺序每行 cols 个；
             仪表盘上已显示的指标（速度 / 配速）不在面板里重复出现。"""
    style = st["style"]
    L = dict(w=W, h=0, dial=None, cells=[], primary=None)
    gap = 26
    has_primary = style in DIAL_STYLES or style == "simple"
    dial_fid = pick_dial_field(st, fields) if has_primary else None
    grid_fields = [f for f in fields if f != dial_fid] if dial_fid else list(fields)

    def make_cells(x0, y0, grid_w, cols, row_h):
        cells, y = [], y0
        uw = (grid_w - (cols - 1) * gap) / float(cols)   # 固定列宽 → 各行列位置对齐
        for row in panel_field_rows(st, grid_fields, cols):
            if len(row) == 1 and row[0] in FIELD_WIDE:    # 整行字段（如地理位置）占满整行
                cells.append((row[0], x0, y, grid_w, row_h))
            else:
                x = x0
                for fid in row:
                    cells.append((fid, x, y, uw, row_h))
                    x += uw + gap
            y += row_h
        return cells, y - y0

    if style in DIAL_STYLES:
        if W - 2 * PAD >= 1420:                       # 宽面板：仪表在左，字段在右
            grid_x = PAD + DIAL_AREA
            grid_w = W - PAD - grid_x
            cols = 3 if grid_w >= 900 else 2
            cells, grid_h = make_cells(grid_x, HEAD_H + 26, grid_w, cols, ROW_H[style])
            area_h = max(DIAL_AREA, grid_h + 56)
            L["dial"] = (PAD + DIAL_AREA / 2.0, HEAD_H + area_h / 2.0, 252)
            L["cells"] = cells
            L["h"] = int(HEAD_H + area_h + 44)
        else:                                          # 窄面板：仪表在上居中，字段在下
            cols = 2
            cells, grid_h = make_cells(PAD, HEAD_H + DIAL_AREA + 16, W - 2 * PAD, cols, ROW_H[style])
            L["dial"] = (W / 2.0, HEAD_H + DIAL_AREA / 2.0, 232)
            L["cells"] = cells
            L["h"] = int(HEAD_H + DIAL_AREA + 16 + grid_h + 40)
    elif style == "simple":
        cols = 4 if W - 2 * PAD >= 1400 else (3 if W - 2 * PAD >= 1000 else 2)
        cells, grid_h = make_cells(PAD, HEAD_H + SIMPLE_PRIMARY_H, W - 2 * PAD, cols, ROW_H[style])
        L["cells"] = cells
        L["primary"] = (HEAD_H, HEAD_H + SIMPLE_PRIMARY_H)
        L["h"] = int(HEAD_H + SIMPLE_PRIMARY_H + grid_h + 40)
    else:                                              # classic 纯数据表
        cols = 4 if W - 2 * PAD >= 1400 else (3 if W - 2 * PAD >= 1000 else 2)
        cells, grid_h = make_cells(PAD, HEAD_H, W - 2 * PAD, cols, ROW_H["classic"])
        L["cells"] = cells
        L["h"] = int(HEAD_H + grid_h + 36)
    return L


def panel_design_size(st: "HudStyle", fields, pos: str):
    W = PANEL_W_SIDE if pos in ("left", "right") else PANEL_W_WIDE
    return W, panel_layout(st, [f for f in fields if f in FIELD_META], W)["h"]


def _draw_cells(cells, D, dr, A, W_, GY, DM, big=False):
    f_lab = font("cjk", 42 if big else 36)
    f_val = {"num": font("num", 74 if big else 62), "mid": font("num", 64 if big else 54),
             "small": font("num", 46)}
    f_unit = font("cjk", 38 if big else 34)
    for fid, x, y, w, h in cells:
        label, unit, kind = FIELD_META[fid]
        no_cap = fid in NO_LABEL_FIELDS            # 日期 / 时间不显示标题
        if not no_cap:
            dr.text((x, y), label, font=f_lab, fill=GY)
        val = field_value(fid, D)
        col = W_
        if fid == "slope" and abs(D["slope"]) >= 3.0:
            col = A
        if fid in ("hr", "cadence", "power", "step") and val == "--":
            col = DM
        fv = f_val[kind]
        vy = y + (50 if big else 46) if not no_cap else \
            max(y + 4, y + (h - fv.size * 1.34) / 2.0)
        dr.text((x, vy), val, font=fv, fill=col)
        if unit:
            vw = dr.textlength(val, font=fv)
            # 单位上移：在「与数值底部对齐」的基础上再上移 50% 单位行高。
            # 实测两字体墨迹底部差（num 与 cjk 的 descent 不同）：
            #   num 62/34 需 11、mid 54/34 需 4、big 74/38 需 14、small 46/34 需 -7，
            # 减掉 0.5*f_unit.size 后与之相差 0~3 px。
            uy = vy + fv.size - f_unit.size - int(round(f_unit.size * 0.5))
            dr.text((x + vw + 12, uy), unit, font=f_unit, fill=DM)


def _draw_dial(st, fid, val, D, dr, dial, A, W_, GY, DM, TRACK):
    """主显仪表：gauge 圆环 / halo 光环 / semi 半环 / dots 点环 / bar 横条
    fid 为 speed 时显示速度（km/h），为 pace 时显示配速（每公里用时）"""
    label, unit, _ = FIELD_META[fid]
    if fid == "pace":
        caption = "最快 " + fmt_pace(D["maxspeed"])
    else:
        caption = "MAX %.1f" % D["maxspeed"]
    cx, cy, R = dial
    vmax = max(st["speed_max"], 1)
    frac = max(0.0, min(1.0, D["speed"] / vmax)) if fid in ("speed", "pace") else \
        max(0.0, min(1.0, (D["maxspeed"] or 1) / vmax))
    style = st["style"]

    if style == "gauge":
        AW = 28
        box = (cx - R, cy - R, cx + R, cy + R)
        a0, sweep = 135.0, 270.0
        dr.arc(box, a0, a0 + sweep, fill=TRACK, width=AW)
        if frac > 0.002:
            dr.arc(box, a0, a0 + sweep * frac, fill=A, width=AW)
        for i in range(0, int(vmax) + 1, 5):
            ang = math.radians(a0 + sweep * i / vmax)
            major = (i % 10 == 0)
            r1 = R - AW / 2 - 14
            r2 = r1 - (28 if major else 16)
            dr.line((cx + r1 * math.cos(ang), cy + r1 * math.sin(ang),
                     cx + r2 * math.cos(ang), cy + r2 * math.sin(ang)),
                    fill=(255, 255, 255, 140 if major else 70), width=6 if major else 3)
            if major:
                lr, t = R + 46, str(i)
                tw = dr.textlength(t, font=font("num", 32))
                dr.text((cx + lr * math.cos(ang) - tw / 2, cy + lr * math.sin(ang) - 20), t,
                        font=font("num", 32), fill=DM)
        ang = math.radians(a0 + sweep * frac)
        px, py = cx + R * math.cos(ang), cy + R * math.sin(ang)
        dr.ellipse((px - 21, py - 21, px + 21, py + 21), fill=(8, 10, 14, 255), outline=A, width=7)
        f_big = font("num", 150)
        dr.text((cx - dr.textlength(val, font=f_big) / 2, cy - 112), val, font=f_big, fill=W_)
        if unit:
            dr.text((cx - dr.textlength(unit, font=font("cjk", 46)) / 2, cy + 62), unit,
                    font=font("cjk", 46), fill=GY)
        mt = "%s · %s" % (label, caption)
        dr.text((cx - dr.textlength(mt, font=font("cjk", 34)) / 2, cy + 136), mt,
                font=font("cjk", 34), fill=DM)

    elif style == "halo":                      # 光环仪表：柔光晕 + 粗弧 + 亮点指针
        for gr, ga, gw in ((R + 46, 20, 8), (R + 26, 34, 13)):
            dr.arc((cx - gr, cy - gr, cx + gr, cy + gr), 120, 420, fill=A + (ga,), width=gw)
        AW = 38
        box = (cx - R, cy - R, cx + R, cy + R)
        dr.arc(box, 120, 420, fill=TRACK, width=AW)
        if frac > 0.002:
            dr.arc(box, 120, 120 + 300 * frac, fill=A + (255,), width=AW)
        ang = math.radians(120 + 300 * frac)
        px, py = cx + R * math.cos(ang), cy + R * math.sin(ang)
        dr.ellipse((px - 26, py - 26, px + 26, py + 26), fill=A + (60,))
        dr.ellipse((px - 15, py - 15, px + 15, py + 15), fill=(255, 255, 255, 255))
        dr.ellipse((cx - 6, cy - 6, cx + 6, cy + 6), outline=(255, 255, 255, 34), width=2)
        f_big = font("num", 150)
        dr.text((cx - dr.textlength(val, font=f_big) / 2, cy - 108), val, font=f_big, fill=W_)
        if unit:
            dr.text((cx - dr.textlength(unit, font=font("cjk", 44)) / 2, cy + 58), unit,
                    font=font("cjk", 44), fill=GY)
        mt = "%s · %s" % (label, caption)
        dr.text((cx - dr.textlength(mt, font=font("cjk", 32)) / 2, cy + 128), mt,
                font=font("cjk", 32), fill=DM)

    elif style == "semi":                      # 半环仪表：上半 180° 弧 + 指针
        RB = R * 1.12
        box = (cx - RB, cy - RB, cx + RB, cy + RB)
        a0, sweep = 180.0, 180.0
        dr.arc(box, a0, a0 + sweep, fill=TRACK, width=26)
        if frac > 0.002:
            dr.arc(box, a0, a0 + sweep * frac, fill=A, width=26)
        for i in range(11):
            ang = math.radians(a0 + sweep * i / 10.0)
            major = (i % 5 == 0)
            r1, r2 = RB - 24, RB - (48 if major else 34)
            dr.line((cx + r1 * math.cos(ang), cy + r1 * math.sin(ang),
                     cx + r2 * math.cos(ang), cy + r2 * math.sin(ang)),
                    fill=(255, 255, 255, 150 if major else 70), width=6 if major else 3)
            if major:
                t = str(int(vmax * i / 10.0))
                tw = dr.textlength(t, font=font("num", 28))
                lr = RB + 44
                dr.text((cx + lr * math.cos(ang) - tw / 2, cy + lr * math.sin(ang) - 16), t,
                        font=font("num", 28), fill=DM)
        ang = math.radians(a0 + sweep * frac)
        dr.line((cx, cy, cx + (RB - 62) * math.cos(ang), cy + (RB - 62) * math.sin(ang)),
                fill=W_, width=9)
        dr.ellipse((cx - 16, cy - 16, cx + 16, cy + 16), fill=(8, 10, 14, 255), outline=A, width=6)
        f_big = font("num", 132)
        dr.text((cx - dr.textlength(val, font=f_big) / 2, cy + 34), val, font=f_big, fill=W_)
        if unit:
            uw = dr.textlength(unit, font=font("cjk", 40))
            dr.text((cx + dr.textlength(val, font=f_big) / 2 + 14, cy + 74), unit,
                    font=font("cjk", 40), fill=GY)
        mt = "%s · %s" % (label, caption)
        dr.text((cx - dr.textlength(mt, font=font("cjk", 32)) / 2, cy + 196), mt,
                font=font("cjk", 32), fill=DM)

    elif style == "dots":                      # 点环仪表：环状点阵，点亮表示进度
        N = 48
        for i in range(N):
            ang = math.radians(120 + 300.0 * i / (N - 1))
            on = i / (N - 1.0) <= frac + 1e-9
            r1, r2 = R - 24, R + 16
            dr.line((cx + r1 * math.cos(ang), cy + r1 * math.sin(ang),
                     cx + r2 * math.cos(ang), cy + r2 * math.sin(ang)),
                    fill=(A if on else (255, 255, 255, 42)), width=12)
        tip = min(N - 1, int(round(frac * (N - 1))))
        ang = math.radians(120 + 300.0 * tip / (N - 1))
        px, py = cx + (R - 4) * math.cos(ang), cy + (R - 4) * math.sin(ang)
        dr.ellipse((px - 20, py - 20, px + 20, py + 20), fill=(8, 10, 14, 255), outline=A, width=6)
        f_big = font("num", 150)
        dr.text((cx - dr.textlength(val, font=f_big) / 2, cy - 108), val, font=f_big, fill=W_)
        if unit:
            dr.text((cx - dr.textlength(unit, font=font("cjk", 44)) / 2, cy + 58), unit,
                    font=font("cjk", 44), fill=GY)
        mt = "%s · %s" % (label, caption)
        dr.text((cx - dr.textlength(mt, font=font("cjk", 32)) / 2, cy + 128), mt,
                font=font("cjk", 32), fill=DM)

    else:                                      # bar 横条仪表：大数值 + 分段速度条
        BW = R * 2 + 60
        bx0, bx1 = cx - BW / 2.0, cx + BW / 2.0
        dr.text((bx0, cy - 226), label, font=font("cjk", 40), fill=GY)
        mt = caption
        dr.text((bx1 - dr.textlength(mt, font=font("num", 36)), cy - 226), mt,
                font=font("num", 36), fill=DM)
        f_big = font("num", 170)
        dr.text((cx - dr.textlength(val, font=f_big) / 2, cy - 150), val, font=f_big, fill=W_)
        if unit:
            dr.text((cx - dr.textlength(unit, font=font("cjk", 42)) / 2, cy + 52), unit,
                    font=font("cjk", 42), fill=GY)
        by = cy + 136
        dr.rounded_rectangle((bx0, by, bx1, by + 24), 12, TRACK)
        if frac > 0.005:
            dr.rounded_rectangle((bx0, by, bx0 + (bx1 - bx0) * frac, by + 24), 12, A)
        segs = 20
        for i in range(1, segs):
            xx = bx0 + (bx1 - bx0) * i / segs
            dr.line((xx, by + 4, xx, by + 20), fill=(8, 10, 14, 170), width=3)
        dr.text((bx0, by + 34), "0", font=font("num", 28), fill=DM)
        t = str(int(vmax))
        dr.text((bx1 - dr.textlength(t, font=font("num", 28)), by + 34), t,
                font=font("num", 28), fill=DM)


def draw_panel(st: "HudStyle", D: dict, pos: str):
    """绘制数据面板（设计基准尺寸，未缩放）"""
    fields = [f for f in st["fields"] if f in FIELD_META]
    W = PANEL_W_SIDE if pos in ("left", "right") else PANEL_W_WIDE
    L = panel_layout(st, fields, W)
    PW, PH = W, L["h"]
    A = tuple(st["accent"])
    W_ = (245, 247, 250)
    GY, DM = (150, 160, 172), (120, 130, 142)
    TRACK = (255, 255, 255, 42)
    # 背景层（透明度可调）——只有背景受 opacity 控制
    bg = Image.new("RGBA", (PW, PH), (0, 0, 0, 0))
    bgr = ImageDraw.Draw(bg)
    bg_alpha = max(0, min(255, int(255 * st["panel"].get("opacity", 60) / 100.0)))
    bgr.rounded_rectangle((0, 0, PW - 1, PH - 1), 48, fill=_rgba([8, 10, 14], bg_alpha))
    # 前景层（文字 + 图形，固定 80% 透明度）
    img = Image.new("RGBA", (PW, PH), (0, 0, 0, 0))
    dr = ImageDraw.Draw(img)
    # 标题行
    dr.ellipse((PAD, 44, PAD + 26, 70), fill=A)
    dr.text((PAD + 42, 30), st["title"] or "GPS", font=font("cjkb", 48), fill=GY)
    # 主显仪表
    if L["dial"]:
        fid = pick_dial_field(st, fields)
        if fid:
            _draw_dial(st, fid, field_value(fid, D), D, dr, L["dial"], A, W_, GY, DM, TRACK)
    if L["primary"]:
        fid = pick_dial_field(st, fields)
        y0, y1 = L["primary"]
        if fid:
            label, unit, _ = FIELD_META[fid]
            val = field_value(fid, D)
            f_big = font("num", 190)
            f_u = font("cjk", 54)
            tw = dr.textlength(val, font=f_big)
            uw = dr.textlength(unit, font=f_u) if unit else 0
            x0 = PW / 2.0 - (tw + (uw + 22 if unit else 0)) / 2.0
            dr.text((x0, y0 + 16), val, font=f_big, fill=W_)
            if unit:
                dr.text((x0 + tw + 22, y0 + 16 + f_big.size - 68), unit, font=f_u, fill=GY)
            by = y1 - 92
            vmax = max(st["speed_max"], 1)
            frac = max(0.0, min(1.0, D["speed"] / vmax)) if fid in ("speed", "pace") else 0.0
            dr.rounded_rectangle((PAD, by, PW - PAD, by + 18), 9, TRACK)
            if frac > 0.01:
                dr.rounded_rectangle((PAD, by, PAD + int((PW - 2 * PAD) * frac), by + 18), 9, A)
            dr.text((PAD, by - 54), label, font=font("cjk", 40), fill=GY)
            mx = ("最快 " + fmt_pace(D["maxspeed"])) if fid == "pace" else ("MAX %.1f" % D["maxspeed"])
            dr.text((PW - PAD - dr.textlength(mx, font=font("num", 38)), by - 52), mx,
                    font=font("num", 38), fill=DM)
    big = st["style"] == "classic"
    _draw_cells(L["cells"], D, dr, A, W_, GY, DM, big=big)
    # 文字/图形固定 80%，背景按其自身透明度保留
    fg = apply_opacity(img, 80)
    out = bg
    out.alpha_composite(fg)
    return out

# ---------------------------------------------------------------- 轨迹图
def map_design_size(track: "Track"):
    if not track.has_pos:
        return None
    mx = 111320.0 * math.cos(math.radians((max(track.lat) + min(track.lat)) / 2.0))
    dx = (max(track.lon) - min(track.lon)) * mx
    dy = (max(track.lat) - min(track.lat)) * 110540.0
    if dx <= 1 and dy <= 1:
        return None
    bw, bh = MAP_BOX
    if dx > dy:
        bw, bh = bh, bw
    s = min(bw / max(dx, 1e-6), bh / max(dy, 1e-6))
    w, h = max(260, dx * s + 96), max(220, dy * s + 230)
    return int(min(w, 860)), int(min(h, 900))


def _project(track: "Track", w, h):
    """等比例、正北朝上投影整条轨迹到 w×h"""
    lat0 = (max(track.lat) + min(track.lat)) / 2.0
    mx = 111320.0 * math.cos(math.radians(lat0))
    X = [(l - min(track.lon)) * mx for l in track.lon]
    Y = [(max(track.lat) - l) * 110540.0 for l in track.lat]
    sx, sy = max(X) - min(X), max(Y) - min(Y)
    s = min(w / sx, h / sy) if sx > 0 and sy > 0 else 1.0
    ox, oy = (w - sx * s) / 2.0, (h - sy * s) / 2.0
    return [(ox + x * s, oy + y * s) for x, y in zip(X, Y)]


def draw_map(st: "HudStyle", track: "Track", D: dict):
    """全景轨迹图：深色底（透明度可调）+ 细边框 + 轨迹（文字/图形固定 80%）"""
    size = map_design_size(track)
    if size is None:
        return None
    MW, MH = size
    A = tuple(st["accent"])
    GY, DM = (150, 160, 172), (120, 130, 142)
    stroke = 200                                          # 文字描边，保证亮背景下可读
    # 背景层（透明度可调）
    bg = Image.new("RGBA", (MW, MH), (0, 0, 0, 0))
    m_alpha = max(0, min(255, int(255 * st["map"].get("opacity", 60) / 100.0)))
    ImageDraw.Draw(bg).rounded_rectangle((0, 0, MW - 1, MH - 1), 40,
                                         fill=_rgba([8, 10, 14], m_alpha))
    # 前景层（文字 + 图形固定 80%）
    img = Image.new("RGBA", (MW, MH), (0, 0, 0, 0))
    dr = ImageDraw.Draw(img)
    # 亮边框，方便在画面上定位
    dr.rounded_rectangle((2, 2, MW - 3, MH - 3), 40,
                         outline=(255, 255, 255, 60), width=3)
    pad = 36
    dr.text((pad, 30), "路线轨迹", font=font("cjkb", 38), fill=GY,
            stroke_width=4, stroke_fill=(0, 0, 0, stroke))
    pct = "%d%%" % round((D["dist"] / D["total"] * 100) if D["total"] else 0)
    dr.text((MW - pad - dr.textlength(pct, font=font("num", 36)), 30), pct,
            font=font("num", 36), fill=A, stroke_width=4, stroke_fill=(0, 0, 0, stroke))
    tx, ty = pad, 106
    tw, th = MW - 2 * pad, MH - 106 - (108 if MH > 320 else 70)
    pts = [(tx + x, ty + y) for x, y in _project(track, tw, th)]
    idx = D["idx"]
    dr.line(pts, fill=(0, 0, 0, 150), width=11, joint="curve")
    dr.line(pts, fill=(255, 255, 255, 105), width=5, joint="curve")
    if idx >= 1:
        dr.line(pts[:idx + 1], fill=(0, 0, 0, 170), width=16, joint="curve")
        dr.line(pts[:idx + 1], fill=A + (255,), width=9, joint="curve")
    sx, sy = pts[0]
    dr.ellipse((sx - 12, sy - 12, sx + 12, sy + 12), fill=(255, 255, 255, 235),
               outline=(0, 0, 0, 170), width=3)
    ex, ey = pts[-1]
    dr.ellipse((ex - 10, ey - 10, ex + 10, ey + 10), fill=(8, 10, 14, 220),
               outline=(255, 255, 255, 150), width=3)
    cx, cy = pts[idx]
    ph = (D["t"] % 2.0) / 2.0
    r = 22 + 14 * ph
    dr.ellipse((cx - r, cy - r, cx + r, cy + r), fill=A + (int(90 * (1 - ph)),))
    dr.ellipse((cx - 19, cy - 19, cx + 19, cy + 19), fill=(0, 0, 0, 190), outline=A + (255,), width=5)
    dr.ellipse((cx - 9, cy - 9, cx + 9, cy + 9), fill=(255, 255, 255, 255))
    # 文字/图形固定 80%，背景按其自身透明度保留
    fg = apply_opacity(img, 80)
    out = bg
    out.alpha_composite(fg)
    return out


# ---------------------------------------------------------------- 放大轨迹图（行进方向朝上）
MAP_ZOOM_BOX = (560, 560)          # 设计基准尺寸（圆形，透明底）
ZOOM_BACK_M = 200.0                # 后方显示范围（米）
ZOOM_FRONT_M = 300.0               # 前方显示范围（米）


def _bearing(lat1, lon1, lat2, lon2) -> float:
    """两点间方位角（正北为 0°，顺时针）"""
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return math.degrees(math.atan2(y, x)) % 360.0


def draw_map_zoom(st: "HudStyle", track: "Track", D: dict):
    """放大轨迹图：圆形边框 + 深色底（透明度可调），显示当前位置后方 200 m、前方 300 m，行进方向朝上"""
    if not track.has_pos:
        return None
    idx = D["idx"]
    d0 = track.dist[idx]
    i0 = bisect.bisect_left(track.dist, d0 - ZOOM_BACK_M)
    i1 = min(bisect.bisect_right(track.dist, d0 + ZOOM_FRONT_M), len(track.ts) - 1)
    if i1 <= i0:
        return None
    lat0, lon0 = track.lat[idx], track.lon[idx]
    # 行进方向：优先取前方 ~40m 的方向，接近终点时改用后方
    j = min(bisect.bisect_left(track.dist, d0 + 40.0), len(track.ts) - 1)
    if track.dist[j] - d0 < 5:
        jb = max(bisect.bisect_left(track.dist, d0 - 40.0), 0)
        brg = _bearing(track.lat[jb], track.lon[jb], lat0, lon0)
    else:
        brg = _bearing(lat0, lon0, track.lat[j], track.lon[j])
    th = math.radians(brg)
    st_, ct_ = math.sin(th), math.cos(th)
    mx = 111320.0 * math.cos(math.radians(lat0))

    MW, MH = MAP_ZOOM_BOX
    A = tuple(st["accent"])
    GY, DM = (150, 160, 172), (120, 130, 142)
    cx0, cy0 = MW / 2.0, MH / 2.0
    R = MW / 2.0 - 6                                     # 圆形边框半径
    Ru = R - 16                                          # 可用半径
    mo = 100                                              # 整体透明度由 apply_opacity 统一处理
    base_a = int(255 * mo / 100.0)

    img = Image.new("RGBA", (MW, MH), (0, 0, 0, 0))
    dr = ImageDraw.Draw(img)
    # 圆形边框（外圈柔光 + 内圈描边），内部保持透明
    dr.ellipse((cx0 - R, cy0 - R, cx0 + R, cy0 + R), outline=A + (max(40, base_a // 3),), width=10)
    dr.ellipse((cx0 - R + 8, cy0 - R + 8, cx0 + R - 8, cy0 + R - 8),
               outline=(255, 255, 255, max(60, base_a // 2)), width=4)
    # 比例尺：直径容纳 前方300m + 后方200m = 500m；当前位置点按比例落位
    SPAN = ZOOM_BACK_M + ZOOM_FRONT_M
    s = 2.0 * Ru / SPAN
    my = cy0 - Ru + ZOOM_FRONT_M * s

    def proj(lat, lon):
        e = (lon - lon0) * mx
        n = (lat - lat0) * 110540.0
        f = e * st_ + n * ct_          # 行进方向分量（向上）
        l = e * ct_ - n * st_          # 侧向分量
        return cx0 + l * s, my - f * s

    pts = [proj(track.lat[i], track.lon[i]) for i in range(i0, i1 + 1)]
    k_local = max(0, min(idx - i0, len(pts) - 1))
    if len(pts) >= 2:
        if k_local >= 1:               # 已骑过：主色
            dr.line(pts[:k_local + 1], fill=(0, 0, 0, 170), width=17, joint="curve")
            dr.line(pts[:k_local + 1], fill=A + (255,), width=10, joint="curve")
        rest = pts[max(k_local, 0):]
        if len(rest) >= 2:             # 前方：白色
            dr.line(rest, fill=(0, 0, 0, 175), width=13, joint="curve")
            dr.line(rest, fill=(255, 255, 255, 205), width=6, joint="curve")
    # 当前位置（脉冲点）
    dr.ellipse((cx0 - 26, my - 26, cx0 + 26, my + 26), fill=A + (60,))
    dr.ellipse((cx0 - 16, my - 16, cx0 + 16, my + 16), fill=(0, 0, 0, 190), outline=A + (255,), width=5)
    dr.ellipse((cx0 - 7, my - 7, cx0 + 7, my + 7), fill=(255, 255, 255, 255))
    # 背景层：圆内深色底（透明度可调）
    bg = Image.new("RGBA", (MW, MH), (0, 0, 0, 0))
    z_alpha = max(0, min(255, int(255 * st["map"].get("opacity", 60) / 100.0)))
    ImageDraw.Draw(bg).ellipse((cx0 - R, cy0 - R, cx0 + R, cy0 + R),
                               fill=_rgba([8, 10, 14], z_alpha))
    # 前景层：文字 + 图形固定 80%
    fg = apply_opacity(img, 80)
    out = bg
    out.alpha_composite(fg)
    # 圆形裁切（超采样抗锯齿），外部完全透明
    SS = 3
    mask = Image.new("L", (MW * SS, MH * SS), 0)
    ImageDraw.Draw(mask).ellipse(((cx0 - R) * SS, (cy0 - R) * SS,
                                  (cx0 + R) * SS, (cy0 + R) * SS), fill=255)
    mask = mask.resize((MW, MH), Image.LANCZOS)
    out.putalpha(ImageChops.multiply(out.getchannel("A"), mask))
    return out


def apply_opacity(im, pct):
    """整体调整图层透明度：0 = 全透明，100 = 不透明（保留原始颜色，只缩放 alpha）"""
    if im is None:
        return None
    p = max(0, min(100, int(pct)))
    if p >= 100:
        return im
    out = im.copy()
    out.putalpha(out.getchannel("A").point([max(0, min(255, v * p // 100)) for v in range(256)]))
    return out


def build_hud_layers(track: Track, st: HudStyle, tq: float, hr: HeartRate | None = None):
    """按设计基准尺寸生成 HUD 图层（未缩放），透明度已按设置作用到整层"""
    D = track.sample(tq)
    D["maxspeed"] = track.cumulative_max_speed(tq)
    if hr:
        D["hr"] = int(round(hr.at(tq))) if hr.t[0] - 1 <= tq <= hr.t[-1] + 1 else D.get("hr")
    # 数值面板 / 轨迹图 / 放大轨迹：内部均已区分背景(透明度可调)与文字图形(固定 80%)
    img = draw_panel(st, D, st["panel"]["pos"])
    mp = draw_map(st, track, D) if st["map"]["enabled"] else None
    mz = draw_map_zoom(st, track, D) if st["map"].get("zoom_enabled") else None
    return img, mp, mz


def fit_layer(im, w, h, resample=Image.LANCZOS):
    """把图层缩放/拉伸到指定像素尺寸（长宽可不同）"""
    if im is None:
        return None
    w, h = max(1, int(w)), max(1, int(h))
    if im.size == (w, h):
        return im
    return im.resize((w, h), resample)


def scale_layer(im, k: float, resample=Image.LANCZOS):
    """等比缩放（保留旧接口）"""
    if im is None or abs(k - 1.0) < 1e-6:
        return im
    return im.resize((max(1, int(im.width * k)), max(1, int(im.height * k))), resample)


def elem_scale(cfg: dict, base: float, kx="sx", ky="sy", legacy="scale"):
    """取某元素的横向/纵向缩放系数（相对设计基准），旧配置的 scale 作为兼容回退"""
    lx = cfg.get(kx, cfg.get(legacy, 1.0))
    ly = cfg.get(ky, cfg.get(legacy, 1.0))
    try:
        fx, fy = float(lx), float(ly)
    except (TypeError, ValueError):
        fx = fy = 1.0
    return base * max(0.06, min(4.0, fx)), base * max(0.06, min(4.0, fy))


def build_hud(track: Track, st: HudStyle, tq: float, frame_w: int, frame_h: int | None = None,
              hr: HeartRate | None = None):
    """生成某轨迹时刻的 HUD：返回 (面板, 全景地图|None, 放大地图|None)，已按各自位置尺寸缩放"""
    imgs = build_hud_layers(track, st, tq, hr)
    if frame_h is None:
        frame_h = int(frame_w * 16 / 9.0)
    lay = hud_layout(st, frame_w, frame_h, track)
    return tuple(fit_layer(im, r[2], r[3]) if r else im for im, r in zip(imgs, lay))


def _pos_xy(pos: str, fw: int, fh: int, w: int, h: int, m: int):
    if pos == "top":
        return (fw - w) // 2, m
    if pos == "bottom":
        return (fw - w) // 2, fh - h - m
    if pos == "left":
        return m, (fh - h) // 2
    if pos == "right":
        return fw - w - m, (fh - h) // 2
    if pos == "top-left":
        return m, m
    if pos == "top-right":
        return fw - w - m, m
    if pos == "bottom-left":
        return m, fh - h - m
    return fw - w - m, fh - h - m          # bottom-right


def _elem_xy(rel, pos: str, fw: int, fh: int, w: int, h: int, m: int):
    """rel=[x,y]（相对画面左上角的比例，来自预览拖动）优先；否则按 8 向 pos"""
    if rel:
        x = int(max(0.0, min(1.0, float(rel[0]))) * fw)
        y = int(max(0.0, min(1.0, float(rel[1]))) * fh)
        return min(max(x, 0), max(0, fw - w)), min(max(y, 0), max(0, fh - h))
    return _pos_xy(pos, fw, fh, w, h, m)


def hud_layout(st: HudStyle, frame_w: int, frame_h: int, track: "Track" = None):
    """HUD 各元素在成片中的位置与尺寸：[面板, 全景地图|None, 放大地图|None]，元素为 (x, y, w, h)
    面板用 panel.sx/sy，全景图用 map.sx/sy，放大图用 map.zsx/zsy —— 三者缩放互相独立，长宽可分别设置。"""
    fields = [f for f in st["fields"] if f in FIELD_META]
    base = frame_w / DESIGN_W
    cfgp = st["panel"]
    kpx, kpy = elem_scale(cfgp, base)
    pw, ph = panel_design_size(st, fields, cfgp["pos"])
    w = min(max(1, int(round(pw * kpx))), frame_w)
    h = min(max(1, int(round(ph * kpy))), frame_h)
    m = int(cfgp.get("margin", 90) * kpx)
    px, py = _elem_xy(cfgp.get("rel"), cfgp["pos"], frame_w, frame_h, w, h, m)
    out = [(px, py, w, h)]

    cfg = st["map"]
    kmx, kmy = elem_scale(cfg, base)
    kzx, kzy = elem_scale(cfg, base, "zsx", "zsy")
    ms_map = map_design_size(track) if (track is not None and cfg["enabled"]) else None
    ms_zoom = MAP_ZOOM_BOX if (track is not None and track.has_pos
                               and cfg.get("zoom_enabled", False)) else None
    for ms, kx, ky, rel_key, pos_key, dft_pos in ((ms_map, kmx, kmy, "rel", "pos", "top-right"),
                                                  (ms_zoom, kzx, kzy, "zoom_rel", "pos_zoom", "top-left")):
        if not ms:
            out.append(None)
            continue
        mw = min(max(1, int(round(ms[0] * kx))), frame_w)
        mh = min(max(1, int(round(ms[1] * ky))), frame_h)
        mm = int(cfg.get("margin", 88) * kx)
        x, y = _elem_xy(cfg.get(rel_key), cfg.get(pos_key, dft_pos), frame_w, frame_h, mw, mh, mm)
        out.append((x, y, mw, mh))
    return out


# ================================================================ 合成流水线
def find_ffmpeg(explicit_dir: str | None = None):
    """返回 (ffmpeg, ffprobe)，找不到时返回 (None, None)"""
    exe = ".exe" if os.name == "nt" else ""
    cands = []
    if explicit_dir:
        cands += [explicit_dir, os.path.join(explicit_dir, "bin")]
    for here in (app_dir(), resource_dir()):
        cands += [os.path.join(here, "tools"), os.path.join(here, "_internal", "tools"),
                  os.path.join(os.path.dirname(here), "tools")]
    for d in cands:
        f1, f2 = os.path.join(d, "ffmpeg" + exe), os.path.join(d, "ffprobe" + exe)
        if os.path.exists(f1) and os.path.exists(f2):
            return f1, f2
    f1, f2 = shutil.which("ffmpeg"), shutil.which("ffprobe")
    if f1 and f2:
        return f1, f2
    return None, None


def download_ffmpeg(target_dir: str, log=print):
    """从 npmmirror 镜像下载 Windows 版 ffmpeg/ffprobe（各约 80MB）"""
    import urllib.request
    os.makedirs(target_dir, exist_ok=True)
    base = "https://registry.npmmirror.com/-/binary/ffmpeg-static/b6.0/"
    for name in ("ffmpeg", "ffprobe"):
        url = base + name + "-win32-x64"
        dst = os.path.join(target_dir, name + ".exe")
        log("下载 %s …" % url)
        with urllib.request.urlopen(url, timeout=600) as r, open(dst, "wb") as f:
            shutil.copyfileobj(r, f, 1024 * 512)
        log("完成 %s (%.1f MB)" % (dst, os.path.getsize(dst) / 1048576.0))
    return os.path.join(target_dir, "ffmpeg.exe"), os.path.join(target_dir, "ffprobe.exe")


def target_size(disp_w: int, disp_h: int, height: int | str):
    """按目标高度算输出尺寸（height='orig' 表示原始）"""
    if height in ("orig", None, 0, "0"):
        return disp_w, disp_h
    oh = int(height)
    ow = int(round(disp_w * oh / float(disp_h)))
    return ow - ow % 2, oh


# ---------------------------------------------------------------- 耗时预估
_HUD_FRAME_COST = [0.16]          # 单帧 HUD 渲染耗时（秒），使用时动态校准
_ENCODE_SPEED = {2160: 0.45, 1440: 1.1, 1080: 2.0, 720: 3.2, 480: 5.0}


def calibrate_hud_cost(sec: float):
    _HUD_FRAME_COST[0] = 0.7 * _HUD_FRAME_COST[0] + 0.3 * sec
    return _HUD_FRAME_COST[0]


OUTPUT_RATE = {}                     # 实测输出速度缓存：{(高度, 画质): 输出秒/片长秒}


def rate_key(height, quality):
    return ("%s" % (height,), "%s" % (quality,))


def calibrate_output_rate(duration, elapsed, height=None, quality=None):
    """用一个「已跑完」的视频校准预估速度：返回新的倍率（输出秒 / 视频秒）"""
    try:
        duration, elapsed = float(duration), float(elapsed)
    except (TypeError, ValueError):
        return None
    if duration < 1.0 or elapsed <= 0.05:
        return None
    r = elapsed / duration
    if r <= 0.001 or r > 600:
        return None
    k = rate_key(height, quality)
    old = OUTPUT_RATE.get(k)
    OUTPUT_RATE[k] = r if old is None else (0.45 * r + 0.55 * old)
    return OUTPUT_RATE[k]


def get_output_rate(height=None, quality=None):
    return OUTPUT_RATE.get(rate_key(height, quality))


def set_output_rates(d):
    """从配置恢复历史实测速度"""
    try:
        for k, v in (d or {}).items():
            if isinstance(k, str) and "|" in k:
                a, b = k.split("|", 1)
                OUTPUT_RATE[(a, b)] = float(v)
    except Exception:
        pass


def output_rates():
    return {"%s|%s" % k: round(v, 4) for k, v in OUTPUT_RATE.items()}


def estimate_output_seconds(duration: float, height, quality: str, st: HudStyle, info=None,
                            workers: int | None = None, use_cal: bool = True):
    """预估单个视频的输出耗时（秒）：有同分辨率同画质的实测记录时优先用实测速度"""
    if use_cal:
        r = get_output_rate(height, quality)
        if r and r > 0:
            return max(1.0, float(duration) * r)
    fps = st["refresh_fps"]
    frames = max(1.0, duration * fps)
    if workers is None:
        workers = min(8, max(1, (os.cpu_count() or 4)))
    hud = frames * _HUD_FRAME_COST[0] / (workers * 0.72)   # 并行渲染效率折算
    oh = height
    if height in ("orig", None, 0, "0"):
        oh = info.disp_size[1] if info is not None else 1080
    base = _ENCODE_SPEED.get(int(oh), 0.45)
    q = QUALITY.get(quality, QUALITY["中"])
    qm = {"fast": 0.8, "veryfast": 1.0, "ultrafast": 1.4}.get(q["preset"], 1.0)
    enc = duration / max(base * qm, 0.05)
    return hud + enc


def _hud_job(args):
    """多进程帧渲染任务（模块级函数，便于 spawn）"""
    track, st, tq, fw, fh, hr, ppath, mpath, zpath = args
    img, mp, mz = build_hud(track, st, tq, fw, fh, hr)
    img.save(ppath + ".png")
    if mp and mpath:
        mp.save(mpath + ".png")
    if mz and zpath:
        mz.save(zpath + ".png")
    return True


def cleanup_workroot(root: str):
    """清掉输出目录里历次中断残留的 hud_*/pv_* 临时目录"""
    if not root or not os.path.isdir(root):
        return
    try:
        for name in os.listdir(root):
            if name.startswith("hud_") or name.startswith("pv_"):
                p = os.path.join(root, name)
                if os.path.isdir(p):
                    shutil.rmtree(p, ignore_errors=True)
    except Exception:
        pass


def process_video(video: str, track: Track, start_utc: float, out_path: str,
                  ffmpeg: str, ffprobe: str, st: HudStyle, info: VideoInfo | None = None,
                  height="orig", crf=23, preset="veryfast", keep_audio=True,
                  hr: HeartRate | None = None, t_range=None, log=print, progress=None,
                  cancel=None, workroot: str | None = None, workers: int | None = None):
    """完整流水线：HUD 帧序列 → ffmpeg 合成 → out_path"""
    info = info or probe_video(ffprobe, video)
    dw, dh = info.disp_size
    ow, oh = target_size(dw, dh, height)
    total = info.duration
    t0, t1 = (0.0, total) if not t_range else t_range
    t1 = min(t1, total)
    n = int(math.ceil((t1 - t0) * st["refresh_fps"])) + 2

    tmp = tempfile.mkdtemp(prefix="hud_", dir=workroot or None)
    dp = os.path.join(tmp, "panel")
    dm = os.path.join(tmp, "map")
    dz = os.path.join(tmp, "mapz")
    os.makedirs(dp, exist_ok=True)
    ms = map_design_size(track)
    has_map = bool(st["map"]["enabled"] and ms)
    has_zoom = bool(st["map"].get("zoom_enabled") and ms)
    if has_map:
        os.makedirs(dm, exist_ok=True)
    if has_zoom:
        os.makedirs(dz, exist_ok=True)
    try:
        import time
        log("  生成 HUD 帧 %d 张（%dfps）…" % (n, st["refresh_fps"]))
        t_cost = time.time()
        done = 0
        workers = workers or min(8, max(1, (os.cpu_count() or 4)))
        jobs = [(track, st, start_utc + t0 + i / float(st["refresh_fps"]), ow, oh, hr,
                 os.path.join(dp, "f%06d" % (i + 1)),
                 os.path.join(dm, "f%06d" % (i + 1)) if has_map else None,
                 os.path.join(dz, "f%06d" % (i + 1)) if has_zoom else None)
                for i in range(n)]
        if n >= 8 and workers > 1:
            try:
                import concurrent.futures as cf
                with cf.ProcessPoolExecutor(max_workers=workers) as ex:
                    for _ in ex.map(_hud_job, jobs, chunksize=4):
                        done += 1
                        if cancel and cancel():
                            raise RuntimeError("已取消")
                        if progress and done % 5 == 0:
                            progress(0.05 + 0.6 * done / n)
            except Exception as e:                     # 并行失败 → 一律回退单进程
                if "已取消" in str(e):
                    raise
                log("  （并行渲染不可用，改用单进程：%s）" % str(e)[:120])
                done = 0
        if done < n:
            for i in range(done, n):
                if cancel and cancel():
                    raise RuntimeError("已取消")
                p, m, z = build_hud(track, st, jobs[i][2], ow, oh, hr)
                p.save(os.path.join(dp, "f%06d.png" % (i + 1)))
                if m:
                    m.save(os.path.join(dm, "f%06d.png" % (i + 1)))
                if z:
                    z.save(os.path.join(dz, "f%06d.png" % (i + 1)))
                if progress and i % 5 == 0:
                    progress(0.05 + 0.6 * (i + 1) / n)
        if n:
            per = (time.time() - t_cost) / n
            calibrate_hud_cost(per)
            log("  HUD 帧完成（%.3f 秒/帧）" % per)

        cmd = [ffmpeg, "-y", "-hide_banner", "-loglevel", "error", "-stats"]
        if t0 > 0:
            cmd += ["-ss", "%.3f" % t0]
        cmd += ["-i", video]
        cmd += ["-framerate", str(st["refresh_fps"]), "-i", os.path.join(dp, "f%06d.png")]
        layout = hud_layout(st, ow, oh, track)
        (px, py, _, _), mpos, zpos = layout
        chain = ""
        base = "[0:v]"
        if (ow, oh) != (dw, dh):
            chain += "[0:v]scale=%d:%d[b];" % (ow, oh)
            base = "[b]"
        chain += "%s[1:v]overlay=x=%d:y=%d:shortest=0[t]" % (base, px, py)
        last = "[t]"
        next_in = 2
        for pos, d in ((mpos, dm), (zpos, dz)):
            if not pos:
                continue
            cmd += ["-framerate", str(st["refresh_fps"]), "-i", os.path.join(d, "f%06d.png")]
            lab = "ov%d" % next_in
            chain += ";%s[%d:v]overlay=x=%d:y=%d:shortest=0[%s]" % (
                last, next_in, pos[0], pos[1], lab)
            last, next_in = "[%s]" % lab, next_in + 1
        chain += ";%sformat=yuv420p[v]" % last
        cmd += ["-filter_complex", chain, "-map", "[v]"]
        cmd += ["-map", "0:a", "-c:a", "copy"] if (keep_audio and info.has_audio) else ["-an"]
        cmd += ["-c:v", "libx264", "-preset", preset, "-crf", str(crf),
                "-movflags", "+faststart", "-map_metadata", "0"]
        if t_range:                       # 输出选项必须放在输出路径之前
            cmd += ["-t", "%.3f" % (t1 - t0)]
        cmd += [out_path]
        log("  ffmpeg 合成中（%dx%d, CRF %s）…" % (ow, oh, crf))
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, encoding="utf-8", errors="ignore", bufsize=1,
                                creationflags=_NO_WINDOW)
        buf = ""
        for line in proc.stdout:
            buf += line
            if cancel and cancel():
                proc.kill()
                raise RuntimeError("已取消")
            m = re.search(r"time=(\d+):(\d+):([\d.]+)", line)
            if m and progress:
                cur = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3)) + t0
                progress(0.65 + 0.35 * min(1.0, cur / max(t1, 1e-6)))
        proc.wait()
        if proc.returncode != 0:
            raise RuntimeError("ffmpeg 失败（%d）：\n%s" % (proc.returncode, buf[-1200:]))
        progress and progress(1.0)
        log("  输出：%s (%.1f MB)" % (out_path, os.path.getsize(out_path) / 1048576.0))
        return out_path
    finally:
        # Windows 上偶尔会因文件句柄未释放导致首删失败，重试几次；再清一遍历史残留
        for _ in range(4):
            shutil.rmtree(tmp, ignore_errors=True)
            if not os.path.exists(tmp):
                break
            time.sleep(0.4)
        if workroot:
            cleanup_workroot(workroot)


def compose_frame(bg: Image.Image, track: Track, st: HudStyle, tq: float,
                  hr: HeartRate | None = None, downscale: float = 1.0):
    """把 HUD（面板 + 全景图 + 放大图）叠加到一张背景帧上（供界面实时预览）"""
    lay = hud_layout(st, bg.width, bg.height, track)
    out = bg.convert("RGBA")
    for im, rect in zip(build_hud_layers(track, st, tq, hr), lay):
        if im is None or not rect:
            continue
        out.alpha_composite(fit_layer(im, rect[2], rect[3]), rect[:2])
    if downscale != 1.0:
        out = out.resize((max(1, int(out.width * downscale)), max(1, int(out.height * downscale))),
                         Image.LANCZOS)
    return out.convert("RGB")


def grab_frame(ffmpeg: str, video: str, seek: float, info: VideoInfo | None = None,
               max_w: int = 1280):
    """抽一帧（等比缩小到 max_w 以内）作为预览背景"""
    if info is not None:
        seek = min(seek, max(info.duration - 0.2, 0))
    tmp = tempfile.mkdtemp(prefix="pv_")
    try:
        raw = os.path.join(tmp, "f.png")
        subprocess.run([ffmpeg, "-hide_banner", "-loglevel", "error", "-y", "-ss", "%.3f" % seek,
                        "-i", video, "-frames:v", "1", "-vf", "scale=%d:-2" % max_w, raw],
                       check=True, creationflags=_NO_WINDOW)
        return Image.open(raw).convert("RGBA")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def preview_frame(video: str, track: Track, start_utc: float, out_png: str,
                  ffmpeg: str, ffprobe: str, st: HudStyle, info=None, seek=2.0,
                  hr: HeartRate | None = None, downscale=0.5):
    """抽一帧与 HUD 合成，输出预览图"""
    info = info or probe_video(ffprobe, video)
    seek = min(seek, max(info.duration - 0.2, 0))
    bg = grab_frame(ffmpeg, video, seek, info, max_w=1080)
    compose_frame(bg, track, st, start_utc + seek, hr, downscale).save(out_png, quality=92)
    return out_png


# ---------------------------------------------------------------- CLI
def _cli(argv):
    import argparse
    ap = argparse.ArgumentParser(description="把运动轨迹信息叠加到视频（命令行）")
    ap.add_argument("--track", "--gpx", dest="track", required=True,
                    help="轨迹文件（GPX / FIT / TCX / XML）")
    ap.add_argument("--video", nargs="+", required=True)
    ap.add_argument("--start", nargs="*", default=None,
                    help="每个视频的拍摄开始时间（'YYYY-MM-DD HH:MM:SS'，缺省自动识别）")
    ap.add_argument("--outdir", default="out")
    ap.add_argument("--style", default=None, help="显示样式：%s" % "/".join(STYLES))
    ap.add_argument("--fields", default=None, help="逗号分隔的字段 id（默认按运动类型）")
    ap.add_argument("--template", default="骑行", choices=TEMPLATE_ORDER, help="数值模板")
    ap.add_argument("--panel-pos", default="下", choices=POSITIONS)
    ap.add_argument("--map-pos", default="右上角", choices=POSITIONS)
    ap.add_argument("--scale", type=float, default=None)
    ap.add_argument("--opacity", type=int, default=None)
    ap.add_argument("--title", default=None)
    ap.add_argument("--height", default="orig")
    ap.add_argument("--quality", default="中", choices=QUALITY_ORDER)
    ap.add_argument("--ffmpeg-dir", default=None)
    ap.add_argument("--hr", default=None, help="心率 CSV（可选）")
    ap.add_argument("--range", default=None, help="只渲染 t0,t1 秒（测试用）")
    ap.add_argument("--sample", default=None, help="只出单帧预览图")
    a = ap.parse_args(argv)

    ff, fp = find_ffmpeg(a.ffmpeg_dir)
    if not ff:
        print("未找到 ffmpeg/ffprobe，请用 --ffmpeg-dir 指定目录")
        return 2
    track = Track.from_file(a.track)
    hr = HeartRate.from_file(a.hr, track) if a.hr else None
    st = HudStyle()
    if a.style:
        st.update(dict(style=STYLE_ID.get(a.style, a.style)))
    if a.fields:
        st.update(dict(fields=[x.strip() for x in a.fields.split(",") if x.strip()]))
    else:
        st.update(dict(fields=list(TEMPLATES[a.template])))
    st.update(dict(panel=dict(pos=POS_ID[a.panel_pos]), map=dict(pos=POS_ID[a.map_pos])))
    if a.title:
        st.update(dict(title=a.title))
    if a.scale:
        st.update(dict(panel=dict(sx=a.scale, sy=a.scale)))
    if a.opacity is not None:
        st.update(dict(panel=dict(opacity=a.opacity)))
    st.update(dict(fields=[f for f in st["fields"] if field_ok(f, track)],
                   speed_max=auto_speed_max(track)))
    print("轨迹:", track.summary())
    q = QUALITY[a.quality]
    rng = None
    if a.range:
        s, e = a.range.split(",")
        rng = (float(s), float(e))
    os.makedirs(a.outdir, exist_ok=True)
    for i, v in enumerate(a.video):
        info = probe_video(fp, v)
        st.update(dict(refresh_fps=auto_refresh_fps(info.duration)))
        if a.start and i < len(a.start) and a.start[i]:
            st_ts = datetime.datetime.strptime(a.start[i], "%Y-%m-%d %H:%M:%S").replace(
                tzinfo=track.tz).timestamp()
            src = "指定"
        else:
            st_ts, src = detect_start_time(info, 8.0)
        print("%s -> 起点 %s (%s) 时长 %.1fs 显示 %dx%d 预计 %.0f 秒" %
              (os.path.basename(v),
               datetime.datetime.fromtimestamp(st_ts, track.tz).strftime("%Y-%m-%d %H:%M:%S") if st_ts else "无",
               src, info.duration, *info.disp_size,
               estimate_output_seconds(info.duration, a.height, a.quality, st, info)))
        if st_ts is None:
            continue
        if a.sample:
            preview_frame(v, track, st_ts, a.sample, ff, fp, st, info, 2.0, hr)
            print("预览图:", a.sample)
            continue
        name = os.path.splitext(os.path.basename(v))[0] + "_GPS.mp4"
        process_video(v, track, st_ts, os.path.join(a.outdir, name), ff, fp, st, info,
                      a.height, q["crf"], q["preset"], True, hr, rng, log=print)
    return 0


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()      # 打包后 HUD 帧并行渲染的子进程依赖此调用
    sys.exit(_cli(sys.argv[1:]))
