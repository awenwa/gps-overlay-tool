# -*- coding: utf-8 -*-
"""GPS 轨迹视频叠加工具 —— 图形界面 v5
左侧：运动信息与视频 / 信息显示设置 / 输出与执行
右侧：实时预览（位置与大小直接在预览图上拖动调整；拖动为“图层级”重绘，不再卡顿）
"""
import datetime
import json
import os
import queue
import subprocess
import sys
import threading
import time
import traceback

import tkinter as tk
from tkinter import colorchooser, filedialog, font as tkfont, messagebox, simpledialog, ttk

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gps_overlay_core as C   # noqa: E402

APP_DIR = C.app_dir()                      # 打包后为 exe 所在目录
SETTINGS = os.path.join(APP_DIR, "settings.json")
LAYOUTS = os.path.join(APP_DIR, "layouts.json")
VIDEO_EXT = (".mp4", ".mov", ".m4v", ".avi", ".mkv", ".insv", ".mts", ".m2ts", ".ts", ".webm")
TRACK_EXT = (".gpx", ".fit", ".tcx", ".xml", ".kml")
COLORS = {"翠绿": [70, 225, 135], "橙色": [255, 150, 40], "青色": [60, 205, 235],
          "品红": [240, 90, 180], "明黄": [250, 215, 70], "红色": [240, 80, 80],
          "天蓝": [80, 150, 255], "紫色": [170, 110, 250]}
BG = "#eef1f6"
CARD = "#ffffff"
FG = "#1c2430"
MUTED = "#5f6b7a"
ACCENT = "#2f6feb"
OK = "#0a8a4f"
WARN_BG = "#ffe3e0"
WARN_FG = "#b3261e"
PREVIEW_W = 400
LOG_MIN_LINES = 5             # 日志框最小行数（内容超出一屏时用它）
SLIDER_LEN = 108
CORNER_TOL = 18.0              # 预览图上“角”的命中半径（像素，会按元素大小自适应）
EDGE_TOL = 11.0                # 预览图上“边”的命中带宽（像素，会按元素大小自适应）
SCALE_GAIN = 0.5               # 缩放灵敏度：鼠标移动 1px，元素边缘只跟随 0.5px（越小越稳）
NO_WINDOW = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
SHUTDOWN_SECONDS = 60          # “输出完成后关机”的倒计时
DEFAULT_LAYOUT = "默认"

try:
    from PIL import Image, ImageDraw, ImageTk
except Exception:              # pragma: no cover
    ImageTk = None


def fmt_dur(sec):
    sec = int(round(sec))
    if sec >= 3600:
        return "%d 小时 %02d 分" % (sec // 3600, sec % 3600 // 60)
    if sec >= 60:
        return "%d 分 %02d 秒" % (sec // 60, sec % 60)
    return "%d 秒" % sec


def win_path(p):
    """转成 Windows 习惯的路径写法（统一反斜杠）"""
    return os.path.normpath(p) if p else p


class App:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("GPS 轨迹视频叠加工具")
        root.geometry("1260x980")
        root.minsize(1160, 880)
        root.configure(bg=BG)
        self.q = queue.Queue()
        self.cancel_flag = threading.Event()
        self.worker = None
        self.track = None
        self.tracks = []              # [dict(path, tr, err, disp)]
        self.videos = []              # [dict(path,dur,start,src,info,auto,offset,disp)]
        self.ffmpeg = self.ffprobe = None
        self.custom_color = [70, 225, 135]
        # 预览相关
        self._pv_bg = None
        self._pv_key = None
        self._pv_timer = None
        self._drag_timer = None
        self._est_timer = None
        self._busy_flag = False
        self._drag = None             # [元素名, 模式, 按下时的矩形x0,y0,w0,h0, 抓取偏移x, 抓取偏移y]
        self._pv_elems = {}           # 元素在预览图上的显示矩形 {name:(x,y,w,h)}
        self._pv_disp = None          # 预览显示图（PIL），用于叠加悬停高亮
        self._pv_hover = None         # 当前鼠标悬停的元素名
        self._pv_mode = None          # 当前悬停对应的操作模式
        self._pv_cursor = None        # 当前鼠标指针形状
        self._pv_ds = 1.0
        self._pv_osize = None         # 成片画幅（预览与输出共用，拖动写回坐标才不错位）
        self._layers = None           # 设计尺寸 HUD 图层（面板/全景/放大）
        self._layers_key = None
        self._layer_busy = False
        self._layer_pending = False
        self.rel = {"panel": None, "map": None, "zoom": None}
        # 每个元素独立的宽/高缩放（1.0 = 100%）
        self.escale = {"panel": [1.0, 1.0], "map": [1.0, 1.0], "zoom": [1.0, 1.0]}
        self.layouts = {}

        self._style_ui()
        self._make_vars()
        self._build()
        self._load_layouts()
        self._load_settings()
        self._init_ffmpeg()
        args = [a for a in sys.argv[1:] if os.path.isfile(a)]
        tr_args = [a for a in args if a.lower().endswith(TRACK_EXT)]
        vid_args = [a for a in args if a.lower().endswith(VIDEO_EXT)]
        if tr_args:
            self._parse_tracks(tr_args)
        if vid_args:
            self.root.after(400, lambda: self._probe_async(vid_args))
        self.root.after(120, self._drain)
        root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------------------------------------------------------- 变量
    def _make_vars(self):
        self.track_info = tk.StringVar(value="未选择轨迹文件")
        self.title_var = tk.StringVar(value="GPS 运动轨迹")
        self.gstyle_var = tk.StringVar(value="圆形仪表盘")
        self.color_var = tk.StringVar(value="翠绿")
        self.panel_op_var = tk.IntVar(value=60)
        self.map_op_var = tk.IntVar(value=60)
        self.tpl_var = tk.StringVar(value="骑行")
        self.map_var = tk.BooleanVar(value=True)
        self.zoom_var = tk.BooleanVar(value=True)
        self.panel_op_lbl = tk.StringVar(value="60%")
        self.map_op_lbl = tk.StringVar(value="60%")
        self.layout_var = tk.StringVar(value=DEFAULT_LAYOUT)
        self.fvars = {f: tk.BooleanVar(value=f in C.TEMPLATES["骑行"]) for f in C.FIELD_ORDER}
        self.outdir_var = tk.StringVar(value=win_path(os.path.join(os.path.expanduser("~"), "Desktop")))
        self.height_var = tk.StringVar(value="1080 (全高清)")
        self.quality_var = tk.StringVar(value="中")
        self.audio_var = tk.BooleanVar(value=True)
        self.shutdown_var = tk.BooleanVar(value=False)
        self.eta_var = tk.StringVar(value="预计输出时间：—")
        self.pv_pos_var = tk.DoubleVar(value=25.0)
        self.pv_time = tk.StringVar(value="")
        self.pv_status = tk.StringVar(value="选择轨迹与视频后自动预览")
        self.prog_var = tk.DoubleVar(value=0.0)
        self.stat_var = tk.StringVar(value="就绪")
        for v in (self.title_var, self.gstyle_var, self.color_var,
                  self.panel_op_var, self.map_op_var, self.map_var, self.zoom_var):
            v.trace_add("write", lambda *_: self._pv_schedule())
        for v in (self.panel_op_var, self.map_op_var):
            v.trace_add("write", lambda *_: self._sync_slider_labels())
        for v in self.fvars.values():
            v.trace_add("write", lambda *_: self._pv_schedule())
        for v in (self.height_var, self.quality_var):
            v.trace_add("write", lambda *_: self._eta_schedule())
        self.pv_pos_var.trace_add("write", lambda *_: self._pv_schedule())

    def _sync_slider_labels(self):
        self.panel_op_lbl.set("%d%%" % int(self.panel_op_var.get()))
        self.map_op_lbl.set("%d%%" % int(self.map_op_var.get()))

    # ---------------------------------------------------------------- 外观
    def _style_ui(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        base = ("Microsoft YaHei UI", 10)
        bold = ("Microsoft YaHei UI", 10, "bold")
        title = ("Microsoft YaHei UI", 11, "bold")
        st.configure(".", background=BG, foreground=FG, font=base)
        st.configure("Card.TLabelframe", background=CARD, borderwidth=1, relief="solid", padding=0)
        st.configure("Card.TLabelframe.Label", background=CARD, foreground=ACCENT, font=title)
        st.configure("Card.TFrame", background=CARD)
        st.configure("Card.TLabel", background=CARD, font=base)
        st.configure("Card.TCheckbutton", background=CARD, font=base)
        st.map("Card.TCheckbutton", background=[("disabled", CARD)])
        st.configure("TLabel", background=BG, font=base)
        st.configure("TFrame", background=BG)
        st.configure("TButton", font=base, padding=(8, 2))
        st.configure("Muted.TLabel", background=CARD, foreground=MUTED, font=("Microsoft YaHei UI", 9))
        st.configure("Info.TLabel", background=CARD, foreground=OK, font=("Microsoft YaHei UI", 9))
        st.configure("Eta.TLabel", background=CARD, foreground=ACCENT, font=bold)
        st.configure("Small.TLabel", background=CARD, font=("Microsoft YaHei UI", 9))
        st.configure("Tiny.TLabel", background=CARD, foreground=MUTED, font=("Microsoft YaHei UI", 8))
        try:
            st.configure("Slider.Horizontal.TScale", background=CARD, troughcolor="#dbe2ec",
                         sliderlength=18, sliderthickness=11, borderwidth=1)
        except tk.TclError:
            st.configure("Slider.Horizontal.TScale", background=CARD, troughcolor="#dbe2ec")
        st.configure("Treeview", rowheight=24, font=("Microsoft YaHei UI", 9),
                     background="#ffffff", fieldbackground="#ffffff")
        st.configure("Treeview.Heading", font=("Microsoft YaHei UI", 9, "bold"),
                     background="#e3e9f2", padding=(2, 2))
        st.configure("GO.TButton", font=("Microsoft YaHei UI", 11, "bold"), padding=(14, 4))
        st.configure("TProgressbar", troughcolor="#dfe5ee", background=ACCENT)
        st.configure("TCombobox", fieldbackground="#ffffff")

    def _card(self, parent, title, top=7):
        """top：卡片上方留白。首张卡片传 0，使其与窗口顶部齐平。"""
        f = ttk.LabelFrame(parent, text="  %s " % title, style="Card.TLabelframe", padding=(10, 3))
        f.pack(fill="x", padx=8, pady=(top, 0))
        return f

    @staticmethod
    def _table(parent, height, columns):
        """带垂直滚动条的表格容器"""
        wrap = ttk.Frame(parent, style="Card.TFrame")
        wrap.pack(fill="x", pady=2)
        tv = ttk.Treeview(wrap, columns=columns, show="headings", height=height)
        sb = ttk.Scrollbar(wrap, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb.set)
        tv.pack(side="left", fill="x", expand=True)
        sb.pack(side="right", fill="y")
        return tv

    def _fit_log(self):
        """让日志框吃掉左侧剩余竖向空间，消除窗口下方的大片空白。

        内容不足一屏 → 日志自动变高把空白填满；内容已超出一屏 → 保持最小行数。
        base 用「inner 总高 − 日志自身高」求得，与当前日志高度无关，故不会自激振荡。
        """
        cv = getattr(self, "_canvas", None)
        log = getattr(self, "log", None)
        if cv is None or log is None or getattr(self, "_inner", None) is None:
            return
        h = cv.winfo_height()
        if h < 200:
            return
        if not getattr(self, "_log_line_px", 0):
            try:
                self._log_line_px = max(10, tkfont.Font(font=log.cget("font")).metrics("linespace"))
            except Exception:
                self._log_line_px = 15
        base = self._inner.winfo_reqheight() - log.winfo_reqheight()   # 除日志外的内容高度
        per = self._log_line_px      # 每行像素（实测 14）
        chrome, margin = 4, 2        # Text 边框+内边距（实测 4）、底部留白
        avail = h - base - chrome - margin
        lines = LOG_MIN_LINES if avail <= 0 else max(LOG_MIN_LINES, int(avail // per))
        # 取整会余下不足一行的空白：只要再补一行仍放得下就补上，吃满空白且保证不溢出
        while base + (lines + 1) * per + chrome + margin <= h:
            lines += 1
        if lines != int(log.cget("height")):
            log.configure(height=lines)

    # ---------------------------------------------------------------- 界面
    def _build(self):
        left = ttk.Frame(self.root)
        left.pack(side="left", fill="both", expand=True)
        canvas = tk.Canvas(left, bg=BG, highlightthickness=0)
        vs = ttk.Scrollbar(left, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vs.set)
        canvas.pack(side="left", fill="both", expand=True)
        vs.pack(side="right", fill="y")
        inner = ttk.Frame(canvas)
        self._inner = inner
        self._win = canvas.create_window((0, 0), window=inner, anchor="nw", tags="inner")
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: (canvas.itemconfigure("inner", width=e.width),
                                              self._fit_log()))
        self._canvas = canvas
        canvas.bind_all("<MouseWheel>", lambda e: canvas.yview_scroll(-1 if e.delta > 0 else 1, "units"))
        self.root.bind("<Prior>", lambda e: canvas.yview_scroll(-1, "pages"))
        self.root.bind("<Next>", lambda e: canvas.yview_scroll(1, "pages"))

        # -------- 1 运动信息与视频 --------
        f1 = self._card(inner, "1 · 运动信息与视频", top=0)   # 首卡贴齐窗口顶部，消除上方空隙
        r = ttk.Frame(f1, style="Card.TFrame"); r.pack(fill="x", pady=(3, 2))
        ttk.Label(r, text="轨迹文件：", style="Card.TLabel").pack(side="left")
        for text, cmd, w in (("添加轨迹…", self.add_tracks, 10),
                             ("移除选中", self.remove_track, 9), ("清空", self.clear_tracks, 6)):
            ttk.Button(r, text=text, width=w, command=cmd).pack(side="left", padx=(0, 5))
        ttk.Label(r, text="支持 GPX / FIT / TCX / XML，可导入多条；选中哪条就用哪条。",
                  style="Muted.TLabel").pack(side="left", padx=(6, 0))

        self.tt = self._table(f1, 2, ("name", "dist", "date", "start", "end", "dur"))
        for c, t, w in (("name", "轨迹文件", 200), ("dist", "距离", 76), ("date", "日期", 88),
                        ("start", "起点时间", 78), ("end", "终点时间", 78), ("dur", "时长", 78)):
            self.tt.heading(c, text=t)
            self.tt.column(c, width=w, anchor="w" if c == "name" else "center",
                           stretch=(c == "name"))
        self.tt.bind("<<TreeviewSelect>>", lambda e: self._select_track())
        ttk.Label(f1, textvariable=self.track_info, style="Info.TLabel").pack(anchor="w", pady=(0, 5))

        r = ttk.Frame(f1, style="Card.TFrame"); r.pack(fill="x", pady=(2, 2))
        ttk.Label(r, text="视频文件：", style="Card.TLabel").pack(side="left")
        for text, cmd, w in (("添加视频…", self.add_videos, 10), ("添加文件夹", self.add_folder, 10),
                             ("批量调整时间", self.batch_adjust, 12), ("移除选中", self.remove_sel, 9),
                             ("清空", self.clear_videos, 6)):
            ttk.Button(r, text=text, width=w, command=cmd).pack(side="left", padx=(0, 5))

        self.tv = self._table(f1, 7, ("no", "name", "dur", "size", "start", "adjust"))
        self.tv.tag_configure("warn", background=WARN_BG, foreground=WARN_FG)
        self.tv.tag_configure("out", background="#fff4e0", foreground="#8a5300")
        for c, t, w in (("no", "No.", 42), ("name", "视频文件", 210), ("dur", "时长", 58),
                        ("size", "分辨率", 78), ("start", "起点时间（点此修改）", 150),
                        ("adjust", "调整(秒)（点此修改）", 106)):
            self.tv.heading(c, text=t)
            self.tv.column(c, width=w, anchor="w" if c == "name" else "center",
                           stretch=(c == "name"))
        self.tv.bind("<Double-1>", self._edit_video)
        self.tv.bind("<Button-1>", self._edit_video)      # 单击直接进入编辑，不必双击
        self.tv.bind("<Return>", lambda e: self._edit_selected("#5"))
        self.tv.bind("<F2>", lambda e: self._edit_selected("#5"))
        self.tv.tag_configure("editable", foreground="#1a56c4")
        self.tv.bind("<<TreeviewSelect>>", lambda e: self._pv_schedule(force=True))
        ttk.Label(f1, text="红色行 = 拍摄时间与轨迹时间范围不相交；橙色行 = 只有部分重叠。\n"
                           "蓝色列可直接点一下就改：『起点时间』填绝对时刻（2026-09-14 07:51:45），"
                           "『调整(秒)』按秒微调（如 +3 或 -2.5）。回车确认，Esc 取消。",
                  style="Tiny.TLabel", justify="left").pack(anchor="w", pady=(3, 0))

        # -------- 2 信息显示设置 --------
        f2 = self._card(inner, "2 · 信息显示设置")
        r = ttk.Frame(f2, style="Card.TFrame"); r.pack(fill="x", pady=(3, 2))
        ttk.Label(r, text="标题：", style="Card.TLabel").pack(side="left")
        ttk.Entry(r, textvariable=self.title_var, width=14).pack(side="left", padx=(0, 12))
        ttk.Label(r, text="主色调：", style="Card.TLabel").pack(side="left")
        self.color_cb = ttk.Combobox(r, textvariable=self.color_var,
                                     values=list(COLORS) + ["自定义…"], width=7, state="readonly")
        self.color_cb.pack(side="left", padx=(0, 5))
        self.color_cb.bind("<<ComboboxSelected>>", lambda e: self._on_color())
        self.sw = tk.Canvas(r, width=24, height=18, highlightthickness=1,
                            highlightbackground="#c6cdd8")
        self.sw.pack(side="left", padx=(0, 12))
        self._swatch()
        ttk.Label(r, text="仪表盘样式：", style="Card.TLabel").pack(side="left")
        ttk.Combobox(r, textvariable=self.gstyle_var, values=C.STYLES, width=10,
                     state="readonly").pack(side="left")

        r = ttk.Frame(f2, style="Card.TFrame"); r.pack(fill="x", pady=1)
        ttk.Label(r, text="数值面板", style="Small.TLabel").pack(side="left")
        ttk.Label(r, text="背景透明度", style="Small.TLabel").pack(side="left", padx=(4, 0))
        ttk.Scale(r, from_=0, to=100, variable=self.panel_op_var, style="Slider.Horizontal.TScale",
                  length=SLIDER_LEN).pack(side="left", padx=(3, 3))
        ttk.Label(r, textvariable=self.panel_op_lbl, width=4, style="Small.TLabel").pack(side="left")
        ttk.Label(r, text="轨迹图", style="Small.TLabel").pack(side="left", padx=(12, 0))
        ttk.Checkbutton(r, text="全景", variable=self.map_var,
                        style="Card.TCheckbutton").pack(side="left", padx=(4, 0))
        ttk.Checkbutton(r, text="放大", variable=self.zoom_var,
                        style="Card.TCheckbutton").pack(side="left")
        ttk.Label(r, text="背景透明度", style="Small.TLabel").pack(side="left", padx=(8, 0))
        ttk.Scale(r, from_=0, to=100, variable=self.map_op_var, style="Slider.Horizontal.TScale",
                  length=SLIDER_LEN).pack(side="left", padx=(3, 3))
        ttk.Label(r, textvariable=self.map_op_lbl, width=4, style="Small.TLabel").pack(side="left")

        r = ttk.Frame(f2, style="Card.TFrame"); r.pack(fill="x", pady=(3, 1))
        ttk.Label(r, text="信息布局：", style="Card.TLabel").pack(side="left")
        self.layout_cb = ttk.Combobox(r, textvariable=self.layout_var,
                                      values=[DEFAULT_LAYOUT], width=14, state="readonly")
        self.layout_cb.pack(side="left", padx=(0, 6))
        self.layout_cb.bind("<<ComboboxSelected>>", lambda e: self._apply_layout())
        ttk.Button(r, text="保存信息布局设置…", width=19,
                   command=self._save_layout).pack(side="left", padx=(0, 5))
        ttk.Button(r, text="删除", width=6, command=self._del_layout).pack(side="left")
        ttk.Label(f2, text="在右侧预览图上：按住数值面板 / 轨迹图拖动可移动位置；按住任一个角拖动＝等比缩放，"
                           "按住某条边拖动＝只移动该边（改宽或改高）。鼠标靠近角/边时元素会显示虚线框。",
                  style="Tiny.TLabel", justify="left", wraplength=760).pack(anchor="w", pady=(2, 0))

        ttk.Separator(f2).pack(fill="x", pady=4)
        r = ttk.Frame(f2, style="Card.TFrame"); r.pack(fill="x")
        ttk.Label(r, text="运动形式：", style="Card.TLabel").pack(side="left")
        self.tpl_cb = ttk.Combobox(r, textvariable=self.tpl_var, values=C.TEMPLATE_ORDER,
                                   width=7, state="readonly")
        self.tpl_cb.pack(side="left", padx=(0, 8))
        self.tpl_cb.bind("<<ComboboxSelected>>", lambda e: self._apply_template())
        ttk.Label(r, text="（灰色的选项表示没有该项数据）", style="Muted.TLabel").pack(side="left")
        grid = ttk.Frame(f2, style="Card.TFrame"); grid.pack(fill="x", pady=(2, 0))
        self.fchecks = {}
        for i, fid in enumerate(C.FIELD_ORDER):
            name = C.FIELD_META[fid][0]
            cb = ttk.Checkbutton(grid, text=name, variable=self.fvars[fid], style="Card.TCheckbutton")
            cb.grid(row=i // 5, column=i % 5, sticky="w", padx=(0, 6), pady=0)
            self.fchecks[fid] = cb
        for c in range(5):
            grid.columnconfigure(c, weight=1)

        # -------- 3 输出与执行 --------
        f3 = self._card(inner, "3 · 输出与执行")
        r = ttk.Frame(f3, style="Card.TFrame"); r.pack(fill="x", pady=(3, 1))
        ttk.Label(r, text="输出目录：", style="Card.TLabel").pack(side="left")
        ttk.Entry(r, textvariable=self.outdir_var, font=("Microsoft YaHei UI", 9)).pack(
            side="left", fill="x", expand=True, padx=(0, 5))
        ttk.Button(r, text="浏览…", width=8, command=self.pick_outdir).pack(side="left", padx=(0, 4))
        ttk.Button(r, text="打开", width=6, command=self._open_outdir).pack(side="left", padx=(0, 10))
        ttk.Checkbutton(r, text="输出完成后关机", variable=self.shutdown_var,
                        style="Card.TCheckbutton").pack(side="left")

        r = ttk.Frame(f3, style="Card.TFrame"); r.pack(fill="x", pady=(4, 1))
        ttk.Label(r, text="输出分辨率：", style="Card.TLabel").pack(side="left")
        ttk.Combobox(r, textvariable=self.height_var, values=list(C.HEIGHTS_UI), width=13,
                     state="readonly").pack(side="left", padx=(0, 14))
        ttk.Label(r, text="画质：", style="Card.TLabel").pack(side="left")
        ttk.Combobox(r, textvariable=self.quality_var, values=C.QUALITY_ORDER, width=6,
                     state="readonly").pack(side="left", padx=(0, 14))
        ttk.Checkbutton(r, text="保留原声", variable=self.audio_var,
                        style="Card.TCheckbutton").pack(side="left")
        self.btn_run = ttk.Button(r, text="开始生成", width=12, style="GO.TButton", command=self.do_run)
        self.btn_run.pack(side="left", padx=(18, 0))
        self.btn_stop = ttk.Button(r, text="停止", width=7, command=self.do_stop, state="disabled")
        self.btn_stop.pack(side="left", padx=(6, 0))
        self.stat_lbl = ttk.Label(r, textvariable=self.stat_var, style="Eta.TLabel")
        self.stat_lbl.pack(side="left", padx=12)

        r = ttk.Frame(f3, style="Card.TFrame"); r.pack(fill="x", pady=(3, 1))
        ttk.Label(r, textvariable=self.eta_var, style="Small.TLabel").pack(side="left")
        ttk.Progressbar(r, variable=self.prog_var, maximum=100.0, length=200).pack(side="right")
        self.log = tk.Text(f3, height=5, wrap="word", bg="#141922", fg="#d5dbe5",
                           insertbackground="#d5dbe5", font=("Consolas", 9), relief="flat")
        self.log.pack(fill="x", pady=(4, 0))
        self.log.configure(state="disabled")

        # ============ 右：实时预览 ============
        right = ttk.Frame(self.root, style="Card.TFrame", width=PREVIEW_W + 44)
        right.pack_propagate(False)
        right.pack(side="left", fill="y", padx=(8, 8), pady=8)
        pr = ttk.LabelFrame(right, text="  实时预览 ", style="Card.TLabelframe", padding=(12, 8))
        pr.pack(fill="both", expand=True)
        self.pv_label = tk.Label(pr, bg="#20242c", fg="#9aa4b2", width=PREVIEW_W,
                                 text="预览区域", font=("Microsoft YaHei UI", 11), cursor="hand2")
        self.pv_label.pack(pady=(2, 6))
        self.pv_label.configure(width=PREVIEW_W, height=int(PREVIEW_W * 1.55))
        self.pv_label.bind("<ButtonPress-1>", self._pv_press)
        self.pv_label.bind("<B1-Motion>", self._pv_drag)
        self.pv_label.bind("<ButtonRelease-1>", self._pv_release)
        self.pv_label.bind("<Motion>", self._pv_motion)
        self.pv_label.bind("<Leave>", lambda e: self._pv_hover_set(None))
        r = ttk.Frame(pr, style="Card.TFrame"); r.pack(fill="x")
        ttk.Label(r, text="预览时刻：", style="Card.TLabel").pack(side="left")
        self.pv_scale = ttk.Scale(r, from_=0, to=100, variable=self.pv_pos_var, length=PREVIEW_W - 150,
                                  command=lambda v: self._pv_schedule())
        self.pv_scale.pack(side="left", fill="x", expand=True)
        ttk.Label(pr, textvariable=self.pv_time, style="Muted.TLabel").pack(anchor="w", pady=(2, 0))
        ttk.Label(pr, textvariable=self.pv_status, style="Muted.TLabel", wraplength=PREVIEW_W).pack(
            anchor="w", pady=(2, 0))
        ttk.Label(pr, text="拖动提示：拖元素主体移动位置；按住任一个角拖动＝等比缩放；\n"
                           "按住某条边拖动＝只移动该边（改宽或改高）。\n"
                           "鼠标靠近角或边时该元素会显示虚线框与对应指针。",
                  style="Muted.TLabel", wraplength=PREVIEW_W, justify="left").pack(anchor="w", pady=(6, 0))

    # ---------------------------------------------------------------- 通用
    def _swatch(self):
        rgb = self._color_rgb()
        self.sw.configure(bg="#%02x%02x%02x" % tuple(rgb))

    def _color_rgb(self):
        if self.color_var.get() == "自定义…":
            return self.custom_color
        return COLORS.get(self.color_var.get(), [70, 225, 135])

    def _on_color(self):
        if self.color_var.get() == "自定义…":
            rgb = colorchooser.askcolor(color="#%02x%02x%02x" % tuple(self.custom_color),
                                        title="选择主色调", parent=self.root)
            if rgb and rgb[0]:
                self.custom_color = [int(x) for x in rgb[0]]
            else:
                self.color_var.set("翠绿")
        self._swatch()
        self._pv_schedule()

    def say(self, msg):
        self.q.put(("log", msg))

    def _drain(self):
        try:
            while True:
                item = self.q.get_nowait()
                kind = item[0]
                if kind == "log":
                    self.log.configure(state="normal")
                    self.log.insert("end", item[1] + "\n")
                    self.log.see("end")
                    self.log.configure(state="disabled")
                elif kind == "progress":
                    self.prog_var.set(item[1] * 100.0)
                elif kind == "status":
                    self.stat_var.set(item[1])
                elif kind == "done":
                    self._finish(item[1])
                elif kind == "trackinfo":
                    self.track_info.set(item[1])
                elif kind == "pvbg":
                    self._pv_bg = item[1]
                    self._pv_render()
                elif kind == "refresh":
                    if item[1] == "tt":
                        self._refresh_tt()
                    else:
                        self._refresh_tv()
                elif kind == "pvlayer":
                    self._layer_busy = False
                    if item[2] == self._layers_key:
                        self._layers = item[1]
                        self._pv_assemble()
                    elif self._layer_pending:
                        self._layer_pending = False
                        self._pv_render()
        except queue.Empty:
            pass
        self.root.after(60, self._drain)

    def _finish(self, ok):
        self._busy_flag = False
        self.btn_run.configure(state="normal")
        self.btn_stop.configure(state="disabled")
        self.stat_var.set("完成 ✔" if ok else "已停止 / 失败")
        if ok and self.shutdown_var.get():
            self._schedule_shutdown()

    # ---------------------------------------------------------------- 关机
    def _schedule_shutdown(self):
        """全部输出完成后按倒计时关机（可随时取消）"""
        try:
            subprocess.run(["shutdown", "/s", "/t", str(SHUTDOWN_SECONDS)],
                           creationflags=NO_WINDOW, check=False)
        except Exception as e:
            self.say("[关机] 无法调用系统关机命令：%s" % e)
            return
        self.say("[关机] 全部视频已输出完成，系统将在 %d 秒后关闭（点『取消关机』可中止）" % SHUTDOWN_SECONDS)
        win = tk.Toplevel(self.root)
        win.title("输出完成")
        win.transient(self.root)
        win.resizable(False, False)
        try:
            win.attributes("-topmost", True)
        except Exception:
            pass
        ttk.Label(win, text="全部视频已输出完成", style="Card.TLabel",
                  font=("Microsoft YaHei UI", 12, "bold")).pack(padx=22, pady=(16, 4))
        lab = ttk.Label(win, text="", style="Card.TLabel", font=("Microsoft YaHei UI", 10))
        lab.pack(padx=22, pady=(0, 10))
        box = ttk.Frame(win, style="Card.TFrame")
        box.pack(padx=22, pady=(0, 16))
        state = {"n": SHUTDOWN_SECONDS}

        def cancel():
            try:
                subprocess.run(["shutdown", "/a"], creationflags=NO_WINDOW, check=False)
            except Exception:
                pass
            self.say("[关机] 已取消关机")
            win.destroy()

        def now():
            try:
                subprocess.run(["shutdown", "/s", "/t", "0"], creationflags=NO_WINDOW, check=False)
            except Exception:
                pass
            win.destroy()

        ttk.Button(box, text="取消关机", width=12, command=cancel).pack(side="left", padx=(0, 8))
        ttk.Button(box, text="立即关机", width=12, command=now).pack(side="left")

        def tick():
            if not win.winfo_exists():
                return
            state["n"] -= 1
            if state["n"] <= 0:
                win.destroy()
                return
            lab.configure(text="%d 秒后自动关机…" % state["n"])
            win.after(1000, tick)
        lab.configure(text="%d 秒后自动关机…" % state["n"])
        win.after(1000, tick)
        win.protocol("WM_DELETE_WINDOW", cancel)

    # ---------------------------------------------------------------- ffmpeg
    def _init_ffmpeg(self):
        self.ffmpeg, self.ffprobe = C.find_ffmpeg()
        if self.ffmpeg:
            self.say("[工具] ffmpeg 已就绪：%s" % self.ffmpeg)
            return

        def work():
            self.say("[工具] tools 文件夹中没有 ffmpeg，正在自动下载（约 160MB）…")
            try:
                ff, fp = C.download_ffmpeg(os.path.join(APP_DIR, "tools"), lambda m: self.say("[下载] " + m))
                self.ffmpeg, self.ffprobe = ff, fp
                self.say("[工具] ffmpeg 下载完成")
            except Exception as e:
                self.say("[错误] ffmpeg 自动下载失败：%s（可手动放到 GPSTool/tools/）" % e)
        threading.Thread(target=work, daemon=True).start()

    # ---------------------------------------------------------------- 轨迹（可多条）
    def add_tracks(self):
        ps = filedialog.askopenfilenames(
            title="选择轨迹文件（可多选）",
            filetypes=[("轨迹文件", "*.gpx *.fit *.tcx *.xml *.kml"), ("所有文件", "*.*")])
        if ps:
            self._parse_tracks(list(ps))

    def _parse_tracks(self, paths):
        fresh = []
        for p0 in paths:
            p = os.path.normcase(os.path.abspath(p0))
            if any(t["path"] == p for t in self.tracks):
                continue
            self.tracks.append(dict(path=p, tr=None, err=None, disp=os.path.basename(p0)))
            fresh.append(p)
        self._refresh_tt()
        if not fresh:
            return
        self._select_track()

        def work():
            for p in fresh:
                item = next((t for t in self.tracks if t["path"] == p), None)
                if item is None:
                    continue
                try:
                    t0 = time.time()
                    item["tr"] = C.Track.from_file(p)
                    self.say("[轨迹] %s\n       %s（解析 %.2f 秒）" %
                             (item["disp"], item["tr"].summary(), time.time() - t0))
                except Exception as e:
                    item["err"] = str(e)
                    self.say("[错误] 轨迹解析失败 %s：%s" % (item["disp"], e))
                self.q.put(("refresh", "tt"))
        threading.Thread(target=work, daemon=True).start()

    def _refresh_tt(self):
        sel = self.tt.selection()
        self.tt.delete(*self.tt.get_children())
        for i, t in enumerate(self.tracks):
            tr = t["tr"]
            if tr is None:
                if t["err"]:
                    vals = (t["disp"], "解析失败", t["err"][:40], "", "", "")
                else:
                    vals = (t["disp"], "解析中…", "", "", "", "")
            else:
                a = datetime.datetime.fromtimestamp(tr.start, tr.tz)
                b = datetime.datetime.fromtimestamp(tr.end, tr.tz)
                dist = ("%.2f km" % (tr.total_dist / 1000.0)) if tr.has_pos else "—"
                vals = (t["disp"], dist, a.strftime("%Y-%m-%d"),
                        a.strftime("%H:%M:%S"), b.strftime("%H:%M:%S"),
                        C.fmt_hms(tr.end - tr.start))
            self.tt.insert("", "end", iid=str(i), values=vals)
        keep = [i for i in sel if i in self.tt.get_children()]
        if keep:
            self.tt.selection_set(keep[0])
        self._select_track()

    def _select_track(self):
        sel = [int(i) for i in self.tt.selection()]
        tr = None
        for i in sel:
            if 0 <= i < len(self.tracks) and self.tracks[i]["tr"]:
                tr = self.tracks[i]["tr"]
                break
        if tr is None:
            for t in self.tracks:
                if t["tr"]:
                    tr = t["tr"]
                    break
        if tr is self.track:
            self._update_track_info()
            return
        self.track = tr
        self._update_track_info()
        self._sync_field_availability()
        self._refresh_tv()          # 轨迹变了，视频行的时间范围高亮要跟着更新
        self._pv_schedule(force=True)
        self._eta_schedule()

    def _update_track_info(self):
        if not self.track:
            self.track_info.set("未选择轨迹文件（可在上方添加，支持多条）"
                                if not self.tracks else "轨迹正在解析，请稍候…")
            return
        tr = self.track
        self.track_info.set("✔ %s（自动量程 %d km/h）" % (tr.summary(), C.auto_speed_max(tr)))

    def remove_track(self):
        for i in sorted([int(i) for i in self.tt.selection()], reverse=True):
            self.tracks.pop(i)
        self.tt.selection_remove(*self.tt.selection())
        self.track = None
        self._refresh_tt()

    def clear_tracks(self):
        self.tracks.clear()
        self.track = None
        self._refresh_tt()

    def _sync_field_availability(self):
        if not self.track:
            for fid, cb in self.fchecks.items():
                cb.state(["!disabled"])
            return
        avail = set(C.available_fields(self.track))
        dropped = []
        for fid, cb in self.fchecks.items():
            if fid in avail:
                try:
                    cb.state(["!disabled"])
                except Exception:
                    pass
            else:
                try:
                    cb.state(["disabled"])
                except Exception:
                    pass
                if self.fvars[fid].get():
                    self.fvars[fid].set(False)
                    dropped.append(C.FIELD_META[fid][0])
        if dropped:
            self.say("[提示] 当前轨迹不含以下数据，已自动取消勾选：%s" % "、".join(dropped))

    # ---------------------------------------------------------------- 视频列表
    def add_videos(self):
        ps = filedialog.askopenfilenames(
            title="选择视频（可多选）",
            filetypes=[("视频", " ".join("*" + e for e in VIDEO_EXT)), ("所有文件", "*.*")])
        if ps:
            self._probe_async(list(ps))

    def add_folder(self):
        """选择文件夹，把里面的视频一次性添加进来"""
        d = filedialog.askdirectory(title="选择包含视频的文件夹")
        if not d:
            return
        found = [os.path.join(d, f) for f in sorted(os.listdir(d))
                 if f.lower().endswith(VIDEO_EXT)]
        if not found:
            messagebox.showinfo("添加文件夹", "该文件夹中没有找到视频文件")
            return
        self.say("[视频] 从文件夹添加 %d 个视频：%s" % (len(found), win_path(d)))
        self._probe_async(found)
        if not self.outdir_var.get().strip():
            self.outdir_var.set(win_path(d))

    def _probe_async(self, paths, prefill=None):
        if not self.ffprobe:
            self._init_ffmpeg()
        if not self.ffprobe:
            messagebox.showwarning("缺少 ffmpeg", "ffmpeg 尚未就绪（tools 文件夹），稍后重试。")
            return
        fresh = []
        for p0 in paths:
            p = os.path.normcase(os.path.abspath(p0))
            if any(v["path"] == p for v in self.videos):
                continue
            self.videos.append(dict(path=p, dur=0.0, start=None, src="识别中", info=None,
                                    auto=None, base=None, offset=0.0,
                                    disp=(prefill or {}).get(p, {}).get("disp") or os.path.basename(p0)))
            fresh.append(p)

        def work():
            for p in fresh:
                item = next((v for v in self.videos if v["path"] == p), None)
                if item is None:
                    continue
                try:
                    info = C.probe_video(self.ffprobe, p)
                except Exception as e:
                    self.say("[错误] 读取失败 %s：%s" % (item["disp"], e))
                    try:
                        self.videos.remove(item)
                    except ValueError:
                        pass
                    continue
                auto, src = C.detect_start_time(info)
                base = auto
                if prefill and p in prefill and prefill[p].get("start"):
                    base = prefill[p].get("base") or prefill[p]["start"]
                    item["offset"] = float(prefill[p].get("offset") or 0.0)
                    src = prefill[p].get("src", "记忆")
                    if prefill[p].get("disp"):
                        item["disp"] = prefill[p]["disp"]
                # base = 基准起点（自动识别值 或 手工绝对时间）；start = base + offset
                item.update(dict(dur=info.duration, base=base, src=src, info=info, auto=auto))
                item["start"] = None if base is None else base + (item["offset"] or 0.0)
                self.say("[视频] %s | %.1fs | %dx%d | 起点 %s（%s）" %
                         (item["disp"], info.duration, *info.disp_size,
                          datetime.datetime.fromtimestamp(item["start"]).strftime("%Y-%m-%d %H:%M:%S")
                          if item["start"] else "未识别", src))
                self.q.put(("refresh", "tv"))
        threading.Thread(target=work, daemon=True).start()
        self.root.after(300, self._refresh_tv)

    def _video_state(self, v):
        """返回 (起点时间文本, 标签)：判断视频时间段与轨迹时间范围的关系"""
        if not v.get("info") or v.get("start") is None:
            return "-- 未识别 --", None
        start = datetime.datetime.fromtimestamp(v["start"]).strftime("%Y-%m-%d %H:%M:%S")
        if not self.track or not self.track.ts:
            return start, None
        s, e = v["start"], v["start"] + v["dur"]
        if e < self.track.start or s > self.track.end:
            return start, "warn"                # 完全不相交
        if s < self.track.start or e > self.track.end:
            return start, "out"                 # 只有部分重叠
        return start, None

    def _refresh_tv(self):
        if getattr(self, "_editing", None):        # 正在就地编辑时不重建，避免输入框错位
            return
        self.tv.delete(*self.tv.get_children())
        for i, v in enumerate(self.videos):
            if not v.get("info"):
                self.tv.insert("", "end", iid=str(i), values=(i + 1, v["disp"], "读取中…", "", "", ""))
                continue
            w, h = v["info"].disp_size
            st, tag = self._video_state(v)
            off = v.get("offset") or 0.0
            adj = "%+.1f" % off
            tags = ["editable"]
            if tag:
                tags.insert(0, tag)
            self.tv.insert("", "end", iid=str(i),
                           values=(i + 1, v["disp"], "%.1fs" % v["dur"], "%dx%d" % (w, h), st, adj),
                           tags=tuple(tags))
        self._eta_schedule()
        self._pv_schedule()

    def _sel_indices(self):
        return [int(i) for i in self.tv.selection()]

    # ------------------------------------------------ 起点时间：单元格就地编辑
    def _cell_at(self, event):
        """把鼠标位置换算成 (行号, 列号)；容错：点到行边缘时也尽量归到相邻的可编辑列"""
        iid = self.tv.identify_row(event.y)
        col = self.tv.identify_column(event.x)
        if not iid:
            rows = self.tv.get_children()
            if not rows:
                return None, None
            # 点到了表格空白处：用 y 找最近的行
            y = event.y
            best, bd = None, None
            for r in rows:
                b = self.tv.bbox(r)
                if not b:
                    continue
                d = 0 if b[1] <= y <= b[1] + b[3] else min(abs(y - b[1]), abs(y - b[1] - b[3]))
                if bd is None or d < bd:
                    best, bd = r, d
            iid = best
        if not iid:
            return None, None
        try:
            i = int(iid)
        except (TypeError, ValueError):
            return None, None
        if i >= len(self.videos):
            return None, None
        return iid, col

    def _edit_video(self, event):
        iid, col = self._cell_at(event)
        if not iid:
            return
        if col in ("#5", "#6"):
            self._begin_edit(iid, col)
        elif col in ("#1", "#2", "#3", "#4"):
            # 起点没识别出来时，点这一行任何位置都直接进入"填起点时间"，避免找不到入口
            if self.videos[int(iid)].get("start") is None:
                self._begin_edit(iid, "#5")
            else:
                self.say("[提示] 时间可改：点『起点时间』列填绝对时刻，点『调整(秒)』列按秒微调。")

    def _begin_edit(self, iid, col):
        """在单元格上直接出现输入框：回车确认，Esc 取消"""
        if getattr(self, "_editing", None) and getattr(self, "_editing_commit", None):
            self._editing_commit(True)
        bb = self.tv.bbox(iid, column=col)
        i = int(iid)
        if not bb or i >= len(self.videos):
            return
        v = self.videos[i]
        is_time = (col == "#5")
        if is_time:
            cur = v.get("start")
            text = datetime.datetime.fromtimestamp(cur).strftime("%Y-%m-%d %H:%M:%S") if cur else ""
        else:
            text = ("%.1f" % (v.get("offset") or 0.0))
        self.tv.selection_set(iid)
        self.tv.focus(iid)
        self.tv.see(iid)
        ed = tk.Entry(self.tv, justify="center", font=("Microsoft YaHei UI", 9),
                      relief="solid", bd=1, bg="#ffffff", fg="#1a56c4")
        ed.insert(0, text)
        ed.place(x=bb[0] + 1, y=bb[1] + 1, width=max(bb[2] - 2, 40), height=max(bb[3] - 2, 18))
        ed.select_range(0, "end")
        ed.focus_set()
        self.root.update_idletasks()      # 立即完成映射与聚焦，保证第一次回车就能收到
        self._editing = (ed, iid, col)

        state = {"closed": False}

        def commit(save):
            # 销毁 Entry 会同步触发 <FocusOut>，必须防递归，否则业务代码会被异常打断
            if state["closed"]:
                return
            state["closed"] = True
            try:
                val = ed.get().strip()
            except Exception:
                val = text
            try:
                ed.unbind("<FocusOut>")
                ed.destroy()
            except Exception:
                pass
            self._editing = None
            self._editing_commit = None
            try:
                self.tv.focus_set()
            except Exception:
                pass
            if not save:
                return
            if val == text:
                return
            try:
                if is_time:
                    if not val:
                        raise ValueError
                    ts = self._parse_dt(val).timestamp()
                    v["base"] = ts
                    v["start"] = ts + (v.get("offset") or 0.0)
                    v["src"] = "手工指定"
                    self.say("[时间] %s 起点时间设为 %s%s" %
                             (v["disp"], datetime.datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S"),
                              "（另含微调 %+.1f 秒）" % (v.get("offset") or 0.0)
                              if abs(v.get("offset") or 0.0) >= 0.05 else ""))
                else:
                    off = float(val.replace("s", "").replace("秒", "").strip() or 0.0)
                    if v.get("base") is None:
                        if v.get("start") is None:     # 完全没有时间，只能先填绝对时间
                            messagebox.showwarning("请先填写起点时间",
                                                   "这个视频还没识别出拍摄时间，\n"
                                                   "请先点『起点时间』列手工填写，再做秒微调。")
                            self._refresh_tv()
                            return
                        v["base"] = v["start"]         # 以当前起点为基准，保证微调一定生效
                    v["offset"] = off
                    v["start"] = v["base"] + off
                    v["src"] = "手工调整"
                    self.say("[时间] %s 起点时间微调 %+.1f 秒 → %s" %
                             (v["disp"], off,
                              datetime.datetime.fromtimestamp(v["start"]).strftime("%H:%M:%S")))
            except ValueError:
                messagebox.showerror("格式错误", ("请按 2026-09-14 07:51:45 或 07:51:45 输入"
                                                  if is_time else "请输入秒数，例如 3 或 -2.5"))
                return
            self._refresh_tv()
            self._check_video_range(v)
            self._pv_schedule(force=True)      # 立刻刷新右侧预览，改动看得见

        self._editing_commit = commit
        ed.bind("<Return>", lambda e: commit(True))
        ed.bind("<KP_Enter>", lambda e: commit(True))
        ed.bind("<Escape>", lambda e: commit(False))
        ed.bind("<FocusOut>", lambda e: commit(True))

    def _edit_selected(self, col="#5"):
        """键盘入口：选中行后按 Enter / F2 直接改"""
        sel = self._sel_indices()
        if sel:
            self._begin_edit(str(sel[0]), col)
        elif self.tv.get_children():
            self._begin_edit(self.tv.get_children()[0], col)

    def _parse_dt(self, val):
        val = str(val).strip()
        if len(val) <= 8:
            base = datetime.datetime.fromtimestamp(self.track.start, self.track.tz) if self.track else None
            hms = datetime.datetime.strptime(val, "%H:%M:%S")
            dt = (base or datetime.datetime.now()).replace(hour=hms.hour, minute=hms.minute,
                                                           second=hms.second)
        else:
            dt = datetime.datetime.strptime(val, "%Y-%m-%d %H:%M:%S")
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=self.track.tz if self.track else
                            datetime.timezone(datetime.timedelta(hours=8)))
        return dt

    def _check_video_range(self, v):
        if not self.track or v.get("start") is None:
            return
        txt, tag = self._video_state(v)
        if tag == "warn":
            self.say("[提醒] %s 的拍摄时间与轨迹时间范围完全不相交：%s（轨迹 %s ~ %s），可点『起点时间』或『调整(秒)』列修正" %
                     (v["disp"], txt,
                      datetime.datetime.fromtimestamp(self.track.start, self.track.tz).strftime("%H:%M:%S"),
                      datetime.datetime.fromtimestamp(self.track.end, self.track.tz).strftime("%H:%M:%S")))
        elif tag == "out":
            self.say("[提醒] %s 的拍摄时间只有部分落在轨迹时间范围内：%s" % (v["disp"], txt))

    @staticmethod
    def _wrap_tip(parent, text, wraplength=520, style="Muted.TLabel"):
        """创建一段自动换行的说明文字（仅展示，不交互）"""
        return ttk.Label(parent, text=text, style=style, wraplength=wraplength, justify="left")

    def _apply_time_offset(self, delta, targets=None):
        """对 targets（默认全部视频）统一叠加时间偏移（秒）；返回实际改动的视频数。

        只调整偏移、不改各视频自身的起点（每个视频仍基于自己识别到的起点叠加），
        因此视频之间的相对时间差保持不变。"""
        targets = list(targets if targets is not None else self.videos)
        n = 0
        for v in targets:
            base = v.get("base")
            if base is None:
                continue                       # 还没识别出起点的视频跳过
            v["offset"] = float(v.get("offset") or 0.0) + delta
            v["start"] = float(base) + float(v["offset"])
            v["src"] = "批量偏移 %+.1fs" % delta
            n += 1
        return n

    def batch_adjust(self):
        """批量调整时间：只调整「时间偏移」（分 + 秒），作用于视频列表里的所有视频。

        不改任何视频的绝对起点时刻——每个视频仍用自己识别到的起点，只是在它上面
        统一叠加（或减去）一个偏移量，因此各视频之间的相对时间差保持不变。"""
        if not self.videos:
            messagebox.showinfo("批量调整时间", "请先添加视频文件。")
            return
        targets = list(self.videos)
        win = tk.Toplevel(self.root)
        win.title("批量调整时间")
        win.configure(bg=BG)
        win.transient(self.root)
        win.resizable(False, False)
        body = ttk.Frame(win, style="Card.TFrame", padding=14)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text="将统一应用于视频列表里的全部 %d 个视频" % len(targets),
                  style="Card.TLabel").pack(anchor="w")
        self._wrap_tip(body, "只调整时间偏移：在每个视频各自识别到的起点时间上统一加减，"
                        "不会把所有视频改成同一个起点时刻。",
                  wraplength=520, style="Muted.TLabel").pack(anchor="w", pady=(2, 8), fill="x")

        dir_var = tk.StringVar(value="推后")        # 推后 = 起点时间变大；提前 = 变小
        min_var = tk.StringVar(value="0")
        sec_var = tk.StringVar(value="0")
        r = ttk.Frame(body, style="Card.TFrame"); r.pack(fill="x", pady=(2, 2))
        ttk.Label(r, text="方向：", style="Card.TLabel").pack(side="left")
        for t in ("推后", "提前"):
            ttk.Radiobutton(r, text=t, variable=dir_var, value=t).pack(side="left", padx=(4, 0))
        ttk.Label(r, text="分：", style="Card.TLabel").pack(side="left", padx=(14, 0))
        ttk.Spinbox(r, from_=0, to=999, textvariable=min_var, width=5,
                    justify="center").pack(side="left")
        ttk.Label(r, text="秒：", style="Card.TLabel").pack(side="left", padx=(10, 0))
        ttk.Spinbox(r, from_=0, to=59.9, increment=0.5, format="%.1f", textvariable=sec_var,
                    width=6, justify="center").pack(side="left")

        sum_var = tk.StringVar(value="当前偏移：+0.0 秒（不改动）")
        ttk.Label(body, textvariable=sum_var, style="Eta.TLabel").pack(anchor="w", pady=(6, 0))

        def refresh(*_a):
            try:
                m = abs(int(float(min_var.get() or 0)))
                s = abs(float(sec_var.get() or 0))
            except ValueError:
                sum_var.set("请填写数字（分为整数、秒可带小数）")
                return
            d = m * 60.0 + s
            if d <= 0:
                sum_var.set("当前偏移：+0.0 秒（不改动）")
            else:
                sum_var.set("当前偏移：%+.1f 秒（%s %d 分 %.1f 秒）"
                            % (-d if dir_var.get() == "提前" else d,
                               dir_var.get(), m, s))
        for v in (dir_var, min_var, sec_var):
            v.trace_add("write", refresh)

        self._wrap_tip(body, "『推后』＝视频起点往后挪，画面里显示的数据会更靠后；"
                        "『提前』＝往前挪。偏移量会累加到『调整(秒)』列上，可随时再次调整。",
                  wraplength=560).pack(anchor="w", pady=(6, 0), fill="x")

        def apply():
            try:
                m = abs(int(float(min_var.get() or 0)))
                s = abs(float(sec_var.get() or 0))
            except ValueError:
                messagebox.showwarning("批量调整时间", "『分』要填整数，『秒』可填小数，例如 0 分 2.5 秒。")
                return
            delta = m * 60.0 + s
            if dir_var.get() == "提前":
                delta = -delta
            if abs(delta) < 1e-6:
                messagebox.showinfo("批量调整时间", "偏移量为 0，未做任何改动。")
                win.destroy()
                return
            n = self._apply_time_offset(delta)
            self._refresh_tv()
            self._pv_schedule(force=True)
            self._eta_schedule()
            self._save_settings()
            self.say("[批量调整时间] 已对全部 %d 个视频应用偏移 %+.1f 秒（%s）"
                     % (n, delta, "提前" if delta < 0 else "推后"))
            if n < len(targets):
                self.say("[批量调整时间] 另有 %d 个视频尚未识别出起点时间，已跳过"
                         % (len(targets) - n))
            win.destroy()

        r2 = ttk.Frame(body, style="Card.TFrame"); r2.pack(fill="x", pady=(10, 0))
        ttk.Button(r2, text="应用", width=10, command=apply).pack(side="right", padx=(6, 0))
        ttk.Button(r2, text="取消", width=10, command=win.destroy).pack(side="right")

    def remove_sel(self):
        for i in sorted(self._sel_indices(), reverse=True):
            self.videos.pop(i)
        self._refresh_tv()

    def clear_videos(self):
        self.videos.clear()
        self._refresh_tv()

    # ---------------------------------------------------------------- 样式对象
    def _fields(self):
        return [f for f in C.FIELD_ORDER if self.fvars[f].get()]

    def style(self) -> C.HudStyle:
        st = C.HudStyle()
        st.update(dict(
            style=C.STYLE_ID.get(self.gstyle_var.get(), "gauge"),
            title=self.title_var.get() or "GPS",
            accent=self._color_rgb(),
            fields=self._fields(),
            # 跑步显示配速，其它运动形式显示速度
            dial_field=("pace" if self.tpl_var.get() == "跑步" else "speed"),
            panel=dict(pos="bottom",
                       opacity=int(self.panel_op_var.get()),
                       sx=self.escale["panel"][0], sy=self.escale["panel"][1],
                       rel=self.rel["panel"]),
            map=dict(enabled=self.map_var.get(), pos="top-right",
                     opacity=int(self.map_op_var.get()),
                     sx=self.escale["map"][0], sy=self.escale["map"][1],
                     rel=self.rel["map"],
                     zoom_enabled=self.zoom_var.get(), pos_zoom="top-left",
                     zoom_rel=self.rel["zoom"],
                     zsx=self.escale["zoom"][0], zsy=self.escale["zoom"][1]),
        ))
        if self.track:
            st.update(dict(speed_max=C.auto_speed_max(self.track)))
        return st

    def _apply_template(self):
        tpl = self.tpl_var.get()
        fields = [f for f in C.TEMPLATES[tpl]
                  if not self.track or C.field_ok(f, self.track)]
        for fid, v in self.fvars.items():
            v.set(fid in fields)
        missing = [C.FIELD_META[f][0] for f in C.TEMPLATES[tpl]
                   if self.track and not C.field_ok(f, self.track)]
        if missing:
            self.say("[运动形式] %s 中的 %s 在当前轨迹中无数据，已跳过" % (tpl, "、".join(missing)))
        self.say("[运动形式] 已套用『%s』：%s" % (tpl, "、".join(C.FIELD_META[f][0] for f in fields)))

    # ---------------------------------------------------------------- 布局方案
    def _load_layouts(self):
        try:
            d = json.load(open(LAYOUTS, encoding="utf-8"))
            self.layouts = d if isinstance(d, dict) else {}
        except Exception:
            self.layouts = {}
        self._refresh_layout_combo()

    def _save_layouts_file(self):
        try:
            json.dump(self.layouts, open(LAYOUTS, "w", encoding="utf-8"),
                      ensure_ascii=False, indent=2)
        except Exception as e:
            self.say("[错误] 布局保存失败：%s" % e)

    def _refresh_layout_combo(self):
        try:
            self.layout_cb.configure(values=[DEFAULT_LAYOUT] + sorted(self.layouts))
        except Exception:
            pass

    def _save_layout(self):
        name = simpledialog.askstring("保存信息布局设置",
                                      "给当前的信息布局起个名字（以后可直接调用）：",
                                      initialvalue=self.gstyle_var.get() + "布局",
                                      parent=self.root)
        if not name:
            return
        name = name.strip()
        if name == DEFAULT_LAYOUT:
            messagebox.showinfo("保存信息布局设置", "该名称已被内置布局占用，请换一个名字。")
            return
        self.layouts[name] = dict(
            style=self.gstyle_var.get(), title=self.title_var.get(),
            color=self.color_var.get(),
            panel_opacity=int(self.panel_op_var.get()),
            map_opacity=int(self.map_op_var.get()),
            escale={k: [float(v[0]), float(v[1])] for k, v in self.escale.items()},
            map_on=self.map_var.get(), zoom_on=self.zoom_var.get(),
            rels=dict(panel=self.rel["panel"], map=self.rel["map"], zoom=self.rel["zoom"]))
        self._save_layouts_file()
        self._refresh_layout_combo()
        self.layout_var.set(name)
        self.say("[布局] 已保存『%s』，以后在『信息布局』下拉框里可直接调用" % name)

    def _apply_layout(self):
        name = self.layout_var.get()
        if name == DEFAULT_LAYOUT:
            self.rel = {"panel": None, "map": None, "zoom": None}
            self.escale = {"panel": [1.0, 1.0], "map": [1.0, 1.0], "zoom": [1.0, 1.0]}
            self.say("[布局] 已恢复默认布局（按默认方位摆放、大小 100%）")
            self._pv_schedule(force=True)
            return
        d = self.layouts.get(name)
        if not d:
            return
        self.gstyle_var.set(d.get("style", self.gstyle_var.get()))
        self.title_var.set(d.get("title", self.title_var.get()))
        self.color_var.set(d.get("color", self.color_var.get()))
        self._swatch()
        self.panel_op_var.set(int(d.get("panel_opacity", 60)))
        self.map_op_var.set(int(d.get("map_opacity", 60)))
        esc = d.get("escale")
        if not esc:                       # 兼容旧方案（panel_scale / map_scale 百分比）
            ps = float(d.get("panel_scale", 100.0)) / 100.0
            ms = float(d.get("map_scale", 100.0)) / 100.0
            esc = {"panel": [ps, ps], "map": [ms, ms], "zoom": [ms, ms]}
        for k in ("panel", "map", "zoom"):
            v = esc.get(k)
            if isinstance(v, (list, tuple)) and len(v) == 2:
                self.escale[k] = [float(v[0]), float(v[1])]
        self.map_var.set(bool(d.get("map_on", True)))
        self.zoom_var.set(bool(d.get("zoom_on", True)))
        rels = d.get("rels") or {}
        for k in ("panel", "map", "zoom"):
            v = rels.get(k)
            if isinstance(v, (list, tuple)) and len(v) == 2:
                self.rel[k] = [float(v[0]), float(v[1])]
            else:
                self.rel[k] = None
        self._sync_slider_labels()
        self.say("[布局] 已套用『%s』" % name)
        self._pv_schedule(force=True)

    def _del_layout(self):
        name = self.layout_var.get()
        if name == DEFAULT_LAYOUT or name not in self.layouts:
            messagebox.showinfo("删除布局", "内置默认布局不可删除。")
            return
        if not messagebox.askyesno("删除布局", "确定删除布局『%s』吗？" % name):
            return
        self.layouts.pop(name, None)
        self._save_layouts_file()
        self._refresh_layout_combo()
        self.layout_var.set(DEFAULT_LAYOUT)
        self.say("[布局] 已删除『%s』" % name)

    # ---------------------------------------------------------------- 预览
    def _pv_video(self):
        vids = [v for v in self.videos if v.get("info")]
        if not vids:
            return None
        sel = [i for i in self._sel_indices() if i < len(self.videos) and self.videos[i].get("info")]
        return self.videos[sel[0]] if sel else vids[0]

    def _pv_seek(self, v):
        frac = min(max(self.pv_pos_var.get(), 0.0), 100.0) / 100.0
        return min(max(v["dur"] * frac, 0.0), max(v["dur"] - 0.2, 0))

    def _pv_schedule(self, force=False):
        if self._pv_timer:
            try:
                self.root.after_cancel(self._pv_timer)
            except Exception:
                pass
        self._pv_timer = self.root.after(0 if force else 200, self._pv_update)

    def _pv_fast(self):
        """仅位置/大小变化时的快速重合成（不重新渲染图层）"""
        if self._drag_timer:
            try:
                self.root.after_cancel(self._drag_timer)
            except Exception:
                pass
        self._drag_timer = self.root.after(25, lambda: self._pv_assemble(fast=True))

    def _pv_update(self):
        self._pv_timer = None
        v = self._pv_video()
        if not self.track or not v or not self.ffmpeg:
            if not self.track:
                self.pv_status.set("选择轨迹文件后开始预览")
            elif not v:
                self.pv_status.set("添加视频后可看到叠加效果")
            return
        seek = self._pv_seek(v)
        key = (v["path"], round(seek, 1))
        self.pv_time.set("取帧位置：%s / %s" %
                         (fmt_dur(seek), datetime.datetime.fromtimestamp(
                             v["start"] + seek).strftime("%H:%M:%S") if v["start"] else "--:--:--"))
        if self._pv_key != key or self._pv_bg is None:
            self._pv_key = key
            self._pv_bg = None
            self._layers = None
            self.pv_status.set("正在读取视频帧…")
            ff = self.ffmpeg
            info = v["info"]

            def grab_work():
                try:
                    img = C.grab_frame(ff, v["path"], seek, info, max_w=720)
                    self.q.put(("pvbg", img))
                except Exception as e:
                    self.say("[错误] 取帧失败：%s" % e)
            threading.Thread(target=grab_work, daemon=True).start()
            return
        self._pv_render()

    def _layer_key(self, seek):
        st = self.style()
        v = self._pv_video()
        # 关键：必须包含"绝对时刻"，否则改了起点时间后图层不重建、画面看起来毫无变化
        t = seek if v is None or v.get("start") is None else (v["start"] + seek)
        return (id(self.track), round(t, 2), st["style"], st["title"], tuple(st["accent"]),
                tuple(st["fields"]), st["speed_max"], st.get("dial_field"),
                bool(st["map"]["enabled"]), bool(st["map"].get("zoom_enabled")),
                int(st["panel"].get("opacity", 60)), int(st["map"].get("opacity", 60)))

    def _pv_render(self):
        """按需重建 HUD 图层（设计尺寸，后台线程）；图层没变时只做快速合成"""
        v = self._pv_video()
        if not v or self._pv_bg is None or not self.track:
            return
        seek = self._pv_seek(v)
        st = self.style()
        tr = self.track
        key = self._layer_key(seek)
        if self._layers is not None and self._layers_key == key:
            self._pv_assemble()
            return
        if self._layer_busy:
            self._layer_pending = True
            return
        self._layer_busy = True
        self._layers_key = key
        self.pv_status.set("正在渲染信息图层…")

        def work():
            try:
                layers = C.build_hud_layers(tr, st, v["start"] + seek)
                self.q.put(("pvlayer", layers, key, "%.2f 秒/图层" % 0))
            except Exception as e:
                self._layer_busy = False
                self.say("[错误] 预览合成失败：%s" % e)
        threading.Thread(target=work, daemon=True).start()

    def _pv_out_size(self):
        """成片的目标画幅（预览与输出必须用同一套，否则拖动写回的坐标会错位）"""
        bg = self._pv_bg
        if bg is not None:
            dw, dh = bg.width, bg.height
        else:
            dw, dh = 1920, 1080
        h = C.HEIGHTS_UI.get(self.height_var.get(), "orig")
        try:
            return tuple(int(x) for x in C.target_size(dw, dh, h))
        except Exception:
            return int(dw), int(dh)

    def _pv_assemble(self, fast=False):
        """把缓存图层按当前位置/大小合成到背景帧上（毫秒级，拖动不卡）"""
        bg = self._pv_bg
        if bg is None or self._layers is None or not self.track or not ImageTk:
            return
        if getattr(self, "_pv_bg_rgba", None) is None or self._pv_bg_rgba[0] is not bg:
            self._pv_bg_rgba = (bg, bg.convert("RGBA"))
        st = self.style()
        ow, oh = self._pv_out_size()
        self._pv_osize = (ow, oh)
        # 抽帧底图按成片画幅等比缩放，后续合成坐标、尺寸都与真正输出逐像素对齐
        lay = C.hud_layout(st, ow, oh, self.track)
        rs = Image.BILINEAR if fast else Image.LANCZOS
        out = self._pv_bg_rgba[1].resize((ow, oh), rs).convert("RGBA")
        for im, rect in zip(self._layers, lay):
            if im is None or not rect:
                continue
            out.alpha_composite(C.fit_layer(im, rect[2], rect[3], rs), rect[:2])
        out = out.convert("RGB")
        disp = out.resize((PREVIEW_W, max(1, int(PREVIEW_W * out.height / out.width))), rs)
        ds = PREVIEW_W / float(ow)          # 预览像素 = 成片像素 × ds
        self._pv_ds = ds
        self._pv_elems = {}
        for name, rect in zip(("panel", "map", "zoom"), lay):
            if not rect:
                continue
            x, y, w, h = [v * ds for v in rect]
            self._pv_elems[name] = (x, y, w, h)
            if self.rel[name] is None:
                self.rel[name] = [rect[0] / float(ow), rect[1] / float(oh)]
        self._pv_disp = disp
        self._pv_paint()
        self.pv_status.set("预览已更新（拖动位置 / 大小即时生效）")

    def _pv_paint(self):
        """在预览图上叠加悬停元素的虚线参考框（仅界面提示，不影响输出）"""
        disp = self._pv_disp
        if disp is None or not ImageTk:
            return
        img = disp
        name = self._pv_hover
        if name:
            r = self._pv_elems.get(name)
            if r:
                img = disp.copy()
                dr = ImageDraw.Draw(img)
                x0, y0, w, h = r
                x1, y1 = x0 + w, y0 + h
                for a, b in (((x0, y0), (x1, y0)), ((x1, y0), (x1, y1)),
                             ((x1, y1), (x0, y1)), ((x0, y1), (x0, y0))):
                    self._dash(dr, a, b, (255, 255, 255, 210), (18, 22, 30, 200))
                for cx, cy in ((x0, y0), (x1, y0), (x0, y1), (x1, y1)):
                    for dx, dy in ((0, 1), (1, 0), (0, -1), (-1, 0)):
                        dr.line((cx, cy, cx + dx * 7, cy + dy * 7), fill=(255, 255, 255, 235), width=2)
        self._ph = ImageTk.PhotoImage(img)
        self.pv_label.configure(image=self._ph, text="", width=img.width, height=img.height)

    @staticmethod
    def _dash(dr, a, b, col, shadow):
        """两点间画虚线（先描深色再画亮色，保证在任意画面上都看得清）"""
        dx, dy = b[0] - a[0], b[1] - a[1]
        n = int(max(abs(dx), abs(dy)) / 9.0) + 1
        for i in range(n):
            t0, t1 = i / float(n), min(1.0, (i + 0.55) / float(n))
            p0 = (a[0] + dx * t0, a[1] + dy * t0)
            p1 = (a[0] + dx * t1, a[1] + dy * t1)
            dr.line((p0, p1), fill=shadow, width=3)
        for i in range(n):
            t0, t1 = i / float(n), min(1.0, (i + 0.55) / float(n))
            p0 = (a[0] + dx * t0, a[1] + dy * t0)
            p1 = (a[0] + dx * t1, a[1] + dy * t1)
            dr.line((p0, p1), fill=col, width=1)

    # ---- 预览拖动 / 缩放 ----
    CURSORS = {"corner:nw": "size_nw_se", "corner:se": "size_nw_se",
               "corner:ne": "size_ne_sw", "corner:sw": "size_ne_sw",
               "edge:l": "size_we", "edge:r": "size_we",
               "edge:t": "size_ns", "edge:b": "size_ns", "move": "fleur"}

    def _pv_hit(self, name, x, y):
        """命中判定：返回 (元素名, 模式)；模式为 corner:xx / edge:x / move / None"""
        r = self._pv_elems.get(name)
        if not r:
            return None
        ex, ey, ew, eh = r
        x1, y1 = ex + ew, ey + eh
        small = min(ew, eh)
        tol = max(3.0, min(EDGE_TOL, small * 0.22))       # 元素越小，判定带越窄
        cor = max(5.0, min(CORNER_TOL, small * 0.28))
        if not (ex - tol <= x <= x1 + tol and ey - tol <= y <= y1 + tol):
            return None
        # 1) 四个角：按住任一个角拖动 = 等比缩放（对角固定）
        for c, (cx, cy) in (("nw", (ex, ey)), ("ne", (x1, ey)),
                            ("sw", (ex, y1)), ("se", (x1, y1))):
            if abs(x - cx) <= cor and abs(y - cy) <= cor:
                return (name, "corner:" + c)
        # 2) 四条边：按住某条边拖动 = 只移动该边
        if abs(x - ex) <= tol:
            return (name, "edge:l")
        if abs(x - x1) <= tol:
            return (name, "edge:r")
        if abs(y - ey) <= tol:
            return (name, "edge:t")
        if abs(y - y1) <= tol:
            return (name, "edge:b")
        # 3) 内部：移动整个元素
        if name == "zoom":                      # 圆形轨迹图按圆判定
            cx, cy, rad = ex + ew / 2.0, ey + eh / 2.0, ew / 2.0
            if (x - cx) ** 2 + (y - cy) ** 2 <= (rad + 3) ** 2:
                return (name, "move")
            return None
        if ex - 3 <= x <= x1 + 3 and ey - 3 <= y <= y1 + 3:
            return (name, "move")
        return None

    def _pv_hit_any(self, x, y):
        for name in ("zoom", "map", "panel"):
            hit = self._pv_hit(name, x, y)
            if hit:
                return hit
        return None

    def _pv_hover_set(self, name, mode=None):
        if self._pv_hover == name and mode == self._pv_mode:
            return
        self._pv_hover, self._pv_mode = name, mode
        cur = self.CURSORS.get(mode, "hand2")
        if cur != self._pv_cursor:
            self._pv_cursor = cur
            try:
                self.pv_label.configure(cursor=cur)
            except Exception:
                self.pv_label.configure(cursor="hand2")
        self._pv_paint()

    def _pv_motion(self, e):
        if self._drag:
            return
        hit = self._pv_hit_any(e.x, e.y)
        if hit:
            self._pv_hover_set(hit[0], hit[1])
        else:
            self._pv_hover_set(None)

    def _pv_press(self, e):
        hit = self._pv_hit_any(e.x, e.y)
        if not hit:
            self._drag = None
            return
        name, mode = hit
        r = self._pv_elems[name]
        # [元素, 模式, 当前矩形x0,y0,w0,h0, move抓取偏移x,y, 上一次鼠标位置x,y]
        self._drag = [name, mode, r[0], r[1], r[2], r[3], e.x - r[0], e.y - r[1], e.x, e.y]
        self._pv_hover_set(name, mode)

    def _pv_drag(self, e):
        if not self._drag or self._pv_bg is None:
            return
        name, mode, x0, y0, w0, h0, ox, oy, lx, ly = self._drag
        if not self._pv_elems.get(name):
            return
        dx, dy = e.x - lx, e.y - ly
        self._drag[8], self._drag[9] = e.x, e.y
        bgw, bgh = self._pv_osize or (self._pv_bg.width, self._pv_bg.height)
        if mode == "move":
            nx = min(max((e.x - ox) / self._pv_ds, 0.0), max(0.0, bgw - w0 / self._pv_ds))
            ny = min(max((e.y - oy) / self._pv_ds, 0.0), max(0.0, bgh - h0 / self._pv_ds))
            self.rel[name] = [nx / bgw, ny / bgh]
            self._pv_fast()
            return
        # 缩放：增量式 + 阻尼，鼠标位移按 SCALE_GAIN 折算，避免一不小心放得很大 / 很小
        x1, y1 = x0 + w0, y0 + h0
        mind = max(16.0, min(w0, h0) * 0.35)
        if mode.startswith("corner:"):
            hx = -1.0 if mode in ("corner:nw", "corner:sw") else 1.0
            hy = -1.0 if mode in ("corner:nw", "corner:ne") else 1.0
            dwx, dwy = dx * hx, dy * hy
            dw = dwx if abs(dwx) >= abs(dwy) else dwy      # 以幅度大的方向为准
            ref = max(w0, h0, 40.0)                        # 参照尺寸，越小越灵敏（有下限，避免小图乱飞）
            g = max(0.5, 1.0 + dw * SCALE_GAIN / ref)
            tw, th = w0 * g, h0 * g                         # 等比（宽高比例保持不变）
        elif mode == "edge:l":
            tw, th = w0 - dx * SCALE_GAIN, h0
        elif mode == "edge:r":
            tw, th = w0 + dx * SCALE_GAIN, h0
        elif mode == "edge:t":
            tw, th = w0, h0 - dy * SCALE_GAIN
        else:                                               # edge:b
            tw, th = w0, h0 + dy * SCALE_GAIN
        limw = bgw * self._pv_ds
        limh = bgh * self._pv_ds
        tw = min(max(mind, tw), limw)
        th = min(max(mind, th), limh)
        sc = self.escale[name]
        nsx = max(0.1, min(4.0, sc[0] * tw / max(w0, 1.0)))
        nsy = max(0.1, min(4.0, sc[1] * th / max(h0, 1.0)))
        # 夹紧后回算真实显示尺寸，保证锚定边不漂移
        aw, ah = w0 * nsx / sc[0], h0 * nsy / sc[1]
        sc[0], sc[1] = nsx, nsy
        px = x1 - aw if mode in ("corner:nw", "corner:sw", "edge:l") else x0
        py = y1 - ah if mode in ("corner:nw", "corner:ne", "edge:t") else y0
        px = min(max(px / self._pv_ds, 0.0), max(0.0, bgw - aw / self._pv_ds))
        py = min(max(py / self._pv_ds, 0.0), max(0.0, bgh - ah / self._pv_ds))
        self.rel[name] = [px / bgw, py / bgh]
        self._drag[2], self._drag[3], self._drag[4], self._drag[5] = px * self._pv_ds, py * self._pv_ds, aw, ah
        self._pv_fast()

    def _pv_release(self, e):
        if self._drag:
            name, mode = self._drag[0], self._drag[1]
            self._drag = None
            hit = self._pv_hit_any(e.x, e.y)
            if hit:
                self._pv_hover_set(hit[0], hit[1])
            else:
                self._pv_hover_set(None)
            self.pv_status.set("数值面板 宽%.0f%% 高%.0f%%｜全景图 宽%.0f%% 高%.0f%%｜放大图 宽%.0f%% 高%.0f%%" % (
                self.escale["panel"][0] * 100, self.escale["panel"][1] * 100,
                self.escale["map"][0] * 100, self.escale["map"][1] * 100,
                self.escale["zoom"][0] * 100, self.escale["zoom"][1] * 100))
            self._save_settings()

    # ---------------------------------------------------------------- 预估
    def _eta_schedule(self):
        if self._est_timer:
            try:
                self.root.after_cancel(self._est_timer)
            except Exception:
                pass
        self._est_timer = self.root.after(300, self._update_eta)

    def _update_eta(self):
        self._est_timer = None
        todo = [v for v in self.videos if v["start"] and v.get("info")]
        if not todo:
            self.eta_var.set("预计输出时间：添加视频并识别时间后自动估算")
            return
        st = self.style()
        h = C.HEIGHTS_UI.get(self.height_var.get(), "orig")
        qn = self.quality_var.get()
        total = sum(C.estimate_output_seconds(v["dur"], h, qn, st, v["info"])
                    for v in todo)
        # 有本机实测速度时说明是按实测校准过的，没跑过就明说这是理论估算
        tag = "已按本机实测校准" if C.get_output_rate(h, qn) else "首次理论估算，输出一次后自动校准"
        self.eta_var.set("预计输出时间 ≈ %s（%d 个视频 · %s · %s · %s）" %
                         (fmt_dur(total), len(todo), self.height_var.get(), qn, tag))

    # ---------------------------------------------------------------- 执行
    def _precheck(self):
        if not self.track:
            messagebox.showwarning("缺少轨迹", "请先添加并选中轨迹文件（GPX / FIT / TCX / XML）。")
            return False
        if not self.ffmpeg:
            self._init_ffmpeg()
            if not self.ffmpeg:
                messagebox.showwarning("缺少 ffmpeg", "ffmpeg 尚未就绪，请稍候自动下载完成。")
                return False
        if not self.videos:
            messagebox.showwarning("缺少视频", "请添加至少一个视频文件。")
            return False
        bad = [v for v in self.videos if not v["start"] or not v.get("info")]
        if bad:
            if not messagebox.askyesno(
                    "有视频未识别起点时间",
                    "以下视频未能识别拍摄时间，将被跳过：\n" +
                    "\n".join(v.get("disp") or os.path.basename(v["path"]) for v in bad) +
                    "\n\n仍要继续吗？（可双击表格『起点时间』手工填写）"):
                return False
        warns = [v for v in self.videos if v.get("info") and self._video_state(v)[1] == "warn"]
        if warns:
            if not messagebox.askyesno(
                    "有视频拍摄时间超出轨迹范围",
                    "以下视频的拍摄时间与轨迹时间范围不相交：\n" +
                    "\n".join("%s（%s）" % (v.get("disp"), self._video_state(v)[0]) for v in warns) +
                    "\n\n建议先点『起点时间』或『调整(秒)』列修正；仍要继续吗？"):
                return False
        if not os.path.isdir(self.outdir_var.get()):
            try:
                os.makedirs(self.outdir_var.get(), exist_ok=True)
            except Exception:
                messagebox.showerror("输出目录无效", "请选择有效的输出目录。")
                return False
        if self.shutdown_var.get() and not messagebox.askyesno(
                "输出完成后关机",
                "已勾选『输出完成后关机』：全部视频输出完成后，系统将在 %d 秒倒计时后自动关机"
                "（倒计时窗口里可点『取消关机』中止）。\n\n确认继续吗？" % SHUTDOWN_SECONDS):
            return False
        return True

    def do_run(self):
        if self._busy_flag:
            return
        if not self._precheck():
            return
        self._save_settings()
        todo = [v for v in self.videos if v["start"] and v.get("info")]
        if not todo:
            return
        st = self.style()
        h = C.HEIGHTS_UI.get(self.height_var.get(), "orig")
        q = C.QUALITY.get(self.quality_var.get(), C.QUALITY["中"])
        outdir = self.outdir_var.get()
        keep_audio = self.audio_var.get()
        self.cancel_flag.clear()
        self._busy_flag = True
        self.btn_run.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        self.say("=" * 62)
        self.say("[开始] %d 个视频 → %s（%s · 画质%s · CRF%d/%s）" %
                 (len(todo), outdir, self.height_var.get(), self.quality_var.get(),
                  q["crf"], q["preset"]))

        def work():
            ok = True
            for i, v in enumerate(todo):
                if self.cancel_flag.is_set():
                    ok = False
                    break
                base = v.get("disp") or os.path.basename(v["path"])
                name = os.path.splitext(base)[0] + "_GPS.mp4"
                out = os.path.join(outdir, name)
                self.q.put(("status", "处理 %d/%d：%s" % (i + 1, len(todo), base)))
                self.say("→ [%d/%d] %s" % (i + 1, len(todo), base))
                try:
                    t0 = time.time()
                    C.process_video(v["path"], self.track, v["start"], out, self.ffmpeg, self.ffprobe,
                                    st, v["info"], h, q["crf"], q["preset"], keep_audio, None, None,
                                    log=self.say,
                                    progress=lambda p, i=i: self.q.put(
                                        ("progress", (i + p) / float(len(todo)))),
                                    cancel=self.cancel_flag.is_set, workroot=outdir)
                    el = time.time() - t0
                    dur = float(v.get("dur") or 0.0)
                    r = C.calibrate_output_rate(dur, el, h, self.quality_var.get())
                    if r:
                        self.say("   实测 %.1f 秒 / 片长 %.1f 秒 → 输出速度 %.2fx（已记入下次预估）"
                                 % (el, dur, r))
                        self.q.put(("rate", C.output_rates()))
                except Exception as e:
                    ok = False
                    self.say("[错误] %s" % e)
            self.q.put(("done", ok))
            self.q.put(("progress", 1.0 if ok else self.prog_var.get() / 100.0))
        self.worker = threading.Thread(target=work, daemon=True)
        self.worker.start()

    def do_stop(self):
        self.cancel_flag.set()
        self.say("[停止] 已请求停止，正在收尾…")

    def pick_outdir(self):
        p = filedialog.askdirectory(title="选择输出目录")
        if p:
            self.outdir_var.set(win_path(p))

    def _open_outdir(self):
        d = self.outdir_var.get()
        if os.path.isdir(d):
            os.startfile(d)

    # ---------------------------------------------------------------- 配置
    def _settings_dict(self):
        return dict(
            version=5,
            tracks=[t["path"] for t in self.tracks],
            title=self.title_var.get(), gstyle=self.gstyle_var.get(),
            color=self.color_var.get(), custom_color=self.custom_color,
            panel_opacity=int(self.panel_op_var.get()),
            map_opacity=int(self.map_op_var.get()),
            escale={k: [float(v[0]), float(v[1])] for k, v in self.escale.items()},
            map_on=self.map_var.get(), zoom_on=self.zoom_var.get(),
            template=self.tpl_var.get(),
            rels=dict(panel=self.rel["panel"], map=self.rel["map"], zoom=self.rel["zoom"]),
            output_rates=C.output_rates(),
            fields=[f for f in C.FIELD_ORDER if self.fvars[f].get()],
            outdir=self.outdir_var.get(), height=self.height_var.get(),
            quality=self.quality_var.get(), audio=self.audio_var.get(),
            shutdown=self.shutdown_var.get(),
            videos=[dict(path=v["path"], base=v.get("base", v["start"]), start=v.get("base", v["start"]),
                         src=v["src"], offset=v.get("offset", 0.0),
                         disp=v.get("disp")) for v in self.videos])

    def _save_settings(self):
        try:
            self.outdir_var.set(win_path(self.outdir_var.get()))
            json.dump(self._settings_dict(), open(SETTINGS, "w", encoding="utf-8"),
                      ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _load_settings(self):
        if not os.path.exists(SETTINGS):
            return
        try:
            d = json.load(open(SETTINGS, encoding="utf-8"))
        except Exception:
            return
        if d.get("version") == 2:
            try:
                d = dict(version=5,
                         tracks=[d.get("track")] if d.get("track") else [],
                         title=d.get("title", ""), gstyle=d.get("gstyle", ""),
                         color=d.get("color", ""), custom_color=d.get("custom_color"),
                         panel_opacity=int(round(int(d.get("opacity", 108)) / 255.0 * 100)),
                         map_opacity=60,
                         escale={"panel": [float(d.get("scale", 1.0))] * 2,
                                 "map": [1.0, 1.0], "zoom": [1.0, 1.0]},
                         map_on=d.get("map_on", True), zoom_on=False,
                         template=d.get("template", "骑行"), rels=None,
                         fields=d.get("fields"), outdir=d.get("outdir", ""),
                         height=d.get("height", "1080 (全高清)"), quality=d.get("quality", "中"),
                         audio=d.get("audio", True), videos=d.get("videos"))
            except Exception:
                return
        if d.get("version") == 3 or d.get("version") == 4:
            # v3/v4 用的是 percent 的 panel_size / map_size，且全景与放大图共用缩放
            ps = float(d.get("panel_size", 100.0)) / 100.0
            ms = float(d.get("map_size", 100.0)) / 100.0
            d = dict(d, version=5,
                     escale={"panel": [ps, ps], "map": [ms, ms], "zoom": [ms, ms]})
        if d.get("version") not in (5, 6, 7):
            return
        self.title_var.set(d.get("title", self.title_var.get()))
        self.gstyle_var.set(d.get("gstyle", self.gstyle_var.get()))
        if self.gstyle_var.get() == "方形仪表盘":
            self.gstyle_var.set("圆形仪表盘")
        self.color_var.set(d.get("color", self.color_var.get()))
        self.custom_color = d.get("custom_color", self.custom_color)
        self.panel_op_var.set(int(d.get("panel_opacity", 60)))
        self.map_op_var.set(int(d.get("map_opacity", 60)))
        esc = d.get("escale") or {}
        for k in ("panel", "map", "zoom"):
            v = esc.get(k)
            if isinstance(v, (list, tuple)) and len(v) == 2:
                self.escale[k] = [float(v[0]), float(v[1])]
        self.map_var.set(d.get("map_on", True))
        self.zoom_var.set(d.get("zoom_on", True))
        self.tpl_var.set(d.get("template", self.tpl_var.get()))
        rels = d.get("rels") or {}
        for k in ("panel", "map", "zoom"):
            v = rels.get(k)
            if isinstance(v, (list, tuple)) and len(v) == 2:
                self.rel[k] = [float(v[0]), float(v[1])]
        saved_fields = d.get("fields")
        if saved_fields:
            for fid, v in self.fvars.items():
                v.set(fid in saved_fields)
        self.outdir_var.set(win_path(d.get("outdir", self.outdir_var.get())))
        self.height_var.set(d.get("height", self.height_var.get()))
        self.quality_var.set(d.get("quality", self.quality_var.get()))
        self.audio_var.set(d.get("audio", True))
        self.shutdown_var.set(bool(d.get("shutdown", False)))
        C.set_output_rates(d.get("output_rates"))
        self._sync_slider_labels()
        self._swatch()
        paths = [p for p in (d.get("tracks") or []) if p and os.path.exists(p)]
        if not paths and d.get("track") and os.path.exists(d["track"]):
            paths = [d["track"]]
        if paths:
            self._parse_tracks(paths)
        else:
            self._update_track_info()
        saved = [v for v in (d.get("videos") or []) if os.path.exists(v.get("path", ""))]
        for v in saved:                       # 兼容旧版设置：旧数据里 start 已含 offset
            if "base" not in v:
                v["base"] = (float(v["start"]) - float(v.get("offset") or 0.0)) \
                    if v.get("start") else None
        if saved:
            prefill = {os.path.normcase(os.path.abspath(v["path"])): v for v in saved}
            self.root.after(600, lambda: self._probe_async([v["path"] for v in saved], prefill))

    def _on_close(self):
        self._save_settings()
        self.root.destroy()


def main():
    C.ensure_console_streams()
    root = tk.Tk()
    app = App(root)

    def excepthook(exc, val, tb):
        traceback.print_exception(exc, val, tb)
        try:
            messagebox.showerror("程序异常", "%s" % val)
        except Exception:
            pass
    root.report_callback_exception = excepthook
    root.mainloop()


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()      # 打包后 HUD 帧并行渲染的子进程依赖此调用
    main()
