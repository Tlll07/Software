#!/usr/bin/env python3
"""
迅捷翻译 v6 — AI 驱动的免费翻译工具
作者：央苏白
"""

import tkinter as tk
from tkinter import messagebox
import urllib.request
import urllib.parse
import json
import threading
import platform
import re
import ssl
import socket
import os
import sys
import base64

try:
    ssl._create_default_https_context = ssl._create_unverified_context
except AttributeError:
    pass

try:
    from PIL import Image, ImageTk
    HAS_PIL = True
except ImportError:
    HAS_PIL = False


# ═══════════════════════════════════════════════════════════════
#                        软件配置（修改这里）
# ═══════════════════════════════════════════════════════════════

APP_NAME     = "迅捷翻译"
APP_VERSION  = "v6.0"
AUTHOR_NAME  = "央苏白"
AUTHOR_QQ    = "2752551361"
AUTHOR_WECHAT = "ysb0722zsy"
AUTHOR_BLOG  = ""
COPYRIGHT    = "该翻译软件纯免费，如有盗版请举报打击"
DONATION_QR_BASE64 = ""

# AI 提供商预设（全部兼容 OpenAI 接口格式）
AI_PROVIDERS = {
    "DeepSeek": {"base_url": "https://api.deepseek.com/v1", "model": "deepseek-chat"},
    "通义千问":  {"base_url": "https://dashscope.aliyuncs.com/compatible-mode/v1", "model": "qwen-turbo"},
    "智谱AI":   {"base_url": "https://open.bigmodel.cn/api/paas/v4", "model": "glm-4-flash"},
}

AI_LANG_MAP = {
    "zh-CN": "简体中文", "en": "English", "ja": "日本語",
    "ko": "한국어", "fr": "Français", "de": "Deutsch",
    "es": "Español", "ru": "Русский", "pt": "Português", "it": "Italiano",
}

EXIT_HOTKEYS = {
    "Escape":      "Esc",
    "Control-q":   "Ctrl+Q",
    "Control-w":   "Ctrl+W",
}

# ═══════════════════════════════════════════════════════════════
#                           主题配色
# ═══════════════════════════════════════════════════════════════

THEMES = {
    "gray": {
        "name": "灰黑", "bg": "#1a1a1a", "surface": "#262626",
        "surface2": "#343434", "accent": "#7aa2f7", "text": "#e0e0e0",
        "dim": "#808080", "border": "#444444", "ok": "#4cd4a6",
        "err": "#f27078", "warn": "#e8c55a",
    },
    "dark": {
        "name": "暗夜紫", "bg": "#0e0e14", "surface": "#161620",
        "surface2": "#20202c", "accent": "#7b6cf6", "text": "#e2e2ec",
        "dim": "#5c5c72", "border": "#2a2a3a", "ok": "#4cd4a6",
        "err": "#f27078", "warn": "#e8c55a",
    },
    "light": {
        "name": "纯白", "bg": "#f4f4f8", "surface": "#ffffff",
        "surface2": "#eaeaf0", "accent": "#6366f1", "text": "#1e1e2e",
        "dim": "#8888a0", "border": "#d0d0dc", "ok": "#059669",
        "err": "#dc2626", "warn": "#d97706",
    },
    "warm": {
        "name": "暖棕", "bg": "#1a1410", "surface": "#241e16",
        "surface2": "#302a20", "accent": "#e8a847", "text": "#f0e8d8",
        "dim": "#7a7060", "border": "#3a342a", "ok": "#4cd4a6",
        "err": "#f27078", "warn": "#e8c55a",
    },
    "ocean": {
        "name": "深海", "bg": "#0a1628", "surface": "#0f1f38",
        "surface2": "#162a48", "accent": "#38bdf8", "text": "#e0f0ff",
        "dim": "#5a7a9a", "border": "#1e3a5a", "ok": "#4cd4a6",
        "err": "#f27078", "warn": "#e8c55a",
    },
}

LANGS = [("中", "zh-CN"), ("EN", "en"), ("日", "ja"),
         ("한", "ko"), ("FR", "fr"), ("DE", "de")]

LANG_NAMES = {
    "zh": "中文", "zh-cn": "中文", "en": "英语", "ja": "日语",
    "ko": "韩语", "fr": "法语", "de": "德语", "es": "西语", "ru": "俄语",
}

YOUDAO_MAP = {
    "auto": "AUTO", "zh-CN": "ZH_CHS", "en": "EN", "ja": "JA",
    "ko": "KR", "fr": "FR", "de": "DE", "es": "ES", "ru": "RU",
}

PLACEHOLDER_FULL = "输入或粘贴要翻译的文字…"
PLACEHOLDER_MINI = "输入文字，自动翻译…"


# ═══════════════════════════════════════════════════════════════
#                        主程序
# ═══════════════════════════════════════════════════════════════

class FloatingTranslator:

    def __init__(self):
        self.root = tk.Tk()
        self._current_theme = "gray"
        self.C = dict(THEMES["gray"])
        self._init_window()
        self._init_fonts()

        self._drag_x = self._drag_y = 0
        self._debounce_id = None
        self._busy = False
        self._seq = 0
        self._src_lang = "auto"
        self._tgt_lang = "en"
        self._collapsed = False
        self._mini_mode = False
        self._has_placeholder = True
        self._mini_has_placeholder = True
        self._proxy = ""
        self._always_on_top = True
        self._settings_win = None
        self._exit_hotkey = "Escape"
        self._pending_retranslate = False

        # AI 设置
        self._ai_provider = "DeepSeek"
        self._ai_base_url = AI_PROVIDERS["DeepSeek"]["base_url"]
        self._ai_api_key = ""
        self._ai_model = AI_PROVIDERS["DeepSeek"]["model"]

        self._load_config()
        if self._current_theme in THEMES:
            self.C = dict(THEMES[self._current_theme])
        self._opener = self._build_opener()
        self._build_ui()
        self._build_mini_ui()
        self._bind_events()
        self._refresh_model_label()
        self._fade_in()

    # ────────────── 初始化 ──────────────

    def _init_window(self):
        r = self.root
        r.title(APP_NAME)
        r.attributes("-topmost", True)
        r.overrideredirect(True)
        r.configure(bg=self.C["bg"])
        w, h = 430, 510
        x = r.winfo_screenwidth() - w - 60
        r.geometry(f"{w}x{h}+{x}+80")
        r.minsize(300, 36)
        r.attributes("-alpha", 0)

    def _init_fonts(self):
        s = platform.system()
        fam = {"Windows": "Microsoft YaHei UI", "Darwin": "PingFang SC"}.get(
            s, "Noto Sans CJK SC")
        self.F = {
            "title": (fam, 10, "bold"), "normal": (fam, 11),
            "small": (fam, 9), "big": (fam, 13, "bold"), "huge": (fam, 18, "bold"),
        }

    def _fade_in(self):
        try:
            a = self.root.attributes("-alpha")
            if a < 0.98:
                self.root.attributes("-alpha", min(a + 0.08, 1.0))
                self.root.after(16, self._fade_in)
            else:
                self.root.attributes("-alpha", 1.0)
        except tk.TclError:
            self.root.attributes("-alpha", 1.0)

    # ────────────── 网络层 ──────────────

    def _build_opener(self):
        try:
            ctx = ssl.create_default_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
            h = urllib.request.HTTPSHandler(context=ctx)
        except Exception:
            h = urllib.request.HTTPSHandler()
        handlers = [h]
        if self._proxy:
            handlers.append(urllib.request.ProxyHandler(
                {"https": self._proxy, "http": self._proxy}))
        return urllib.request.build_opener(*handlers)

    # ────────────── 配置持久化 ──────────────

    def _config_path(self):
        base = os.path.dirname(sys.executable if getattr(sys, 'frozen', False)
                               else os.path.abspath(__file__))
        return os.path.join(base, "config.json")

    def _load_config(self):
        path = self._config_path()
        if not os.path.exists(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            self._ai_provider = cfg.get("ai_provider", self._ai_provider)
            self._ai_base_url = cfg.get("ai_base_url", self._ai_base_url)
            self._ai_api_key = cfg.get("ai_api_key", self._ai_api_key)
            self._ai_model = cfg.get("ai_model", self._ai_model)
            self._proxy = cfg.get("proxy", self._proxy)
            self._exit_hotkey = cfg.get("exit_hotkey", self._exit_hotkey)
            self._always_on_top = cfg.get("always_on_top", self._always_on_top)
            self._current_theme = cfg.get("current_theme", self._current_theme)
            if self._current_theme in THEMES:
                self.C = dict(THEMES[self._current_theme])
        except Exception:
            pass

    def _save_config(self):
        cfg = {
            "ai_provider": self._ai_provider,
            "ai_base_url": self._ai_base_url,
            "ai_api_key": self._ai_api_key,
            "ai_model": self._ai_model,
            "proxy": self._proxy,
            "exit_hotkey": self._exit_hotkey,
            "always_on_top": self._always_on_top,
            "current_theme": self._current_theme,
        }
        try:
            with open(self._config_path(), "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _http_get(self, url, headers=None, timeout=5):
        if not headers:
            headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                     "Chrome/125.0 Safari/537.36"}
        req = urllib.request.Request(url, headers=headers)
        with self._opener.open(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def _http_post_json(self, url, body, headers=None, timeout=15):
        if not headers:
            headers = {"Content-Type": "application/json",
                       "User-Agent": "Mozilla/5.0"}
        data = json.dumps(body, ensure_ascii=False).encode("utf-8")
        req = urllib.request.Request(url, data=data, headers=headers)
        with self._opener.open(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def _run_diagnostic(self):
        tests = [("基础网络", "www.baidu.com", 443),
                 ("MyMemory", "api.mymemory.translated.net", 443),
                 ("有道翻译", "fanyi.youdao.com", 443),
                 ("Google", "translate.googleapis.com", 443)]
        results = []
        for name, host, port in tests:
            try:
                s = socket.create_connection((host, port), timeout=3)
                s.close()
                results.append(f"  ✓  {name}")
            except Exception as e:
                err = "超时" if "timed" in str(e).lower() or "10060" in str(e) \
                    else "DNS失败" if "11001" in str(e) else "连接失败"
                results.append(f"  ✗  {name}  — {err}")
        return results

    def _get_resource_path(self, filename):
        base = os.path.dirname(sys.executable if getattr(sys, 'frozen', False)
                               else os.path.abspath(__file__))
        return os.path.join(base, filename)

    # ────────────── 图片加载 ──────────────

    def _load_qr_image(self, max_w=240, max_h=240):
        if DONATION_QR_BASE64.strip():
            try:
                raw = base64.b64decode(DONATION_QR_BASE64.strip())
                if HAS_PIL:
                    return ImageTk.PhotoImage(
                        self._resize_pil(Image.open(__import__("io").BytesIO(raw)),
                                         max_w, max_h))
                return self._scale_tk_image(tk.PhotoImage(data=raw), max_w)
            except Exception:
                pass
        for name in ["收款码.png", "收款码.jpg", "收款码.gif",
                     "donation.png", "donation.gif"]:
            path = self._get_resource_path(name)
            if not os.path.exists(path):
                continue
            try:
                if HAS_PIL:
                    return ImageTk.PhotoImage(
                        self._resize_pil(Image.open(path), max_w, max_h))
                return self._scale_tk_image(tk.PhotoImage(file=path), max_w)
            except Exception:
                continue
        return None

    def _resize_pil(self, img, mw, mh):
        w, h = img.size
        if w <= mw and h <= mh:
            return img
        r = min(mw / w, mh / h)
        return img.resize((int(w * r), int(h * r)), Image.LANCZOS)

    def _scale_tk_image(self, img, ms):
        w, h = img.width(), img.height()
        if w <= ms and h <= ms:
            return img
        return img.subsample(max(1, int(max(w, h) / ms)))

    # ════════════════════ 全模式 UI ════════════════════

    def _build_ui(self):
        self._build_titlebar()
        self._main = tk.Frame(self.root, bg=self.C["bg"])
        self._main.pack(fill="both", expand=True, padx=10, pady=(6, 10))
        self._build_input_area()
        self._build_lang_bar()
        self._build_output_area()
        self._build_bottom_bar()
        self._build_disclaimer()

    def _build_titlebar(self):
        C, F = self.C, self.F
        bar = tk.Frame(self.root, bg=C["surface"], height=36, cursor="fleur")
        bar.pack(fill="x")
        bar.pack_propagate(False)

        brand = tk.Label(bar, text=f"  ◆ {APP_NAME}", bg=C["surface"],
                         fg=C["accent"], font=F["title"], cursor="hand2")
        brand.pack(side="left", padx=4)
        brand.bind("<Button-1>", lambda e: self._show_about())
        brand.bind("<Enter>", lambda e: brand.configure(fg=C["text"]))
        brand.bind("<Leave>", lambda e: brand.configure(fg=C["accent"]))

        bf = tk.Frame(bar, bg=C["surface"])
        bf.pack(side="right", padx=6)

        self._btn_mini = self._make_btn(bf, "⬜", C["dim"], C["text"],
                                        lambda e: self._toggle_mini_mode())
        self._btn_mini.pack(side="right")
        self._btn_topmost = self._make_btn(bf, "📌", C["accent"], C["text"],
                                           lambda e: self._toggle_topmost())
        self._btn_topmost.pack(side="right", padx=(4, 0))
        self._make_btn(bf, "⚡", C["dim"], C["warn"],
                       lambda e: self._show_diagnostic()).pack(side="right", padx=(4, 0))
        self._make_btn(bf, "⚙", C["dim"], C["warn"],
                       lambda e: self._open_settings()).pack(side="right", padx=(4, 0))
        self._make_btn(bf, "─", C["dim"], C["text"],
                       lambda e: self._toggle_collapse()).pack(side="right", padx=(4, 0))
        self._make_btn(bf, "✕", C["dim"], C["err"],
                       lambda e: self.root.destroy()).pack(side="right", padx=(4, 0))

        bar.bind("<Button-1>", self._on_drag_start)
        bar.bind("<B1-Motion>", self._on_drag_move)

    def _build_input_area(self):
        C, F = self.C, self.F
        m = self._main
        row = tk.Frame(m, bg=C["bg"])
        row.pack(fill="x", pady=(0, 3))
        tk.Label(row, text="原文", bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(side="left")
        self._lbl_count = tk.Label(row, text="", bg=C["bg"], fg=C["dim"],
                                    font=F["small"])
        self._lbl_count.pack(side="right")
        self._input = tk.Text(m, height=5, bg=C["surface"], fg=C["dim"],
                              insertbackground=C["accent"], font=F["normal"],
                              relief="flat", bd=0, padx=10, pady=8, wrap="word",
                              selectbackground=C["accent"], selectforeground="#fff",
                              highlightthickness=1, highlightbackground=C["border"],
                              highlightcolor=C["accent"])
        self._input.pack(fill="x", pady=(0, 6))
        self._input.insert("1.0", PLACEHOLDER_FULL)

    def _build_lang_bar(self):
        C, F = self.C, self.F
        bar = tk.Frame(self._main, bg=C["bg"])
        bar.pack(fill="x", pady=(0, 6))
        self._lbl_src = tk.Label(bar, text="自动检测", bg=C["surface2"],
                                 fg=C["dim"], font=F["small"], padx=10, pady=3)
        self._lbl_src.pack(side="left")
        swap = tk.Label(bar, text=" ⇄ ", bg=C["bg"], fg=C["accent"],
                        font=F["big"], cursor="hand2")
        swap.pack(side="left", padx=6)
        swap.bind("<Button-1>", lambda e: self._swap_languages())
        swap.bind("<Enter>", lambda e: swap.configure(fg=C["text"]))
        swap.bind("<Leave>", lambda e: swap.configure(fg=C["accent"]))
        self._lang_btns = {}
        for label, code in LANGS:
            btn = tk.Label(bar, text=label, bg=C["surface2"], fg=C["dim"],
                           font=F["small"], padx=8, pady=3, cursor="hand2")
            btn.pack(side="left", padx=2)
            btn.bind("<Button-1>", lambda e, c=code: self._set_target_lang(c))
            self._lang_btns[code] = btn
        self._refresh_lang_btns()

    def _build_output_area(self):
        C, F = self.C, self.F
        row = tk.Frame(self._main, bg=C["bg"])
        row.pack(fill="x", pady=(0, 3))
        tk.Label(row, text="译文", bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(side="left")
        self._lbl_status = tk.Label(row, text="", bg=C["bg"], fg=C["ok"],
                                     font=F["small"])
        self._lbl_status.pack(side="right", padx=(0, 6))
        cp = tk.Label(row, text="复制", bg=C["bg"], fg=C["accent"],
                      font=F["small"], cursor="hand2")
        cp.pack(side="right")
        cp.bind("<Button-1>", lambda e: self._copy_output())
        cp.bind("<Enter>", lambda e: cp.configure(fg=C["text"]))
        cp.bind("<Leave>", lambda e: cp.configure(fg=C["accent"]))
        self._output = tk.Text(self._main, height=5, bg=C["surface"], fg=C["text"],
                               font=F["normal"], relief="flat", bd=0, padx=10, pady=8,
                               wrap="word", state="disabled",
                               selectbackground=C["accent"], selectforeground="#fff",
                               highlightthickness=1, highlightbackground=C["border"],
                               highlightcolor=C["accent"], cursor="arrow")
        self._output.pack(fill="x")

    def _build_bottom_bar(self):
        C, F = self.C, self.F
        bar = tk.Frame(self._main, bg=C["bg"])
        bar.pack(fill="x", pady=(6, 2))
        self._lbl_engine = tk.Label(bar, text="引擎：自动选择",
                                     bg=C["bg"], fg=C["dim"], font=F["small"])
        self._lbl_engine.pack(side="left")
        self._lbl_model = tk.Label(bar, text="", bg=C["bg"], fg=C["dim"],
                                    font=F["small"])
        self._lbl_model.pack(side="left", padx=(8, 0))
        self._lbl_proxy_state = tk.Label(bar, text="", bg=C["bg"],
                                          fg=C["warn"], font=F["small"])
        self._lbl_proxy_state.pack(side="right")
        self._refresh_proxy_label()
        self._refresh_model_label()

    def _build_disclaimer(self):
        C, F = self.C, self.F
        tk.Label(self._main, text=COPYRIGHT,
                 bg=C["bg"], fg=C["dim"], font=F["small"]).pack(pady=(4, 0))
        tk.Label(self._main, text=f"作者：{AUTHOR_NAME}  {APP_VERSION}",
                 bg=C["bg"], fg=C["dim"], font=F["small"]).pack(pady=(2, 0))

    # ════════════════════ 极简模式 UI ════════════════════

    def _build_mini_ui(self):
        C, F = self.C, self.F
        self._mini_frame = tk.Frame(self.root, bg=C["bg"])

        # 极简标题栏
        mbar = tk.Frame(self._mini_frame, bg=C["surface"], height=30, cursor="fleur")
        mbar.pack(fill="x")
        mbar.pack_propagate(False)

        lang_hint = self._get_lang_hint()
        self._mini_lang_label = tk.Label(mbar, text=lang_hint, bg=C["surface"],
                                          fg=C["dim"], font=F["small"])
        self._mini_lang_label.pack(side="left", padx=8)

        expand_btn = self._make_btn(mbar, "全", C["dim"], C["text"],
                                    lambda e: self._toggle_mini_mode())
        expand_btn.pack(side="right", padx=(0, 8))
        close_btn = self._make_btn(mbar, "✕", C["dim"], C["err"],
                                   lambda e: self.root.destroy())
        close_btn.pack(side="right", padx=(0, 4))

        mbar.bind("<Button-1>", self._on_drag_start)
        mbar.bind("<B1-Motion>", self._on_drag_move)

        # 极简输入
        self._mini_input = tk.Text(
            self._mini_frame, height=3, bg=C["surface"], fg=C["dim"],
            insertbackground=C["accent"], font=F["normal"],
            relief="flat", bd=0, padx=10, pady=6, wrap="word",
            selectbackground=C["accent"], selectforeground="#fff",
            highlightthickness=1, highlightbackground=C["border"],
            highlightcolor=C["accent"])
        self._mini_input.pack(fill="x", padx=8, pady=(6, 3))
        self._mini_input.insert("1.0", PLACEHOLDER_MINI)

        # 极简输出
        self._mini_output = tk.Text(
            self._mini_frame, height=3, bg=C["surface"], fg=C["text"],
            font=F["normal"], relief="flat", bd=0, padx=10, pady=6,
            wrap="word", state="disabled",
            selectbackground=C["accent"], selectforeground="#fff",
            highlightthickness=1, highlightbackground=C["border"],
            highlightcolor=C["accent"], cursor="arrow")
        self._mini_output.pack(fill="x", padx=8, pady=(3, 8))

        # 绑定事件
        self._mini_input.bind("<FocusIn>", self._on_mini_focus_in)
        self._mini_input.bind("<FocusOut>", self._on_mini_focus_out)
        self._mini_input.bind("<KeyRelease>", self._on_any_key_release)

    def _get_lang_hint(self):
        src = "自动" if self._src_lang == "auto" else LANG_NAMES.get(
            self._src_lang, self._src_lang)
        tgt = LANG_NAMES.get(self._tgt_lang, self._tgt_lang)
        return f"{src}→{tgt}"

    def _toggle_mini_mode(self):
        input_text = self._get_active_input_text()
        output_text = self._get_active_output_text()

        if self._mini_mode:
            self._mini_frame.pack_forget()
            self._main.pack(fill="both", expand=True, padx=10, pady=(6, 10))
            self._set_win_size(430, 510)
            if input_text:
                self._input.delete("1.0", "end")
                self._input.insert("1.0", input_text)
                self._input.configure(fg=self.C["text"])
                self._has_placeholder = False
            if output_text:
                self._set_output_text(output_text)
            self._mini_mode = False
        else:
            self._main.pack_forget()
            self._mini_frame.pack(fill="both", expand=True)
            self._mini_lang_label.configure(text=self._get_lang_hint())
            self._set_win_size(360, 230)
            if input_text:
                self._mini_input.delete("1.0", "end")
                self._mini_input.insert("1.0", input_text)
                self._mini_input.configure(fg=self.C["text"])
                self._mini_has_placeholder = False
            if output_text:
                self._set_mini_output_text(output_text)
            self._mini_mode = True
            self._mini_input.focus_set()

        # 重新绑定退出快捷键
        self._rebind_exit_hotkey()

    def _rebind_exit_hotkey(self):
        for key in EXIT_HOTKEYS:
            try:
                self.root.unbind(f"<{key}>")
            except Exception:
                pass
        if self._mini_mode:
            self.root.bind(f"<{self._exit_hotkey}>",
                           lambda e: self.root.destroy())

    # ────────────── 极简模式事件 ──────────────

    def _on_mini_focus_in(self, event):
        if self._mini_has_placeholder:
            self._mini_input.delete("1.0", "end")
            self._mini_input.configure(fg=self.C["text"])
            self._mini_has_placeholder = False

    def _on_mini_focus_out(self, event):
        if not self._mini_input.get("1.0", "end-1c").strip():
            self._mini_input.insert("1.0", PLACEHOLDER_MINI)
            self._mini_input.configure(fg=self.C["dim"])
            self._mini_has_placeholder = True

    def _set_mini_output_text(self, text):
        self._mini_output.configure(state="normal")
        self._mini_output.delete("1.0", "end")
        if text:
            self._mini_output.insert("1.0", text)
        self._mini_output.configure(state="disabled")

    # ════════════════════ 事件绑定 ════════════════════

    def _bind_events(self):
        self._input.bind("<FocusIn>", self._on_full_focus_in)
        self._input.bind("<FocusOut>", self._on_full_focus_out)
        self._input.bind("<KeyRelease>", self._on_any_key_release)
        self._input.bind("<Control-Return>", lambda e: self._translate_now())
        self.root.bind("<Escape>", lambda e: self._toggle_collapse()
                       if not self._mini_mode else self.root.destroy())
        self.root.bind("<Button-3>", lambda e: self.root.destroy())
        self.root.bind("<Map>", self._on_window_map)

    def _on_full_focus_in(self, event):
        if self._has_placeholder:
            self._input.delete("1.0", "end")
            self._input.configure(fg=self.C["text"])
            self._has_placeholder = False

    def _on_full_focus_out(self, event):
        if not self._input.get("1.0", "end-1c").strip():
            self._input.insert("1.0", PLACEHOLDER_FULL)
            self._input.configure(fg=self.C["dim"])
            self._has_placeholder = True
            self._lbl_count.configure(text="")

    def _on_any_key_release(self, event):
        text = self._get_active_input_text()
        if not self._mini_mode and not self._has_placeholder:
            self._lbl_count.configure(
                text=f"{len(text)} 字" if text.strip() else "")
        if self._debounce_id:
            self.root.after_cancel(self._debounce_id)
        if text.strip():
            self._debounce_id = self.root.after(500, self._do_translate)
        else:
            self._set_active_output("")
            if not self._mini_mode:
                self._lbl_status.configure(text="")

    def _on_drag_start(self, event):
        self._drag_x = event.x
        self._drag_y = event.y

    def _on_drag_move(self, event):
        self.root.geometry(
            f"+{self.root.winfo_x() + event.x - self._drag_x}"
            f"+{self.root.winfo_y() + event.y - self._drag_y}")

    def _toggle_collapse(self):
        if self._mini_mode:
            return
        if self._collapsed:
            self._main.pack(fill="both", expand=True, padx=10, pady=(6, 10))
            self._set_win_size(430, 510)
            self._collapsed = False
        else:
            self._main.pack_forget()
            self._set_win_size(430, 36)
            self._collapsed = True

    def _set_win_size(self, w, h):
        g = self.root.geometry()
        m = re.match(r"(\d+)x(\d+)\+(\d+)\+(\d+)", g)
        if m:
            self.root.geometry(f"{w}x{h}+{m.group(3)}+{m.group(4)}")

    def _on_window_map(self, event):
        if self.root.state() == "normal":
            self.root.after(50, lambda: self.root.overrideredirect(True))

    def _toggle_topmost(self):
        self._always_on_top = not self._always_on_top
        self.root.attributes("-topmost", self._always_on_top)
        self._btn_topmost.configure(
            fg=self.C["accent"] if self._always_on_top else self.C["dim"])
        self._save_config()

    # ════════════════════ 关于页面 ════════════════════

    def _show_about(self):
        C, F = self.C, self.F
        win = tk.Toplevel(self.root)
        win.title(f"关于 {APP_NAME}")
        win.configure(bg=C["bg"])
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.geometry("380x380+"
                     f"{self.root.winfo_x() + 25}+{self.root.winfo_y() + 50}")

        tk.Label(win, text=f"◆  {APP_NAME}", bg=C["bg"], fg=C["accent"],
                 font=F["huge"]).pack(pady=(28, 4))
        tk.Label(win, text=APP_VERSION, bg=C["bg"], fg=C["dim"],
                 font=F["normal"]).pack()
        tk.Label(win, text="─" * 22, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(pady=(8, 12))

        for lbl, val in [("作    者", AUTHOR_NAME),
                         ("QQ", AUTHOR_QQ), ("微    信", AUTHOR_WECHAT),
                         ("博    客", AUTHOR_BLOG)]:
            if not val:
                continue
            row = tk.Frame(win, bg=C["bg"])
            row.pack(fill="x", padx=40, pady=3)
            tk.Label(row, text=lbl, bg=C["bg"], fg=C["dim"],
                     font=F["normal"], width=8, anchor="e").pack(side="left")
            tk.Label(row, text=val, bg=C["bg"], fg=C["text"],
                     font=F["normal"], anchor="w").pack(side="left", padx=(12, 0))

        tk.Label(win, text="─" * 22, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(pady=(16, 8))
        tk.Label(win, text="免费 · 无广告 · 无捆绑", bg=C["bg"],
                 fg=C["ok"], font=F["normal"]).pack(pady=2)
        tk.Label(win, text=COPYRIGHT, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(pady=2)

        btn = tk.Label(win, text="  关  闭  ", bg=C["surface2"], fg=C["text"],
                       font=F["normal"], padx=24, pady=6, cursor="hand2")
        btn.pack(pady=(16, 0))
        btn.bind("<Button-1>", lambda e: win.destroy())
        btn.bind("<Enter>", lambda e: btn.configure(bg=C["accent"]))
        btn.bind("<Leave>", lambda e: btn.configure(bg=C["surface2"]))

    # ════════════════════ 设置页面（可滚动） ════════════════════

    def _open_settings(self):
        if self._settings_win and self._settings_win.winfo_exists():
            self._settings_win.lift()
            return

        C, F = self.C, self.F
        win = tk.Toplevel(self.root)
        self._settings_win = win
        win.title(f"{APP_NAME} - 设置")
        win.configure(bg=C["bg"])
        win.attributes("-topmost", True)
        win.resizable(False, False)
        w_w, h_w = 450, 600
        win.geometry(f"{w_w}x{h_w}+"
                     f"{self.root.winfo_x() + (self.root.winfo_width() - w_w) // 2}"
                     f"+{self.root.winfo_y() + 30}")

        # ── 可滚动容器 ──
        container = tk.Frame(win, bg=C["bg"])
        container.pack(fill="both", expand=True)

        canvas = tk.Canvas(container, bg=C["bg"], highlightthickness=0, bd=0)
        vsb = tk.Scrollbar(container, orient="vertical", command=canvas.yview)
        sf = tk.Frame(canvas, bg=C["bg"])  # scrollable frame

        sf_id = canvas.create_window((0, 0), window=sf, anchor="nw")
        sf.bind("<Configure>", lambda e: canvas.configure(
            scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(sf_id, width=e.width))
        canvas.configure(yscrollcommand=vsb.set)
        canvas.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        # 鼠标滚轮
        def _mw(event):
            canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

        def _bind_mw(w):
            w.bind("<MouseWheel>", _mw)
            for ch in w.winfo_children():
                _bind_mw(ch)

        # ── 标题 ──
        tk.Label(sf, text=f"{' '.join(APP_NAME)}", bg=C["bg"], fg=C["accent"],
                 font=F["huge"]).pack(pady=(24, 2))
        tk.Label(sf, text=f"作者：{AUTHOR_NAME}  |  {APP_VERSION}",
                 bg=C["bg"], fg=C["dim"], font=F["small"]).pack()
        tk.Label(sf, text="─" * 24, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(pady=(4, 0))

        # ── AI 翻译设置 ──
        tk.Label(sf, text="◈  AI 翻译设置", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))

        # 提供商选择
        tk.Label(sf, text="提供商", bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(anchor="w", padx=24)
        prov_frame = tk.Frame(sf, bg=C["bg"])
        prov_frame.pack(fill="x", padx=24, pady=(2, 6))
        self._prov_btns = {}
        for prov in list(AI_PROVIDERS.keys()) + ["自定义"]:
            btn = tk.Label(prov_frame, text=prov, bg=C["surface2"], fg=C["dim"],
                           font=F["small"], padx=10, pady=4, cursor="hand2")
            btn.pack(side="left", padx=3)
            btn.bind("<Button-1>", lambda e, p=prov: self._select_provider(p))
            self._prov_btns[prov] = btn
        self._refresh_prov_btns()

        # API 地址
        api_url_entry = self._settings_entry(sf, "API 地址", self._ai_base_url)
        # API Key
        api_key_entry = self._settings_entry(sf, "API Key", self._ai_api_key,
                                              show="*")
        # 模型
        model_entry = self._settings_entry(sf, "模型名称", self._ai_model)

        # 提供商切换时自动填充
        self._settings_url_entry = api_url_entry
        self._settings_model_entry = model_entry

        # 测试连接
        test_row = tk.Frame(sf, bg=C["bg"])
        test_row.pack(fill="x", padx=24, pady=(4, 0))
        self._ai_test_label = tk.Label(test_row, text="", bg=C["bg"], fg=C["dim"],
                                        font=F["small"])
        self._ai_test_label.pack(side="left")
        test_btn = tk.Label(test_row, text="  测试连接  ", bg=C["surface2"],
                            fg=C["accent"], font=F["small"], padx=10, pady=3,
                            cursor="hand2")
        test_btn.pack(side="right")
        test_btn.bind("<Button-1>", lambda e: self._test_ai_connection(
            api_url_entry.get().strip(),
            api_key_entry.get().strip(),
            model_entry.get().strip()))
        test_btn.bind("<Enter>", lambda e: test_btn.configure(bg=C["accent"],
                                                               fg="#fff"))
        test_btn.bind("<Leave>", lambda e: test_btn.configure(bg=C["surface2"],
                                                               fg=C["accent"]))

        # ── 界面主题 ──
        tk.Label(sf, text="◈  界面主题", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))
        tf = tk.Frame(sf, bg=C["bg"])
        tf.pack(fill="x", padx=24)
        for key, th in THEMES.items():
            act = (key == self._current_theme)
            b = tk.Label(tf, text=th["name"],
                         bg=th["accent"] if act else C["surface2"],
                         fg="#fff" if act else C["dim"],
                         font=F["small"], padx=12, pady=6, cursor="hand2",
                         relief="solid" if act else "flat",
                         borderwidth=2 if act else 0)
            b.pack(side="left", padx=3, pady=2)
            b.bind("<Button-1>", lambda e, k=key: self._apply_theme(k))

        # ── 网络设置 ──
        tk.Label(sf, text="◈  网络设置", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))
        proxy_entry = self._settings_entry(sf, "HTTP 代理", self._proxy)
        tk.Label(sf, text="留空 = 不使用代理  |  例如 http://127.0.0.1:7890",
                 bg=C["bg"], fg=C["dim"], font=F["small"]).pack(
            anchor="w", padx=24, pady=(2, 0))

        # ── 快捷键设置 ──
        tk.Label(sf, text="◈  快捷键设置", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))
        hk_row = tk.Frame(sf, bg=C["bg"])
        hk_row.pack(fill="x", padx=24)
        tk.Label(hk_row, text="极简模式退出键：", bg=C["bg"], fg=C["dim"],
                 font=F["normal"]).pack(side="left")
        self._hk_display = tk.StringVar(
            value=EXIT_HOTKEYS.get(self._exit_hotkey, "Esc"))
        hk_label = tk.Label(hk_row, textvariable=self._hk_display,
                            bg=C["surface2"], fg=C["text"], font=F["normal"],
                            padx=16, pady=4, cursor="hand2")
        hk_label.pack(side="left", padx=(8, 0))
        hk_label.bind("<Button-1>", lambda e: self._cycle_exit_hotkey())
        tk.Label(sf, text="点击切换  |  极简模式下按此键退出程序",
                 bg=C["bg"], fg=C["dim"], font=F["small"]).pack(
            anchor="w", padx=24, pady=(2, 0))

        # ── 窗口行为 ──
        tk.Label(sf, text="◈  窗口行为", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))
        ts = "已开启" if self._always_on_top else "已关闭"
        tc = C["ok"] if self._always_on_top else C["dim"]
        self._lbl_topmost_state = tk.Label(
            sf, text=f"📌 窗口置顶：{ts}", bg=C["surface2"], fg=tc,
            font=F["normal"], padx=16, pady=6, cursor="hand2")
        self._lbl_topmost_state.pack(anchor="w", padx=24)
        self._lbl_topmost_state.bind(
            "<Button-1>", lambda e: self._toggle_topmost_from_settings())

        # ── 支持作者 ──
        tk.Label(sf, text="◈  支持作者", bg=C["bg"], fg=C["text"],
                 font=F["normal"]).pack(anchor="w", padx=24, pady=(20, 8))
        dn = tk.Label(sf, text="  ☕  打赏支持  ", bg=C["accent"], fg="#fff",
                      font=F["big"], padx=24, pady=8, cursor="hand2")
        dn.pack(anchor="w", padx=24)
        dn.bind("<Button-1>", lambda e: self._show_donation())
        dn.bind("<Enter>", lambda e: dn.configure(bg=C["text"]))
        dn.bind("<Leave>", lambda e: dn.configure(bg=C["accent"]))

        # ── 保存 ──
        def save():
            self._ai_base_url = api_url_entry.get().strip()
            self._ai_api_key = api_key_entry.get().strip()
            self._ai_model = model_entry.get().strip()
            self._proxy = proxy_entry.get().strip()
            self._opener = self._build_opener()
            self._refresh_proxy_label()
            self._refresh_model_label()
            self._save_config()
            win.destroy()
            self._settings_win = None

        sv = tk.Label(sf, text="  保 存 设 置  ", bg=C["surface2"], fg=C["text"],
                      font=F["normal"], padx=20, pady=6, cursor="hand2")
        sv.pack(pady=(24, 30))
        sv.bind("<Button-1>", lambda e: save())
        sv.bind("<Enter>", lambda e: sv.configure(bg=C["accent"]))
        sv.bind("<Leave>", lambda e: sv.configure(bg=C["surface2"]))

        # 绑定滚轮
        _bind_mw(sf)

    def _settings_entry(self, parent, label, default, show=None):
        C, F = self.C, self.F
        tk.Label(parent, text=label, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack(anchor="w", padx=24, pady=(8, 2))
        e = tk.Entry(parent, bg=C["surface"], fg=C["text"], font=F["normal"],
                     insertbackground=C["accent"], relief="flat",
                     highlightthickness=1, highlightbackground=C["border"],
                     highlightcolor=C["accent"], show=show)
        e.pack(fill="x", padx=24, ipady=4)
        e.insert(0, default)
        return e

    def _select_provider(self, prov):
        self._ai_provider = prov
        self._refresh_prov_btns()
        if prov in AI_PROVIDERS:
            p = AI_PROVIDERS[prov]
            if hasattr(self, '_settings_url_entry'):
                self._settings_url_entry.delete(0, "end")
                self._settings_url_entry.insert(0, p["base_url"])
            if hasattr(self, '_settings_model_entry'):
                self._settings_model_entry.delete(0, "end")
                self._settings_model_entry.insert(0, p["model"])
            self._ai_base_url = p["base_url"]
            self._ai_model = p["model"]
        self._refresh_model_label()

    def _refresh_prov_btns(self):
        C = self.C
        for prov, btn in self._prov_btns.items():
            if prov == self._ai_provider:
                btn.configure(bg=C["accent"], fg="#fff")
            else:
                btn.configure(bg=C["surface2"], fg=C["dim"])

    def _cycle_exit_hotkey(self):
        keys = list(EXIT_HOTKEYS.keys())
        idx = keys.index(self._exit_hotkey) if self._exit_hotkey in keys else 0
        self._exit_hotkey = keys[(idx + 1) % len(keys)]
        self._hk_display.set(EXIT_HOTKEYS[self._exit_hotkey])
        self._rebind_exit_hotkey()
        self._save_config()

    def _toggle_topmost_from_settings(self):
        self._toggle_topmost()
        ts = "已开启" if self._always_on_top else "已关闭"
        tc = self.C["ok"] if self._always_on_top else self.C["dim"]
        if hasattr(self, '_lbl_topmost_state'):
            self._lbl_topmost_state.configure(text=f"📌 窗口置顶：{ts}", fg=tc)

    def _test_ai_connection(self, url, key, model):
        if not key:
            self._ai_test_label.configure(text="请先填写 API Key", fg=self.C["warn"])
            return
        self._ai_test_label.configure(text="测试中…", fg=self.C["dim"])

        def do():
            try:
                r = self._ai_translate_raw("Hello world", url, key, model)
                self.root.after(0, lambda: self._ai_test_label.configure(
                    text=f"✓ 成功: {r[:30]}", fg=self.C["ok"]))
            except Exception as e:
                self.root.after(0, lambda: self._ai_test_label.configure(
                    text=f"✗ {type(e).__name__}", fg=self.C["err"]))

        threading.Thread(target=do, daemon=True).start()

    def _refresh_proxy_label(self):
        if hasattr(self, '_lbl_proxy_state'):
            self._lbl_proxy_state.configure(
                text=f"代理: {self._proxy}" if self._proxy else "")

    def _refresh_model_label(self):
        if not hasattr(self, '_lbl_model'):
            return
        if self._ai_api_key.strip():
            self._lbl_model.configure(text=f"模型：{self._ai_provider} / {self._ai_model}")
        else:
            self._lbl_model.configure(text="模型：未配置 AI")

    # ════════════════════ 诊断 / 打赏 ════════════════════

    def _show_diagnostic(self):
        C, F = self.C, self.F
        win = tk.Toplevel(self.root)
        win.configure(bg=C["bg"], padx=0, pady=0)
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.geometry(f"400x280+{self.root.winfo_x() + 15}"
                     f"+{self.root.winfo_y() + 100}")
        tk.Label(win, text="⚡ 网络诊断", bg=C["bg"], fg=C["accent"],
                 font=F["big"]).pack(pady=(14, 8))
        rt = tk.Text(win, bg=C["surface"], fg=C["text"], font=F["normal"],
                     relief="flat", bd=0, padx=12, pady=8, height=8,
                     highlightthickness=1, highlightbackground=C["border"],
                     state="disabled")
        rt.pack(fill="x", padx=16)

        def set_r(lines):
            rt.configure(state="normal")
            rt.delete("1.0", "end")
            rt.insert("1.0", "\n".join(lines))
            rt.configure(state="disabled")

        set_r(["正在检测…"])

        def run():
            rs = self._run_diagnostic()
            ok = sum(1 for r in rs if "✓" in r)
            n = f"\n✓ 全部正常" if ok == len(rs) else \
                f"\n部分可用 ({ok}/{len(rs)})" if ok else "\n⚠ 全部失败"
            self.root.after(0, lambda: set_r(rs + [n]))

        threading.Thread(target=run, daemon=True).start()

    def _show_donation(self):
        C, F = self.C, self.F
        win = tk.Toplevel(self.root)
        win.configure(bg=C["bg"])
        win.attributes("-topmost", True)
        win.resizable(False, False)
        qr = self._load_qr_image(240, 240)
        h = 440 if qr else 300
        win.geometry(f"360x{h}+{self.root.winfo_x() + 35}"
                     f"+{self.root.winfo_y() + 60}")
        tk.Label(win, text="☕  打赏支持", bg=C["bg"], fg=C["accent"],
                 font=F["huge"]).pack(pady=(24, 4))
        tk.Label(win, text="─" * 18, bg=C["bg"], fg=C["dim"],
                 font=F["small"]).pack()
        if qr:
            lbl = tk.Label(win, image=qr, bg=C["bg"])
            lbl.image = qr
            lbl.pack(pady=(16, 8))
            tk.Label(win, text="扫描二维码即可打赏", bg=C["bg"],
                     fg=C["dim"], font=F["small"]).pack()
            tk.Label(win, text=f"感谢支持 {AUTHOR_NAME}！", bg=C["bg"],
                     fg=C["ok"], font=F["normal"]).pack(pady=(4, 0))
        else:
            d = os.path.dirname(os.path.abspath(__file__))
            tk.Label(win, text=f"收款码未配置\n\n请将图片命名为\n收款码.png\n"
                               f"放在程序目录：\n{d}",
                     bg=C["bg"], fg=C["dim"], font=F["normal"],
                     justify="left", wraplength=320).pack(padx=24, pady=16)

    # ════════════════════ 主题切换 ════════════════════

    def _apply_theme(self, name):
        if name not in THEMES or name == self._current_theme:
            return
        self._current_theme = name
        self.C = dict(THEMES[name])
        it = self._get_active_input_text()
        ot = self._get_active_output_text()
        sl, tl = self._src_lang, self._tgt_lang
        top, px = self._always_on_top, self._proxy
        mm = self._mini_mode

        if self._settings_win and self._settings_win.winfo_exists():
            self._settings_win.destroy()
            self._settings_win = None

        for w in self.root.winfo_children():
            w.destroy()

        self._build_ui()
        self._build_mini_ui()
        self._bind_events()

        self._src_lang, self._tgt_lang = sl, tl
        self._proxy, self._always_on_top = px, top
        self.root.attributes("-topmost", top)
        if not top:
            self._btn_topmost.configure(fg=self.C["dim"])

        if mm:
            self._mini_mode = False
            self._toggle_mini_mode()
            if it:
                self._mini_input.delete("1.0", "end")
                self._mini_input.insert("1.0", it)
                self._mini_input.configure(fg=self.C["text"])
                self._mini_has_placeholder = False
            if ot:
                self._set_mini_output_text(ot)
        else:
            if it:
                self._input.delete("1.0", "end")
                self._input.insert("1.0", it)
                self._input.configure(fg=self.C["text"])
                self._has_placeholder = False
            if ot:
                self._set_output_text(ot)

        self._refresh_lang_btns()
        self._refresh_proxy_label()
        self._save_config()

    # ════════════════════ 翻译核心 ════════════════════

    def _get_active_input_text(self):
        if self._mini_mode:
            if self._mini_has_placeholder:
                return ""
            return self._mini_input.get("1.0", "end-1c").strip()
        if self._has_placeholder:
            return ""
        return self._input.get("1.0", "end-1c").strip()

    def _get_active_output_text(self):
        w = self._mini_output if self._mini_mode else self._output
        return w.get("1.0", "end-1c").strip()

    def _set_active_output(self, text):
        if self._mini_mode:
            self._set_mini_output_text(text)
        else:
            self._set_output_text(text)

    def _translate_now(self):
        if self._debounce_id:
            self.root.after_cancel(self._debounce_id)
        self._do_translate()

    def _do_translate(self):
        text = self._get_active_input_text()
        if not text or self._busy:
            return
        self._busy = True
        self._seq += 1
        seq = self._seq
        if self._mini_mode:
            self._set_mini_output_text("翻译中…")
        else:
            self._lbl_status.configure(text="翻译中…", fg=self.C["dim"])
        threading.Thread(target=self._translate_worker,
                         args=(text, seq), daemon=True).start()

    def _translate_worker(self, text, seq):
        engines = []

        # AI 引擎优先（如果配置了 API Key）
        if self._ai_api_key.strip():
            engines.append(("AI", self._try_ai_translate))

        # 传统引擎备用（Bing 较稳定优先）
        engines += [("Bing", self._try_bing),
                    ("Google", self._try_google),
                    ("MyMemory", self._try_mymemory),
                    ("有道", self._try_youdao)]

        errors = []
        for name, func in engines:
            try:
                result = func(text)
                if result:
                    trans, det = result
                    self.root.after(0, self._on_done,
                                    seq, trans, det, None, name)
                    return
            except Exception as e:
                errors.append(f"[{name}] {type(e).__name__}")

        err = " → ".join(errors) if errors else "未知错误"
        hint = "\n\n提示：请在 ⚙ 设置 中配置 AI API Key 以获得更好的翻译效果" if not self._ai_api_key.strip() else ""
        self.root.after(0, self._on_done, seq, "", "",
                        f"全部失败: {err}{hint}", "")

    # ── AI 翻译 ──

    def _ai_translate_raw(self, text, base_url, api_key, model):
        tgt = AI_LANG_MAP.get(self._tgt_lang, self._tgt_lang)
        if self._src_lang == "auto":
            prompt = f"请将以下文本翻译为{tgt}，只输出翻译结果，不要任何解释：\n\n{text}"
        else:
            src = AI_LANG_MAP.get(self._src_lang, self._src_lang)
            prompt = f"请将以下{src}文本翻译为{tgt}，只输出翻译结果：\n\n{text}"

        body = {
            "model": model,
            "messages": [
                {"role": "system",
                 "content": "你是专业翻译，只输出翻译结果，不加解释和引号。"},
                {"role": "user", "content": prompt}
            ],
            "temperature": 0.1,
            "max_tokens": 2000,
        }

        url = f"{base_url.rstrip('/')}/chat/completions"
        result = self._http_post_json(url, body, headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
            "User-Agent": "Mozilla/5.0",
        }, timeout=20)

        return result["choices"][0]["message"]["content"].strip()

    def _try_ai_translate(self, text):
        translated = self._ai_translate_raw(
            text, self._ai_base_url, self._ai_api_key, self._ai_model)
        if translated:
            return translated, "auto"
        raise Exception("空结果")

    # ── MyMemory（GET，自动处理编码）──

    def _try_mymemory(self, text):
        lang_fix = {"zh-CN": "zh-CN", "zh": "zh-CN", "zh-TW": "zh-TW"}
        if self._src_lang == "auto":
            src = "autodetect"
        else:
            src = lang_fix.get(self._src_lang, self._src_lang.split("-")[0])
        tgt = lang_fix.get(self._tgt_lang, self._tgt_lang.split("-")[0])

        params = urllib.parse.urlencode({
            "q": text, "langpair": f"{src}|{tgt}"
        })
        data = self._http_get(
            f"https://api.mymemory.translated.net/get?{params}",
            timeout=10)

        if data.get("responseStatus") == 200:
            t = data["responseData"]["translatedText"]
            if t and t.strip():
                return t.strip(), "auto"
        raise Exception(f"status={data.get('responseStatus')}")

    # ── 有道（POST 方式，避免特殊字符编码问题）──

    def _try_youdao(self, text):
        tgt = YOUDAO_MAP.get(self._tgt_lang, "EN")
        src = YOUDAO_MAP.get(self._src_lang, "AUTO")
        lt = f"AUTO2{tgt}" if src == "AUTO" else f"{src}2{tgt}"

        post_data = urllib.parse.urlencode({
            "doctype": "json", "type": lt, "i": text
        }).encode("utf-8")

        req = urllib.request.Request(
            "https://fanyi.youdao.com/translate",
            data=post_data,
            headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                              "Chrome/125.0 Safari/537.36",
                "Referer": "https://fanyi.youdao.com/",
            })

        with self._opener.open(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))

        if data.get("errorCode") == 0:
            t = "".join(
                s["tgt"] for l in data["translateResult"] for s in l
            )
            if t and t.strip():
                return t.strip(), "auto"
        raise Exception(f"errorCode={data.get('errorCode')}")

    # ── Google ──

    def _try_google(self, text):
        params = urllib.parse.urlencode({
            "client": "gtx", "sl": self._src_lang,
            "tl": self._tgt_lang, "dt": "t", "q": text,
        })
        data = self._http_get(
            f"https://translate.googleapis.com/translate_a/single?{params}",
            timeout=10)
        t = "".join(s[0] for s in data[0] if s[0])
        if t and t.strip():
            return t.strip(), data[2] if len(data) > 2 else "auto"
        raise Exception("Google 返回空结果")

    # ── Bing 翻译 ──

    def _try_bing(self, text):
        tgt = AI_LANG_MAP.get(self._tgt_lang, self._tgt_lang)
        src = "auto" if self._src_lang == "auto" else AI_LANG_MAP.get(self._src_lang, self._src_lang)
        url = "https://api.cognitive.microsofttranslator.com/translate"
        params = urllib.parse.urlencode({"api-version": "3.0", "to": tgt})
        if src != "auto":
            params += f"&from={src}"
        body = [{"Text": text}]
        data = self._http_post_json(
            f"{url}?{params}", body,
            headers={
                "Content-Type": "application/json",
                "User-Agent": "Mozilla/5.0",
            }, timeout=8)
        t = data[0]["translations"][0]["text"]
        if t and t.strip():
            return t.strip(), data[0].get("detectedLanguage", {}).get("language", "auto")
        raise Exception("Bing 返回空结果")

    def _on_done(self, seq, translated, detected, error, engine):
        if seq != self._seq:
            return
        self._busy = False

        if self._pending_retranslate:
            self._pending_retranslate = False
            self.root.after(50, self._do_translate)
            return

        if error:
            if self._mini_mode:
                self._set_mini_output_text(f"失败: {error}")
            else:
                self._lbl_status.configure(text="失败", fg=self.C["err"])
                self._set_output_text(
                    f"{error}\n\n请按 ⚡ 诊断 或在 ⚙ 设置中配置 AI/代理")
            return

        self._set_active_output(translated)
        if not self._mini_mode:
            self._lbl_status.configure(text="✓", fg=self.C["ok"])
            if engine:
                self._lbl_engine.configure(text=f"引擎：{engine}")
            if detected and detected != "auto":
                self._lbl_src.configure(
                    text=LANG_NAMES.get(detected.lower(), detected))
            self.root.after(2500,
                            lambda: self._lbl_status.configure(text=""))

    # ════════════════════ 语言管理 ════════════════════

    def _set_target_lang(self, code):
        self._tgt_lang = code
        self._refresh_lang_btns()
        if self._get_active_input_text():
            if self._busy:
                self._pending_retranslate = True
            else:
                self._do_translate()

    def _refresh_lang_btns(self):
        for code, btn in self._lang_btns.items():
            btn.configure(bg=self.C["accent"] if code == self._tgt_lang
                          else self.C["surface2"],
                          fg="#fff" if code == self._tgt_lang else self.C["dim"])

    def _swap_languages(self):
        if self._src_lang == "auto":
            self._lbl_status.configure(text="自动检测时无法交换",
                                        fg=self.C["warn"])
            self.root.after(1500, lambda: self._lbl_status.configure(text=""))
            return
        self._src_lang, self._tgt_lang = self._tgt_lang, self._src_lang
        st = self._get_active_input_text()
        ot = self._get_active_output_text()
        self._input.delete("1.0", "end")
        if ot:
            self._input.insert("1.0", ot)
            self._input.configure(fg=self.C["text"])
            self._has_placeholder = False
        self._set_output_text(st)
        self._refresh_lang_btns()
        if ot:
            self._do_translate()

    # ════════════════════ 输出操作 ════════════════════

    def _set_output_text(self, text):
        self._output.configure(state="normal")
        self._output.delete("1.0", "end")
        if text:
            self._output.insert("1.0", text)
        self._output.configure(state="disabled")

    def _copy_output(self):
        text = self._get_active_output_text()
        if text:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self._lbl_status.configure(text="已复制 ✓", fg=self.C["ok"])
            self.root.after(1500, lambda: self._lbl_status.configure(text=""))

    # ════════════════════ 辅助 ════════════════════

    def _make_btn(self, parent, text, fg_normal, fg_hover, command):
        btn = tk.Label(parent, text=text, bg=self.C["surface"],
                       fg=fg_normal, font=self.F["small"], padx=6,
                       cursor="hand2")
        btn.bind("<Button-1>", command)
        btn.bind("<Enter>", lambda e, c=fg_hover: btn.configure(fg=c))
        btn.bind("<Leave>", lambda e, c=fg_normal: btn.configure(fg=c))
        return btn

    def run(self):
        self.root.mainloop()


# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    app = FloatingTranslator()
    app.run()
