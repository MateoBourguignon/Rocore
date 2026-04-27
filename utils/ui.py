import os
import json
import sys
import queue
import subprocess
import tkinter as tk
from tkinter import ttk, messagebox, colorchooser, simpledialog
import requests
import threading
import msvcrt
import ctypes
from ctypes import wintypes
import webbrowser
import time
import re
import win32event
import win32api
import win32gui
from datetime import datetime, timedelta, timezone
import zipfile
import tempfile
import shutil
import platform
import traceback
import psutil
import random
import stat
import math
import win32process
import tkinter.font as tkfont
import xml.etree.ElementTree as ET
import win32clipboard
from PIL import Image, ImageTk
from io import BytesIO
from tkinter import filedialog
from urllib.request import urlretrieve
from classes.roblox_api import RobloxAPI
from classes.account_manager import RobloxAccountManager
from utils.encryption_setup import EncryptionSetupUI
from utils.theme_manager import ThemeManager

class AccountManagerUI:
    def __init__(self, root, manager, icon_path=None, discord_logo_path=None):
        self.root = root
        self.manager = manager
        self.icon_path = icon_path
        self.discord_logo_path = discord_logo_path
        self.discord_logo_img = None
        self.APP_VERSION = "1"
        self._game_name_after_id = None
        self._save_settings_timer = None
        
        self.console_output = []
        self.console_window = None
        self.console_text_widget = None
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr
        
        self.tooltip = None
        self.tooltip_timer = None
        
        sys.stdout = self
        sys.stderr = self

        self._ui_task_queue = queue.Queue()
        
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except:
            try:
                ctypes.windll.user32.SetProcessDPIAware()
            except:
                pass
        
        self.data_folder = "AccountManagerData"
        if not os.path.exists(self.data_folder):
            os.makedirs(self.data_folder)
        
        self.settings_file = os.path.join(self.data_folder, "ui_settings.json")
        self.load_settings()
        
        self.root.title("Rocore V1")
        
        saved_pos = self.settings.get('main_window_position')
        if saved_pos:
            self.root.geometry(f"1120x760+{saved_pos['x']}+{saved_pos['y']}")
        else:
            self.root.geometry("1120x760")
        self.root.minsize(980, 680)
        self.root.configure(bg="#0f172a")
        self.root.resizable(True, True)
        
        self.multi_roblox_handle = None
        self.handle64_monitoring = False
        self.handle64_monitor_thread = None
        self.handle64_path = None
        
        self.anti_afk_thread = None
        self.anti_afk_stop_event = threading.Event()
        
        self.rename_thread = None
        self.rename_stop_event = threading.Event()
        self.renamed_pids = set()
        
        self.instances_monitor_thread = None
        self.instances_monitor_stop = threading.Event()
        self.instances_data = []
        self.instances_pids = set()
        self.instances_failed_pids = {} 
        self.instances_data_updated = False
        self.instances_cache = {
            "user_id_to_username": {},
            "user_id_to_avatar": {},
            "user_id_to_photo": {}
        }
        
        self.auto_rejoin_threads = {}
        self.auto_rejoin_stop_events = {}
        self.auto_rejoin_configs = self.settings.get("auto_rejoin_configs", {})
        self.auto_rejoin_pids = {}
        self.auto_rejoin_launch_lock = threading.Lock()
        self.auto_rejoin_presence_lock = threading.Lock()
        self.auto_rejoin_next_presence_time = 0.0
        self._webhook_screenshot_thread = None
        
        self.cookie_status = {}
        for _u, _d in self.manager.accounts.items():
            if isinstance(_d, dict):
                self.cookie_status[_u] = _d.get('cookie_valid', None)
        self.account_tooltip = None
        self.account_tooltip_timer = None
        self.account_tooltip_last_index = None

        self._list_row_map = []
        self._collapsed_groups = set(self.settings.get("group_collapsed", []))

        self.theme_manager = ThemeManager(os.path.join(self.data_folder, "themes"))
        selected_theme = self.settings.get("selected_theme", "Dark")
        current_theme_config = self._load_current_theme_config()
        if current_theme_config:
            source_theme = str(current_theme_config.get("source_theme", selected_theme) or selected_theme)
            base_data = self.theme_manager.load_theme(source_theme)
            merged_data = self.theme_manager._merge_with_defaults(base_data)
            merged_data = self.theme_manager._merge_with_defaults(current_theme_config)
            self.current_theme_data = merged_data
        else:
            self.current_theme_data = self.theme_manager.load_theme(selected_theme)
        
        self.BG_DARK = self.current_theme_data["colors"].get("bg_dark", "#2b2b2b")
        self.BG_MID = self.current_theme_data["colors"].get("bg_mid", "#3a3a3a")
        self.BG_LIGHT = self.current_theme_data["colors"].get("bg_light", "#4b4b4b")
        self.FG_TEXT = self.current_theme_data["colors"].get("fg_text", "white")
        self.FG_ACCENT = self.current_theme_data["colors"].get("fg_accent", "#0078D7")
        self.FONT_FAMILY = self.current_theme_data["fonts"].get("family", "Segoe UI")
        self.FONT_SIZE = self.current_theme_data["fonts"].get("size_base", 10)
        self.root.configure(bg=self.BG_DARK)

        self.BG_APP = self.BG_DARK
        self.BG_PANEL = self.BG_MID
        self.BG_SURFACE = self.BG_LIGHT
        self.BG_BORDER = self._normalize_hex_color("#334155", self.BG_SURFACE)
        self.TEXT_MUTED = self._normalize_hex_color("#94a3b8", self.FG_TEXT)
        self.ACCENT_SOFT = self._normalize_hex_color("#a5b4fc", self.FG_ACCENT)
        self.ON_ACCENT = self._normalize_hex_color("#0f172a", self.FG_TEXT)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure(".", background=self.BG_APP, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.configure("Dark.TFrame", background=self.BG_APP)
        style.configure("Dark.TLabel", background=self.BG_APP, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.configure("Dark.TButton", background=self.BG_PANEL, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1)), padding=(16, 10), borderwidth=0, relief="flat")
        style.map("Dark.TButton", background=[("active", self.BG_SURFACE), ("pressed", self.BG_BORDER)], foreground=[("active", self.FG_TEXT), ("pressed", self.FG_TEXT)])
        style.configure("Accent.TButton", background=self.FG_ACCENT, foreground=self.ON_ACCENT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1), "bold"), padding=(16, 10), borderwidth=0, relief="flat")
        style.map("Accent.TButton", background=[("active", self.ACCENT_SOFT), ("pressed", self.BG_BORDER)], foreground=[("active", self.ON_ACCENT), ("pressed", self.FG_TEXT)])
        style.configure("Accent.Dropdown.TButton", background=self.FG_ACCENT, foreground=self.ON_ACCENT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1), "bold"), padding=(12, 10), borderwidth=0, relief="flat")
        style.map("Accent.Dropdown.TButton", background=[("active", self.ACCENT_SOFT), ("pressed", self.BG_BORDER)], foreground=[("active", self.ON_ACCENT), ("pressed", self.FG_TEXT)])
        style.configure("Dark.TEntry", fieldbackground=self.BG_PANEL, background=self.BG_PANEL, foreground=self.FG_TEXT, insertcolor=self.FG_TEXT, borderwidth=0, relief="flat", padding=10)
        style.map("Dark.TEntry", fieldbackground=[("focus", self.BG_SURFACE), ("active", self.BG_SURFACE)])
        style.configure("Dark.TCheckbutton", background=self.BG_APP, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE), padding=8)
        style.map("Dark.TCheckbutton", background=[("active", self.BG_APP)], foreground=[("active", self.FG_TEXT)])
        style.configure("Dark.TRadiobutton", background=self.BG_APP, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE), padding=8)
        style.map("Dark.TRadiobutton", background=[("active", self.BG_APP)], foreground=[("active", self.FG_TEXT)])
        style.configure("TNotebook", background=self.BG_APP, borderwidth=0, tabmargins=(0, 10, 0, 0))
        style.configure("TNotebook.Tab", background=self.BG_PANEL, foreground=self.FG_TEXT, padding=(18, 12), borderwidth=0)
        style.map("TNotebook.Tab", background=[("selected", self.BG_SURFACE), ("active", self.BG_SURFACE)], foreground=[("selected", self.FG_TEXT), ("active", self.FG_TEXT)])
        style.configure("Treeview", background=self.BG_PANEL, fieldbackground=self.BG_PANEL, foreground=self.FG_TEXT, borderwidth=0, rowheight=32, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.configure("Treeview.Heading", background=self.BG_SURFACE, foreground=self.FG_TEXT, relief="flat", font=(self.FONT_FAMILY, self.FONT_SIZE, "bold"), padding=10)
        style.map("Treeview", background=[("selected", self.FG_ACCENT)], foreground=[("selected", self.ON_ACCENT)])
        style.configure("TScrollbar", gripcount=0, background=self.BG_SURFACE, troughcolor=self.BG_APP, bordercolor=self.BG_APP, arrowcolor=self.FG_TEXT, width=14)
        style.configure("TSeparator", background=self.BG_BORDER)
        style.configure("TLabelframe", background=self.BG_APP, borderwidth=0)
        style.configure("TLabelframe.Label", background=self.BG_APP, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE, "bold"))
        style.configure("TMenubutton", background=self.BG_PANEL, foreground=self.FG_TEXT, padding=(14, 10), relief="flat")

        main_frame = ttk.Frame(self.root, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=10, pady=10)

        left_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        left_frame.pack(side="left", fill="both", expand=True, padx=(0, 10))

        header_frame = ttk.Frame(left_frame, style="Dark.TFrame")
        header_frame.pack(fill="x", anchor="w")
        
        ttk.Label(header_frame, text="Account List", style="Dark.TLabel").pack(side="left")
        
        encryption_status = ""
        encryption_color = self.FG_TEXT
        if self.manager.encryption_config.is_encryption_enabled():
            method = self.manager.encryption_config.get_encryption_method()
            if method == 'hardware':
                encryption_status = "[HARDWARE ENCRYPTED]"
                encryption_color = "#90EE90"
            elif method == 'password':
                encryption_status = "[PASSWORD ENCRYPTED]"
                encryption_color = "#87CEEB"
        else:
            encryption_status = "[NOT ENCRYPTED]"
            encryption_color = "#FFB6C1"
            
        self.encryption_label = tk.Label(
            header_frame,
            text=encryption_status,
            bg=self.BG_APP,
            fg=encryption_color,
            font=(self.FONT_FAMILY, 8, "bold"),
            padx=10,
            pady=4
        )
        self.encryption_label.pack(side="right", padx=(5, 0))

        list_frame = ttk.Frame(left_frame, style="Dark.TFrame")
        list_frame.pack(fill="both", expand=True)

        selectmode = tk.EXTENDED if False else tk.SINGLE
        
        self.account_list = tk.Listbox(
            list_frame,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            selectbackground=self.FG_ACCENT,
            selectforeground=self.ON_ACCENT,
            highlightthickness=1,
            highlightbackground=self.BG_BORDER,
            highlightcolor=self.FG_ACCENT,
            border=0,
            selectborderwidth=0,
            font=(self.FONT_FAMILY, 10),
            width=20,
            selectmode=selectmode,
            activestyle="none",
        )
        self.account_list.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(list_frame, command=self.account_list.yview)
        scrollbar.pack(side="right", fill="y")
        self.account_list.config(yscrollcommand=scrollbar.set)
        
        self.drag_data = {
            "item": None, 
            "index": None, 
            "start_x": 0, 
            "start_y": 0,
            "dragging": False,
            "hold_timer": None
        }
        self.drag_indicator = None
        
        self.account_list.bind("<Button-1>", self.on_drag_start)
        self.account_list.bind("<B1-Motion>", self.on_drag_motion)
        self.account_list.bind("<ButtonRelease-1>", self.on_drag_release)
        self.account_list.bind("<Button-3>", self.show_account_context_menu)
        self.account_list.bind("<Motion>", self.on_account_list_hover)
        self.account_list.bind("<Leave>", self.on_account_list_leave)

        right_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        right_frame.pack(side="right", fill="y")
        
        self.game_name_label = ttk.Label(right_frame, text="", style="Dark.TLabel", font=(self.FONT_FAMILY, 9))
        self.game_name_label.pack(anchor="w", pady=(0, 5))
        
        ttk.Label(right_frame, text="Place ID", style="Dark.TLabel", font=(self.FONT_FAMILY, 9, "bold")).pack(anchor="w")
        self.place_entry = ttk.Entry(right_frame, style="Dark.TEntry")
        self.place_entry.pack(fill="x", pady=(0, 5))
        self.place_entry.insert(0, self.settings.get("last_place_id", ""))
        self.place_entry.bind("<KeyRelease>", self.on_place_id_change)

        ttk.Label(right_frame, text="Private Server ID (Optional)", style="Dark.TLabel", font=(self.FONT_FAMILY, 9, "bold")).pack(anchor="w")
        self.private_server_entry = ttk.Entry(right_frame, style="Dark.TEntry")
        self.private_server_entry.pack(fill="x", pady=(0, 5))
        self.private_server_entry.insert(0, self.settings.get("last_private_server", ""))
        self.private_server_entry.bind("<KeyRelease>", self.on_private_server_change)

        self.join_place_split_btn = ttk.Button(
            right_frame,
            text="Join Place ID",
            style="Accent.TButton"
        )
        self.join_place_split_btn.pack(fill="x", pady=(0, 10))
        self.join_place_split_btn.bind("<Button-1>", self.on_join_place_split_click)
        self.join_place_split_btn.bind("<Button-3>", self.on_join_place_right_click)
        self.join_place_split_btn.bind("<Enter>", self.on_join_place_hover)
        self.join_place_split_btn.bind("<Leave>", self.on_join_place_leave)
        
        recent_games_header = ttk.Frame(right_frame, style="Dark.TFrame")
        recent_games_header.pack(fill="x", anchor="w", pady=(10, 2))
        
        ttk.Label(recent_games_header, text="Recent games", style="Dark.TLabel", font=(self.FONT_FAMILY, 9, "bold")).pack(side="left")
        


        game_list_frame = ttk.Frame(right_frame, style="Dark.TFrame")
        game_list_frame.pack(fill="both", expand=True)
        
        self.game_list = tk.Listbox(
            game_list_frame,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            selectbackground=self.FG_ACCENT,
            selectforeground=self.ON_ACCENT,
            highlightthickness=1,
            highlightbackground=self.BG_BORDER,
            highlightcolor=self.FG_ACCENT,
            border=0,
            selectborderwidth=0,
            font=(self.FONT_FAMILY, 9),
            height=5,
        )
        self.game_list.pack(side="left", fill="both", expand=True)
        self.game_list.bind("<<ListboxSelect>>", self.on_game_select)
        
        game_scrollbar = ttk.Scrollbar(game_list_frame, command=self.game_list.yview)
        game_scrollbar.pack(side="right", fill="y")
        self.game_list.config(yscrollcommand=game_scrollbar.set)
        
        ttk.Button(right_frame, text="Delete Selected", style="Dark.TButton", command=self.delete_game_from_list).pack(fill="x", pady=(5, 0))

        quick_actions_row = ttk.Frame(right_frame, style="Dark.TFrame")
        quick_actions_row.pack(fill="x", pady=(10, 5))
        ttk.Label(quick_actions_row, text="Quick Actions", style="Dark.TLabel").pack(side="left")
        self.quick_actions_row = quick_actions_row
        self.discord_btn = None

        _discord_img = None
        if self.discord_logo_path and os.path.exists(self.discord_logo_path):
            try:
                _discord_img = tk.PhotoImage(file=self.discord_logo_path)
                _w, _h = _discord_img.width(), _discord_img.height()
                _factor = max(1, max(_w, _h) // 20)
                if _factor > 1:
                    _discord_img = _discord_img.subsample(_factor, _factor)
                self.discord_logo_img = _discord_img
            except Exception:
                _discord_img = None

        if _discord_img:
            self.discord_btn = tk.Button(
                quick_actions_row,
                image=_discord_img,
                bg=self.BG_DARK,
                activebackground=self.BG_DARK,
                relief="flat",
                bd=0,
                cursor="hand2",
                padx=0,
                pady=0,
                highlightthickness=0,
                command=lambda: webbrowser.open("https://discord.gg/xvWK6BkGD6")
            )
            self.discord_btn.pack(side="right")

        action_frame = ttk.Frame(right_frame, style="Dark.TFrame")
        action_frame.pack(fill="x")

        ttk.Button(action_frame, text="Edit Note", style="Dark.TButton", command=self.edit_account_note).pack(fill="x", pady=2)
        ttk.Button(action_frame, text="Refresh List", style="Dark.TButton", command=self.refresh_accounts).pack(fill="x", pady=2)

        bottom_frame = ttk.Frame(self.root, style="Dark.TFrame")
        bottom_frame.pack(fill="x", padx=10, pady=(0, 10))

        self.add_account_split_btn = ttk.Frame(bottom_frame, style="Dark.TFrame")
        self.add_account_split_btn.pack(side="left", fill="x", expand=True, padx=(0, 2))

        self.add_account_main_btn = ttk.Button(
            self.add_account_split_btn,
            text="Add Account",
            style="Accent.TButton",
            command=self.add_account,
        )
        self.add_account_main_btn.pack(side="left", fill="x", expand=True)

        self.add_account_dropdown_btn = ttk.Button(
            self.add_account_split_btn,
            text="▾",
            style="Accent.Dropdown.TButton",
            width=2,
            command=self.toggle_add_account_dropdown,
        )
        self.add_account_dropdown_btn.pack(side="left", padx=(4, 0))

        self.add_account_dropdown = None
        self.add_account_dropdown_visible = False
        
        self.join_place_dropdown = None
        self.join_place_dropdown_visible = False
        
        ttk.Button(bottom_frame, text="Remove", style="Dark.TButton", command=self.remove_account).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(bottom_frame, text="Launch Roblox Home", style="Dark.TButton", command=self.launch_home).pack(side="left", fill="x", expand=True, padx=2)
        ttk.Button(bottom_frame, text="Settings", style="Dark.TButton", command=self.open_settings).pack(side="left", fill="x", expand=True, padx=(2, 0))
        
        self.root.bind("<Button-1>", self.hide_dropdown_on_click_outside)
        self.root.bind("<Configure>", self.on_root_configure)
        self.root.bind("<Delete>", lambda e: self.remove_account())

        self.refresh_accounts()
        self.refresh_game_list()
        self.update_game_name_on_startup()
        
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.root.after(50, self._process_ui_task_queue)
        
        threading.Thread(target=self._silent_check_cookies_worker, daemon=True).start()
        threading.Thread(target=self._watch_discord_logo, daemon=True).start()
        
        if self.settings.get("lock_roblox_settings", False):
            self.root.after(1000, self.apply_and_lock_roblox_settings)

        # Apply native chrome after the window is mapped so the title bar can match the theme.
        self.root.after(50, self.apply_window_chrome)

    def _apply_theme_data(self, theme_data, selected_theme_name=None, persist_selection=False):
        merged_theme = self.theme_manager._merge_with_defaults(theme_data)

        colors = merged_theme.get("colors", {})
        fonts = merged_theme.get("fonts", {})
        defaults = self.theme_manager.DEFAULT_THEME

        self.BG_DARK = self._normalize_hex_color(colors.get("bg_dark"), defaults["colors"]["bg_dark"])
        self.BG_MID = self._normalize_hex_color(colors.get("bg_mid"), defaults["colors"]["bg_mid"])
        self.BG_LIGHT = self._normalize_hex_color(colors.get("bg_light"), defaults["colors"]["bg_light"])
        self.FG_TEXT = self._normalize_hex_color(colors.get("fg_text"), defaults["colors"]["fg_text"])
        self.FG_ACCENT = self._normalize_hex_color(colors.get("fg_accent"), defaults["colors"]["fg_accent"])

        self.FONT_FAMILY = str(fonts.get("family", defaults["fonts"]["family"]))
        try:
            self.FONT_SIZE = max(8, min(24, int(fonts.get("size_base", defaults["fonts"]["size_base"]))))
        except Exception:
            self.FONT_SIZE = defaults["fonts"]["size_base"]

        self.current_theme_data = self._deepcopy_theme_data(merged_theme)
        self.current_theme_data["colors"]["bg_dark"] = self.BG_DARK
        self.current_theme_data["colors"]["bg_mid"] = self.BG_MID
        self.current_theme_data["colors"]["bg_light"] = self.BG_LIGHT
        self.current_theme_data["colors"]["fg_text"] = self.FG_TEXT
        self.current_theme_data["colors"]["fg_accent"] = self.FG_ACCENT
        self.current_theme_data["fonts"]["family"] = self.FONT_FAMILY
        self.current_theme_data["fonts"]["size_base"] = self.FONT_SIZE

        self.root.configure(bg=self.BG_DARK)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Dark.TFrame", background=self.BG_DARK)
        style.configure("Dark.TLabel", background=self.BG_DARK, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.configure("Dark.TButton", background=self.BG_MID, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1)))
        style.map("Dark.TButton", background=[("active", self.BG_LIGHT)], foreground=[("active", self.FG_TEXT)])
        style.configure("Dark.TEntry", fieldbackground=self.BG_MID, background=self.BG_MID, foreground=self.FG_TEXT)
        style.configure("Dark.TCheckbutton", background=self.BG_DARK, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.map("Dark.TCheckbutton", background=[("active", self.BG_DARK)], foreground=[("active", self.FG_TEXT)])
        style.configure("Dark.TRadiobutton", background=self.BG_DARK, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, self.FONT_SIZE))
        style.map("Dark.TRadiobutton", background=[("active", self.BG_DARK)], foreground=[("active", self.FG_TEXT)])
        style.configure("TNotebook", background=self.BG_DARK, borderwidth=0)
        style.configure("TNotebook.Tab", background=self.BG_MID, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1)), focuscolor="none")
        style.map("TNotebook.Tab", background=[("selected", self.BG_LIGHT)], focuscolor=[("!focus", "none")])
        style.configure(
            "ThemeEditor.TCombobox",
            fieldbackground=self.BG_MID,
            background=self.BG_MID,
            foreground=self.FG_TEXT,
            arrowcolor=self.FG_TEXT,
            bordercolor=self.BG_LIGHT,
            lightcolor=self.BG_LIGHT,
            darkcolor=self.BG_LIGHT,
            relief="flat",
        )
        style.map(
            "ThemeEditor.TCombobox",
            fieldbackground=[("readonly", self.BG_MID)],
            foreground=[("readonly", self.FG_TEXT)],
            selectbackground=[("readonly", self.BG_MID)],
            selectforeground=[("readonly", self.FG_TEXT)],
        )

        if hasattr(self, "settings_window") and self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.configure(bg=self.BG_DARK)

        if hasattr(self, "discord_btn") and self.discord_btn:
            self.discord_btn.config(bg=self.BG_DARK, activebackground=self.BG_DARK)

        for widget_name in (
            "topmost_check",
            "multi_roblox_check",
            "confirm_check",
            "multi_select_check",
            "disable_launch_popup_check",
            "auto_tile_check",
            "start_menu_check",
            "rename_check",
            "anti_afk_check",
        ):
            widget = getattr(self, widget_name, None)
            if widget:
                try:
                    widget.configure(style="Dark.TCheckbutton")
                except Exception:
                    pass

        settings_btn = getattr(self, "settings_btn", None)
        if settings_btn:
            try:
                settings_btn.configure(bg=self.BG_DARK, fg=self.FG_TEXT, activebackground=self.BG_MID, activeforeground=self.FG_TEXT)
            except Exception:
                pass

        for widget_name in (
            "key_button",
            "max_games_spinner",
            "interval_spinner",
            "amount_spinner",
        ):
            widget = getattr(self, widget_name, None)
            if widget:
                try:
                    widget.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, buttonbackground=self.BG_LIGHT, readonlybackground=self.BG_MID, selectbackground=self.FG_ACCENT, selectforeground=self.FG_TEXT, insertbackground=self.FG_TEXT, highlightbackground=self.BG_LIGHT)
                except Exception:
                    pass

        for widget_name in (
            "theme_editor_shell",
            "theme_editor_area",
            "theme_editor_canvas",
            "theme_editor_content",
            "theme_color_section",
            "theme_color_rows",
            "theme_font_section",
        ):
            widget = getattr(self, widget_name, None)
            if widget:
                try:
                    widget.configure(bg=self.BG_MID)
                except Exception:
                    pass

        editor_widgets = getattr(self, "theme_editor_widgets", [])
        color_swatch_widgets = getattr(self, "theme_color_swatch_widgets", {})
        for widget in editor_widgets:
            try:
                if widget in color_swatch_widgets.values():
                    continue
                if isinstance(widget, tk.Entry):
                    widget.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, insertbackground=self.FG_TEXT, highlightbackground=self.BG_LIGHT, highlightcolor=self.FG_ACCENT)
                elif isinstance(widget, tk.Button):
                    widget.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, activebackground=self.BG_SURFACE, activeforeground=self.FG_TEXT)
                elif isinstance(widget, tk.Checkbutton):
                    widget.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, selectcolor=self.BG_LIGHT, activebackground=self.BG_MID, activeforeground=self.FG_TEXT)
                elif isinstance(widget, tk.Label):
                    widget.configure(bg=self.BG_PANEL, fg=self.FG_TEXT)
                elif isinstance(widget, tk.Frame):
                    widget.configure(bg=self.BG_MID)
            except Exception:
                pass

        color_vars = getattr(self, "theme_color_vars", {})
        for key, swatch in color_swatch_widgets.items():
            try:
                value = color_vars.get(key).get().strip() if key in color_vars else ""
                if re.fullmatch(r"#[0-9a-fA-F]{6}", value):
                    swatch.configure(bg=value)
            except Exception:
                pass

        for widget_name in ("theme_family_combo",):
            widget = getattr(self, widget_name, None)
            if widget:
                try:
                    widget.configure(style="ThemeEditor.TCombobox")
                except Exception:
                    pass

        if hasattr(self, "account_list") and self.account_list:
            self.account_list.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, selectbackground=self.FG_ACCENT, selectforeground=self.FG_TEXT)
        if hasattr(self, "game_list") and self.game_list:
            self.game_list.configure(bg=self.BG_PANEL, fg=self.FG_TEXT, selectbackground=self.FG_ACCENT, selectforeground=self.FG_TEXT)
        if hasattr(self, "encryption_label") and self.encryption_label:
            self.encryption_label.configure(bg=self.BG_DARK)

        if hasattr(self, "account_list"):
            try:
                self.refresh_accounts()
            except Exception:
                pass
        if hasattr(self, "game_list"):
            try:
                self.refresh_game_list()
            except Exception:
                pass

        if persist_selection and selected_theme_name:
            self.settings["selected_theme"] = selected_theme_name
            self.save_settings()

    def _load_current_theme_config(self):
        path = os.path.join(self.data_folder, "themes", "current_theme.json")
        if not os.path.exists(path):
            return None

        try:
            with open(path, "r", encoding="utf-8") as handle:
                return json.load(handle)
        except Exception as exc:
            print(f"[ERROR] Failed to load current theme config: {exc}")
            return None

    def _save_current_theme_config(self, theme_data, source_theme_name="Dark"):
        path = os.path.join(self.data_folder, "themes", "current_theme.json")
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            current_theme_data = self._deepcopy_theme_data(theme_data)
            current_theme_data.pop("metadata", None)
            current_theme_data["source_theme"] = source_theme_name or "Dark"

            with open(path, "w", encoding="utf-8") as handle:
                json.dump(current_theme_data, handle, indent=2)
            return True
        except Exception as exc:
            print(f"[ERROR] Failed to save current theme config: {exc}")
            return False

    def open_theme_manager(self, parent=None, on_themes_changed=None):
        if hasattr(self, "theme_manager_window") and self.theme_manager_window and self.theme_manager_window.winfo_exists():
            self.theme_manager_window.lift()
            self.theme_manager_window.focus()
            return

        owner = parent if parent and parent.winfo_exists() else self.root
        manager_window = tk.Toplevel(owner)
        self.theme_manager_window = manager_window
        self.apply_window_icon(manager_window)
        manager_window.title("Theme Manager")
        manager_window.configure(bg=self.BG_DARK)
        manager_window.geometry("680x420")
        manager_window.resizable(False, False)
        manager_window.transient(owner)

        if False:
            manager_window.attributes("-topmost", True)

        if owner is not self.root:
            manager_window.grab_set()

        container = ttk.Frame(manager_window, style="Dark.TFrame")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(
            container,
            text="Themes",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 11, "bold")
        ).pack(anchor="w", pady=(0, 6))

        list_shell = tk.Frame(container, bg=self.BG_PANEL, relief="solid", borderwidth=1)
        list_shell.pack(fill="both", expand=True)

        header = tk.Frame(list_shell, bg=self.BG_LIGHT)
        header.pack(fill="x")
        tk.Label(header, text="Name", bg=self.BG_LIGHT, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 9, "bold"), anchor="w", width=18).pack(side="left", padx=(8, 4), pady=6)
        tk.Label(header, text="Author", bg=self.BG_LIGHT, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 9, "bold"), anchor="w", width=16).pack(side="left", padx=4, pady=6)
        tk.Label(header, text="Description", bg=self.BG_LIGHT, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 9, "bold"), anchor="w").pack(side="left", fill="x", expand=True, padx=4, pady=6)

        list_body = tk.Frame(list_shell, bg=self.BG_MID)
        list_body.pack(fill="both", expand=True)

        theme_list_scroll = tk.Scrollbar(list_body, orient="vertical")
        theme_list_scroll.pack(side="right", fill="y")

        theme_list_canvas = tk.Canvas(list_body, bg=self.BG_PANEL, highlightthickness=0, yscrollcommand=theme_list_scroll.set)
        theme_list_canvas.pack(side="left", fill="both", expand=True)
        theme_list_scroll.config(command=theme_list_canvas.yview)

        theme_list_container = tk.Frame(theme_list_canvas, bg=self.BG_MID)
        theme_list_window = theme_list_canvas.create_window((0, 0), window=theme_list_container, anchor="nw")

        def _sync_theme_list_scrollregion(_event=None):
            theme_list_canvas.configure(scrollregion=theme_list_canvas.bbox("all"))

        def _sync_theme_list_width(event):
            theme_list_canvas.itemconfigure(theme_list_window, width=event.width)

        theme_list_container.bind("<Configure>", _sync_theme_list_scrollregion)
        theme_list_canvas.bind("<Configure>", _sync_theme_list_width)

        selected_theme_name = [None]
        row_widgets = {}

        def _set_row_selected(name):
            selected_theme_name[0] = name
            for row_name, widgets in row_widgets.items():
                is_selected = row_name == name
                row_bg = self.BG_LIGHT if is_selected else self.BG_MID
                for widget in widgets:
                    try:
                        widget.configure(bg=row_bg)
                    except Exception:
                        pass

        def refresh_theme_list(select_name=None):
            for child in theme_list_container.winfo_children():
                child.destroy()
            row_widgets.clear()

            catalog = self.theme_manager.get_available_themes()
            names = sorted(catalog.keys(), key=str.lower)

            for name in names:
                data = self.theme_manager.load_theme(name)
                metadata = data.get("metadata", {})
                author = str(metadata.get("author", ""))
                description = str(metadata.get("description", ""))

                row = tk.Frame(theme_list_container, bg=self.BG_MID)
                row.pack(fill="x", padx=4, pady=1)
                name_label = tk.Label(row, text=name, bg=self.BG_PANEL, fg=self.FG_TEXT, anchor="w", width=18, font=(self.FONT_FAMILY, 9))
                author_label = tk.Label(row, text=author, bg=self.BG_PANEL, fg=self.FG_TEXT, anchor="w", width=16, font=(self.FONT_FAMILY, 9))
                desc_label = tk.Label(row, text=description, bg=self.BG_PANEL, fg=self.FG_TEXT, anchor="w", font=(self.FONT_FAMILY, 9))
                name_label.pack(side="left", padx=(8, 4), pady=5)
                author_label.pack(side="left", padx=4, pady=5)
                desc_label.pack(side="left", fill="x", expand=True, padx=4, pady=5)

                row_widgets[name] = [row, name_label, author_label, desc_label]
                for widget in row_widgets[name]:
                    widget.bind("<Button-1>", lambda _event, n=name: _set_row_selected(n))

            preferred = select_name
            if not preferred and selected_theme_name[0] in names:
                preferred = selected_theme_name[0]
            if not preferred and names:
                preferred = names[0]
            if preferred:
                for name in names:
                    if name.lower() == str(preferred).lower():
                        preferred = name
                        break
                _set_row_selected(preferred)

        def get_selected_theme_name():
            return selected_theme_name[0]

        def import_theme():
            path = filedialog.askopenfilename(
                title="Import Theme JSON",
                filetypes=[("JSON Files", "*.json"), ("All Files", "*.*")],
                parent=manager_window,
            )
            if not path:
                return

            if not self.theme_manager.import_theme(path):
                messagebox.showerror("Import Failed", "Could not import this theme file.", parent=manager_window)
                return

            imported_name = None
            try:
                with open(path, "r", encoding="utf-8") as f:
                    imported_name = json.load(f).get("metadata", {}).get("name")
            except Exception:
                imported_name = None

            refresh_theme_list(select_name=imported_name)
            if callable(on_themes_changed):
                on_themes_changed(imported_name)

        def export_theme():
            selected_name = get_selected_theme_name()
            if not selected_name:
                messagebox.showwarning("Export Theme", "Select a theme to export.", parent=manager_window)
                return

            path = filedialog.asksaveasfilename(
                title="Export Theme",
                defaultextension=".json",
                initialfile=f"{selected_name}.json",
                filetypes=[("JSON Files", "*.json")],
                parent=manager_window,
            )
            if not path:
                return

            if not self.theme_manager.export_theme(selected_name, path):
                messagebox.showerror("Export Failed", "Could not export theme.", parent=manager_window)
                return

        def remove_theme():
            selected_name = get_selected_theme_name()
            if not selected_name:
                messagebox.showwarning("Remove Theme", "Select a theme to remove.", parent=manager_window)
                return

            themes = self.theme_manager.get_available_themes()
            if selected_name not in themes:
                messagebox.showwarning("Remove Theme", "Theme not found.", parent=manager_window)
                return

            if not messagebox.askyesno("Remove Theme", f"Remove '{selected_name}'?", parent=manager_window):
                return

            if not self.theme_manager.delete_theme(selected_name):
                messagebox.showerror("Remove Failed", "Could not remove theme.", parent=manager_window)
                return

            refresh_theme_list()
            if callable(on_themes_changed):
                on_themes_changed(None)

        button_row = ttk.Frame(container, style="Dark.TFrame")
        button_row.pack(fill="x", pady=(8, 0))

        ttk.Button(button_row, text="Import", style="Dark.TButton", command=import_theme).pack(side="left", fill="x", expand=True, padx=(0, 4))
        ttk.Button(button_row, text="Export", style="Dark.TButton", command=export_theme).pack(side="left", fill="x", expand=True, padx=4)
        ttk.Button(button_row, text="Remove", style="Dark.TButton", command=remove_theme).pack(side="left", fill="x", expand=True, padx=4)
        ttk.Button(button_row, text="Close", style="Dark.TButton", command=manager_window.destroy).pack(side="left", fill="x", expand=True, padx=(4, 0))

        def on_close_manager():
            self.theme_manager_window = None
            manager_window.destroy()

        manager_window.protocol("WM_DELETE_WINDOW", on_close_manager)
        refresh_theme_list()

    def _normalize_hex_color(self, value, fallback):
        text = str(value or "").strip()
        if re.fullmatch(r"#[0-9a-fA-F]{6}", text):
            return text

        try:
            rgb = self.root.winfo_rgb(text)
            return "#{:02x}{:02x}{:02x}".format(rgb[0] // 256, rgb[1] // 256, rgb[2] // 256)
        except Exception:
            return fallback

    def _deepcopy_theme_data(self, theme_data):
        return json.loads(json.dumps(theme_data))

    def _apply_modern_window_defaults(self):
        """Apply native window tweaks and shared widget defaults."""
        try:
            if sys.platform == "win32":
                self._apply_windows_corner_preferences()
        except Exception:
            pass

    def _apply_windows_corner_preferences(self):
        """Request rounded corners and dark title bar on supported Windows builds."""
        try:
            hwnd = self.root.winfo_id()
            DWMWA_WINDOW_CORNER_PREFERENCE = 33
            DWMWCP_ROUND = 2
            DWMWA_USE_IMMERSIVE_DARK_MODE = 20
            value = ctypes.c_int(DWMWCP_ROUND)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd,
                DWMWA_WINDOW_CORNER_PREFERENCE,
                ctypes.byref(value),
                ctypes.sizeof(value),
            )
            dark_value = ctypes.c_int(1)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd,
                DWMWA_USE_IMMERSIVE_DARK_MODE,
                ctypes.byref(dark_value),
                ctypes.sizeof(dark_value),
            )
        except Exception:
            pass

    def apply_window_icon(self, window):
        icon_path = self.icon_path

        if icon_path and os.path.exists(icon_path):
            try:
                window.iconbitmap(icon_path)
            except Exception as e:
                print(f"[ERROR] Could not set window icon: {e}")

    def apply_window_chrome(self):
        """Apply Windows theme-aware title bar and rounded-corner preference when available."""
        try:
            if platform.system().lower() != "windows":
                return

            hwnd = self.root.winfo_id()
            if not hwnd:
                return

            DWMWA_USE_IMMERSIVE_DARK_MODE = 20
            DWMWA_USE_IMMERSIVE_DARK_MODE_BEFORE_20H1 = 19
            DWMWA_WINDOW_CORNER_PREFERENCE = 33
            DWMWCP_ROUND = 2
            DWMWCP_ROUND_SMALL = 3

            try:
                dark_mode = ctypes.c_int(1)
                for attr in (DWMWA_USE_IMMERSIVE_DARK_MODE, DWMWA_USE_IMMERSIVE_DARK_MODE_BEFORE_20H1):
                    try:
                        ctypes.windll.dwmapi.DwmSetWindowAttribute(
                            wintypes.HWND(hwnd),
                            wintypes.DWORD(attr),
                            ctypes.byref(dark_mode),
                            ctypes.sizeof(dark_mode),
                        )
                        break
                    except Exception:
                        pass
            except Exception:
                pass

            try:
                corner_pref = ctypes.c_int(DWMWCP_ROUND)
                ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    wintypes.HWND(hwnd),
                    wintypes.DWORD(DWMWA_WINDOW_CORNER_PREFERENCE),
                    ctypes.byref(corner_pref),
                    ctypes.sizeof(corner_pref),
                )
            except Exception:
                pass

            for attr, color_value in ((35, self.BG_APP), (36, self.FG_TEXT), (34, self.BG_BORDER)):
                try:
                    # Windows 11+ supports caption, text, and border colors via DWM.
                    color = int(color_value.lstrip('#'), 16)
                    color_ref = ctypes.c_int(color)
                    ctypes.windll.dwmapi.DwmSetWindowAttribute(
                        wintypes.HWND(hwnd),
                        wintypes.DWORD(attr),
                        ctypes.byref(color_ref),
                        ctypes.sizeof(color_ref),
                    )
                except Exception:
                    pass
        except Exception:
            pass



    """settings"""
    def open_roblox_settings_window(self):
        """Open Roblox Settings window to view/edit GlobalBasicSettings_13.xml"""
        settings_window = tk.Toplevel(self.root)
        self.apply_window_icon(settings_window)
        settings_window.title("Roblox Settings")
        settings_window.geometry("500x400")
        settings_window.configure(bg=self.BG_DARK)
        settings_window.resizable(False, False)
        settings_window.minsize(600, 400)
        
        if False:
            settings_window.attributes("-topmost", True)
        
        settings_window.transient(self.root)
        
        roblox_settings_path = os.path.join(
            os.environ.get("LOCALAPPDATA", ""),
            "Roblox",
            "GlobalBasicSettings_13.xml"
        )
        
        local_settings_path = os.path.join(self.data_folder, "roblox_settings.xml")
        
        settings_data = {}
        xml_tree = None
        
        def ensure_local_settings_file():
            """Create local settings file if it doesn't exist by copying from Roblox"""
            if not os.path.exists(local_settings_path):
                if os.path.exists(roblox_settings_path):
                    try:
                        shutil.copy2(roblox_settings_path, local_settings_path)
                        print(f"[INFO] Created local Roblox settings file: {local_settings_path}")
                    except Exception as e:
                        print(f"[ERROR] Failed to create local settings file: {e}")
        
        def parse_settings():
            """Parse the local XML settings file"""
            nonlocal settings_data, xml_tree
            settings_data.clear()
            
            ensure_local_settings_file()
            
            if not os.path.exists(local_settings_path):
                return False
            
            try:
                xml_tree = ET.parse(local_settings_path)
                root = xml_tree.getroot()
                
                properties = root.find(".//Properties")
                if properties is None:
                    return False
                
                for child in properties:
                    tag = child.tag
                    name = child.get("name", "")
                    
                    if name:
                        if tag == "Vector2":
                            x_elem = child.find("X")
                            y_elem = child.find("Y")
                            value = f"{x_elem.text if x_elem is not None else '0'}, {y_elem.text if y_elem is not None else '0'}"
                        else:
                            value = child.text if child.text else ""
                        
                        settings_data[name] = {
                            "type": tag,
                            "value": value,
                            "element": child
                        }
                
                return True
            except Exception as e:
                print(f"[ERROR] Failed to parse settings: {e}")
                return False
        
        def refresh_list(filter_text=""):
            """Refresh the settings list, optionally filtering by search text"""
            settings_list.delete(0, tk.END)
            
            for name, data in sorted(settings_data.items()):
                if filter_text.lower() in name.lower() or filter_text.lower() in str(data["value"]).lower():
                    display = f"{name}: {data['value']}"
                    if len(display) > 60:
                        display = display[:57] + "..."
                    settings_list.insert(tk.END, display)
        
        def on_search(*args):
            """Filter list based on search input"""
            refresh_list(search_var.get())
        
        def on_select(event):
            """Handle list selection"""
            selection = settings_list.curselection()
            if not selection:
                return
            
            selected_text = settings_list.get(selection[0])
            selected_name = selected_text.split(":")[0]
            
            if selected_name in settings_data:
                data = settings_data[selected_name]
                selected_name_label.config(text=f"Selected: {selected_name}")
                type_label.config(text=f"Type: {data['type']}")
                value_entry.delete(0, tk.END)
                value_entry.insert(0, data["value"])
        
        def set_value():
            """Set value locally (in memory)"""
            selection = settings_list.curselection()
            if not selection:
                messagebox.showwarning("No Selection", "Please select a setting first.")
                return
            
            selected_text = settings_list.get(selection[0])
            selected_name = selected_text.split(":")[0]
            new_value = value_entry.get()
            
            if selected_name in settings_data:
                data = settings_data[selected_name]
                element = data["element"]
                
                if data["type"] == "Vector2":
                    parts = new_value.split(",")
                    if len(parts) == 2:
                        x_elem = element.find("X")
                        y_elem = element.find("Y")
                        if x_elem is not None:
                            x_elem.text = parts[0].strip()
                        if y_elem is not None:
                            y_elem.text = parts[1].strip()
                else:
                    element.text = new_value
                
                settings_data[selected_name]["value"] = new_value
                save_settings_to_local()
                refresh_list(search_var.get())
                messagebox.showinfo("Set", f"Value for '{selected_name}' set and saved to local file.")
        
        def refresh_settings():
            """Reload settings from local XML file"""
            if parse_settings():
                refresh_list(search_var.get())
                messagebox.showinfo("Refreshed", "Settings reloaded from local file.")
            else:
                messagebox.showerror("Error", f"Could not load settings from:\n{local_settings_path}")
        
        def save_settings_to_local():
            """Save settings to local XML file"""
            nonlocal xml_tree
            if xml_tree is None:
                messagebox.showerror("Error", "No settings loaded to save.")
                return False
            
            try:
                xml_tree.write(local_settings_path, encoding="utf-8", xml_declaration=True)
                print(f"[INFO] Settings saved to local file: {local_settings_path}")
                return True
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save settings: {e}")
                return False
        
        def apply_settings_to_roblox():
            """Apply local settings to Roblox's GlobalBasicSettings_13.xml"""
            if not os.path.exists(local_settings_path):
                messagebox.showerror("Error", "No local settings file found.")
                return False
            
            try:
                try:
                    os.chmod(roblox_settings_path, stat.S_IWRITE | stat.S_IREAD)
                except:
                    pass
                
                shutil.copy2(local_settings_path, roblox_settings_path)
                print(f"[INFO] Applied settings to Roblox: {roblox_settings_path}")
                return True
            except Exception as e:
                messagebox.showerror("Error", f"Failed to apply settings: {e}")
                return False
        
        def lock_roblox_settings():
            """Lock Roblox settings file to read-only"""
            if not os.path.exists(roblox_settings_path):
                print(f"[WARNING] Roblox settings file not found: {roblox_settings_path}")
                return False
            
            try:
                os.chmod(roblox_settings_path, stat.S_IREAD | stat.S_IRGRP | stat.S_IROTH)
                print(f"[INFO] Locked Roblox settings to read-only")
                return True
            except Exception as e:
                print(f"[ERROR] Failed to lock settings: {e}")
                return False
        
        def unlock_roblox_settings():
            """Unlock Roblox settings file"""
            if not os.path.exists(roblox_settings_path):
                print(f"[WARNING] Roblox settings file not found: {roblox_settings_path}")
                return False
            
            try:
                os.chmod(roblox_settings_path, stat.S_IWRITE | stat.S_IREAD)
                print(f"[INFO] Unlocked Roblox settings (writable)")
                return True
            except Exception as e:
                print(f"[ERROR] Failed to unlock settings: {e}")
                return False
        
        def toggle_lock_settings():
            """Handle Lock Settings checkbox toggle"""
            enabled = lock_settings_var.get()
            self.settings["lock_roblox_settings"] = enabled
            self.save_settings()
            
            if enabled:
                if save_settings_to_local():
                    if apply_settings_to_roblox():
                        if lock_roblox_settings():
                            messagebox.showinfo("Locked", "Settings applied and locked to read-only!")
                        else:
                            messagebox.showwarning("Warning", "Settings applied but failed to lock.")
            else:
                if unlock_roblox_settings():
                    messagebox.showinfo("Unlocked", "Roblox settings file is now writable!")
        
        main_frame = ttk.Frame(settings_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=15, pady=15)
        
        lock_settings_var = tk.BooleanVar(value=self.settings.get("lock_roblox_settings", False))
        
        search_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        search_frame.pack(fill="x", pady=(0, 10))
        
        ttk.Label(search_frame, text="Search:", style="Dark.TLabel").pack(side="left", padx=(0, 5))
        
        search_var = tk.StringVar()
        search_var.trace("w", on_search)
        search_entry = ttk.Entry(search_frame, textvariable=search_var, style="Dark.TEntry")
        search_entry.pack(side="left", fill="x", expand=True)
        
        content_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        content_frame.pack(fill="both", expand=True)
        
        list_frame = ttk.Frame(content_frame, style="Dark.TFrame")
        list_frame.pack(side="left", fill="both", expand=True, padx=(0, 10))
        
        ttk.Label(list_frame, text="Roblox Settings", style="Dark.TLabel", 
                  font=(self.FONT_FAMILY, 10, "bold")).pack(anchor="w", pady=(0, 5))
        
        list_container = ttk.Frame(list_frame, style="Dark.TFrame")
        list_container.pack(fill="both", expand=True)
        
        settings_list = tk.Listbox(
            list_container,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            selectbackground=self.FG_ACCENT,
            selectforeground="white",
            font=(self.FONT_FAMILY, 9),
            relief="flat",
            borderwidth=0,
            highlightthickness=1,
            highlightcolor=self.BG_LIGHT,
            highlightbackground=self.BG_LIGHT,
            exportselection=False
        )
        settings_list.pack(side="left", fill="both", expand=True)
        settings_list.bind("<<ListboxSelect>>", on_select)
        
        list_scrollbar = ttk.Scrollbar(list_container, command=settings_list.yview)
        list_scrollbar.pack(side="right", fill="y")
        settings_list.config(yscrollcommand=list_scrollbar.set)
        
        edit_frame = ttk.Frame(content_frame, style="Dark.TFrame", width=200)
        edit_frame.pack(side="right", fill="y", padx=(10, 0))
        edit_frame.pack_propagate(False)
        
        ttk.Label(edit_frame, text="Edit Setting", style="Dark.TLabel",
                  font=(self.FONT_FAMILY, 10, "bold")).pack(anchor="w", pady=(0, 10))
        
        selected_name_label = ttk.Label(edit_frame, text="Selected: (none)", style="Dark.TLabel",
                                         font=(self.FONT_FAMILY, 9))
        selected_name_label.pack(anchor="w", pady=(0, 5))
        
        type_label = ttk.Label(edit_frame, text="Type: -", style="Dark.TLabel",
                               font=(self.FONT_FAMILY, 9))
        type_label.pack(anchor="w", pady=(0, 10))
        
        ttk.Label(edit_frame, text="Set Value:", style="Dark.TLabel").pack(anchor="w", pady=(0, 5))
        
        value_entry = ttk.Entry(edit_frame, style="Dark.TEntry")
        value_entry.pack(fill="x", pady=(0, 10))
        
        ttk.Button(edit_frame, text="Set", style="Dark.TButton", command=set_value).pack(fill="x", pady=(0, 5))
        ttk.Button(edit_frame, text="Refresh", style="Dark.TButton", command=refresh_settings).pack(fill="x", pady=(0, 5))
        ttk.Button(edit_frame, text="Apply to Roblox", style="Dark.TButton", command=lambda: apply_settings_to_roblox() and messagebox.showinfo("Applied", "Settings applied to Roblox!")).pack(fill="x", pady=(0, 5))
        
        ttk.Checkbutton(
            edit_frame,
            text="Lock settings (auto-apply)",
            variable=lock_settings_var,
            command=toggle_lock_settings,
            style="Dark.TCheckbutton"
        ).pack(anchor="w", pady=(10, 0))

        if parse_settings():
            refresh_list()
        else:
            settings_list.insert(tk.END, "Could not load settings file.")
            settings_list.insert(tk.END, "Make sure Roblox has been run at least once.")

    def load_settings(self):
        """Load UI settings from file"""
        try:
            if os.path.exists(self.settings_file):
                with open(self.settings_file, 'r') as f:
                    self.settings = json.load(f)
            else:
                self.settings = {
                    "last_place_id": "",
                    "last_private_server": "",
                    "game_list": [],
                    "favorite_games": [],
                    "enable_multi_roblox": False,
                    "confirm_before_launch": False,
                    "custom_roblox_launcher_path": "",
                    "max_recent_games": 10,
                    "anti_afk_enabled": False,
                    "anti_afk_interval_minutes": 10,
                    "anti_afk_key": "w",
                    "disable_launch_popup": False,
                    "auto_rejoin_configs": {},
                    "multi_roblox_method": "default",
                    "last_joined_user": "",
                    "selected_theme": "Dark",
                    "rejoin_webhook": {}
                }
        except:
            self.settings = {
                "last_place_id": "",
                "last_private_server": "",
                "game_list": [],
                "favorite_games": [],
                "enable_multi_roblox": False,
                "confirm_before_launch": False,
                "custom_roblox_launcher_path": "",
                "max_recent_games": 10,
                "anti_afk_enabled": False,
                "anti_afk_interval_minutes": 10,
                "anti_afk_key": "w",
                "auto_rejoin_configs": {},
                "disable_launch_popup": False,
                "multi_roblox_method": "default",
                "last_joined_user": "",
                "selected_theme": "Dark",
                "rejoin_webhook": {}
            }

        for obsolete_key in ("enable_topmost", "enable_multi_select", "auto_tile_windows"):
            if obsolete_key in self.settings:
                self.settings.pop(obsolete_key, None)

        if self.settings.get("enable_multi_roblox", False):
            self.root.after(100, self.initialize_multi_roblox)

    def save_settings(self, force_immediate=False):
        """Save UI settings to file with debouncing"""
        if self._save_settings_timer is not None:
            try:
                self.root.after_cancel(self._save_settings_timer)
            except:
                pass
            self._save_settings_timer = None
        
        def do_save():
            try:
                with open(self.settings_file, 'w') as f:
                    json.dump(self.settings, f, indent=2)
            except Exception as e:
                print(f"[ERROR] Failed to save settings: {e}")
            self._save_settings_timer = None
        
        if force_immediate:
            do_save()
        else:
            self._save_settings_timer = self.root.after(500, do_save)

    def open_settings(self):
        """Open the Settings window"""
        if hasattr(self, 'settings_window') and self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.lift()
            self.settings_window.focus()
            return
        
        settings_window = tk.Toplevel(self.root)
        self.apply_window_icon(settings_window)
        self.settings_window = settings_window
        settings_window.title("Settings")
        settings_window.configure(bg=self.BG_DARK)
        settings_window.resizable(False, False)
        
        settings_window.transient(self.root)
        
        def on_close():
            self.settings_window = None
            settings_window.destroy()
        
        def on_settings_close():
            """Save window position before closing"""
            save_current_theme = getattr(self, "_theme_editor_save_current_config", None)
            if callable(save_current_theme):
                try:
                    save_current_theme()
                except Exception as exc:
                    print(f"[ERROR] Failed to save current theme config on close: {exc}")

            self.settings['settings_window_position'] = {
                'x': settings_window.winfo_x(),
                'y': settings_window.winfo_y()
            }
            self.save_settings()
            self.settings_window = None
            settings_window.destroy()
        
        settings_window.protocol("WM_DELETE_WINDOW", on_settings_close)
        
        if False:
            settings_window.attributes("-topmost", True)
        
        self.root.update_idletasks()
        
        settings_width = 315
        settings_height = 385
        
        saved_pos = self.settings.get('settings_window_position')
        if saved_pos and saved_pos.get('x') is not None and saved_pos.get('y') is not None:
            x = saved_pos['x']
            y = saved_pos['y']
        else:
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            main_height = self.root.winfo_height()
            x = main_x + (main_width - settings_width) // 2
            y = main_y + (main_height - settings_height) // 2
        
        settings_window.geometry(f"{settings_width}x{settings_height}+{x}+{y}")
        
        tabs = ttk.Notebook(settings_window)
        tabs.pack(fill=tk.BOTH, expand=True)
        
        general_tab = ttk.Frame(tabs, style="Dark.TFrame")
        tabs.add(general_tab, text="General")
        
        themes_tab = ttk.Frame(tabs, style="Dark.TFrame")
        tabs.add(themes_tab, text="Themes")
        
        roblox_tab = ttk.Frame(tabs, style="Dark.TFrame")
        tabs.add(roblox_tab, text="Roblox")
        
        tool_tab = ttk.Frame(tabs, style="Dark.TFrame")
        tabs.add(tool_tab, text="Tool")
        

        about_tab = ttk.Frame(tabs, style="Dark.TFrame")
        tabs.add(about_tab, text="About")
        
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background=self.BG_DARK, borderwidth=0)
        style.configure('TNotebook.Tab', background=self.BG_MID, foreground=self.FG_TEXT, font=(self.FONT_FAMILY, max(8, self.FONT_SIZE - 1)), focuscolor='none')
        style.map('TNotebook.Tab', background=[('selected', self.BG_LIGHT)], focuscolor=[('!focus', 'none')])
        
        main_frame = ttk.Frame(general_tab, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=20, pady=15)
        confirm_launch_var = tk.BooleanVar(value=self.settings.get("confirm_before_launch", False))
        
        checkbox_style = ttk.Style()
        checkbox_style.configure(
            "Dark.TCheckbutton",
            background=self.BG_DARK,
            foreground=self.FG_TEXT,
            font=(self.FONT_FAMILY, self.FONT_SIZE)
        )

        def auto_save_setting(setting_name, variable):
            def _save():
                self.settings[setting_name] = variable.get()
                self.save_settings()
            return _save

        confirm_check = ttk.Checkbutton(
            main_frame,
            text="Confirm Before Launch",
            variable=confirm_launch_var,
            style="Dark.TCheckbutton",
            command=auto_save_setting("confirm_before_launch", confirm_launch_var)
        )
        confirm_check.pack(anchor="w", pady=2)
        self.confirm_check = confirm_check

        disable_launch_popup_var = tk.BooleanVar(value=self.settings.get("disable_launch_popup", False))
        disable_launch_popup_check = ttk.Checkbutton(
            main_frame,
            text="Disable Launch Success Popup",
            variable=disable_launch_popup_var,
            style="Dark.TCheckbutton",
            command=auto_save_setting("disable_launch_popup", disable_launch_popup_var)
        )
        disable_launch_popup_check.pack(anchor="w", pady=2)
        self.disable_launch_popup_check = disable_launch_popup_check

        def is_start_menu_shortcut_present():
            """Check if Start Menu shortcut exists"""
            start_menu = os.path.join(os.environ.get("APPDATA", ""), "Microsoft", "Windows", "Start Menu", "Programs")
            shortcut_path = os.path.join(start_menu, "Roblox Account Manager.lnk")
            return os.path.exists(shortcut_path)

        def toggle_start_menu_shortcut():
            """Create or remove Start Menu shortcut"""
            start_menu = os.path.join(os.environ.get("APPDATA", ""), "Microsoft", "Windows", "Start Menu", "Programs")
            shortcut_path = os.path.join(start_menu, "Roblox Account Manager.lnk")

            if start_menu_var.get():
                try:
                    exe_path = os.path.abspath(sys.executable if getattr(sys, 'frozen', False) else sys.argv[0])
                    if not getattr(sys, 'frozen', False):
                        exe_path = os.path.abspath(sys.argv[0])

                    ps_script = f'''
                    $WshShell = New-Object -comObject WScript.Shell
                    $Shortcut = $WshShell.CreateShortcut("{shortcut_path}")
                    $Shortcut.TargetPath = "{exe_path}"
                    $Shortcut.WorkingDirectory = "{os.path.dirname(exe_path)}"
                    $Shortcut.Description = "Rocore V1"
                    $Shortcut.Save()
                    '''
                    subprocess.run(["powershell", "-Command", ps_script], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
                    print("[INFO] Start Menu shortcut created")
                except Exception as e:
                    print(f"[ERROR] Failed to create Start Menu shortcut: {e}")
                    start_menu_var.set(False)
            else:
                try:
                    if os.path.exists(shortcut_path):
                        os.remove(shortcut_path)
                        print("[INFO] Start Menu shortcut removed")
                except Exception as e:
                    print(f"[ERROR] Failed to remove Start Menu shortcut: {e}")

        start_menu_var = tk.BooleanVar(value=is_start_menu_shortcut_present())
        start_menu_check = ttk.Checkbutton(
            main_frame,
            text="Add to Start Menu",
            variable=start_menu_var,
            style="Dark.TCheckbutton",
            command=toggle_start_menu_shortcut
        )
        start_menu_check.pack(anchor="w", pady=2)
        self.start_menu_check = start_menu_check

        max_games_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        max_games_frame.pack(fill="x", pady=2)

        ttk.Label(
            max_games_frame,
            text="Max Recent Games:",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 10)
        ).pack(side="left")

        max_games_var = tk.IntVar(value=self.settings.get("max_recent_games", 10))

        def on_max_games_change():
            try:
                new_value = max_games_var.get()
                self.settings["max_recent_games"] = new_value
                self.save_settings()
                if len(self.settings["game_list"]) > new_value:
                    self.settings["game_list"] = self.settings["game_list"][:new_value]
                    self.save_settings()
                    self.refresh_game_list()
            except:
                pass

        max_games_spinner = tk.Spinbox(
            max_games_frame,
            from_=5,
            to=50,
            textvariable=max_games_var,
            width=8,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            buttonbackground=self.BG_LIGHT,
            font=(self.FONT_FAMILY, 9),
            command=on_max_games_change,
            readonlybackground=self.BG_MID,
            selectbackground=self.FG_ACCENT,
            selectforeground=self.FG_TEXT,
            insertbackground=self.FG_TEXT,
            relief="flat",
            borderwidth=1,
            highlightthickness=0
        )
        max_games_spinner.pack(side="right")
        self.max_games_spinner = max_games_spinner

        max_games_spinner.bind("<KeyRelease>", lambda e: on_max_games_change())
        max_games_spinner.bind("<FocusOut>", lambda e: on_max_games_change())

        ttk.Label(main_frame, text="", style="Dark.TLabel").pack(pady=3)
        
        console_button = ttk.Button(
            main_frame,
            text="Console Output",
            style="Dark.TButton",
            command=self.open_console_window
        )
        console_button.pack(fill="x", pady=(0, 5))
        
        close_button = ttk.Button(
            main_frame,
            text="Close",
            style="Dark.TButton",
            command=settings_window.destroy
        )
        close_button.pack(fill="x", pady=(5, 5))
        
        is_unstable = bool(re.search(r'(alpha|beta)', self.APP_VERSION, re.IGNORECASE))
        version_text = f"Version: {self.APP_VERSION}"
        if is_unstable:
            version_text += "\nThis is an unstable version"
        
        version_label = ttk.Label(
            main_frame,
            text=version_text,
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 9)
        )
        version_label.pack(anchor="e", pady=(6, 0))
        
        roblox_frame = ttk.Frame(roblox_tab, style="Dark.TFrame")
        roblox_frame.pack(fill="both", expand=True, padx=20, pady=15)
        
        def force_close_roblox():
            confirm = messagebox.askyesno(
                "Confirm Force Close",
                "Are you sure you want to force close all Roblox instances?"
            )
            if not confirm:
                return

            try:
                result = subprocess.run(
                    ['taskkill', '/F', '/IM', 'RobloxPlayerBeta.exe'],
                    capture_output=True,
                    text=True,
                    creationflags=subprocess.CREATE_NO_WINDOW
                )
                
                if result.returncode == 0:
                    messagebox.showinfo("Success", "All Roblox instances have been closed.")
                else:
                    messagebox.showinfo("Info", "No Roblox instances were found running.")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to close Roblox: {e}")
        
        force_close_btn = ttk.Button(
            roblox_frame,
            text="Force Close All Roblox",
            style="Dark.TButton",
            command=force_close_roblox
        )
        force_close_btn.pack(fill="x", pady=(0, 5))
        
        rename_var = tk.BooleanVar(value=self.settings.get("rename_roblox_windows", False))
        
        def on_rename_toggle():
            enabled = rename_var.get()
            self.settings["rename_roblox_windows"] = enabled
            self.save_settings()
            
            if enabled:
                self.start_rename_monitoring()
            else:
                self.stop_rename_monitoring()
        
        ttk.Checkbutton(
            roblox_frame,
            text="Rename Roblox Windows",
            variable=rename_var,
            style="Dark.TCheckbutton",
            command=on_rename_toggle
        ).pack(anchor="w", pady=(0, 10))
        
        
        if self.settings.get("rename_roblox_windows", False):
            self.root.after(1000, self.start_rename_monitoring)
        
        if self.settings.get("active_instances_monitoring", False):
            self.root.after(1500, self.start_instances_monitoring)
        
        themes_frame = ttk.Frame(themes_tab, style="Dark.TFrame")
        themes_frame.pack(fill="both", expand=True, padx=20, pady=15)

        theme_state = {
            "loaded_theme_name": self.settings.get("selected_theme", "Dark"),
            "base_theme_data": None,
            "theme_is_dirty": False,
            "suspend_dirty_events": False,
        }

        theme_title_var = tk.StringVar(value=f"Theme: {theme_state['loaded_theme_name']}")
        theme_selector_var = tk.StringVar()
        theme_status_var = tk.StringVar(value="")

        theme_catalog = {}

        def set_theme_title(text):
            theme_title_var.set(f"Theme: {text}")

        def refresh_theme_catalog(preferred_name=None):
            nonlocal theme_catalog
            theme_catalog = self.theme_manager.get_available_themes()
            theme_names = sorted(theme_catalog.keys(), key=str.lower)
            theme_selector["values"] = theme_names

            target = preferred_name or theme_state["loaded_theme_name"]
            if target not in theme_catalog:
                for name in theme_names:
                    if name.lower() == str(target).lower():
                        target = name
                        break
            if target not in theme_catalog and theme_names:
                target = theme_names[0]

            theme_selector_var.set(target or "")

        header_row = ttk.Frame(themes_frame, style="Dark.TFrame")
        header_row.pack(fill="x", pady=(0, 8))

        ttk.Label(
            header_row,
            textvariable=theme_title_var,
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 10, "bold")
        ).pack(side="left")

        def open_theme_manager_from_settings():
            self.open_theme_manager(parent=settings_window, on_themes_changed=lambda preferred=None: refresh_theme_catalog(preferred))

        ttk.Button(
            header_row,
            text="Themes",
            style="Dark.TButton",
            command=open_theme_manager_from_settings
        ).pack(side="right")

        selector_row = ttk.Frame(themes_frame, style="Dark.TFrame")
        selector_row.pack(fill="x", pady=(0, 8))

        ttk.Label(
            selector_row,
            text="Load Theme:",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 9)
        ).pack(side="left", padx=(0, 6))

        theme_selector = ttk.Combobox(
            selector_row,
            textvariable=theme_selector_var,
            state="readonly",
            width=28
        )
        theme_selector.pack(side="left", fill="x", expand=True)

        editor_box_height = 220
        editor_shell = tk.Frame(
            themes_frame,
            bg=self.BG_PANEL,
            relief="solid",
            borderwidth=1,
            height=editor_box_height,
        )
        editor_shell.pack(fill="x", expand=False, pady=(0, 8))
        editor_shell.pack_propagate(False)
        self.theme_editor_shell = editor_shell

        editor_area = tk.Frame(editor_shell, bg=self.BG_MID)
        editor_area.pack(fill="both", expand=True, padx=8, pady=8)
        self.theme_editor_area = editor_area

        editor_scrollbar = tk.Scrollbar(editor_area, orient="vertical")
        editor_scrollbar.pack(side="left", fill="y", padx=(0, 8))
        editor_scrollbar.config(width=10)

        editor_canvas = tk.Canvas(
            editor_area,
            bg=self.BG_PANEL,
            highlightthickness=0,
            yscrollcommand=editor_scrollbar.set,
            height=editor_box_height,
        )
        editor_canvas.pack(side="left", fill="both", expand=True)
        editor_scrollbar.config(command=editor_canvas.yview)
        self.theme_editor_canvas = editor_canvas

        editor_content = tk.Frame(editor_canvas, bg=self.BG_MID)
        editor_window = editor_canvas.create_window((0, 0), window=editor_content, anchor="nw")
        self.theme_editor_content = editor_content
        self.theme_editor_widgets = []

        style = ttk.Style()
        style.configure(
            "ThemeEditor.TCombobox",
            fieldbackground=self.BG_MID,
            background=self.BG_MID,
            foreground=self.FG_TEXT,
            arrowcolor=self.FG_TEXT,
            bordercolor=self.BG_LIGHT,
            lightcolor=self.BG_LIGHT,
            darkcolor=self.BG_LIGHT,
            relief="flat",
        )

        def _sync_editor_scrollregion(_event=None):
            editor_canvas.configure(scrollregion=editor_canvas.bbox("all"))

        def _sync_editor_width(event):
            editor_canvas.itemconfigure(editor_window, width=event.width)

        editor_content.bind("<Configure>", _sync_editor_scrollregion)
        editor_canvas.bind("<Configure>", _sync_editor_width)

        def _scroll_editor(event):
            editor_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            return "break"

        def _bind_mousewheel_recursive(widget):
            widget.bind("<MouseWheel>", _scroll_editor)
            for child in widget.winfo_children():
                _bind_mousewheel_recursive(child)

        def _refresh_editor_mousewheel_bindings(*_):
            _bind_mousewheel_recursive(editor_shell)

        editor_shell.bind("<Enter>", _refresh_editor_mousewheel_bindings)
        editor_shell.bind("<Leave>", lambda _event: editor_canvas.unbind_all("<MouseWheel>"))

        current_theme_config = self._load_current_theme_config()
        initial_theme_name = self.settings.get("selected_theme", "Dark")
        if current_theme_config:
            initial_theme_name = str(current_theme_config.get("source_theme", initial_theme_name) or initial_theme_name)

        theme_state = {
            "loaded_theme_name": initial_theme_name,
            "base_theme_name": initial_theme_name,
            "base_theme_data": None,
            "theme_is_dirty": False,
            "suspend_dirty_events": False,
        }

        color_keys = [
            ("bg_dark", "Background Dark"),
            ("bg_mid", "Background Mid"),
            ("bg_light", "Background Light"),
            ("fg_text", "Text Color"),
            ("fg_accent", "Accent Color"),
        ]

        color_vars = {key: tk.StringVar() for key, _ in color_keys}
        self.theme_color_vars = color_vars

        font_field_defaults = {
            "family": self.theme_manager.DEFAULT_THEME["fonts"]["family"],
            "size_base": str(self.theme_manager.DEFAULT_THEME["fonts"]["size_base"]),
        }
        font_vars = {key: tk.StringVar(value=value) for key, value in font_field_defaults.items()}

        def _validated_font_size(text_value, fallback):
            try:
                return max(6, min(36, int(str(text_value).strip())))
            except Exception:
                return fallback

        def get_editor_theme_data():
            data = self._deepcopy_theme_data(theme_state["base_theme_data"] or self.theme_manager.DEFAULT_THEME)
            colors = data.setdefault("colors", {})
            fonts = data.setdefault("fonts", {})

            for key, _label in color_keys:
                colors[key] = self._normalize_hex_color(color_vars[key].get(), self.theme_manager.DEFAULT_THEME["colors"].get(key, "#000000"))

            fonts["family"] = font_vars["family"].get().strip() or self.theme_manager.DEFAULT_THEME["fonts"]["family"]
            fonts["size_base"] = _validated_font_size(font_vars["size_base"].get(), 10)

            return data

        def theme_data_matches_base(current_data):
            base_data = theme_state["base_theme_data"] or self.theme_manager.DEFAULT_THEME
            current_colors = current_data.get("colors", {})
            base_colors = base_data.get("colors", {})
            current_fonts = current_data.get("fonts", {})
            base_fonts = base_data.get("fonts", {})
            for key, _label in color_keys:
                if self._normalize_hex_color(current_colors.get(key), "") != self._normalize_hex_color(base_colors.get(key), ""):
                    return False
            for key in ("family", "size_base"):
                if str(current_fonts.get(key, "")).strip() != str(base_fonts.get(key, "")).strip():
                    return False
            return True

        def update_theme_title_from_state(current_data=None):
            if theme_state["theme_is_dirty"]:
                set_theme_title("Custom")
                return
            loaded_name = theme_state["loaded_theme_name"] or "Dark"
            if current_data is not None and not theme_data_matches_base(current_data):
                theme_state["theme_is_dirty"] = True
                set_theme_title("Custom")
            else:
                set_theme_title(loaded_name)

        def set_status(text):
            theme_status_var.set(text)

        def mark_theme_dirty(*_):
            if theme_state["suspend_dirty_events"]:
                return
            current_data = get_editor_theme_data()
            theme_state["theme_is_dirty"] = not theme_data_matches_base(current_data)
            update_theme_title_from_state(current_data)
            set_status("Unsaved changes" if theme_state["theme_is_dirty"] else "")

        for var in color_vars.values():
            var.trace_add("write", mark_theme_dirty)
        for var in font_vars.values():
            var.trace_add("write", mark_theme_dirty)
        def apply_theme_to_editor(theme_name, theme_data_override=None):
            resolved = theme_name
            if resolved not in theme_catalog:
                for existing in theme_catalog.keys():
                    if existing.lower() == str(theme_name).lower():
                        resolved = existing
                        break
            if resolved not in theme_catalog:
                return

            base_theme_data = self.theme_manager.load_theme(resolved)
            merged = self.theme_manager._merge_with_defaults(theme_data_override or base_theme_data)
            theme_state["suspend_dirty_events"] = True
            theme_state["base_theme_name"] = resolved
            theme_state["base_theme_data"] = self._deepcopy_theme_data(base_theme_data)
            for key, _label in color_keys:
                color_vars[key].set(str(merged.get("colors", {}).get(key, self.theme_manager.DEFAULT_THEME["colors"].get(key, "#000000"))))
            fonts = merged.get("fonts", {})
            font_vars["family"].set(str(fonts.get("family", self.theme_manager.DEFAULT_THEME["fonts"]["family"])))
            font_vars["size_base"].set(str(int(fonts.get("size_base", 10))))
            theme_state["suspend_dirty_events"] = False

            theme_state["loaded_theme_name"] = resolved
            theme_state["theme_is_dirty"] = not theme_data_matches_base(merged)
            theme_selector_var.set(resolved)
            set_theme_title("Custom" if theme_state["theme_is_dirty"] else resolved)
            set_status("")

        def on_theme_selector_change(_event=None):
            selected_name = theme_selector_var.get().strip()
            if selected_name:
                apply_theme_to_editor(selected_name)

        theme_selector.bind("<<ComboboxSelected>>", on_theme_selector_change)

        def choose_theme_color(setting_key, label_text):
            current_color = color_vars[setting_key].get() or "#000000"
            picked = colorchooser.askcolor(initialcolor=current_color, title=f"Choose {label_text}", parent=settings_window)
            if picked and picked[1]:
                color_vars[setting_key].set(picked[1])

        color_section = tk.Frame(editor_content, bg=self.BG_MID)
        color_section.pack(fill="x", pady=(0, 8))
        self.theme_color_section = color_section

        color_header = tk.Label(color_section, text="Colors", bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 10, "bold"))
        color_header.pack(anchor="w", pady=(0, 4))
        self.theme_editor_widgets.append(color_header)

        color_rows = tk.Frame(color_section, bg=self.BG_MID)
        color_rows.pack(fill="x")
        self.theme_color_rows = color_rows

        color_swatches = {}
        self.theme_color_swatch_widgets = color_swatches

        def make_color_row(parent, key, label_text):
            row = tk.Frame(parent, bg=self.BG_MID)
            row.pack(fill="x", pady=2)

            label = tk.Label(row, text=label_text, bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 8), width=18, anchor="w")
            label.pack(side="left")
            self.theme_editor_widgets.append(label)
            self.theme_editor_widgets.append(row)

            entry = tk.Entry(
                row,
                textvariable=color_vars[key],
                width=12,
                bg=self.BG_PANEL,
                fg=self.FG_TEXT,
                insertbackground=self.FG_TEXT,
                relief="solid",
                borderwidth=1,
                highlightthickness=1,
                highlightbackground=self.BG_LIGHT,
                highlightcolor=self.FG_ACCENT,
            )
            entry.pack(side="left", padx=(0, 6))
            self.theme_editor_widgets.append(entry)

            swatch = tk.Frame(row, bg="#000000", width=18, height=18, relief="solid", borderwidth=1)
            swatch.pack(side="left", padx=(0, 6))
            swatch.pack_propagate(False)
            color_swatches[key] = swatch

            def refresh_swatch(*_):
                value = color_vars[key].get().strip()
                if re.fullmatch(r"#[0-9a-fA-F]{6}", value):
                    swatch.config(bg=value)

            color_vars[key].trace_add("write", refresh_swatch)
            refresh_swatch()

            picker_btn = tk.Button(
                row,
                text="...",
                width=3,
                bg=self.BG_PANEL,
                fg=self.FG_TEXT,
                relief="flat",
                activebackground=self.BG_SURFACE,
                activeforeground=self.FG_TEXT,
                command=lambda k=key, t=label_text: choose_theme_color(k, t),
            )
            picker_btn.pack(side="right")
            self.theme_editor_widgets.append(picker_btn)

        for key, label in color_keys:
            make_color_row(color_rows, key, label)

        font_section = tk.Frame(editor_content, bg=self.BG_MID)
        font_section.pack(fill="x", pady=(4, 8))
        self.theme_font_section = font_section

        font_header = tk.Label(font_section, text="Fonts", bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 10, "bold"))
        font_header.pack(anchor="w", pady=(0, 4))
        self.theme_editor_widgets.append(font_header)

        def font_row(parent, label_text, create_widget):
            row = tk.Frame(parent, bg=self.BG_MID)
            row.pack(fill="x", pady=2)
            self.theme_editor_widgets.append(row)
            label = tk.Label(row, text=label_text, bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 8), width=18, anchor="w")
            label.pack(side="left")
            self.theme_editor_widgets.append(label)
            widget = create_widget(row)
            widget.pack(side="right", fill="x", expand=True)
            self.theme_editor_widgets.append(widget)
            return widget

        font_families = sorted({family for family in tkfont.families() if family and not family.startswith("@")})
        if "Segoe UI" in font_families:
            font_families.insert(0, font_families.pop(font_families.index("Segoe UI")))

        font_family_combo = font_row(
            font_section,
            "Family",
            lambda parent: ttk.Combobox(
                parent,
                textvariable=font_vars["family"],
                values=font_families,
                state="readonly",
                width=24,
                style="ThemeEditor.TCombobox",
            ),
        )
        self.theme_family_combo = font_family_combo

        def make_size_entry(variable):
            return lambda parent: tk.Entry(
                parent,
                textvariable=variable,
                width=10,
                bg=self.BG_PANEL,
                fg=self.FG_TEXT,
                insertbackground=self.FG_TEXT,
                relief="solid",
                borderwidth=1,
                highlightthickness=1,
                highlightbackground=self.BG_LIGHT,
                highlightcolor=self.FG_ACCENT,
            )

        font_row(font_section, "Base Size", make_size_entry(font_vars["size_base"]))

        def set_theme_from_editor():
            current_data = get_editor_theme_data()
            dirty = not theme_data_matches_base(current_data)
            theme_state["theme_is_dirty"] = dirty
            update_theme_title_from_state(current_data)
            self._save_current_theme_config(current_data, theme_state["base_theme_name"])
            self._apply_theme_data(current_data, selected_theme_name=("Custom" if dirty else theme_state["loaded_theme_name"]), persist_selection=True)
            set_status("Applied custom theme" if dirty else f"Applied {theme_state['loaded_theme_name']}")

        def save_theme_from_editor():
            current_data = get_editor_theme_data()
            suggested_name = theme_state["loaded_theme_name"]
            theme_name = simpledialog.askstring(
                "Save Theme",
                "Theme name:",
                initialvalue=suggested_name,
                parent=settings_window,
            )
            if theme_name is None:
                return

            theme_name = str(theme_name).strip()
            if not theme_name:
                messagebox.showwarning("Save Theme", "Theme name cannot be empty.", parent=settings_window)
                return

            safe_theme_name = re.sub(r'[<>:"/\\|?*]', "_", theme_name).strip()
            if not safe_theme_name:
                messagebox.showwarning("Save Theme", "Theme name contains only invalid filename characters.", parent=settings_window)
                return

            suggested_author = ""
            suggested_description = ""
            if suggested_name in self.theme_manager.get_available_themes():
                existing_theme = self.theme_manager.load_theme(suggested_name)
                suggested_author = existing_theme.get("metadata", {}).get("author", "")
                suggested_description = existing_theme.get("metadata", {}).get("description", "")

            author_name = simpledialog.askstring(
                "Save Theme",
                "Author:",
                initialvalue=suggested_author,
                parent=settings_window,
            )
            if author_name is None:
                return
            author_name = str(author_name).strip()
            if not author_name:
                messagebox.showwarning("Save Theme", "Author cannot be empty.", parent=settings_window)
                return

            description_text = simpledialog.askstring(
                "Save Theme",
                "Description:",
                initialvalue=suggested_description,
                parent=settings_window,
            )
            if description_text is None:
                return
            description_text = str(description_text).strip()
            if not description_text:
                messagebox.showwarning("Save Theme", "Description cannot be empty.", parent=settings_window)
                return

            available = self.theme_manager.get_available_themes()
            if safe_theme_name in available and available[safe_theme_name].get("builtin", False):
                messagebox.showwarning("Save Theme", "Cannot overwrite a builtin theme. Choose another name.", parent=settings_window)
                return

            if safe_theme_name in available and not messagebox.askyesno(
                "Save Theme",
                f"Overwrite existing custom theme '{safe_theme_name}'?",
                parent=settings_window,
            ):
                return

            save_data = self._deepcopy_theme_data(current_data)
            metadata = save_data.setdefault("metadata", {})
            metadata["name"] = safe_theme_name
            metadata["author"] = author_name
            metadata["description"] = description_text

            if not self.theme_manager.save_theme(safe_theme_name, save_data, is_custom=True):
                messagebox.showerror("Save Theme", "Failed to save theme.", parent=settings_window)
                return

            self._save_current_theme_config(save_data, safe_theme_name)
            theme_state["base_theme_name"] = safe_theme_name
            theme_state["loaded_theme_name"] = safe_theme_name
            theme_state["theme_is_dirty"] = False
            refresh_theme_catalog(safe_theme_name)
            apply_theme_to_editor(safe_theme_name, save_data)
            set_theme_title(safe_theme_name)
            set_status("Theme saved")
            messagebox.showinfo("Save Theme", f"Saved theme '{safe_theme_name}'.", parent=settings_window)

        button_row = ttk.Frame(themes_frame, style="Dark.TFrame")
        button_row.pack(fill="x")

        ttk.Button(button_row, text="Set Theme", style="Dark.TButton", command=set_theme_from_editor).pack(side="left", fill="x", expand=True, padx=(0, 4))
        ttk.Button(button_row, text="Save Theme", style="Dark.TButton", command=save_theme_from_editor).pack(side="left", fill="x", expand=True, padx=(4, 0))

        refresh_theme_catalog(self.settings.get("selected_theme", "Dark"))
        if current_theme_config:
            apply_theme_to_editor(theme_state["loaded_theme_name"], current_theme_config)
        else:
            apply_theme_to_editor(theme_state["loaded_theme_name"])
        self._theme_editor_save_current_config = lambda: self._save_current_theme_config(get_editor_theme_data(), theme_state["base_theme_name"])
        if theme_state["theme_is_dirty"]:
            set_theme_title("Custom")
        else:
            set_theme_title(theme_state["loaded_theme_name"])
        

       
        ttk.Label(

            style="Dark.TLabel", font=(self.FONT_FAMILY, 11, "bold")
        ).pack(side="left")

        dc_mode_btn = ttk.Button(

            style="Dark.TButton",
        )
        dc_mode_btn.pack(side="right")

   
        about_frame = ttk.Frame(about_tab, style="Dark.TFrame")
        about_frame.pack(fill="both", expand=True, padx=20, pady=15)
        
        ttk.Label(
            about_frame,
            text="Rocore",
            style="Dark.TLabel",
            font=("Segoe UI", 14, "bold")
        ).pack(anchor="center", pady=(10, 5))
        
        is_unstable = bool(re.search(r'(alpha|beta)', self.APP_VERSION, re.IGNORECASE))
        version_text = f"Version {self.APP_VERSION}"
        
        ttk.Label(
            about_frame,
            text=version_text,
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 10)
        ).pack(anchor="center", pady=(0, 5))
        
        if is_unstable:
            ttk.Label(
                about_frame,
                text="⚠️ This is an unstable version",
                style="Dark.TLabel",
                font=("Segoe UI", 9, "italic"),
                foreground="#FFA500"
            ).pack(anchor="center", pady=(0, 10))
        else:
            ttk.Label(about_frame, text="", style="Dark.TLabel").pack(pady=(0, 10))
        
        ttk.Label(
            about_frame,
            text="Made by Mateo",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 9)
        ).pack(anchor="center", pady=(5, 15))
        
        ttk.Button(
            about_frame,
            text="Discord Server",
            style="Dark.TButton",
            command=lambda: webbrowser.open("https://discord.gg/xvWK6BkGD6")
        ).pack(fill="x", pady=(0, 10))
        

        tool_frame = ttk.Frame(tool_tab, style="Dark.TFrame")
        tool_frame.pack(fill="both", expand=True, padx=20, pady=15)
        
        ttk.Label(
            tool_frame,
            text="Tools",
            style="Dark.TLabel",
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w", pady=(0, 15))
        
        def wipe_data():
            """Wipe data"""
            if not messagebox.askyesno("Confirm Wipe Data", "Are you sure you want to wipe ALL data?\n\nThis action cannot be undone!"):
                return
            
            encryption_method = self.manager.get_encryption_method()
            
            if encryption_method == "password":
                password_window = tk.Toplevel(settings_window)
                self.apply_window_icon(password_window)
                password_window.title("Enter Password")
                password_window.geometry("350x150")
                password_window.configure(bg=self.BG_DARK)
                password_window.resizable(False, False)
                password_window.transient(settings_window)
                password_window.grab_set()
                
                settings_window.update_idletasks()
                x = settings_window.winfo_x() + (settings_window.winfo_width() - 350) // 2
                y = settings_window.winfo_y() + (settings_window.winfo_height() - 150) // 2
                password_window.geometry(f"350x150+{x}+{y}")
                
                main_frame = ttk.Frame(password_window, style="Dark.TFrame")
                main_frame.pack(fill="both", expand=True, padx=20, pady=20)
                
                ttk.Label(main_frame, text="Enter your password:", style="Dark.TLabel").pack(anchor="w", pady=(0, 10))
                
                password_entry = ttk.Entry(main_frame, style="Dark.TEntry", show="*")
                password_entry.pack(fill="x", pady=(0, 15))
                password_entry.focus_set()
                
                def verify_and_wipe():
                    password = password_entry.get()
                    if not password:
                        messagebox.showwarning("Missing Password", "Please enter your password.")
                        return
                    
                    if self.manager.verify_password(password):
                        password_window.destroy()
                        if messagebox.askyesno("Final Confirmation", "This will permanently delete ALL data. Continue?"):
                            settings_window.destroy()
                            self.manager.wipe_all_data()
                            messagebox.showinfo("Success", "All data has been wiped!")
                            settings_window.quit()
                    else:
                        messagebox.showerror("Invalid Password", "Password is incorrect.")
                
                btn_frame = ttk.Frame(main_frame, style="Dark.TFrame")
                btn_frame.pack(fill="x")
                
                ttk.Button(btn_frame, text="Verify", style="Dark.TButton", command=verify_and_wipe).pack(side="left", fill="x", expand=True, padx=(0, 5))
                ttk.Button(btn_frame, text="Cancel", style="Dark.TButton", command=password_window.destroy).pack(side="left", fill="x", expand=True, padx=(5, 0))
            else:
                if messagebox.askyesno("Final Confirmation", "This will permanently delete ALL data. Continue?"):
                    settings_window.destroy()
                    self.manager.wipe_all_data()
                    messagebox.showinfo("Success", "All data has been wiped!")
                    settings_window.quit()
        
        
        def switch_encryption_method():
            """Switch encryption method"""
            current_method = self.manager.get_encryption_method()
            
            if current_method == "password":
                password_window = tk.Toplevel(settings_window)
                self.apply_window_icon(password_window)
                password_window.title("Verify Password")
                password_window.geometry("350x150")
                password_window.configure(bg=self.BG_DARK)
                password_window.resizable(False, False)
                password_window.transient(settings_window)
                password_window.grab_set()
                
                settings_window.update_idletasks()
                x = settings_window.winfo_x() + (settings_window.winfo_width() - 350) // 2
                y = settings_window.winfo_y() + (settings_window.winfo_height() - 150) // 2
                password_window.geometry(f"350x150+{x}+{y}")
                
                pwd_frame = ttk.Frame(password_window, style="Dark.TFrame")
                pwd_frame.pack(fill="both", expand=True, padx=20, pady=20)
                
                ttk.Label(pwd_frame, text="Enter your password to continue:", style="Dark.TLabel").pack(anchor="w", pady=(0, 10))
                
                password_entry = ttk.Entry(pwd_frame, style="Dark.TEntry", show="*")
                password_entry.pack(fill="x", pady=(0, 15))
                password_entry.focus_set()
                
                def verify_and_proceed():
                    password = password_entry.get()
                    if not password:
                        messagebox.showwarning("Missing Password", "Please enter your password.")
                        return
                    
                    if self.manager.verify_password(password):
                        password_window.destroy()
                        settings_window.destroy()
                        self._run_encryption_switch()
                    else:
                        messagebox.showerror("Invalid Password", "Password is incorrect.")
                
                pwd_btn_frame = ttk.Frame(pwd_frame, style="Dark.TFrame")
                pwd_btn_frame.pack(fill="x")
                
                ttk.Button(pwd_btn_frame, text="Verify", style="Dark.TButton", command=verify_and_proceed).pack(side="left", fill="x", expand=True, padx=(0, 5))
                ttk.Button(pwd_btn_frame, text="Cancel", style="Dark.TButton", command=password_window.destroy).pack(side="left", fill="x", expand=True, padx=(5, 0))
            else:
                settings_window.destroy()
                self._run_encryption_switch()
        
    
        ttk.Button(
            tool_frame,
            text="Browser Engine",
            style="Dark.TButton",
            command=self.open_browser_engine_window
        ).pack(fill="x", pady=(0, 5))
        
        ttk.Button(
            tool_frame,
            text="Switch Encryption Method",
            style="Dark.TButton",
            command=switch_encryption_method
        ).pack(fill="x", pady=(0, 5))
        
        ttk.Button(
            tool_frame,
            text="Roblox Settings",
            style="Dark.TButton",
            command=self.open_roblox_settings_window
        ).pack(fill="x", pady=(0, 5))
        
        ttk.Button(
            tool_frame,
            text="Active Instances",
            style="Dark.TButton",
            command=self.open_active_instances_window
        ).pack(fill="x", pady=(0, 5))
        

        ttk.Button(
            tool_frame,
            text="Wipe Data",
            style="Dark.TButton",
            command=wipe_data
        ).pack(side="bottom", fill="x", pady=(10, 0))
    


    """"chrome"""

    def is_chrome_installed(self):
        """Best-effort check to see if Google Chrome is installed (Windows)."""
        try:
            candidates = []
            pf = os.environ.get('ProgramFiles')
            pfx86 = os.environ.get('ProgramFiles(x86)')
            localapp = os.environ.get('LOCALAPPDATA')
            if pf:
                candidates.append(os.path.join(pf, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            if pfx86:
                candidates.append(os.path.join(pfx86, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            if localapp:
                candidates.append(os.path.join(localapp, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            for path in candidates:
                if path and os.path.exists(path):
                    return True
        except Exception:
            pass
        return False

    def open_browser_engine_window(self):
        """Open Browser Engine selection window"""
        browser_window = tk.Toplevel(self.root)
        self.apply_window_icon(browser_window)
        browser_window.title("Browser Engine Settings")
        browser_window.geometry("420x330")
        browser_window.configure(bg=self.BG_DARK)
        browser_window.resizable(False, False)
        browser_window.transient(self.root)
        

        browser_window.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (browser_window.winfo_width() // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (browser_window.winfo_height() // 2)
        browser_window.geometry(f"+{x}+{y}")
        
        current_browser = self.settings.get("browser_type", "chrome")
        browser_var = tk.StringVar(value=current_browser)
        chrome_installed = self.is_chrome_installed()
        chromium_path = os.path.join(self.data_folder, "Chromium", "chrome-win64", "chrome.exe")
        chromium_installed = os.path.exists(chromium_path)
        
        container = ttk.Frame(browser_window, style="Dark.TFrame")
        container.pack(fill="both", expand=True, padx=20, pady=20)
        
        header_frame = ttk.Frame(container, style="Dark.TFrame")
        header_frame.pack(fill="x", pady=(0, 15))
        
        ttk.Label(
            header_frame,
            text="Select Browser Engine",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 11, "bold")
        ).pack(anchor="w")
        
        ttk.Label(
            header_frame,
            text="Choose which browser to use for Add Account",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 8)
        ).pack(anchor="w", pady=(2, 0))
        
        separator = ttk.Frame(container, style="Dark.TFrame", height=1)
        separator.pack(fill="x", pady=(0, 15))
        separator.configure(relief="solid", borderwidth=1)
        
        options_frame = ttk.Frame(container, style="Dark.TFrame")
        options_frame.pack(fill="both", expand=True)
        
        radio_style = ttk.Style()
        radio_style.configure(
            "Browser.TRadiobutton",
            background=self.BG_DARK,
            foreground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 10)
        )
        radio_style.map(
            "Browser.TRadiobutton",
            background=[("active", self.BG_DARK)],
            foreground=[("active", self.FG_TEXT)]
        )
        
        chrome_frame = ttk.Frame(options_frame, style="Dark.TFrame")
        chrome_frame.pack(fill="x", pady=(0, 8))
        
        chrome_radio = ttk.Radiobutton(
            chrome_frame,
            text="Google Chrome",
            variable=browser_var,
            value="chrome",
            style="Browser.TRadiobutton"
        )
        chrome_radio.pack(side="left")
        
        chrome_status = "✓ Installed" if chrome_installed else "Not Installed"
        chrome_color = "#00FF00" if chrome_installed else "#FF6666"
        tk.Label(
            chrome_frame,
            text=f"  [{chrome_status}]",
            bg=self.BG_DARK,
            fg=chrome_color,
            font=(self.FONT_FAMILY, 9)
        ).pack(side="left")
        
        chromium_frame = ttk.Frame(options_frame, style="Dark.TFrame")
        chromium_frame.pack(fill="x", pady=(0, 15))
        
        chromium_radio = ttk.Radiobutton(
            chromium_frame,
            text="Chromium",
            variable=browser_var,
            value="chromium",
            style="Browser.TRadiobutton"
        )
        chromium_radio.pack(side="left")
        
        chromium_status_text = "✓ Installed" if chromium_installed else "Not Installed"
        chromium_color = "#00FF00" if chromium_installed else "#FF6666"
        chromium_status_label = tk.Label(
            chromium_frame,
            text=f"  [{chromium_status_text}]",
            bg=self.BG_DARK,
            fg=chromium_color,
            font=(self.FONT_FAMILY, 9)
        )
        chromium_status_label.pack(side="left")
        
        progress_outer = tk.Frame(options_frame, bg=self.BG_LIGHT, relief="solid", borderwidth=1)
        
        progress_inner = tk.Frame(progress_outer, bg=self.BG_PANEL, height=22)
        progress_inner.pack(fill="x", padx=1, pady=1)
        progress_inner.pack_propagate(False)
        
        progress_fill = tk.Frame(progress_inner, bg=self.BG_LIGHT, width=0)
        progress_fill.place(x=0, y=0, relheight=1)
        
        progress_label = tk.Label(
            progress_inner,
            text="0%",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9, "bold")
        )
        progress_label.place(relx=0.5, rely=0.5, anchor="center")
        
        status_label = ttk.Label(
            options_frame,
            text="",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 9)
        )
        
        def update_progress(percent):
            """Update the custom progress bar"""
            progress_inner.update_idletasks()
            total_width = progress_inner.winfo_width()
            fill_width = int((percent / 100) * total_width)
            progress_fill.place(x=0, y=0, relheight=1, width=fill_width)
            
            label_x = total_width // 2
            if fill_width >= label_x:
                progress_label.config(bg=self.BG_LIGHT, fg=self.BG_DARK)
            else:
                progress_label.config(bg=self.BG_PANEL, fg=self.FG_TEXT)
            
            progress_label.config(text=f"{int(percent)}%")
            browser_window.update()
        
        download_btn = None
        
        def download_chromium():
            """Download portable Chromium"""
            nonlocal chromium_installed
            
            download_btn.config(state="disabled", text="Downloading...")
            progress_outer.pack(fill="x", pady=(0, 10))
            status_label.pack(anchor="w", pady=(0, 10))
            status_label.config(text="Downloading Chromium...")
            browser_window.update()
            
            def do_download():
                try:
                    chromium_dir = os.path.join(self.data_folder, "Chromium")
                    os.makedirs(chromium_dir, exist_ok=True)
                    
                    browser_window.after(0, lambda: status_label.config(text="Fetching latest version..."))
                    last_change_url = "https://storage.googleapis.com/chromium-browser-snapshots/Win_x64/LAST_CHANGE"
                    last_change_response = requests.get(last_change_url, timeout=30)
                    if last_change_response.status_code != 200:
                        raise Exception("Failed to fetch latest Chromium version")
                    build_number = last_change_response.text.strip()
                    
                    download_url = f"https://storage.googleapis.com/chromium-browser-snapshots/Win_x64/{build_number}/chrome-win.zip"
                    browser_window.after(0, lambda: status_label.config(text=f"Downloading build {build_number}..."))
                    zip_path = os.path.join(chromium_dir, "chromium.zip")
                    
                    response = requests.get(download_url, stream=True, timeout=60)
                    total_size = int(response.headers.get('content-length', 0))
                    downloaded = 0
                    last_progress = 0
                    
                    with open(zip_path, 'wb') as f:
                        for chunk in response.iter_content(chunk_size=65536):
                            if chunk:
                                f.write(chunk)
                                downloaded += len(chunk)
                                if total_size > 0:
                                    progress = int((downloaded / total_size) * 100)
                                    if progress >= last_progress + 1:
                                        last_progress = progress
                                        browser_window.after(10, lambda p=progress: update_progress(p))
                    
                    browser_window.after(0, lambda: update_progress(100))
                    browser_window.after(0, lambda: status_label.config(text="Extracting Chromium..."))
                    browser_window.after(50, lambda: update_progress(0))
                    
                    with zipfile.ZipFile(zip_path, 'r') as zip_ref:
                        file_list = zip_ref.namelist()
                        total_files = len(file_list)
                        for i, file in enumerate(file_list):
                            zip_ref.extract(file, chromium_dir)
                            if i % 50 == 0:
                                progress = int((i / total_files) * 100)
                                browser_window.after(0, lambda p=progress: update_progress(p))
                    
                    browser_window.after(0, lambda: update_progress(100))
                    
                    extracted_folder = os.path.join(chromium_dir, "chrome-win")
                    target_folder = os.path.join(chromium_dir, "chrome-win64")
                    if os.path.exists(extracted_folder) and not os.path.exists(target_folder):
                        os.rename(extracted_folder, target_folder)
                    
                    os.remove(zip_path)
                    
                    browser_window.after(0, lambda: status_label.config(text="Downloading ChromeDriver..."))
                    browser_window.after(50, lambda: update_progress(0))
                    
                    chromedriver_url = f"https://storage.googleapis.com/chromium-browser-snapshots/Win_x64/{build_number}/chromedriver_win32.zip"
                    chromedriver_zip_path = os.path.join(chromium_dir, "chromedriver.zip")
                    
                    chromedriver_response = requests.get(chromedriver_url, stream=True, timeout=60)
                    cd_total_size = int(chromedriver_response.headers.get('content-length', 0))
                    cd_downloaded = 0
                    cd_last_progress = 0
                    
                    with open(chromedriver_zip_path, 'wb') as f:
                        for chunk in chromedriver_response.iter_content(chunk_size=65536):
                            if chunk:
                                f.write(chunk)
                                cd_downloaded += len(chunk)
                                if cd_total_size > 0:
                                    progress = int((cd_downloaded / cd_total_size) * 100)
                                    if progress >= cd_last_progress + 1:
                                        cd_last_progress = progress
                                        browser_window.after(10, lambda p=progress: update_progress(p))
                    
                    browser_window.after(0, lambda: update_progress(100))
                    browser_window.after(0, lambda: status_label.config(text="Extracting ChromeDriver..."))
                    browser_window.after(50, lambda: update_progress(0))
                    
                    with zipfile.ZipFile(chromedriver_zip_path, 'r') as zip_ref:
                        zip_ref.extractall(chromium_dir)
                    
                    browser_window.after(0, lambda: update_progress(100))
                    
                    chromedriver_extracted = os.path.join(chromium_dir, "chromedriver-win32", "chromedriver.exe")
                    chromedriver_target = os.path.join(target_folder, "chromedriver.exe")
                    if os.path.exists(chromedriver_extracted):
                        shutil.copy2(chromedriver_extracted, chromedriver_target)
                        shutil.rmtree(os.path.join(chromium_dir, "chromedriver-win32"))
                    
                    os.remove(chromedriver_zip_path)
                    
                    def update_ui():
                        nonlocal chromium_installed
                        chromium_installed = os.path.exists(os.path.join(chromium_dir, "chrome-win64", "chrome.exe"))
                        if chromium_installed:
                            chromium_status_label.config(text="  [✓ Installed]", fg="#00FF00")
                            download_btn.config(state="disabled", text="✓ Downloaded")
                            status_label.config(text="Chromium downloaded successfully!")
                        else:
                            download_btn.config(state="normal", text="Download Chromium")
                            status_label.config(text="Failed to extract Chromium.")
                        progress_outer.pack_forget()
                    
                    browser_window.after(0, update_ui)
                    
                except Exception as download_error:
                    error_msg = str(download_error)
                    def show_error():
                        download_btn.config(state="normal", text="Download Chromium")
                        progress_outer.pack_forget()
                        status_label.config(text=f"Download failed: {error_msg[:50]}...")
                    browser_window.after(0, show_error)
            
            thread = threading.Thread(target=do_download, daemon=True)
            thread.start()
        
        if not chromium_installed:
            download_btn = ttk.Button(
                options_frame,
                text="Download Chromium",
                style="Dark.TButton",
                command=download_chromium
            )
            download_btn.pack(fill="x", pady=(0, 10))
        else:
            download_btn = ttk.Button(
                options_frame,
                text="✓ Downloaded",
                style="Dark.TButton",
                state="disabled"
            )
            download_btn.pack(fill="x", pady=(0, 10))
        
        def on_browser_change(*args):
            nonlocal chromium_installed
            selected = browser_var.get()
            if selected == "chromium" and not chromium_installed:
                messagebox.showwarning(
                    "Chromium Not Installed",
                    "Please download Chromium first."
                )
                browser_var.set("chrome")
                return
            if selected == "chrome" and not chrome_installed:
                messagebox.showwarning(
                    "Chrome Not Installed",
                    "Google Chrome is not installed.\nPlease install Chrome or use Chromium."
                )
                if chromium_installed:
                    browser_var.set("chromium")
                return
            self.settings["browser_type"] = selected
            self.save_settings()
        
        browser_var.trace_add("write", on_browser_change)
        
        ttk.Button(
            container,
            text="Close",
            style="Dark.TButton",
            command=browser_window.destroy
        ).pack(fill="x", pady=(10, 0))
    


    """"JOIN"""


    def launch_home(self):
        """Launch Roblox application to home page with the selected account(s) logged in (non-blocking)"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
            if len(usernames) >= 3:
                confirm = messagebox.askyesno(
                    "Confirm Launch",
                    f"Are you sure you want to launch {len(usernames)} Roblox instances to home?\n\nThis will open multiple Roblox windows."
                )
                if not confirm:
                    return
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]

        def worker(selected_usernames):
            launcher_pref, custom_launcher_path = self._get_roblox_launcher_config()
            success_count = 0
            failed_launch = False
            for uname in selected_usernames:
                try:
                    if self.manager.launch_roblox(uname, "", "", launcher_pref, "", custom_launcher_path):
                        success_count += 1
                    else:
                        failed_launch = True
                except Exception as e:
                    print(f"[ERROR] Failed to launch Roblox home for {uname}: {e}")
            if failed_launch:
                self._silent_check_cookies()
            

            def on_done():
                if success_count > 0:
                    self.settings["last_joined_user"] = selected_usernames[-1]
                    self.save_settings()
                    if not self.settings.get("disable_launch_popup", False):
                        if len(selected_usernames) == 1:
                            messagebox.showinfo("Success", "Roblox is launching to home! Check your desktop.")
                        else:
                            messagebox.showinfo("Success", f"Roblox is launching to home for {success_count} account(s)! Check your desktop.")
                else:
                    messagebox.showerror("Error", "Failed to launch Roblox.")
            
            self.root.after(0, on_done)

        threading.Thread(target=worker, args=(usernames,), daemon=True).start()

    def launch_game(self):
        """Launch Roblox game with the selected account(s)"""
        
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]

        game_id_input = self.place_entry.get().strip()
        private_server_input = self.private_server_entry.get().strip()

        if game_id_input:
            if not game_id_input.isdigit():
                messagebox.showerror("Invalid Input", "Place ID must be a valid number.")
                return
            game_id = game_id_input
        elif private_server_input:
            vip_pid = re.search(r'roblox\.com/games/(\d+)', private_server_input)
            game_id = vip_pid.group(1) if vip_pid else ""
        else:
            messagebox.showwarning("Missing Info", "Please enter a Place ID or paste a VIP server / share link in the Private Server field.")
            return

        private_server = private_server_input 

        if self.settings.get("confirm_before_launch", False):
            game_name = RobloxAPI.get_game_name(game_id)
            if not game_name:
                game_name = f"Place {game_id}"
            if len(usernames) == 1:
                confirm = messagebox.askyesno("Confirm Launch", f"Are you sure you want to join {game_name}?")
            else:
                confirm = messagebox.askyesno("Confirm Launch", f"Are you sure you want to join {game_name} with {len(usernames)} accounts?")
            if not confirm:
                return

        def worker(selected_usernames, pid, psid):
            launcher_pref, custom_launcher_path = self._get_roblox_launcher_config()
            success_count = 0
            failed_launch = False
            for i, uname in enumerate(selected_usernames):
                try:
                    if self.manager.launch_roblox(uname, pid, psid, launcher_pref, "", custom_launcher_path):
                        success_count += 1
                    else:
                        failed_launch = True
                except Exception as e:
                    print(f"[ERROR] Failed to launch game for {uname}: {e}")
                if i < len(selected_usernames) - 1:
                    time.sleep(2)
            if failed_launch:
                self._silent_check_cookies()


            def on_done():
                if success_count > 0:
                    self.settings["last_joined_user"] = selected_usernames[-1]
                    self.save_settings()
                    gname = RobloxAPI.get_game_name(pid)
                    if gname:
                        self.add_game_to_list(pid, gname, psid)
                    else:
                        self.add_game_to_list(pid, f"Place {pid}", psid)
                    if not self.settings.get("disable_launch_popup", False):
                        if len(selected_usernames) == 1:
                            messagebox.showinfo("Success", "Roblox is launching! Check your desktop.")
                        else:
                            messagebox.showinfo("Success", f"Roblox is launching for {success_count} account(s)! Check your desktop.")
                else:
                    messagebox.showerror("Error", "Failed to launch Roblox.")

            self.root.after(0, on_done)

        threading.Thread(target=worker, args=(usernames, game_id, private_server), daemon=True).start()

    def join_user(self):
        """Join a user's current game"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]
        
        join_window = tk.Toplevel(self.root)
        self.apply_window_icon(join_window)
        join_window.title("Join User")
        join_window.geometry("450x220")
        join_window.configure(bg=self.BG_DARK)
        join_window.resizable(False, False)
        
        self.root.update_idletasks()
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        
        x = main_x + (main_width - 450) // 2
        y = main_y + (main_height - 220) // 2
        join_window.geometry(f"450x220+{x}+{y}")
        
        join_window.transient(self.root)
        join_window.grab_set()
        
        main_frame = ttk.Frame(join_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=20, pady=20)
        
        ttk.Label(
            main_frame,
            text="Join User's Game",
            style="Dark.TLabel",
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w", pady=(0, 10))
        
        ttk.Label(
            main_frame,
            text="⚠️ User must have their joins enabled!",
            style="Dark.TLabel",
            font=("Segoe UI", 9, "italic"),
            foreground="#FFA500"
        ).pack(anchor="w", pady=(0, 10))
        
        ttk.Label(main_frame, text="Username to join:", style="Dark.TLabel").pack(anchor="w", pady=(0, 5))
        
        username_entry = ttk.Entry(main_frame, style="Dark.TEntry")
        username_entry.pack(fill="x", pady=(0, 15))
        username_entry.focus_set()
        
        def do_join():
            target_username = username_entry.get().strip()
            
            if not target_username:
                messagebox.showwarning("Missing Information", "Please enter a username.")
                return
            
            join_window.destroy()
            
            def worker(selected_usernames, target_user):
                
                user_id = RobloxAPI.get_user_id_from_username(target_user)
                if not user_id:
                    self.root.after(0, lambda: messagebox.showerror(
                        "Error",
                        f"User '{target_user}' not found."
                    ))
                    return
                
                account_cookie = self.manager.accounts.get(selected_usernames[0])
                if isinstance(account_cookie, dict):
                    account_cookie = account_cookie.get('cookie')
                
                if not account_cookie:
                    self.root.after(0, lambda: messagebox.showerror(
                        "Error",
                        "Failed to get account cookie."
                    ))
                    return
                
                presence = RobloxAPI.get_player_presence(user_id, account_cookie)
                
                if not presence:
                    self.root.after(0, lambda: messagebox.showerror(
                        "Error",
                        f"Failed to get presence for '{target_user}'. Please try again."
                    ))
                    return
                
                if not presence.get('in_game'):
                    self.root.after(0, lambda: messagebox.showinfo(
                        "Not In Game",
                        f"'{target_user}' is not currently in a game.\n\nStatus: {presence.get('last_location', 'Unknown')}"
                    ))
                    return
                
                place_id = str(presence.get('place_id', ''))
                game_id = str(presence.get('game_id', ''))
                
                if not place_id:
                    self.root.after(0, lambda: messagebox.showerror(
                        "Error",
                        f"Could not get game info for '{target_user}'."
                    ))
                    return
                
                launcher_pref, custom_launcher_path = self._get_roblox_launcher_config()
                success_count = 0
                
                for uname in selected_usernames:
                    try:
                        if self.manager.launch_roblox(uname, place_id, "", launcher_pref, game_id, custom_launcher_path):
                            success_count += 1
                    except Exception as e:
                        print(f"[ERROR] Failed to launch game for {uname}: {e}")
                
                def on_done():
                    if success_count > 0:
                        game_name = RobloxAPI.get_game_name(place_id)
                        if game_name:
                            self.add_game_to_list(place_id, game_name, "")
                        else:
                            self.add_game_to_list(place_id, f"Place {place_id}", "")
                        
                        if len(selected_usernames) == 1:
                            messagebox.showinfo(
                                "Success",
                                f"Joining '{target_user}' in their game! Check your desktop."
                            )
                        else:
                            messagebox.showinfo(
                                "Success",
                                f"Joining '{target_user}' with {success_count} account(s)! Check your desktop."
                            )
                    else:
                        messagebox.showerror("Error", "Failed to launch Roblox.")
                
                self.root.after(0, on_done)
            
            threading.Thread(target=worker, args=(usernames, target_username), daemon=True).start()
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x")
        
        ttk.Button(
            button_frame,
            text="Join",
            style="Dark.TButton",
            command=do_join
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Cancel",
            style="Dark.TButton",
            command=join_window.destroy
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))

    def join_by_job_id(self):
        """Join a game by Job ID"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]
        
        job_id_window = tk.Toplevel(self.root)
        self.apply_window_icon(job_id_window)
        job_id_window.title("Join by Job-ID")
        job_id_window.geometry("450x220")
        job_id_window.configure(bg=self.BG_DARK)
        job_id_window.resizable(False, False)
        
        self.root.update_idletasks()
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        
        x = main_x + (main_width - 450) // 2
        y = main_y + (main_height - 220) // 2
        job_id_window.geometry(f"450x220+{x}+{y}")
        
        if False:
            job_id_window.attributes("-topmost", True)
        
        job_id_window.transient(self.root)
        job_id_window.grab_set()
        
        main_frame = ttk.Frame(job_id_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=20, pady=20)
        
        ttk.Label(
            main_frame,
            text="Join by Job-ID",
            style="Dark.TLabel",
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w", pady=(0, 10))
        
        ttk.Label(main_frame, text="Job-ID:", style="Dark.TLabel").pack(anchor="w", pady=(0, 5))
        
        job_id_entry = ttk.Entry(main_frame, style="Dark.TEntry")
        job_id_entry.pack(fill="x", pady=(0, 15))
        job_id_entry.focus_set()
        
        def do_join_job():
            place_id = self.place_entry.get().strip()
            if not place_id:
                messagebox.showwarning("Missing Information", "Please enter a Place ID first.")
                return
            
            job_id = job_id_entry.get().strip()
            if not job_id:
                messagebox.showwarning("Missing Information", "Please enter a Job-ID.")
                return
            
            job_id_window.destroy()
            
            def worker(selected_usernames, pid, jid):
                launcher_pref, custom_launcher_path = self._get_roblox_launcher_config()
                success_count = 0
                
                for uname in selected_usernames:
                    try:
                        if self.manager.launch_roblox(uname, pid, "", launcher_pref, jid, custom_launcher_path):
                            success_count += 1
                    except Exception as e:
                        print(f"[ERROR] Failed to launch game for {uname}: {e}")
                
                def on_done():
                    if success_count > 0:
                        game_name = RobloxAPI.get_game_name(pid)
                        if game_name:
                            self.add_game_to_list(pid, game_name, "")
                        else:
                            self.add_game_to_list(pid, f"Place {pid}", "")
                        
                        messagebox.showinfo(
                            "Success",
                            f"Joining Job-ID {jid} with {success_count} account(s)! Check your desktop."
                        )
                    else:
                        messagebox.showerror("Error", "Failed to launch Roblox.")
                
                self.root.after(0, on_done)
            
            threading.Thread(target=worker, args=(usernames, place_id, job_id), daemon=True).start()
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x")
        
        ttk.Button(
            button_frame,
            text="Join",
            style="Dark.TButton",
            command=do_join_job
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Cancel",
            style="Dark.TButton",
            command=job_id_window.destroy
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))

    def join_small_server(self):
        """Join the smallest available server for a given place ID"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]
        
        place_id = self.place_entry.get().strip()
        if not place_id:
            messagebox.showwarning("Missing Information", "Please enter a Place ID first.")
            return
        
        try:
            int(place_id)
        except ValueError:
            messagebox.showerror("Invalid Input", "Place ID must be a valid number.")
            return
        
        def worker(selected_usernames, pid):
            print(f"[INFO] Searching for smallest server in place {pid}...")
            game_id = RobloxAPI.get_smallest_server(pid)
            
            if not game_id:
                self.root.after(0, lambda: messagebox.showerror(
                    "Error",
                    f"Could not find any available servers for place {pid}.\n\nPlease try again later or check the Place ID."
                ))
                return
            
            print(f"[SUCCESS] Found smallest server: {game_id}")
            
            launcher_pref, custom_launcher_path = self._get_roblox_launcher_config()
            success_count = 0
            
            for uname in selected_usernames:
                try:
                    if self.manager.launch_roblox(uname, pid, "", launcher_pref, game_id, custom_launcher_path):
                        success_count += 1
                except Exception as e:
                    print(f"[ERROR] Failed to launch game for {uname}: {e}")
            
            def on_done():
                if success_count > 0:
                    game_name = RobloxAPI.get_game_name(pid)
                    if game_name:
                        self.add_game_to_list(pid, game_name, "")
                    else:
                        self.add_game_to_list(pid, f"Place {pid}", "")
                    
                    if len(selected_usernames) == 1:
                        messagebox.showinfo(
                            "Success",
                            f"Joining smallest server! Check your desktop."
                        )
                    else:
                        messagebox.showinfo(
                            "Success",
                            f"Joining smallest server with {success_count} account(s)! Check your desktop."
                        )
                else:
                    messagebox.showerror("Error", "Failed to launch Roblox.")
            
            self.root.after(0, on_done)
        
        threading.Thread(target=worker, args=(usernames, place_id), daemon=True).start()

    def on_join_place_split_click(self, event):
        """Handle clicks on the button: left click launches game, right click shows dropdown."""
        self.launch_game()
        return "break"
    
    def hide_dropdown_on_click_outside(self, event):
        """Hide dropdown when clicking outside of it"""
        widget = event.widget
        if self.add_account_dropdown_visible and self.add_account_dropdown is not None:
            if not self.is_child_of(widget, self.add_account_split_btn):
                try:
                    if not self.is_child_of(widget, self.add_account_dropdown):
                        self.hide_add_account_dropdown()
                except:
                    self.hide_add_account_dropdown()
        
        if self.join_place_dropdown_visible and self.join_place_dropdown is not None:
            if not self.is_child_of(widget, self.join_place_split_btn):
                try:
                    if not self.is_child_of(widget, self.join_place_dropdown):
                        self.hide_join_place_dropdown()
                except:
                    self.hide_join_place_dropdown()

    def toggle_join_place_dropdown(self):
        """Toggle the Join Place dropdown menu"""
        self.join_place_dropdown_visible = not self.join_place_dropdown_visible
        if self.join_place_dropdown_visible:
            self.show_join_place_dropdown()
        else:
            self.hide_join_place_dropdown()

    def on_join_place_right_click(self, event):
        """Handle right click on the button: show dropdown menu."""
        self.toggle_join_place_dropdown()
        return "break"
    
    def on_join_place_hover(self, event):
        """Show tooltip when hovering over Join Place ID button"""
        if self.tooltip_timer:
            self.root.after_cancel(self.tooltip_timer)
        
        def show_tooltip():
            if self.tooltip:
                return
            
            x = event.widget.winfo_rootx() + event.widget.winfo_width() // 2
            y = event.widget.winfo_rooty() + event.widget.winfo_height() + 5
            
            self.tooltip = tk.Toplevel(self.root)
            self.tooltip.wm_overrideredirect(True)
            self.tooltip.wm_geometry(f"+{x}+{y}")
            
            label = tk.Label(
                self.tooltip,
                text="Right click to see more options",
                bg="#333333",
                fg="white",
                font=(self.FONT_FAMILY, 9),
                padx=8,
                pady=4,
                relief="solid",
                borderwidth=1
            )
            label.pack()
            
            self.tooltip.update_idletasks()
            tooltip_width = self.tooltip.winfo_width()
            self.tooltip.wm_geometry(f"+{x - tooltip_width // 2}+{y}")
            
            if False:
                self.tooltip.attributes("-topmost", True)
        
        self.tooltip_timer = self.root.after(800, show_tooltip)
    
    def on_join_place_leave(self, event):
        """Hide tooltip when leaving Join Place ID button"""
        if self.tooltip_timer:
            self.root.after_cancel(self.tooltip_timer)
            self.tooltip_timer = None
        
        if self.tooltip:
            self.tooltip.destroy()
            self.tooltip = None
    
    def show_join_place_dropdown(self):
        """Show the Join Place dropdown menu"""
        if self.join_place_dropdown is not None:
            self.join_place_dropdown.destroy()
        
        self.join_place_dropdown = tk.Toplevel(self.root)
        self.join_place_dropdown.overrideredirect(True)
        self.join_place_dropdown.configure(bg=self.BG_APP, highlightthickness=0)
        self._apply_windows_corner_preferences()

        container = tk.Frame(self.join_place_dropdown, bg=self.BG_PANEL, highlightthickness=1, highlightbackground=self.BG_BORDER)
        container.pack(fill="both", expand=True, padx=10, pady=10)
        
        self.position_join_place_dropdown()
        
        join_user_btn = tk.Button(
            container,
            text="Join User",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=lambda: [self.hide_join_place_dropdown(), self.join_user()]
        )
        join_user_btn.pack(fill="x", padx=10, pady=5)
        
        job_id_btn = tk.Button(
            container,
            text="Job-ID",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=lambda: [self.hide_join_place_dropdown(), self.join_by_job_id()]
        )
        job_id_btn.pack(fill="x", padx=10, pady=5)
        
        small_server_btn = tk.Button(
            container,
            text="Small Server",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=lambda: [self.hide_join_place_dropdown(), self.join_small_server()]
        )
        small_server_btn.pack(fill="x", padx=10, pady=(5, 10))
        
        self.position_join_place_dropdown()
        
        if False:
            self.join_place_dropdown.attributes("-topmost", True)
        
        self.join_place_dropdown.bind("<FocusOut>", lambda e: self.hide_join_place_dropdown())

    def position_join_place_dropdown(self):
        """Position the dropdown right under the split button and match its width."""
        try:
            if self.join_place_dropdown is None or not self.join_place_dropdown_visible:
                return
            self.root.update_idletasks()
            x = self.join_place_split_btn.winfo_rootx()
            y = self.join_place_split_btn.winfo_rooty() + self.join_place_split_btn.winfo_height()
            width = self.join_place_split_btn.winfo_width()
            req_h = self.join_place_dropdown.winfo_reqheight()
            self.join_place_dropdown.geometry(f"{width}x{req_h}+{x}+{y}")
            if False:
                self.join_place_dropdown.attributes("-topmost", True)
        except Exception:
            pass
    
    def hide_join_place_dropdown(self):
        """Hide the Join Place dropdown menu"""
        if self.join_place_dropdown is not None:
            self.join_place_dropdown.destroy()
            self.join_place_dropdown = None
        self.join_place_dropdown_visible = False


    """Console/Debug"""


    _MAX_CONSOLE_LINES = 2000

    def log_to_console(self, message):
        """Log message to console output buffer"""
        self.console_output.append(message)
        if len(self.console_output) > self._MAX_CONSOLE_LINES:
            del self.console_output[: len(self.console_output) - self._MAX_CONSOLE_LINES]

        if self.console_text_widget:
            try:
                self.console_text_widget.config(state="normal")
                insert_start = self.console_text_widget.index(f"{tk.END}-1c linestart")
                self.console_text_widget.insert(tk.END, message)
                line_count = int(self.console_text_widget.index(tk.END).split(".")[0]) - 1
                if line_count > self._MAX_CONSOLE_LINES:
                    excess = line_count - self._MAX_CONSOLE_LINES
                    self.console_text_widget.delete("1.0", f"{excess + 1}.0")
                    insert_start = "1.0"
                self._apply_console_tags(search_from=insert_start)
                self.console_text_widget.see(tk.END)
                self.console_text_widget.config(state="disabled")
            except:
                pass
    
    def _apply_console_tags(self, search_from: str = "1.0"):
        """Apply color tags to console keywords."""
        if not self.console_text_widget:
            return
        
        keywords = {
            "[SUCCESS]": "success",
            "[ERROR]": "error",
            "[INFO]": "info",
            "[WARNING]": "warning"
        }
        
        for keyword, tag in keywords.items():
            search_start = search_from
            while True:
                pos = self.console_text_widget.search(keyword, search_start, tk.END, nocase=False)
                if not pos:
                    break
                end_pos = f"{pos}+{len(keyword)}c"
                self.console_text_widget.tag_add(tag, pos, end_pos)
                search_start = end_pos
    
    def open_console_window(self):
        """Open the Console Output window"""
        if self.console_window and tk.Toplevel.winfo_exists(self.console_window):
            self.console_window.focus()
            return
        
        self.console_window = tk.Toplevel(self.root)
        self.apply_window_icon(self.console_window)
        self.console_window.title("Console Output")
        self.console_window.configure(bg=self.BG_DARK)
        self.console_window.minsize(500, 450)
        
        if False:
            self.console_window.attributes("-topmost", True)
        
        self.root.update_idletasks()
        
        saved_console = self.settings.get('console_window_geometry')
        if saved_console and saved_console.get('x') is not None and saved_console.get('y') is not None:
            width = saved_console.get('width', 700)
            height = saved_console.get('height', 500)
            x = saved_console['x']
            y = saved_console['y']
            self.console_window.geometry(f"{width}x{height}+{x}+{y}")
        else:
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            main_height = self.root.winfo_height()
            x = main_x + (main_width - 700) // 2
            y = main_y + (main_height - 500) // 2
            self.console_window.geometry(f"700x500+{x}+{y}")
        
        main_frame = ttk.Frame(self.console_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=10, pady=10)
        
        title_label = ttk.Label(
            main_frame,
            text="Console Output",
            style="Dark.TLabel",
            font=("Segoe UI", 12, "bold")
        )
        title_label.pack(anchor="w", pady=(0, 10))
        
        text_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        text_frame.pack(fill="both", expand=True)
        
        self.console_text_widget = tk.Text(
            text_frame,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            font=("Consolas", 9),
            wrap="word",
            state="disabled"
        )
        self.console_text_widget.pack(side="left", fill="both", expand=True)
        
        self.console_text_widget.tag_configure("success", foreground="#00FF00")
        self.console_text_widget.tag_configure("error", foreground="#FF0000")
        self.console_text_widget.tag_configure("info", foreground="#0078D7")
        self.console_text_widget.tag_configure("warning", foreground="#FFD700")
        
        scrollbar = ttk.Scrollbar(text_frame, command=self.console_text_widget.yview)
        scrollbar.pack(side="right", fill="y")
        self.console_text_widget.config(yscrollcommand=scrollbar.set)
        
        self.console_text_widget.config(state="normal")
        for message in self.console_output:
            self.console_text_widget.insert(tk.END, message)
        
        self._apply_console_tags()
        self.console_text_widget.config(state="disabled")
        
        self.console_text_widget.see(tk.END)
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x", pady=(10, 0))
        
        def clear_console():
            self.console_output.clear()
            self.console_text_widget.config(state="normal") 
            self.console_text_widget.delete(1.0, tk.END)
            self.console_text_widget.config(state="disabled") 
        
        def copy_all():
            text = self.console_text_widget.get(1.0, tk.END)
            try:
                win32clipboard.OpenClipboard()
                win32clipboard.EmptyClipboard()
                win32clipboard.SetClipboardText(text, win32clipboard.CF_UNICODETEXT)
                win32clipboard.CloseClipboard()
            except Exception:
                self.root.clipboard_clear()
                self.root.clipboard_append(text)
            messagebox.showinfo("Copied", "Console output copied to clipboard!")

        ttk.Button(
            button_frame,
            text="Clear",
            style="Dark.TButton",
            command=clear_console
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Copy All",
            style="Dark.TButton",
            command=copy_all
        ).pack(side="left", fill="x", expand=True, padx=5)
        
        ttk.Button(
            button_frame,
            text="Close",
            style="Dark.TButton",
            command=self.console_window.destroy
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))
        
        def on_console_close():
            """Save window geometry (position and size) before closing"""
            self.settings['console_window_geometry'] = {
                'x': self.console_window.winfo_x(),
                'y': self.console_window.winfo_y(),
                'width': self.console_window.winfo_width(),
                'height': self.console_window.winfo_height()
            }
            self.save_settings()
            self.console_text_widget = None
            self.console_window.destroy()
            self.console_window = None
        
        self.console_window.protocol("WM_DELETE_WINDOW", on_console_close)
    
    def write(self, text):
        """Redirect stdout/stderr writes to console"""
        if text.strip():
            timestamp = datetime.now().strftime("%H:%M:%S")
            self.log_to_console(f"[{timestamp}] {text}\n")
        if self.original_stdout:
            self.original_stdout.write(text)
    
    def flush(self):
        """Flush stdout"""
        if self.original_stdout:
            self.original_stdout.flush()
    












    def on_closing(self):
        """Handle application closing - restore installers and exit"""
        
        self.settings['main_window_position'] = {
            'x': self.root.winfo_x(),
            'y': self.root.winfo_y()
        }
        self.save_settings(force_immediate=True)
        

        if hasattr(self, 'rename_stop_event'):
            self.stop_rename_monitoring()
        

        
        RobloxAPI.restore_installers()
        self.root.destroy()


    def _get_roblox_launcher_config(self):
        launcher_pref = self.settings.get("roblox_launcher", "default")
        custom_path = str(self.settings.get("custom_roblox_launcher_path", "") or "").strip()
        return launcher_pref, custom_path

    
    def toggle_add_account_dropdown(self):
        """Toggle the Add Account dropdown menu"""
        self.add_account_dropdown_visible = not self.add_account_dropdown_visible
        if self.add_account_dropdown_visible:
            self.show_add_account_dropdown()
        else:
            self.hide_add_account_dropdown()
    
    def on_add_account_split_click(self, event):
        """Kept for compatibility with older configs; the new split control uses dedicated buttons."""
        return "break"
    
    def show_add_account_dropdown(self):
        """Show the Add Account dropdown menu"""
        if self.add_account_dropdown is not None:
            self.add_account_dropdown.destroy()
        
        self.add_account_dropdown = tk.Toplevel(self.root)
        self.add_account_dropdown.overrideredirect(True)
        self.add_account_dropdown.configure(bg=self.BG_APP, highlightthickness=0)
        self._apply_windows_corner_preferences()

        container = tk.Frame(self.add_account_dropdown, bg=self.BG_PANEL, highlightthickness=1, highlightbackground=self.BG_BORDER)
        container.pack(fill="both", expand=True, padx=10, pady=10)
        
        self.position_add_account_dropdown()
        
        import_cookie_btn = tk.Button(
            container,
            text="Import Cookie",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=lambda: [self.hide_add_account_dropdown(), self.import_cookie()]
        )
        import_cookie_btn.pack(fill="x", padx=10, pady=(10, 5))
        
       
        self.position_add_account_dropdown()
        
        if False:
            self.add_account_dropdown.attributes("-topmost", True)
        
        self.add_account_dropdown.bind("<FocusOut>", lambda e: self.hide_add_account_dropdown())

    def position_add_account_dropdown(self):
        """Position the dropdown right under the split button and match its width."""
        try:
            if self.add_account_dropdown is None or not self.add_account_dropdown_visible:
                return
            self.root.update_idletasks()
            x = self.add_account_split_btn.winfo_rootx()
            y = self.add_account_split_btn.winfo_rooty() + self.add_account_split_btn.winfo_height()
            width = self.add_account_split_btn.winfo_width()
            req_h = self.add_account_dropdown.winfo_reqheight()
            self.add_account_dropdown.geometry(f"{width}x{req_h}+{x}+{y}")
            if False:
                self.add_account_dropdown.attributes("-topmost", True)
        except Exception:
            pass

    def on_root_configure(self, event=None):
        """Called when the main window moves/resizes; keep dropdown attached."""
        if self.add_account_dropdown_visible and self.add_account_dropdown is not None:
            self.position_add_account_dropdown()
        if self.join_place_dropdown_visible and self.join_place_dropdown is not None:
            self.position_join_place_dropdown()
    
    def hide_add_account_dropdown(self):
        """Hide the Add Account dropdown menu"""
        if self.add_account_dropdown is not None:
            self.add_account_dropdown.destroy()
            self.add_account_dropdown = None
        self.add_account_dropdown_visible = False
    
    def is_child_of(self, child, parent):
        """Check if a widget is a child of another widget"""
        while child is not None:
            if child == parent:
                return True
            child = child.master
        return False
    


    def _process_ui_task_queue(self):
        try:
            while True:
                func, args, kwargs, done_event, result_box = self._ui_task_queue.get_nowait()
                try:
                    result_box["value"] = func(*args, **kwargs)
                except Exception as exc:
                    result_box["error"] = exc
                finally:
                    if done_event is not None:
                        done_event.set()
        except queue.Empty:
            pass

        try:
            if self.root.winfo_exists():
                self.root.after(50, self._process_ui_task_queue)
        except Exception:
            pass

    def _run_on_ui_thread(self, func, *args, wait=True, timeout=30, **kwargs):
        if threading.current_thread() is threading.main_thread():
            return func(*args, **kwargs)

        done_event = threading.Event() if wait else None
        result_box = {"value": None, "error": None}
        self._ui_task_queue.put((func, args, kwargs, done_event, result_box))

        if not wait:
            return None

        if not done_event.wait(timeout):
            raise TimeoutError("UI task timed out")
        if result_box["error"] is not None:
            raise result_box["error"]
        return result_box["value"]



    def get_browser_path(self):
        """Get path to the selected browser (Chrome or Chromium)."""
        browser_type = self.settings.get("browser_type", "chrome")
        
        if browser_type == "chromium":
            chromium_path = os.path.join(self.data_folder, "Chromium", "chrome-win64", "chrome.exe")
            if os.path.exists(chromium_path):
                return chromium_path, "Chromium"
            browser_type = "chrome"
        
        if browser_type == "chrome":
            candidates = []
            pf = os.environ.get('ProgramFiles')
            pfx86 = os.environ.get('ProgramFiles(x86)')
            localapp = os.environ.get('LOCALAPPDATA')
            if pf:
                candidates.append(os.path.join(pf, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            if pfx86:
                candidates.append(os.path.join(pfx86, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            if localapp:
                candidates.append(os.path.join(localapp, 'Google', 'Chrome', 'Application', 'chrome.exe'))
            for path in candidates:
                if path and os.path.exists(path):
                    return path, "Google Chrome"
        
        return None, None

    def update_game_name_on_startup(self):
        """Check both Place ID and Private Server fields to update game name on startup"""
        place_id = self.place_entry.get().strip()
        private_server = self.private_server_entry.get().strip()

        if place_id:
            self.update_game_name()
        elif private_server:
            vip_match = re.search(r'roblox\.com/games/(\d+)', private_server)
            if vip_match:
                self.update_game_name_from_id(vip_match.group(1))
            else:
                share_match = re.search(r'roblox\.com/share\?[^#]*code=([A-Za-z0-9]+)', private_server)
                if share_match:
                    def _resolve_startup(ps=private_server):
                        ck = next((d.get('cookie') for d in self.manager.accounts.values() if isinstance(d, dict) and d.get('cookie')), None)
                        resolved_pid, _ = RobloxAPI.resolve_share_url(ps, cookie=ck)
                        if resolved_pid:
                            self.root.after(0, lambda: self.update_game_name_from_id(resolved_pid))
                    threading.Thread(target=_resolve_startup, daemon=True).start()

    def on_place_id_change(self, event=None):
        place_id = self.place_entry.get().strip()
        self.settings["last_place_id"] = place_id
        self.save_settings()
        self.update_game_name()

    def on_private_server_change(self, event=None):        
        private_server = self.private_server_entry.get().strip()
        place_id_input = self.place_entry.get().strip()

        self.settings["last_private_server"] = private_server
        self.save_settings()

        if not place_id_input and private_server:
            vip_match = re.search(r'roblox\.com/games/(\d+)', private_server)
            if vip_match:
                self.update_game_name_from_id(vip_match.group(1))
            else:
                share_match = re.search(r'roblox\.com/share\?[^#]*code=([A-Za-z0-9]+)', private_server)
                if share_match:
                    def _resolve_and_update(ps=private_server):
                        ck = next((d.get('cookie') for d in self.manager.accounts.values() if isinstance(d, dict) and d.get('cookie')), None)
                        resolved_pid, _ = RobloxAPI.resolve_share_url(ps, cookie=ck)
                        if resolved_pid:
                            self.root.after(0, lambda: self.update_game_name_from_id(resolved_pid))
                    threading.Thread(target=_resolve_and_update, daemon=True).start()
    
    def update_game_name_from_id(self, place_id):
        """Update game name label from a specific place ID (without reading from text box)"""
        if self._game_name_after_id is not None:
            try:
                self.root.after_cancel(self._game_name_after_id)
            except Exception:
                pass
            self._game_name_after_id = None

        def schedule_fetch():
            if not place_id or not place_id.isdigit():
                self.game_name_label.config(text="")
                return

            def worker(pid):
                name = RobloxAPI.get_game_name(pid)
                if name:
                    max_name_length = 20
                    if len(name) > max_name_length:
                        name = name[:max_name_length-2] + ".."
                    display_text = f"Current: {name}"
                else:
                    display_text = ""
                
                def update_label(text=display_text):
                    try:
                        self.game_name_label.config(text=text)
                    except:
                        pass
                
                self.root.after(0, update_label)

            threading.Thread(target=worker, args=(place_id,), daemon=True).start()

        self._game_name_after_id = self.root.after(350, schedule_fetch)
    

    def update_game_name(self):
        """Debounced, non-blocking update of the game name label"""
        if self._game_name_after_id is not None:
            try:
                self.root.after_cancel(self._game_name_after_id)
            except Exception:
                pass
            self._game_name_after_id = None

        def schedule_fetch():
            place_id = self.place_entry.get().strip()
            if not place_id or not place_id.isdigit():
                self.game_name_label.config(text="")
                return

            def worker(pid):
                name = RobloxAPI.get_game_name(pid)
                if name:
                    max_name_length = 20
                    if len(name) > max_name_length:
                        name = name[:max_name_length-2] + ".."
                    display_text = f"Current: {name}"
                else:
                    display_text = ""
                
                def update_label(text=display_text):
                    try:
                        self.game_name_label.config(text=text)
                    except:
                        pass
                
                self.root.after(0, update_label)

            threading.Thread(target=worker, args=(place_id,), daemon=True).start()

        self._game_name_after_id = self.root.after(350, schedule_fetch)

    def add_game_to_list(self, place_id, game_name, private_server=""):
        """Add a game to the saved list (max based on settings)"""
        for game in self.settings["game_list"]:
            if game["place_id"] == place_id and game.get("private_server", "") == private_server:
                return
        
        self.settings["game_list"].insert(0, {
            "place_id": place_id,
            "name": game_name,
            "private_server": private_server
        })
        
        max_games = self.settings.get("max_recent_games", 10)
        if len(self.settings["game_list"]) > max_games:
            self.settings["game_list"] = self.settings["game_list"][:max_games]
        
        self.save_settings()
        self.refresh_game_list()

    def refresh_game_list(self):
        """Refresh the game list display"""
        self.game_list.delete(0, tk.END)
        for game in self.settings["game_list"]:
            private_server = game.get("private_server", "")
            prefix = "[P] " if private_server else ""
            display_text = f"{prefix}{game['name']} ({game['place_id']})"
            self.game_list.insert(tk.END, display_text)

    def on_game_select(self, event=None):
        """Called when a game is selected from the list"""
        selection = self.game_list.curselection()
        if selection:
            index = selection[0]
            game = self.settings["game_list"][index]
            self.place_entry.delete(0, tk.END)
            self.place_entry.insert(0, game["place_id"])
            self.settings["last_place_id"] = game["place_id"]
            
            private_server = game.get("private_server", "")
            self.private_server_entry.delete(0, tk.END)
            self.private_server_entry.insert(0, private_server)
            self.settings["last_private_server"] = private_server
            
            self.save_settings()
            self.update_game_name()

    def delete_game_from_list(self):
        """Delete selected game from the list"""
        selection = self.game_list.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select a game to delete.")
            return
        
        index = selection[0]
        game = self.settings["game_list"][index]
        confirm = messagebox.askyesno("Confirm Delete", f"Delete '{game['name']}' from list?")
        if confirm:
            self.settings["game_list"].pop(index)
            self.save_settings()
            self.refresh_game_list()
            messagebox.showinfo("Success", "Game removed from list!")

    def _get_groups(self):
        return self.settings.get("groups", {})

    def _save_groups(self, groups):
        self.settings["groups"] = groups
        self.settings["group_collapsed"] = list(self._collapsed_groups)
        self.save_settings()

    def _get_username_group(self, username):
        for gname, members in self._get_groups().items():
            if username in members:
                return gname
        return None

    def _add_account_to_group(self, username, group_name):
        groups = self._get_groups()
        if group_name not in groups:
            groups[group_name] = []
        for gn in list(groups):
            if gn != group_name and username in groups[gn]:
                groups[gn].remove(username)
        if username not in groups[group_name]:
            groups[group_name].append(username)
        self._save_groups(groups)
        self.refresh_accounts()

    def _remove_account_from_group(self, username):
        groups = self._get_groups()
        for gn in list(groups):
            if username in groups[gn]:
                groups[gn].remove(username)
        self._save_groups(groups)
        self.refresh_accounts()

    def _handle_group_header_click(self, index):
        if index < 0 or index >= len(self._list_row_map):
            return
        kind, name = self._list_row_map[index]
        if kind != "group_header":
            return
        if name in self._collapsed_groups:
            self._collapsed_groups.discard(name)
        else:
            self._collapsed_groups.add(name)
        self._save_groups(self._get_groups())
        self.refresh_accounts()

    def _build_group_header_text(self, group_name, member_count, collapsed):
        arrow = "v" if collapsed else "^"
        prefix = f" {group_name} ({member_count}) "

        try:
            lb_font = tkfont.Font(font=self.account_list.cget("font"))
            list_width = self.account_list.winfo_width()
            if list_width <= 1:
                list_width = 220
            usable = list_width - 4
            prefix_px = lb_font.measure(prefix)
            suffix_reserved = max(lb_font.measure(" v "), lb_font.measure(" ^ "))
            dash_px = lb_font.measure("\u2500")
            remaining = usable - prefix_px - suffix_reserved
            if remaining > 0 and dash_px > 0:
                n_dashes = remaining // dash_px
            else:
                n_dashes = 3
        except Exception:
            n_dashes = 10

        dash_char = "\u2500"
        dashes = dash_char * max(3, n_dashes)
        return f"{prefix}{dashes} {arrow} "

    def _show_group_context_menu(self, event, group_name):
        """Right-click menu on a group header."""
        if hasattr(self, 'account_context_menu') and self.account_context_menu is not None:
            try: self.account_context_menu.destroy()
            except: pass

        menu = tk.Toplevel(self.root)
        menu.overrideredirect(True)
        menu.configure(bg=self.BG_PANEL, highlightthickness=1, highlightbackground="white")
        self.account_context_menu = menu

        def _btn(text, cmd):
            b = tk.Button(menu, text=text, anchor="w", relief="flat",
                          bg=self.BG_PANEL, fg=self.FG_TEXT,
                          activebackground=self.BG_SURFACE, activeforeground=self.FG_TEXT,
                          font=(self.FONT_FAMILY, 9), bd=0, highlightthickness=0,
                          command=lambda: [self.hide_account_context_menu(), cmd()])
            b.pack(fill="x", padx=2, pady=1)

        _btn("Rename Group", lambda: self._rename_group_dialog(group_name))
        _btn("Delete Group", lambda: self._delete_group(group_name))

        menu.geometry(f"+{event.x_root}+{event.y_root}")
        menu.update_idletasks()
        if False:
            menu.attributes("-topmost", True)
        menu.bind("<FocusOut>", lambda e: self.hide_account_context_menu())
        self.root.bind("<Button-1>", lambda e: self.hide_account_context_menu(), add="+")

    def _create_group_dialog(self):
        """Dialog to create a new group."""
        dlg = tk.Toplevel(self.root)
        self.apply_window_icon(dlg)
        dlg.title("Create Group")
        dlg.geometry("300x120")
        dlg.configure(bg=self.BG_DARK)
        dlg.resizable(False, False)
        dlg.transient(self.root)

        dlg.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - 300) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - 120) // 2
        dlg.geometry(f"+{x}+{y}")

        if False:
            dlg.attributes("-topmost", True)

        ttk.Label(dlg, text="Group Name:", style="Dark.TLabel").pack(padx=10, pady=(10, 2), anchor="w")
        entry = ttk.Entry(dlg, style="Dark.TEntry")
        entry.pack(fill="x", padx=10)
        entry.focus_set()

        def do_create(e=None):
            name = entry.get().strip()
            if not name:
                return
            groups = self._get_groups()
            if name in groups:
                messagebox.showwarning("Exists", f"Group '{name}' already exists.", parent=dlg)
                return
            groups[name] = []
            self._save_groups(groups)
            dlg.destroy()
            self.refresh_accounts()

        entry.bind("<Return>", do_create)
        ttk.Button(dlg, text="Create", style="Dark.TButton", command=do_create).pack(pady=10)

    def _rename_group_dialog(self, old_name):
        """Dialog to rename a group."""
        dlg = tk.Toplevel(self.root)
        self.apply_window_icon(dlg)
        dlg.title("Rename Group")
        dlg.geometry("300x120")
        dlg.configure(bg=self.BG_DARK)
        dlg.resizable(False, False)
        dlg.transient(self.root)

        dlg.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - 300) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - 120) // 2
        dlg.geometry(f"+{x}+{y}")

        if False:
            dlg.attributes("-topmost", True)

        ttk.Label(dlg, text="New Name:", style="Dark.TLabel").pack(padx=10, pady=(10, 2), anchor="w")
        entry = ttk.Entry(dlg, style="Dark.TEntry")
        entry.pack(fill="x", padx=10)
        entry.insert(0, old_name)
        entry.select_range(0, tk.END)
        entry.focus_set()

        def do_rename(e=None):
            new_name = entry.get().strip()
            if not new_name or new_name == old_name:
                dlg.destroy()
                return
            groups = self._get_groups()
            if new_name in groups:
                messagebox.showwarning("Exists", f"Group '{new_name}' already exists.", parent=dlg)
                return
            members = groups.pop(old_name, [])
            groups[new_name] = members
            if old_name in self._collapsed_groups:
                self._collapsed_groups.discard(old_name)
                self._collapsed_groups.add(new_name)
            self._save_groups(groups)
            dlg.destroy()
            self.refresh_accounts()

        entry.bind("<Return>", do_rename)
        ttk.Button(dlg, text="Rename", style="Dark.TButton", command=do_rename).pack(pady=10)

    def _delete_group(self, group_name):
        """Delete a group"""
        if not messagebox.askyesno("Delete Group", f"Delete group '{group_name}'?\nAccounts will be ungrouped."):
            return
        groups = self._get_groups()
        groups.pop(group_name, None)
        self._collapsed_groups.discard(group_name)
        self._save_groups(groups)
        self.refresh_accounts()

    def refresh_accounts(self):
        """Refresh the account list"""
        needs_rerender = self.account_list.winfo_width() <= 1
        
        self.account_list.delete(0, tk.END)
        self._list_row_map = []
        groups = self._get_groups()

        grouped_usernames = set()
        for members in groups.values():
            grouped_usernames.update(members)

        for username, data in self.manager.accounts.items():
            if username in grouped_usernames:
                continue
            self._insert_account_row(username, data)

        for gname, members in groups.items():
            collapsed = gname in self._collapsed_groups
            visible_members = [u for u in members if u in self.manager.accounts]
            header_text = self._build_group_header_text(gname, len(visible_members), collapsed)
            idx = self.account_list.size()
            self.account_list.insert(tk.END, header_text)
            self._list_row_map.append(("group_header", gname))
            self.account_list.itemconfig(
                idx,
                fg=self.FG_ACCENT,
                bg=self.BG_PANEL,
                selectbackground=self.BG_MID,
                selectforeground=self.FG_ACCENT,
            )
            if not collapsed:
                for uname in visible_members:
                    self._insert_account_row(uname, self.manager.accounts[uname])

        last_joined = self.settings.get("last_joined_user", "")
        if last_joined:
            for i, (kind, val) in enumerate(self._list_row_map):
                if kind == "account" and val == last_joined:
                    self.account_list.selection_clear(0, tk.END)
                    self.account_list.selection_set(i)
                    self.account_list.see(i)
                    break

        if needs_rerender:
            self.root.after(50, self.refresh_accounts)

    def _insert_account_row(self, username, data):
        """Insert a single account row into the Listbox and _list_row_map."""
        note = data.get('note', '') if isinstance(data, dict) else ''
        cookie_valid = self.cookie_status.get(username)
        if cookie_valid is False:
            display_text = f"\u26a0 {username}"
        else:
            display_text = f"{username}"
        if note:
            display_text += f" \u2022 {note}"
        idx = self.account_list.size()
        self.account_list.insert(tk.END, display_text)
        self._list_row_map.append(("account", username))
        if cookie_valid is False:
            self.account_list.itemconfig(idx, fg="#FFB347")

    def on_account_list_hover(self, event):
        """Show tooltip when hovering over an expired account row"""
        index = self.account_list.nearest(event.y)
        
        if index < 0 or index >= self.account_list.size():
            self.hide_account_tooltip()
            return
        
        if index == self.account_tooltip_last_index:
            return
        
        self.hide_account_tooltip()
        self.account_tooltip_last_index = index
        
        display_text = self.account_list.get(index)
        if not display_text.startswith('\u26a0 '):
            return
        
        username = self.extract_username_from_display(display_text)
        
        def create_tooltip():
            if self.account_tooltip:
                return
            
            x_pos = event.x_root + 15
            y_pos = event.y_root + 15
            
            self.account_tooltip = tk.Toplevel(self.root)
            self.account_tooltip.wm_overrideredirect(True)
            self.account_tooltip.wm_geometry(f"+{x_pos}+{y_pos}")
            
            label = tk.Label(
                self.account_tooltip,
                text=f"Cookie expired for '{username}'.\nPlease remove this account and add it again.",
                bg=self.BG_DARK,
                fg=self.FG_TEXT,
                font=(self.FONT_FAMILY, 9),
                padx=8,
                pady=4,
                relief="solid",
                borderwidth=1
            )
            label.pack()
            
            if False:
                self.account_tooltip.attributes("-topmost", True)
        
        self.account_tooltip_timer = self.root.after(500, create_tooltip)
    
    def on_account_list_leave(self, event):
        """Hide tooltip when leaving the account list"""
        self.hide_account_tooltip()
    
    def hide_account_tooltip(self):
        """Hide the account list tooltip"""
        if self.account_tooltip_timer:
            self.root.after_cancel(self.account_tooltip_timer)
            self.account_tooltip_timer = None
        
        if self.account_tooltip:
            self.account_tooltip.destroy()
            self.account_tooltip = None
        
        self.account_tooltip_last_index = None
    
    def extract_username_from_display(self, display_text):
        """Extract username from display text (handles indicators like ⚠)"""
        username_part = display_text.split(' • ')[0]
        
        username_part = username_part.strip()
        if username_part.startswith('⚠ '):
            username_part = username_part[2:]
        
        return username_part.strip()
    


    def _save_cookie_status(self, username, is_valid):
        """Update cookie status in memory and persist to accounts file"""
        self.cookie_status[username] = is_valid
        if username in self.manager.accounts and isinstance(self.manager.accounts[username], dict):
            self.manager.accounts[username]['cookie_valid'] = is_valid

    def _watch_discord_logo(self):
        """Background thread: wait for discordlogo.png to appear, then apply it to the UI."""
        if self.discord_btn is not None:
            return
        path = self.discord_logo_path
        if not path:
            return
        for _ in range(60):
            if os.path.exists(path):
                self.root.after(0, self._apply_discord_logo_to_ui)
                return
            time.sleep(0.5)

    def _apply_discord_logo_to_ui(self):
        """Load (or reload) the discord logo and create/update the button."""
        path = self.discord_logo_path
        if not path or not os.path.exists(path):
            return
        try:
            img = tk.PhotoImage(file=path)
            w, h = img.width(), img.height()
            factor = max(1, max(w, h) // 20)
            if factor > 1:
                img = img.subsample(factor, factor)
            self.discord_logo_img = img
        except Exception:
            return
        if self.discord_btn is not None:
            self.discord_btn.config(image=img, bg=self.BG_DARK, activebackground=self.BG_DARK)
        else:
            self.discord_btn = tk.Button(
                self.quick_actions_row,
                image=img,
                bg=self.BG_DARK,
                activebackground=self.BG_DARK,
                relief="flat",
                bd=0,
                cursor="hand2",
                padx=0,
                pady=0,
                highlightthickness=0,
                command=lambda: webbrowser.open("https://discord.gg/xvWK6BkGD6")
            )
            self.discord_btn.pack(side="right")

    def _silent_check_cookies(self):
        """Trigger a background silent cookie check. Safe to call from any thread."""
        if getattr(self, '_cookie_check_running', False):
            return
        threading.Thread(target=self._silent_check_cookies_worker, daemon=True).start()

    def _silent_check_cookies_worker(self):
        """Check all accounts not already known invalid."""
        if getattr(self, '_cookie_check_running', False):
            return
        self._cookie_check_running = True
        try:
            accounts = [u for u in self.manager.accounts
                        if self.cookie_status.get(u) is not False]
            if not accounts:
                return
            changed = False
            for username in accounts:
                try:
                    is_valid = self.manager.validate_account(username)
                    self._save_cookie_status(username, is_valid)
                    changed = True
                except Exception as e:
                    print(f"[ERROR] Cookie check failed for {username}: {e}")
            if changed:
                self.manager.save_accounts()
                self.root.after(0, self.refresh_accounts)
        finally:
            self._cookie_check_running = False
    
    def on_drag_start(self, event):
        """Initiate drag - store position and wait for hold"""
        widget = event.widget
        index = widget.nearest(event.y)
        
        if self.drag_data["hold_timer"]:
            self.root.after_cancel(self.drag_data["hold_timer"])
        
        if index >= 0:
            if index < len(self._list_row_map) and self._list_row_map[index][0] == "group_header":
                widget.selection_clear(0, tk.END)
                try:
                    lb_font = tkfont.Font(font=widget.cget("font"))
                    arrow_zone = max(lb_font.measure(" v "), lb_font.measure(" ^ ")) + 4
                    list_width = widget.winfo_width()
                    if event.x >= list_width - arrow_zone - 4:
                        self._handle_group_header_click(index)
                    else:
                        group_name = self._list_row_map[index][1]
                        for i, (kind, val) in enumerate(self._list_row_map):
                            if kind == "account" and self._get_username_group(val) == group_name:
                                widget.selection_set(i)
                except Exception:
                    self._handle_group_header_click(index)
                return

            self.drag_data["index"] = index
            self.drag_data["item"] = widget.get(index)
            self.drag_data["start_x"] = event.x
            self.drag_data["start_y"] = event.y
            self.drag_data["dragging"] = False
            
            if not False:
                widget.selection_clear(0, tk.END)
                widget.selection_set(index)
            
            self.drag_data["hold_timer"] = self.root.after(500, lambda: self.activate_drag(event))
    
    def activate_drag(self, event):
        """Activate dragging after hold timer"""
        self.drag_data["dragging"] = True
        self.drag_data["hold_timer"] = None
        
        if not self.drag_indicator:
            self.drag_indicator = tk.Toplevel(self.root)
            self.drag_indicator.overrideredirect(True)
            self.drag_indicator.attributes("-alpha", 0.7)
            self.drag_indicator.attributes("-topmost", True)
            
            label = tk.Label(
                self.drag_indicator,
                text=self.drag_data["item"],
                bg=self.BG_LIGHT,
                fg=self.FG_TEXT,
                font=(self.FONT_FAMILY, 10),
                padx=10,
                pady=5,
                relief="raised",
                borderwidth=2
            )
            label.pack()
            
            x = self.root.winfo_pointerx() + 10
            y = self.root.winfo_pointery() + 10
            self.drag_indicator.geometry(f"+{x}+{y}")
    
    def on_drag_motion(self, event):
        """Handle drag motion, show indicator and highlight drop position"""
        if self.drag_data["hold_timer"] and self.drag_data["index"] is not None:
            dx = abs(event.x - self.drag_data["start_x"])
            dy = abs(event.y - self.drag_data["start_y"])
            if dx > 5 or dy > 5:
                self.root.after_cancel(self.drag_data["hold_timer"])
                self.drag_data["hold_timer"] = None
        
        if not self.drag_data["dragging"] or self.drag_data["index"] is None:
            return
        
        widget = event.widget
        
        if self.drag_indicator:
            x = event.x_root + 10
            y = event.y_root + 10
            self.drag_indicator.geometry(f"+{x}+{y}")
        
        index = widget.nearest(event.y)
        if index >= 0:
            if not False:
                widget.selection_clear(0, tk.END)
            widget.selection_set(index)
    
    def on_drag_release(self, event):
        """Release drag and reorder accounts"""
        try:
            if self.drag_data["hold_timer"]:
                self.root.after_cancel(self.drag_data["hold_timer"])
                self.drag_data["hold_timer"] = None
            
            if not self.drag_data["dragging"] or self.drag_data["index"] is None:
                return
            
            widget = event.widget
            drop_index = widget.nearest(event.y)
            drag_index = self.drag_data["index"]
            
            if drop_index >= 0 and drag_index != drop_index:
                if drop_index < len(self._list_row_map) and self._list_row_map[drop_index][0] == "group_header":
                    group_name = self._list_row_map[drop_index][1]
                    if drag_index < len(self._list_row_map) and self._list_row_map[drag_index][0] == "account":
                        username = self._list_row_map[drag_index][1]
                        self._add_account_to_group(username, group_name)
                    return

                ordered_usernames = list(self.manager.accounts.keys())
                
                if drag_index < len(self._list_row_map) and self._list_row_map[drag_index][0] == "account":
                    drag_username = self._list_row_map[drag_index][1]
                else:
                    return
                
                if drag_username not in ordered_usernames:
                    return
                old_pos = ordered_usernames.index(drag_username)
                ordered_usernames.pop(old_pos)
                
                if drop_index < len(self._list_row_map) and self._list_row_map[drop_index][0] == "account":
                    drop_username = self._list_row_map[drop_index][1]
                    if drop_username in ordered_usernames:
                        new_pos = ordered_usernames.index(drop_username)
                        ordered_usernames.insert(new_pos, drag_username)
                    else:
                        ordered_usernames.append(drag_username)
                else:
                    ordered_usernames.append(drag_username)
                
                new_accounts = {}
                for uname in ordered_usernames:
                    new_accounts[uname] = self.manager.accounts[uname]
                
                self.manager.accounts = new_accounts
                self.manager.save_accounts()
                
                self.refresh_accounts()
                
                if not False:
                    widget.selection_clear(0, tk.END)
                    widget.selection_set(drop_index)
        finally:
            if self.drag_indicator:
                self.drag_indicator.destroy()
                self.drag_indicator = None
            
            self.drag_data = {
                "item": None, 
                "index": None, 
                "start_x": 0, 
                "start_y": 0,
                "dragging": False,
                "hold_timer": None
            }
    
    def get_selected_username(self):
        """Get the currently selected username"""
        selection = self.account_list.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select an account first.")
            return None
        
        idx = selection[0]
        if idx < len(self._list_row_map) and self._list_row_map[idx][0] == "group_header":
            group_name = self._list_row_map[idx][1]
            for kind, val in self._list_row_map:
                if kind == "account" and self._get_username_group(val) == group_name:
                    return val
            messagebox.showwarning("Empty Group", f"Group '{group_name}' has no accounts.")
            return None
        
        display_text = self.account_list.get(idx)
        username = self.extract_username_from_display(display_text)
        return username
    
    def add_account(self):
        """
        Add a new account using browser automation
        """
        browser_path, browser_name = self.get_browser_path()
        
        if not browser_path:
            messagebox.showwarning(
                "Browser Required",
                "Add Account requires a browser.\n\n"
                "Please either:\n"
                "• Install Google Chrome, or\n"
                "• Download Chromium in Settings → Tools → Browser Engine"
            )
            return

        messagebox.showinfo("Add Account", f"Browser ({browser_name}) will open for account login.\nPlease log in and wait for the process to complete.")
        
        def add_account_thread():
            """
            Thread function to add account without blocking UI
            """
            try:
                success = self.manager.add_account(1, "https://www.roblox.com/login", "", browser_path)
                self.root.after(0, lambda: self._add_account_complete(success))
            except Exception as e:
                self.root.after(0, lambda: self._add_account_error(str(e)))
        
        thread = threading.Thread(target=add_account_thread, daemon=True)
        thread.start()
    
    def _add_account_complete(self, success):
        """
        Called when account addition completes (on main thread)
        """
        if success:
            self.refresh_accounts()
            messagebox.showinfo("Success", "Account added successfully!")
        else:
            messagebox.showerror("Error", "Failed to add account.\nPlease make sure you completed the login process.")
    
    def _add_account_error(self, error_msg):
        """
        Called when account addition encounters an error (on main thread)
        """
        messagebox.showerror("Error", f"Failed to add account: {error_msg}")
    
    def import_cookie(self):
        """
        Import an account using a .ROBLOSECURITY cookie
        """
        import_window = tk.Toplevel(self.root)
        self.apply_window_icon(import_window)
        import_window.title("Import Cookie")
        import_window.geometry("450x250")
        import_window.configure(bg=self.BG_DARK)
        import_window.resizable(False, False)
        
        self.root.update_idletasks()
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        
        x = main_x + (main_width - 450) // 2
        y = main_y + (main_height - 250) // 2
        import_window.geometry(f"450x250+{x}+{y}")
        
        if False:
            import_window.attributes("-topmost", True)
        
        import_window.transient(self.root)
        import_window.grab_set()
        
        main_frame = ttk.Frame(import_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=20, pady=20)
        
        ttk.Label(
            main_frame,
            text="Import Account from Cookie",
            style="Dark.TLabel",
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w", pady=(0, 15))
        
        ttk.Label(main_frame, text="Cookie(s)", style="Dark.TLabel").pack(anchor="w", pady=(0, 5))
        
        cookie_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        cookie_frame.pack(fill="both", expand=True, pady=(0, 15))
        
        cookie_text = tk.Text(
            cookie_frame,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            height=5,
            wrap="word"
        )
        cookie_text.pack(side="left", fill="both", expand=True)
        
        cookie_scrollbar = ttk.Scrollbar(cookie_frame, command=cookie_text.yview)
        cookie_scrollbar.pack(side="right", fill="y")
        cookie_text.config(yscrollcommand=cookie_scrollbar.set)
        
        def do_import():
            cookie_input = cookie_text.get("1.0", "end-1c").strip()
            
            if not cookie_input:
                messagebox.showwarning("Missing Information", "Please enter the cookie(s).")
                return
            
            cookies = []
            if "_|WARNING:-" in cookie_input:
                parts = cookie_input.split("_|WARNING:-")
                for part in parts:
                    if part.strip():
                        cookies.append("_|WARNING:-" + part.strip())
            else:
                cookies = [cookie_input]
            
            imported_count = 0
            failed_count = 0
            imported_accounts = []
            
            for cookie in cookies:
                try:
                    success, username = self.manager.import_cookie_account(cookie)
                    if success:
                        imported_count += 1
                        imported_accounts.append(username)
                    else:
                        failed_count += 1
                except Exception as e:
                    failed_count += 1
                    print(f"[ERROR] Failed to import cookie: {e}")
            
            self.refresh_accounts()
            
            if imported_count > 0:
                if imported_count == 1:
                    messagebox.showinfo("Success", f"Account '{imported_accounts[0]}' imported successfully!")
                else:
                    messagebox.showinfo("Success", f"Successfully imported {imported_count} account(s)!\n\n{', '.join(imported_accounts)}")
                import_window.destroy()
            
            if failed_count > 0:
                if imported_count == 0:
                    messagebox.showerror("Error", f"Failed to import {failed_count} cookie(s). Please check the cookies.")
                else:
                    messagebox.showwarning("Partial Success", f"Imported {imported_count} account(s), but {failed_count} failed.")
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x")
        
        ttk.Button(
            button_frame,
            text="Import",
            style="Dark.TButton",
            command=do_import
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Cancel",
            style="Dark.TButton",
            command=import_window.destroy
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))


    def remove_account(self):
        """Remove the selected account(s)"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
            
            if len(usernames) == 1:
                confirm = messagebox.askyesno("Confirm Delete", f"Are you sure you want to delete '{usernames[0]}'?")
            else:
                confirm = messagebox.askyesno("Confirm Delete", f"Are you sure you want to delete {len(usernames)} accounts?\n\n" + "\n".join(usernames))
            
            if confirm:
                for username in usernames:
                    self.manager.delete_account(username)
                self.refresh_accounts()
                messagebox.showinfo("Success", f"{len(usernames)} account(s) deleted successfully!")
        else:
            username = self.get_selected_username()
            if username:
                confirm = messagebox.askyesno("Confirm Delete", f"Are you sure you want to delete '{username}'?")
                if confirm:
                    self.manager.delete_account(username)
                    self.refresh_accounts()
                    messagebox.showinfo("Success", f"Account '{username}' deleted successfully!")

    def validate_account(self):
        """Validate the selected account"""
        username = self.get_selected_username()
        if username:
            is_valid = self.manager.validate_account(username)
            if is_valid:
                messagebox.showinfo("Validation", f"Account '{username}' is valid! ✓")
            else:
                messagebox.showwarning("Validation", f"Account '{username}' is invalid or expired.")
    
    def edit_account_note(self):
        """Edit note for the selected account(s)"""
        if False:
            usernames = self.get_selected_usernames()
            if not usernames:
                return
            
            if len(usernames) == 1:
                username = usernames[0]
                current_note = self.manager.get_account_note(username)
                title_text = f"Edit Note - {username}"
            else:
                username = None
                current_note = ""
                title_text = f"Edit Note - {len(usernames)} accounts"
        else:
            username = self.get_selected_username()
            if not username:
                return
            usernames = [username]
            current_note = self.manager.get_account_note(username)
            title_text = f"Edit Note - {username}"
        
        note_window = tk.Toplevel(self.root)
        self.apply_window_icon(note_window)
        note_window.title(title_text)
        note_window.geometry("450x220")
        note_window.configure(bg=self.BG_DARK)
        note_window.resizable(False, False)
        
        self.root.update_idletasks()
        main_x = self.root.winfo_x()
        main_y = self.root.winfo_y()
        main_width = self.root.winfo_width()
        main_height = self.root.winfo_height()
        
        x = main_x + (main_width - 450) // 2
        y = main_y + (main_height - 220) // 2
        note_window.geometry(f"450x220+{x}+{y}")
        
        if False:
            note_window.attributes("-topmost", True)
        
        note_window.transient(self.root)
        note_window.grab_set()
        
        main_frame = ttk.Frame(note_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=20, pady=20)
        
        if len(usernames) == 1:
            label_text = f"Edit note for '{usernames[0]}'"
        else:
            label_text = f"Edit note for {len(usernames)} accounts"
        
        ttk.Label(
            main_frame,
            text=label_text,
            style="Dark.TLabel",
            font=("Segoe UI", 11, "bold")
        ).pack(anchor="w", pady=(0, 10))
        
        ttk.Label(main_frame, text="Note:", style="Dark.TLabel").pack(anchor="w", pady=(0, 5))
        
        note_text = tk.Text(
            main_frame,
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            height=3,
            wrap="word"
        )
        note_text.pack(fill="both", expand=True, pady=(0, 15))
        note_text.insert("1.0", current_note)
        note_text.focus_set()
        
        def save_note():
            new_note = note_text.get("1.0", "end-1c").strip()
            for uname in usernames:
                self.manager.set_account_note(uname, new_note)
            self.refresh_accounts()
            if len(usernames) == 1:
                messagebox.showinfo("Success", f"Note updated for '{usernames[0]}'!")
            else:
                messagebox.showinfo("Success", f"Note updated for {len(usernames)} accounts!")
            note_window.destroy()
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x")
        
        ttk.Button(
            button_frame,
            text="Save",
            style="Dark.TButton",
            command=save_note
        ).pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Cancel",
            style="Dark.TButton",
            command=note_window.destroy
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))

    def show_account_context_menu(self, event):
        """Show context menu on right-click"""
        index = self.account_list.nearest(event.y)

        if index >= 0:
            bbox = self.account_list.bbox(index)
            if bbox is None or event.y > bbox[1] + bbox[3]:
                index = -1

        if index < 0 or index >= len(self._list_row_map):
            self._show_empty_context_menu(event)
            return

        kind, val = self._list_row_map[index]

        if kind == "group_header":
            self._show_group_context_menu(event, val)
            return

        self.account_list.selection_clear(0, tk.END)
        self.account_list.selection_set(index)
        self.account_list.activate(index)
        
        username = val
        account = self.manager.accounts.get(username)
        
        if not account:
            return
        
        if not isinstance(account, dict):
            return
        
        user_id = account.get('user_id', 0)
        password = account.get('password', '')
        
        if hasattr(self, 'account_context_menu') and self.account_context_menu is not None:
            try:
                self.account_context_menu.destroy()
            except:
                pass
        
        self.account_context_menu = tk.Toplevel(self.root)
        self.account_context_menu.overrideredirect(True)
        self.account_context_menu.configure(bg=self.BG_PANEL, highlightthickness=1, highlightbackground="white")
        
        def copy_to_clipboard(text):
            try:
                win32clipboard.OpenClipboard()
                win32clipboard.EmptyClipboard()
                win32clipboard.SetClipboardText(str(text), win32clipboard.CF_UNICODETEXT)
                win32clipboard.CloseClipboard()
            except Exception:
                self.root.clipboard_clear()
                self.root.clipboard_append(str(text))
                self.root.update()
            self.hide_account_context_menu()
        
        def hide_menu():
            self.hide_account_context_menu()
        
        username_btn = tk.Button(
            self.account_context_menu,
            text=f"Copy Username",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=lambda: copy_to_clipboard(username)
        )
        username_btn.pack(fill="x", padx=2, pady=1)
        
        if user_id:
            userid_btn = tk.Button(
                self.account_context_menu,
                text=f"Copy User ID",
                anchor="w",
                relief="flat",
                bg=self.BG_PANEL,
                fg=self.FG_TEXT,
                activebackground=self.BG_SURFACE,
                activeforeground=self.FG_TEXT,
                font=(self.FONT_FAMILY, 9),
                bd=0,
                highlightthickness=0,
                command=lambda: copy_to_clipboard(user_id)
            )
        else:
            userid_btn = tk.Button(
                self.account_context_menu,
                text=f"Copy User ID",
                anchor="w",
                relief="flat",
                bg=self.BG_PANEL,
                fg="#666666",
                font=(self.FONT_FAMILY, 9),
                bd=0,
                highlightthickness=0,
                state="disabled"
            )
        userid_btn.pack(fill="x", padx=2, pady=1)
        
        if password:
            password_btn = tk.Button(
                self.account_context_menu,
                text=f"Copy Password",
                anchor="w",
                relief="flat",
                bg=self.BG_PANEL,
                fg=self.FG_TEXT,
                activebackground=self.BG_SURFACE,
                activeforeground=self.FG_TEXT,
                font=(self.FONT_FAMILY, 9),
                bd=0,
                highlightthickness=0,
                command=lambda: copy_to_clipboard(password)
            )
        else:
            password_btn = tk.Button(
                self.account_context_menu,
                text=f"Copy Password",
                anchor="w",
                relief="flat",
                bg=self.BG_PANEL,
                fg="#666666",
                font=(self.FONT_FAMILY, 9),
                bd=0,
                highlightthickness=0,
                state="disabled"
            )
        password_btn.pack(fill="x", padx=2, pady=1)
        
        separator = tk.Frame(self.account_context_menu, height=1, bg="#666666")
        separator.pack(fill="x", padx=2, pady=2)
        
        def check_single_cookie():
            self.hide_account_context_menu()
            print(f"[INFO] Checking cookie for {username}...")
            
            def check_thread():
                try:
                    is_valid = self.manager.validate_account(username)
                    self._save_cookie_status(username, is_valid)
                    self.manager.save_accounts()
                    self.root.after(0, lambda: self.refresh_accounts())
                    
                    if is_valid:
                        self.root.after(0, lambda: messagebox.showinfo(
                            "Cookie Valid",
                            f"Cookie for '{username}' is valid!"
                        ))
                    else:
                        self.root.after(0, lambda: messagebox.showwarning(
                            "Cookie Expired",
                            f"⚠ Cookie for '{username}' is expired or invalid!"
                        ))
                except Exception as e:
                    print(f"[ERROR] Failed to check cookie: {e}")
                    self._save_cookie_status(username, None)
                    self.manager.save_accounts()
                    self.root.after(0, lambda: messagebox.showerror(
                        "Check Failed",
                        f"Failed to check cookie for '{username}':\\n{str(e)}"
                    ))
            
            thread = threading.Thread(target=check_thread, daemon=True)
            thread.start()
        
        check_cookie_btn = tk.Button(
            self.account_context_menu,
            text="Check Cookie",
            anchor="w",
            relief="flat",
            bg=self.BG_PANEL,
            fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE,
            activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9),
            bd=0,
            highlightthickness=0,
            command=check_single_cookie
        )
        check_cookie_btn.pack(fill="x", padx=2, pady=1)
        
        group_sep = tk.Frame(self.account_context_menu, height=1, bg="#666666")
        group_sep.pack(fill="x", padx=2, pady=2)

        current_group = self._get_username_group(username)

        if current_group:
            remove_grp_btn = tk.Button(
                self.account_context_menu,
                text=f"Remove from \"{current_group}\"",
                anchor="w", relief="flat",
                bg=self.BG_PANEL, fg=self.FG_TEXT,
                activebackground=self.BG_SURFACE, activeforeground=self.FG_TEXT,
                font=(self.FONT_FAMILY, 9), bd=0, highlightthickness=0,
                command=lambda: [self.hide_account_context_menu(), self._remove_account_from_group(username)]
            )
            remove_grp_btn.pack(fill="x", padx=2, pady=1)

        create_grp_btn = tk.Button(
            self.account_context_menu,
            text="Create Group",
            anchor="w", relief="flat",
            bg=self.BG_PANEL, fg=self.FG_TEXT,
            activebackground=self.BG_SURFACE, activeforeground=self.FG_TEXT,
            font=(self.FONT_FAMILY, 9), bd=0, highlightthickness=0,
            command=lambda: [self.hide_account_context_menu(), self._create_group_dialog()]
        )
        create_grp_btn.pack(fill="x", padx=2, pady=1)

        self.account_context_menu.geometry(f"+{event.x_root}+{event.y_root}")
        self.account_context_menu.update_idletasks()
        
        if False:
            self.account_context_menu.attributes("-topmost", True)
        
        self.account_context_menu.bind("<FocusOut>", lambda e: self.hide_account_context_menu())
        self.root.bind("<Button-1>", lambda e: self.hide_account_context_menu(), add="+")
    
    def hide_account_context_menu(self):
        """Hide the account context menu"""
        if hasattr(self, 'account_context_menu') and self.account_context_menu is not None:
            try:
                self.account_context_menu.destroy()
            except:
                pass
            self.account_context_menu = None

    def _show_empty_context_menu(self, event):
        if hasattr(self, 'account_context_menu') and self.account_context_menu is not None:
            try: self.account_context_menu.destroy()
            except: pass

        menu = tk.Toplevel(self.root)
        menu.overrideredirect(True)
        menu.configure(bg=self.BG_PANEL, highlightthickness=1, highlightbackground="white")
        self.account_context_menu = menu

        btn = tk.Button(menu, text="Create Group", anchor="w", relief="flat",
                        bg=self.BG_PANEL, fg=self.FG_TEXT,
                        activebackground=self.BG_SURFACE, activeforeground=self.FG_TEXT,
                        font=(self.FONT_FAMILY, 9), bd=0, highlightthickness=0,
                        command=lambda: [self.hide_account_context_menu(), self._create_group_dialog()])
        btn.pack(fill="x", padx=2, pady=1)

        menu.geometry(f"+{event.x_root}+{event.y_root}")
        menu.update_idletasks()
        if False:
            menu.attributes("-topmost", True)
        menu.bind("<FocusOut>", lambda e: self.hide_account_context_menu())
        self.root.bind("<Button-1>", lambda e: self.hide_account_context_menu(), add="+")



    def _run_encryption_switch(self):
        """Run the encryption method switch process"""
        
        current_accounts = self.manager.accounts.copy()
        
        self.manager.encryption_config.reset_encryption()
        self.manager.encryptor = None
        self.manager.accounts = current_accounts
        self.manager.save_accounts()
        
        self.root.destroy()
        
        setup_ui = EncryptionSetupUI()
        result = setup_ui.setup_encryption_ui()
        
        if setup_ui.should_exit:
            sys.exit(0)
        
        
        try:
            new_method = setup_ui.encryption_config.get_encryption_method()
            
            if new_method == 'password':
                if result is None:
                    raise ValueError("Password setup failed - no password returned")
                new_manager = RobloxAccountManager(password=result)
            else:
                new_manager = RobloxAccountManager()
            
            new_manager.save_accounts()
            
            messagebox.showinfo("Success", "Encryption method switched successfully!\nYour accounts have been re-encrypted.")
            
            new_root = tk.Tk()
            app = AccountManagerUI(new_root, new_manager)
            new_root.mainloop()
            
        except Exception as e:
            print(f"[ERROR] Failed to switch encryption: {e}")
            traceback.print_exc()
            messagebox.showerror("Error", f"Failed to switch encryption: {e}")
            sys.exit(1)

    def start_instances_monitoring(self):
        """Start background monitoring of active Roblox instances"""
        if self.instances_monitor_thread and self.instances_monitor_thread.is_alive():
            return
        
        self.instances_monitor_stop.clear()
        self.instances_monitor_thread = threading.Thread(target=self._instances_monitor_worker, daemon=True)
        self.instances_monitor_thread.start()
        print("[INFO] Active Instances background monitoring started")
    
    def stop_instances_monitoring(self):
        """Stop background monitoring of active Roblox instances"""
        if self.instances_monitor_thread:
            self.instances_monitor_stop.set()
            self.instances_monitor_thread = None
            self.instances_data.clear()
            self.instances_pids.clear()
            print("[INFO] Active Instances background monitoring stopped")
    
    def _instances_monitor_worker(self):
        """Background thread that continuously monitors Roblox instances"""
        last_memory_refresh = 0.0
        poll_interval_seconds = 4
        failed_retry_delay_seconds = 8

        while not self.instances_monitor_stop.is_set():
            try:
                new_pids = set()
                processes = []
                pid_to_proc = {}
                
                for proc in psutil.process_iter(['pid', 'name', 'create_time', 'memory_info']):
                    try:
                        if proc.info['name'].lower() == 'robloxplayerbeta.exe':
                            pid = proc.info['pid']
                            if self._is_valid_roblox_game_client(pid, 'robloxplayerbeta.exe'):
                                new_pids.add(pid)
                                processes.append(proc)
                                pid_to_proc[pid] = proc
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                current_time = time.time()
                for pid in list(self.instances_failed_pids.keys()):
                    if pid not in new_pids:
                        del self.instances_failed_pids[pid]
                
                if new_pids != self.instances_pids:
                    print(f"[INFO] Active Instances: PID change detected. Old: {self.instances_pids}, New: {new_pids}")
                    self.instances_pids = new_pids.copy()

                    old_data_by_pid = {entry['pid']: entry for entry in self.instances_data}
                    new_data = []

                    for proc in processes:
                        pid = proc.info['pid']
                        
                        try:
                            memory_mb = proc.info['memory_info'].rss / 1024 / 1024
                            create_time = proc.info['create_time']
                        except:
                            memory_mb = 0
                            create_time = 0

                        prev = old_data_by_pid.get(pid, {})
                        new_data.append({
                            "pid": pid,
                            "user_id": prev.get("user_id"),
                            "username": prev.get("username"),
                            "avatar_url": prev.get("avatar_url"),
                            "create_time": create_time,
                            "memory_mb": memory_mb,
                        })

                    self.instances_data = new_data
                    self.instances_data_updated = True

                if current_time - last_memory_refresh >= poll_interval_seconds:
                    last_memory_refresh = current_time
                    for entry in self.instances_data:
                        try:
                            proc = pid_to_proc.get(entry["pid"]) or psutil.Process(entry["pid"])
                            entry["memory_mb"] = proc.memory_info().rss / 1024 / 1024
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            pass

                unresolved_entry = None
                for entry in self.instances_data:
                    if entry.get("user_id"):
                        continue
                    pid = entry.get("pid")
                    failed_data = self.instances_failed_pids.get(pid)
                    if failed_data and (current_time - failed_data[0] < failed_retry_delay_seconds):
                        continue
                    unresolved_entry = entry
                    break

                if unresolved_entry:
                    pid = unresolved_entry["pid"]
                    used_logs = set()
                    user_id, _ = self._get_user_id_from_pid(pid, used_logs)

                    if user_id:
                        username = None
                        avatar_url = None

                        if user_id in self.instances_cache["user_id_to_username"]:
                            username = self.instances_cache["user_id_to_username"][user_id]
                        else:
                            for account in self.manager.accounts:
                                stored_uid = self.manager.accounts[account].get("user_id")
                                if stored_uid == user_id or stored_uid == str(user_id):
                                    username = account
                                    self.instances_cache["user_id_to_username"][user_id] = username
                                    break

                            if not username:
                                username = RobloxAPI.get_username_from_user_id(user_id)
                                if username:
                                    self.instances_cache["user_id_to_username"][user_id] = username
                                    for account in self.manager.accounts:
                                        if account == username:
                                            self.manager.accounts[account]["user_id"] = str(user_id)
                                            self.manager.save_accounts()
                                            break

                        if user_id in self.instances_cache["user_id_to_avatar"]:
                            avatar_url = self.instances_cache["user_id_to_avatar"][user_id]
                        else:
                            avatar_url = RobloxAPI.get_user_avatar_url(user_id, "150x150")
                            if avatar_url:
                                self.instances_cache["user_id_to_avatar"][user_id] = avatar_url

                        unresolved_entry["user_id"] = user_id
                        unresolved_entry["username"] = username
                        unresolved_entry["avatar_url"] = avatar_url
                        if pid in self.instances_failed_pids:
                            del self.instances_failed_pids[pid]
                        self.instances_data_updated = True
                    else:
                        self.instances_failed_pids[pid] = (
                            current_time,
                            unresolved_entry.get("create_time", 0),
                            unresolved_entry.get("memory_mb", 0),
                        )
                
            except Exception as e:
                print(f"[ERROR] Active Instances monitor error: {e}")
            
            self.instances_monitor_stop.wait(poll_interval_seconds)
    
    def open_active_instances_window(self):
        """Open window showing all active Roblox instances with pre-cached data"""
        instances_window = tk.Toplevel(self.root)
        self.apply_window_icon(instances_window)
        instances_window.title("Active Roblox Instances")
        instances_window.geometry("400x400")
        instances_window.configure(bg=self.BG_DARK)
        instances_window.resizable(False, False)
        
        if False:
            instances_window.attributes("-topmost", True)
        
        instances_window.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (instances_window.winfo_width() // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (instances_window.winfo_height() // 2)
        instances_window.geometry(f"+{x}+{y}")
        
        main_frame = ttk.Frame(instances_window, style="Dark.TFrame")
        main_frame.pack(fill="both", expand=True, padx=15, pady=15)
        
        header_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        header_frame.pack(fill="x", pady=(0, 10))
        
        title_label = ttk.Label(
            header_frame,
            text="Active Roblox Instances",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 12, "bold")
        )
        title_label.pack(side="left")
        
        monitoring_enabled = tk.BooleanVar(value=self.settings.get("active_instances_monitoring", False))
        
        monitor_checkbox = ttk.Checkbutton(
            header_frame,
            text="Enable Active Instances",
            variable=monitoring_enabled,
            style="Dark.TCheckbutton"
        )
        monitor_checkbox.pack(side="right")
        
        canvas_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        canvas_frame.pack(fill="both", expand=True)
        
        canvas = tk.Canvas(canvas_frame, bg=self.BG_DARK, highlightthickness=0)
        scrollbar = ttk.Scrollbar(canvas_frame, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas, style="Dark.TFrame")
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        status_label = ttk.Label(
            main_frame,
            text="Loading instances...",
            style="Dark.TLabel",
            font=(self.FONT_FAMILY, 9)
        )
        status_label.pack(pady=(10, 0))
        
        window_active = [True]
        refresh_timer = [None]
        last_rendered_pids = [set()]
        instance_widgets = {}
        
        def on_window_close():
            window_active[0] = False
            if refresh_timer[0]:
                instances_window.after_cancel(refresh_timer[0])
            instances_window.destroy()
        
        instances_window.protocol("WM_DELETE_WINDOW", on_window_close)
        
        def render_instances():
            """Render the pre-cached instance data to the UI"""
            if not window_active[0]:
                return
            
            if not monitoring_enabled.get():
                return
            
            data = list(self.instances_data)
            current_pids_set = {d["pid"] for d in data}
            
            data_was_updated = self.instances_data_updated
            if data_was_updated:
                self.instances_data_updated = False
            
            if current_pids_set != last_rendered_pids[0] or data_was_updated:
                reason = "PIDs changed" if current_pids_set != last_rendered_pids[0] else "data updated"
                print(f"[INFO] Active Instances window: {reason}, rebuilding UI")
                last_rendered_pids[0] = current_pids_set
                instance_widgets.clear()
                
                for widget in scrollable_frame.winfo_children():
                    widget.destroy()
                
                if not data:
                    status_label.config(text="No active Roblox instances found")
                    ttk.Label(
                        scrollable_frame,
                        text="No active Roblox instances",
                        style="Dark.TLabel",
                        font=(self.FONT_FAMILY, 10)
                    ).pack(pady=20)
                else:
                    status_label.config(text=f"Found {len(data)} instance(s) - Last updated: {datetime.now().strftime('%H:%M:%S')}")
                    
                    for entry in data:
                        pid = entry["pid"]
                        user_id = entry["user_id"]
                        username = entry["username"]
                        avatar_url = entry["avatar_url"]
                        create_time = entry["create_time"]
                        memory_mb = entry["memory_mb"]
                        
                        instance_frame = tk.Frame(
                            scrollable_frame, bg=self.BG_PANEL, relief="solid", borderwidth=1
                        )
                        instance_frame.pack(fill="x", pady=5, padx=5)
                        
                        inner_frame = tk.Frame(instance_frame, bg=self.BG_MID)
                        inner_frame.pack(fill="x", padx=10, pady=10)
                        
                        try:
                            ct = datetime.fromtimestamp(create_time)
                            uptime = datetime.now() - ct
                            uptime_str = f"{int(uptime.total_seconds() // 3600)}h {int((uptime.total_seconds() % 3600) // 60)}m"
                        except:
                            uptime_str = "Unknown"
                        
                        if username:
                            avatar_label = tk.Label(inner_frame, bg=self.BG_MID)
                            avatar_label.pack(side="left", padx=(0, 15))
                            
                            if user_id and user_id in self.instances_cache["user_id_to_photo"]:
                                photo = self.instances_cache["user_id_to_photo"][user_id]
                                avatar_label.config(image=photo)
                                avatar_label.image = photo
                            else:
                                avatar_label.config(text="...", font=(self.FONT_FAMILY, 24), fg=self.FG_TEXT)
                                
                                def download_avatar(uid, url, label, win):
                                    try:
                                        if url:
                                            response = requests.get(url, timeout=5)
                                            if response.status_code == 200:
                                                img_data = BytesIO(response.content)
                                                img = Image.open(img_data)
                                                img = img.resize((70, 70), Image.Resampling.LANCZOS)
                                                photo = ImageTk.PhotoImage(img)
                                                self.instances_cache["user_id_to_photo"][uid] = photo
                                                def update_label():
                                                    try:
                                                        if window_active[0] and label.winfo_exists():
                                                            label.config(image=photo)
                                                            label.image = photo
                                                    except:
                                                        pass
                                                win.after(0, update_label)
                                                return
                                        def update_fallback():
                                            try:
                                                if window_active[0] and label.winfo_exists():
                                                    label.config(text="[?]", font=(self.FONT_FAMILY, 24), fg=self.FG_TEXT)
                                            except:
                                                pass
                                        win.after(0, update_fallback)
                                    except Exception as e:
                                        print(f"[ERROR] Failed to load avatar for user {uid}: {e}")
                                        def update_error():
                                            try:
                                                if window_active[0] and label.winfo_exists():
                                                    label.config(text="[?]", font=(self.FONT_FAMILY, 24), fg=self.FG_TEXT)
                                            except:
                                                pass
                                        win.after(0, update_error)
                                
                                if user_id and avatar_url:
                                    threading.Thread(target=download_avatar, args=(user_id, avatar_url, avatar_label, instances_window), daemon=True).start()
                                else:
                                    avatar_label.config(text="[?]", font=(self.FONT_FAMILY, 24), fg=self.FG_TEXT)
                            
                            info_frame = tk.Frame(inner_frame, bg=self.BG_MID)
                            info_frame.pack(side="left", fill="both", expand=True)
                            
                            tk.Label(info_frame, text=username, bg=self.BG_PANEL, fg=self.FG_TEXT,
                                     font=(self.FONT_FAMILY, 12, "bold"), anchor="w").pack(anchor="w")
                            
                            details1_frame = tk.Frame(info_frame, bg=self.BG_MID)
                            details1_frame.pack(anchor="w", pady=(2, 0))
                            tk.Label(details1_frame, text=f"PID: {pid}", bg=self.BG_PANEL, fg=self.FG_TEXT,
                                     font=(self.FONT_FAMILY, 9), anchor="w").pack(side="left", padx=(0, 15))
                            tk.Label(details1_frame, text=f"User ID: {user_id}", bg=self.BG_PANEL, fg=self.FG_TEXT,
                                     font=(self.FONT_FAMILY, 9), anchor="w").pack(side="left")
                            
                            details2_frame = tk.Frame(info_frame, bg=self.BG_MID)
                            details2_frame.pack(anchor="w", pady=(2, 0))
                            uptime_label = tk.Label(details2_frame, text=f"Uptime: {uptime_str}", bg=self.BG_PANEL, fg="#90EE90",
                                     font=(self.FONT_FAMILY, 9), anchor="w")
                            uptime_label.pack(side="left", padx=(0, 15))
                            memory_label = tk.Label(details2_frame, text=f"Memory: {memory_mb:.0f} MB", bg=self.BG_PANEL, fg="#87CEEB",
                                     font=(self.FONT_FAMILY, 9), anchor="w")
                            memory_label.pack(side="left")
                            
                            instance_widgets[pid] = {'uptime_label': uptime_label, 'memory_label': memory_label, 'create_time': create_time}
                        elif user_id:
                            tk.Label(inner_frame, text=f"PID: {pid} - Failed to get username (Uptime: {uptime_str})",
                                     bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 10)).pack()
                        else:
                            tk.Label(inner_frame, text=f"PID: {pid} - Failed to get user ID (Uptime: {uptime_str}, Memory: {memory_mb:.0f} MB)",
                                     bg=self.BG_PANEL, fg=self.FG_TEXT, font=(self.FONT_FAMILY, 10)).pack()
            else:
                if data:
                    status_label.config(text=f"Found {len(data)} instance(s) - Last updated: {datetime.now().strftime('%H:%M:%S')}")
                    
                    for entry in data:
                        pid = entry["pid"]
                        if pid in instance_widgets:
                            widgets = instance_widgets[pid]
                            
                            try:
                                create_time = widgets['create_time']
                                ct = datetime.fromtimestamp(create_time)
                                uptime = datetime.now() - ct
                                uptime_str = f"{int(uptime.total_seconds() // 3600)}h {int((uptime.total_seconds() % 3600) // 60)}m"
                                if widgets['uptime_label'].winfo_exists():
                                    widgets['uptime_label'].config(text=f"Uptime: {uptime_str}")
                            except:
                                pass
                            
                            try:
                                memory_mb = entry.get("memory_mb", 0)
                                if widgets['memory_label'].winfo_exists():
                                    widgets['memory_label'].config(text=f"Memory: {memory_mb:.0f} MB")
                            except:
                                pass
            
            if window_active[0] and monitoring_enabled.get():
                refresh_timer[0] = instances_window.after(2000, render_instances)
        
        def toggle_monitoring():
            enabled = monitoring_enabled.get()
            self.settings["active_instances_monitoring"] = enabled
            self.save_settings()
            print(f"[INFO] Active Instances {'enabled' if enabled else 'disabled'}")
            if enabled:
                last_rendered_pids[0] = set()
                instance_widgets.clear()
                for widget in scrollable_frame.winfo_children():
                    widget.destroy()
                
                self.start_instances_monitoring()
                refresh_btn.config(state="normal")
                status_label.config(text="Starting monitoring...")
                render_instances()
            else:
                self.stop_instances_monitoring()
                refresh_btn.config(state="disabled")
                if refresh_timer[0]:
                    instances_window.after_cancel(refresh_timer[0])
                    refresh_timer[0] = None
                for widget in scrollable_frame.winfo_children():
                    widget.destroy()
                status_label.config(text="Active Instances disabled")
                ttk.Label(
                    scrollable_frame,
                    text="Enable the checkbox to start monitoring",
                    style="Dark.TLabel",
                    font=(self.FONT_FAMILY, 10)
                ).pack(pady=20)
        
        monitor_checkbox.config(command=toggle_monitoring)
        
        button_frame = ttk.Frame(main_frame, style="Dark.TFrame")
        button_frame.pack(fill="x", pady=(10, 0))
        
        refresh_btn = ttk.Button(
            button_frame,
            text="Refresh Now",
            style="Dark.TButton",
            command=render_instances,
            state="normal" if monitoring_enabled.get() else "disabled"
        )
        refresh_btn.pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        ttk.Button(
            button_frame,
            text="Close",
            style="Dark.TButton",
            command=on_window_close
        ).pack(side="left", fill="x", expand=True, padx=(5, 0))
        
        if monitoring_enabled.get():
            render_instances()
        else:
            status_label.config(text="Active Instances disabled")
            ttk.Label(
                scrollable_frame,
                text="Enable the checkbox to start monitoring",
                style="Dark.TLabel",
                font=(self.FONT_FAMILY, 10)
            ).pack(pady=20)
  


    def start_rename_monitoring(self):
        """Start monitoring and renaming Roblox windows"""
        if self.rename_thread and self.rename_thread.is_alive():
            return
        
        self.rename_stop_event.clear()
        self.renamed_pids.clear()
        self.rename_thread = threading.Thread(target=self._rename_monitoring_worker, daemon=True)
        self.rename_thread.start()
        print("[INFO] Rename monitoring started")
    
    def stop_rename_monitoring(self):
        """Stop rename monitoring"""
        if self.rename_thread:
            self.rename_stop_event.set()
            self.rename_thread = None
            self.renamed_pids.clear()
            print("[INFO] Rename monitoring stopped")
    
    def _rename_monitoring_worker(self):
        """Monitor for new Roblox PIDs and renames them"""
        while not self.rename_stop_event.is_set():
            try:
                current_pids = set()
                for proc in psutil.process_iter(['pid', 'name']):
                    try:
                        if proc.info['name'] and proc.info['name'].lower() == 'robloxplayerbeta.exe':
                            pid = proc.info['pid']
                            if self._is_valid_roblox_game_client(pid, 'robloxplayerbeta.exe'):
                                current_pids.add(pid)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                new_pids = current_pids - self.renamed_pids
                
                for pid in new_pids:
                    if self.rename_stop_event.is_set():
                        break
                    
                    user_id, _ = self._get_user_id_from_pid(pid)
                    
                    if user_id:
                        username = RobloxAPI.get_username_from_user_id(user_id)
                        
                        if username:
                            self._rename_roblox_window(pid, username)
                            self.renamed_pids.add(pid)
                            print(f"[INFO] Renamed Roblox window for PID {pid} to '{username}'")
                    
                    time.sleep(0.5)
                
                self.renamed_pids = self.renamed_pids.intersection(current_pids)
                
            except Exception as e:
                print(f"[ERROR] Error in rename monitoring: {e}")
            
            time.sleep(2)
    
    def _rename_roblox_window(self, pid, username):
        """Rename a Roblox window by PID"""
        try:
            def enum_windows_callback(hwnd, pid_target):
                _, found_pid = win32process.GetWindowThreadProcessId(hwnd)
                if found_pid == pid_target:
                    if win32gui.IsWindowVisible(hwnd):
                        current_title = win32gui.GetWindowText(hwnd)
                        if 'roblox' in current_title.lower():
                            win32gui.SetWindowText(hwnd, username)
                            return False
                return True
            
            win32gui.EnumWindows(enum_windows_callback, pid)
        except Exception as e:
            print(f"[ERROR] Failed to rename window for PID {pid}: {e}")
    


    def _get_exe_description(self, pid):
        try:
            proc = psutil.Process(pid)
            exe = proc.exe()
            translations = win32api.GetFileVersionInfo(exe, r'\VarFileInfo\Translation')
            lang, codepage = translations[0]
            key = f'\\StringFileInfo\\{lang:04X}{codepage:04X}\\FileDescription'
            return win32api.GetFileVersionInfo(exe, key) or ""
        except Exception:
            return ""

    def _is_valid_roblox_game_client(self, pid, process_name_lower=None):
        try:
            if process_name_lower is None:
                try:
                    process = psutil.Process(pid)
                    process_name_lower = process.name().lower()
                except:
                    return False

            if process_name_lower != "robloxplayerbeta.exe":
                return False

            desc = self._get_exe_description(pid)
            if desc:
                return "roblox" in desc.lower()

            return True

        except Exception:
            return process_name_lower == "robloxplayerbeta.exe" if process_name_lower else False
    
    def _get_user_id_from_pid(self, pid, used_logs=None):
        """Get user ID from a Roblox process PID"""
        if used_logs is None:
            used_logs = set()
            
        try:
            process = psutil.Process(pid)
            if not (process.is_running() and process.name().lower() == "robloxplayerbeta.exe"):
                return None, None
            
            create_time_local = datetime.fromtimestamp(process.create_time())
            create_time_utc = datetime.fromtimestamp(process.create_time(), tz=timezone.utc).replace(tzinfo=None)
            
            logs_dir = os.path.join(os.getenv("LOCALAPPDATA"), "Roblox", "logs")
            if not os.path.exists(logs_dir):
                return None, None
            
            time_window = timedelta(seconds=10)
            matching_logs = []
            
            for filename in os.listdir(logs_dir):
                if not filename.endswith("_last.log"):
                    continue
                
                full_path = os.path.join(logs_dir, filename)
                
                if full_path in used_logs:
                    continue
                
                match = re.search(r'(\d{8}T\d{6}Z)', filename)
                if not match:
                    continue
                
                timestamp_str = match.group(1)
                try:
                    log_time = datetime.strptime(timestamp_str, "%Y%m%dT%H%M%SZ")
                    time_diff = (log_time - create_time_utc).total_seconds()
                    
                    if 0 <= time_diff <= 10:
                        matching_logs.append((time_diff, full_path, log_time))
                except ValueError:
                    continue
            
            matching_logs.sort(key=lambda x: x[0])
            
            for time_diff, log_path, log_time in matching_logs:
                try:
                    with open(log_path, "r", encoding="utf-8", errors="ignore") as f:
                        content = f.read(50000)
                    
                    if "userid:" in content:
                        user_id = content.split("userid:")[1].split(",")[0].strip()
                        if user_id.isdigit():
                            used_logs.add(log_path)
                            return user_id, log_path
                except Exception as e:
                    print(f"[Auto-Rejoin] Error reading log {log_path}: {e}")
                    continue
            
            return None, None
            
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            return None, None
        except Exception as e:
            print(f"[Auto-Rejoin] Error getting user ID for PID {pid}: {e}")
            return None, None
      


    def apply_and_lock_roblox_settings(self):
        """Apply local Roblox settings and lock file"""
        try:
            local_settings_path = os.path.join(self.data_folder, "roblox_settings.xml")
            roblox_settings_path = os.path.join(
                os.environ.get("LOCALAPPDATA", ""),
                "Roblox",
                "GlobalBasicSettings_13.xml"
            )
            
            if not os.path.exists(local_settings_path):
                if os.path.exists(roblox_settings_path):
                    shutil.copy2(roblox_settings_path, local_settings_path)
                    print(f"[INFO] Created local Roblox settings file")
                else:
                    print(f"[WARNING] Roblox settings file not found, skipping auto-apply")
                    return
            
            try:
                os.chmod(roblox_settings_path, stat.S_IWRITE | stat.S_IREAD)
            except:
                pass
            
            shutil.copy2(local_settings_path, roblox_settings_path)
            print(f"[INFO] Applied local settings to Roblox")
            
            os.chmod(roblox_settings_path, stat.S_IREAD | stat.S_IRGRP | stat.S_IROTH)
            print(f"[INFO] Locked Roblox settings to read-only")
            
        except Exception as e:
            print(f"[ERROR] Failed to apply and lock Roblox settings: {e}")
    
