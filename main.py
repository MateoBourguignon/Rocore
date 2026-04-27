"""
Roblox Account Manager
Main entry point for the application
"""

# if you find this tool helpful, consider starring the repo!

import os
import warnings
import tkinter as tk
from tkinter import messagebox, simpledialog
import requests
import threading

warnings.filterwarnings("ignore")

from classes import RobloxAccountManager
from classes.encryption import EncryptionConfig
from utils.encryption_setup import setup_encryption
from utils.ui import AccountManagerUI


def setup_icon(data_folder):
    icon_path = os.path.join(data_folder, "icon.ico")

    if os.path.exists(icon_path):
        print("[INFO] Using local icon.")
        return icon_path

    print("[WARNING] Local icon not found:", icon_path)
    return None

def setup_discord_logo(data_folder):
    logo_path = os.path.join(data_folder, "discordlogo.png")

    if os.path.exists(logo_path):
        print("[INFO] Using local Discord logo.")
        return logo_path

    print("[WARNING] Local Discord logo not found:", logo_path)
    return None

def apply_icon_to_window(window, icon_path):
    if icon_path and os.path.exists(icon_path):
        try:
            window.iconbitmap(icon_path)
        except Exception as e:
            print(f"[ERROR] Could not set window icon: {e}")


def apply_icon_async(root, data_folder):
    icon_path = os.path.join(data_folder, "icon.ico")
    discord_logo_path = os.path.join(data_folder, "discordlogo.png")
    
    if os.path.exists(icon_path):
        apply_icon_to_window(root, icon_path)
    
    needs_icon = not os.path.exists(icon_path)
    needs_discord = not os.path.exists(discord_logo_path)

    if needs_icon or needs_discord:
        def download_assets():
            if needs_icon:
                try:
                    setup_icon(data_folder)
                except:
                    pass
            if needs_discord:
                try:
                    setup_discord_logo(data_folder)
                except:
                    pass
        threading.Thread(target=download_assets, daemon=True).start()

    return icon_path if os.path.exists(icon_path) else None, \
           discord_logo_path


def main():
    """Main application entry point"""
    password = setup_encryption()
    
    data_folder = "AccountManagerData"
    if not os.path.exists(data_folder):
        os.makedirs(data_folder)
        
    encryption_config = EncryptionConfig(os.path.join(data_folder, "encryption_config.json"))
    
    if encryption_config.is_encryption_enabled() and encryption_config.get_encryption_method() == 'password':
        if password is None:
            root = tk.Tk()
            root.withdraw()
            password = simpledialog.askstring("Password Required", "Enter your password to unlock:", show='*')
            root.destroy()
            
            if password is None:
                messagebox.showerror("Error", "Password is required to access encrypted accounts.")
                return
    
    try:
        manager = RobloxAccountManager(password=password)
    except ValueError as e:
        messagebox.showerror("Error", "Password is invalid. Please try again.")
        return
    except Exception as e:
        messagebox.showerror("Error", f"Failed to initialize: {e}")
        return
    
    root = tk.Tk()
    root.withdraw()
    root.option_add("*BorderWidth", 0)
    root.option_add("*highlightThickness", 0)
    root.option_add("*Relief", "flat")
    
    script_dir = os.path.dirname(os.path.abspath(__file__))
    icon_path, discord_logo_path = apply_icon_async(root, script_dir)

    app = AccountManagerUI(root, manager, icon_path=icon_path, discord_logo_path=discord_logo_path)
    try:
        app._apply_modern_window_defaults()
    except Exception:
        pass
    
    root.deiconify()
    root.mainloop()


if __name__ == "__main__":
    main()