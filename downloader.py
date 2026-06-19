"""
Universal rezka.ag Video Downloader

Downloads movies and series from rezka.ag / hdrezka domains using
Selenium-based network interception with yt-dlp and ffmpeg backends.
"""

import os
import re
import sys
import time
import base64
import json
import shutil
import logging
import argparse
import zipfile
import subprocess
import urllib.request
from itertools import product
from urllib.parse import urlparse

try:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")
except Exception:
    pass

import atexit

from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.action_chains import ActionChains
import seleniumwire.undetected_chromedriver as uc
import yt_dlp

# Suppress the OSError: [WinError 6] from uc.Chrome.__del__ on Windows exit
try:
    _original_del = uc.Chrome.__del__
    def _safe_del(self):  # type: ignore[override]
        try:
            _original_del(self)
        except Exception:
            pass
    uc.Chrome.__del__ = _safe_del
except Exception:
    pass

# ---------------------------------------------------------------------------
# Logging setup
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("downloader.log", encoding="utf-8"),
    ],
)
log = logging.getLogger(__name__)

for _noisy in ("seleniumwire", "hpack", "urllib3", "selenium.webdriver"):
    logging.getLogger(_noisy).setLevel(logging.WARNING)

# ---------------------------------------------------------------------------
# Constants & Selectors
# ---------------------------------------------------------------------------
STREAM_EXCLUDE_KEYWORDS: tuple[str, ...] = (
    "subtitle", "caption", "google", "analytics", "click",
    "metric", "doubleclick", "beacon", "stat.", "ima", "prebid",
)

KEEP_HEADERS: frozenset[str] = frozenset(("referer", "user-agent", "cookie", "origin"))

class Selectors:
    """Centralized CSS selectors to ease maintenance if DOM changes."""
    TRANSLATORS = "#translators-list .b-translator__item, .b-translator__item"
    SEASONS = ".b-simple_seasons__item, .b-simple_season__item"
    EPISODES = ".b-simple_episodes__item, .b-simple_episode__item"
    EPISODE_ACTIVE = ".b-simple_episode__item.active, .b-simple_episodes__item.active"
    TRANSLATOR_ACTIVE = "#translators-list .b-translator__item.active"
    POST_ID = "#post_id, #send-video-issue"

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def validate_url(url: str) -> bool:
    try:
        parsed = urlparse(url)
    except Exception:
        return False
    if parsed.scheme not in ("http", "https"):
        return False
    host = parsed.netloc.lower().split(":")[0]
    if host.startswith("www."):
        host = host[4:]
    return bool("rezka" in host and parsed.path and parsed.path != "/")


def extract_title_from_url(url: str) -> str:
    try:
        parts = url.rstrip("/").split("/")
        last_part = parts[-1]
        if last_part.endswith(".html"):
            last_part = last_part[:-5]
        return last_part.split("?")[0].split("#")[0]
    except Exception:
        return "rezka_video"


def sanitize_filename(name: str) -> str:
    name = re.sub(r'[\\/*?:"<>|]', "_", name)
    return name.strip().rstrip(". ")


def extract_number(text: str) -> str:
    match = re.search(r"\d+", text)
    return match.group(0) if match else text


def _sanitize_header_value(value: str) -> str:
    return re.sub(r"[\r\n\x00]", "", str(value))


def _deduplicate_elements(elements: list) -> list:
    seen: set[str] = set()
    unique: list = []
    for el in elements:
        eid = el.id
        if eid not in seen:
            seen.add(eid)
            unique.append(el)
    return unique


def parse_subtitles(subtitle_str: str | None, subtitle_lns: dict | None) -> dict[str, str]:
    subs: dict[str, str] = {}
    if not subtitle_str:
        return subs
    try:
        for item in subtitle_str.split(","):
            item = item.strip()
            if not item or "[" not in item or "]" not in item:
                continue
            parts = item.split("[", 1)[1].split("]", 1)
            if len(parts) == 2:
                lang = parts[0].strip()
                url = parts[1].strip().replace(r"\/", "/")
                code = subtitle_lns.get(lang) if isinstance(subtitle_lns, dict) else None
                if code:
                    subs[code.lower()] = url
                else:
                    lang_lower = lang.lower()
                    if "рус" in lang_lower: subs["ru"] = url
                    elif "анг" in lang_lower or "eng" in lang_lower: subs["en"] = url
                    else: subs[lang_lower] = url
    except (KeyError, IndexError, AttributeError) as e:
        log.error("Error parsing subtitles: %s", e)
    return subs


def select_subtitle_url(subtitles: dict[str, str]) -> tuple[str | None, str | None]:
    if not subtitles:
        return None, None
    if "ru" in subtitles: return "ru", subtitles["ru"]
    for k in subtitles:
        if "ru" in k: return k, subtitles[k]
    if "en" in subtitles: return "en", subtitles["en"]
    for k in subtitles:
        if "en" in k: return k, subtitles[k]
    first_lang = list(subtitles.keys())[0]
    return first_lang, subtitles[first_lang]


def download_subtitle(url: str, headers: dict[str, str], output_path: str) -> bool:
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=30) as response:
            with open(output_path, "wb") as f:
                f.write(response.read())
        log.info("Subtitles downloaded to: %s", output_path)
        return True
    except Exception as e:
        log.error("Failed to download subtitles from %s: %s", url, e)
        return False


def _get_ffmpeg_path() -> str:
    """Finds ffmpeg executable in local dir or system PATH."""
    local_exe = "ffmpeg.exe" if os.name == "nt" else "ffmpeg"
    if os.path.exists(local_exe):
        return os.path.abspath(local_exe)
    return "ffmpeg" # Fallback to PATH


# ---------------------------------------------------------------------------
# Page information helpers
# ---------------------------------------------------------------------------

def collect_page_info(driver: uc.Chrome) -> tuple[list[str], list[str], list[str]]:
    translators = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.TRANSLATORS))
    translator_names = [t.text.strip() for t in translators if t.text.strip()]

    seasons = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.SEASONS))
    season_texts = [s.text.strip() for s in seasons if s.text.strip()]

    episodes = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.EPISODES))
    episode_texts = [e.text.strip() for e in episodes if e.text.strip()]

    return translator_names, season_texts, episode_texts


def print_page_summary(translator_names: list[str], season_texts: list[str], episode_texts: list[str]) -> None:
    print("\n--- PAGE CONTENT SUMMARY ---")
    print(f"Translators (Voice Actings) found: {len(translator_names)}")
    if translator_names: print(f"  List: {', '.join(translator_names)}")
    else: print("  (Using site's default voice acting)")

    if season_texts: print(f"Seasons found: {len(season_texts)}\n  List: {', '.join(season_texts)}")
    else: print("Seasons found: 0 (Single movie or one-season video)")

    if episode_texts: print(f"Episodes found: {len(episode_texts)}\n  List: {', '.join(episode_texts)}")
    else: print("Episodes found: 0 (Single movie)")
    print("----------------------------\n")


def perform_pre_check(driver: uc.Chrome) -> tuple[int, int, int]:
    translator_names, season_texts, episode_texts = collect_page_info(driver)
    print_page_summary(translator_names, season_texts, episode_texts)
    return len(translator_names), len(season_texts), len(episode_texts)


# ---------------------------------------------------------------------------
# Episode range selection
# ---------------------------------------------------------------------------

def select_episode_range(episodes_list: list[dict], default_range_str: str | None = None) -> list[dict]:
    total_episodes = len(episodes_list)
    if total_episodes == 0: return []

    ep_map: dict[int, int] = {}
    for idx, ep in enumerate(episodes_list):
        try: ep_map[int(extract_number(ep["text"]))] = idx
        except ValueError: ep_map[idx + 1] = idx

    min_ep, max_ep = min(ep_map.keys()), max(ep_map.keys())
    start_num, end_num = min_ep, max_ep

    if default_range_str:
        parts = str(default_range_str).split("-")
        try:
            start_num = int(parts[0])
            end_num = int(parts[1]) if len(parts) == 2 else start_num
        except ValueError:
            log.warning("Could not parse episode range '%s'. Falling back to interactive.", default_range_str)
            default_range_str = None
        else:
            if not (min_ep <= start_num <= max_ep): start_num = min_ep
            if not (min_ep <= end_num <= max_ep): end_num = max_ep
            if start_num > end_num: return []

    if not default_range_str:
        print(f"Select episode range (from {min_ep} to {max_ep}):")
        while True:
            try:
                start_input = input(f"Enter start episode ({min_ep}-{max_ep}, default {min_ep}): ").strip()
                start_num = int(start_input) if start_input else min_ep
                if start_num in ep_map: break
                print(f"Invalid episode. Must be one of: {list(ep_map.keys())}")
            except ValueError: print("Please enter a valid number.")

        while True:
            try:
                end_input = input(f"Enter end episode ({start_num}-{max_ep}, default {max_ep}): ").strip()
                end_num = int(end_input) if end_input else max_ep
                if end_num in ep_map and end_num >= start_num: break
                print(f"Invalid episode. Must be >= {start_num} and <= {max_ep}.")
            except ValueError: print("Please enter a valid number.")

    return [episodes_list[ep_map[num]] for num in range(start_num, end_num + 1) if num in ep_map]


# ---------------------------------------------------------------------------
# uBlock Origin Lite auto-installer
# ---------------------------------------------------------------------------

def setup_ubol() -> str | None:
    extension_dir = os.path.join(os.getcwd(), "ubol_extension")
    if os.path.isdir(extension_dir) and os.listdir(extension_dir):
        return extension_dir

    log.info("Setting up uBlock Origin Lite extension...")
    if os.path.exists(extension_dir):
        shutil.rmtree(extension_dir, ignore_errors=True)
    os.makedirs(extension_dir, exist_ok=True)

    api_url = "https://api.github.com/repos/uBlockOrigin/uBOL-home/releases/latest"
    http_headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}

    try:
        req = urllib.request.Request(api_url, headers=http_headers)
        with urllib.request.urlopen(req, timeout=30) as response:
            data = json.loads(response.read().decode("utf-8"))

        zip_url = next((asset.get("browser_download_url") for asset in data.get("assets", []) 
                        if asset.get("name", "").endswith(".chromium.zip")), None)
        if not zip_url:
            raise RuntimeError("Chromium zip asset not found.")

        zip_path = os.path.join(os.getcwd(), "ubol.zip")
        req_zip = urllib.request.Request(zip_url, headers=http_headers)
        with urllib.request.urlopen(req_zip, timeout=60) as response, open(zip_path, "wb") as out_file:
            shutil.copyfileobj(response, out_file)

        with zipfile.ZipFile(zip_path, "r") as zip_ref:
            if "manifest.json" not in zip_ref.namelist():
                raise RuntimeError("Downloaded archive is not a valid Chrome extension.")
            zip_ref.extractall(extension_dir)

        os.remove(zip_path)
        log.info("uBlock Origin Lite successfully installed.")
        return extension_dir
    except Exception as exc:
        log.error("Failed to set up uBlock Origin Lite: %s", exc)
        if os.path.exists(extension_dir):
            shutil.rmtree(extension_dir, ignore_errors=True)
        return None


# ---------------------------------------------------------------------------
# Chrome version detection
# ---------------------------------------------------------------------------

def get_chrome_main_version() -> int | None:
    if os.name == "nt":
        try:
            import winreg
            paths = [
                r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall\Google Chrome",
                r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall\Google Chrome",
            ]
            for path in paths:
                try:
                    with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, path, 0, winreg.KEY_READ) as key:
                        version, _ = winreg.QueryValueEx(key, "DisplayVersion")
                        return int(version.split(".")[0])
                except Exception: continue
        except Exception: pass

        exe_paths = [
            os.path.expandvars(r"%ProgramFiles%\Google\Chrome\Application\chrome.exe"),
            os.path.expandvars(r"%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe"),
            os.path.expandvars(r"%LocalAppData%\Google\Chrome\Application\chrome.exe"),
        ]
        for path in exe_paths:
            if os.path.exists(path):
                try:
                    cmd = f'(Get-Item "{path}").VersionInfo.FileVersion'
                    res = subprocess.run(["powershell", "-Command", cmd], capture_output=True, text=True)
                    if res.stdout.strip(): return int(res.stdout.strip().split(".")[0])
                except Exception: continue
    else:
        # Linux / Mac fallback
        for cmd in ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"]:
            try:
                res = subprocess.run([cmd, "--version"], capture_output=True, text=True)
                match = re.search(r'(\d+)\.', res.stdout)
                if match: return int(match.group(1))
            except Exception: continue
                
    return None


# ---------------------------------------------------------------------------
# Driver initialisation
# ---------------------------------------------------------------------------

_active_driver: uc.Chrome | None = None

def _safe_quit_driver() -> None:
    global _active_driver
    if _active_driver is not None:
        try: _active_driver.quit()
        except Exception: pass
        _active_driver = None

atexit.register(_safe_quit_driver)

def init_driver(headless: bool = False) -> uc.Chrome:
    global _active_driver
    options = uc.ChromeOptions()
    if headless: options.add_argument("--headless")

    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--ignore-ssl-errors")
    options.add_argument("--allow-insecure-localhost")
    options.add_argument("--disable-features=SafeBrowsing")
    options.add_argument("--safebrowsing-disable-download-protection")
    options.add_argument("--safebrowsing-disable-extension-blacklist")
    options.add_argument("--disable-site-isolation-trials")

    ubol_dir = setup_ubol()
    if ubol_dir: options.add_argument(f"--load-extension={ubol_dir}")

    seleniumwire_options = {"verify_ssl": False, "suppress_connection_errors": True}
    chrome_version = get_chrome_main_version()
    if chrome_version:
        log.info("Detected Chrome major version: %d.", chrome_version)

    driver = uc.Chrome(version_main=chrome_version, options=options, seleniumwire_options=seleniumwire_options)
    _active_driver = driver
    return driver


# ---------------------------------------------------------------------------
# Cloudflare bypass
# ---------------------------------------------------------------------------

def wait_for_cloudflare_bypass(driver: uc.Chrome, timeout: int = 300, poll_interval: float = 0.5) -> bool:
    log.info("Checking for Cloudflare challenge...")
    start_time, last_print = time.time(), 0.0

    while time.time() - start_time < timeout:
        try:
            if driver.find_elements(By.CSS_SELECTOR, ".b-post, #inside-main, #translators-list, #cdnplayer"):
                log.info("Rezka page elements detected. Cloudflare bypassed.")
                return True
        except Exception: pass

        title = driver.title if hasattr(driver, 'title') else ""
        elapsed = time.time() - start_time

        if ("Just a moment" in title or "Cloudflare" in title) and elapsed - last_print >= 10:
            log.info("  Waiting... (%ds remaining) | Page title: '%s'", int(timeout - elapsed), title)
            last_print = elapsed
        time.sleep(poll_interval)

    return False


# ---------------------------------------------------------------------------
# Interactive user choice
# ---------------------------------------------------------------------------

def get_user_choice(options: list[str], prompt_text: str, timeout: int = 15, default_idx: int = 0) -> int:
    print("\nAvailable options:")
    for idx, opt in enumerate(options): print(f"  [{idx + 1}] {opt}")

    prompt = f"{prompt_text} (default [{default_idx + 1}] in {timeout}s): "
    try:
        import msvcrt
        start_time, input_str = time.time(), ""
        sys.stdout.write(prompt); sys.stdout.flush()
        
        while time.time() - start_time < timeout:
            if msvcrt.kbhit():
                char = msvcrt.getch()
                if char in (b"\r", b"\n"):
                    print()
                    val = input_str.strip()
                    if not val: return default_idx
                    try:
                        choice = int(val) - 1
                        if 0 <= choice < len(options): return choice
                    except ValueError: pass
                    print("Invalid selection. Try again.")
                    sys.stdout.write(prompt); sys.stdout.flush(); input_str = ""
                elif char == b"\b":
                    if input_str:
                        input_str = input_str[:-1]; sys.stdout.write("\b \b"); sys.stdout.flush()
                else:
                    try:
                        decoded_char = char.decode("utf-8")
                        input_str += decoded_char; sys.stdout.write(decoded_char); sys.stdout.flush()
                    except Exception: pass
            time.sleep(0.1)
        print(f"\nTimeout. Selecting default: {options[default_idx]}")
        return default_idx
    except (ImportError, Exception):
        try:
            val = input(prompt)
            if not val.strip(): return default_idx
            choice = int(val) - 1
            if 0 <= choice < len(options): return choice
        except Exception: pass
        return default_idx


# ---------------------------------------------------------------------------
# Translator selection
# ---------------------------------------------------------------------------

def select_translator(driver: uc.Chrome, preferred_name: str | None = None) -> str | None:
    try:
        WebDriverWait(driver, 15).until(EC.presence_of_element_located((By.CSS_SELECTOR, Selectors.TRANSLATORS)))
    except Exception: pass

    translators = driver.find_elements(By.CSS_SELECTOR, Selectors.TRANSLATORS)
    if not translators: return None

    translator_options = [{"element": t, "name": t.text.strip()} for t in translators if t.text.strip()]
    selected_opt = None

    if preferred_name:
        for opt in translator_options:
            if preferred_name.lower() in opt["name"].lower():
                selected_opt = opt
                log.info("Auto-selected translator: %s", opt["name"])
                break

    if not selected_opt:
        choice_idx = get_user_choice([opt["name"] for opt in translator_options], "Select translator", default_idx=0)
        selected_opt = translator_options[choice_idx]

    if "active" not in selected_opt["element"].get_attribute("class"):
        driver.execute_script("arguments[0].click();", selected_opt["element"])
        time.sleep(1.0)

    return selected_opt["name"]


# ---------------------------------------------------------------------------
# Player / network helpers
# ---------------------------------------------------------------------------

def click_player(driver: uc.Chrome) -> None:
    try:
        time.sleep(0.3)
        selectors = ["iframe#oframecdnplayer", "iframe[id*='cdnplayer']", "div#cdnplayer", "div#player", "div#cdnplayer-container", "div#videoplayer"]
        player = next((driver.find_element(By.CSS_SELECTOR, s) for s in selectors if driver.find_elements(By.CSS_SELECTOR, s) and driver.find_element(By.CSS_SELECTOR, s).is_displayed()), None)

        if player:
            if player.tag_name == "iframe":
                driver.switch_to.frame(player)
                try:
                    play_selectors = ["div.vjs-big-play-button", "button.vjs-big-play-button", ".play-btn", "[aria-label='Play']", "body"]
                    clicked = next((True for ps in play_selectors if driver.execute_script("arguments[0].click();", driver.find_element(By.CSS_SELECTOR, ps))), False)
                    if not clicked:
                        ActionChains(driver).move_to_element(driver.find_element(By.TAG_NAME, "body")).click().perform()
                finally:
                    driver.switch_to.default_content()
            else:
                driver.execute_script("arguments[0].click();", player)
            log.info("Video playback trigger fired.")
    except Exception as exc:
        log.error("Error triggering player click: %s", exc)


def clear_requests(driver: uc.Chrome) -> None:
    try: del driver.requests
    except AttributeError: pass


def get_stream_url(driver: uc.Chrome, timeout: int = 30) -> tuple[str | None, dict | None]:
    start_time = time.time()
    while time.time() - start_time < timeout:
        for request in list(driver.requests):
            if not request.response: continue
            url: str = request.url
            url_path = url.split("?")[0]
            is_stream = ".m3u8" in url or url_path.endswith(".mp4")
            is_excluded = any(k in url for k in STREAM_EXCLUDE_KEYWORDS)
            is_segment = bool(re.search(r"\.(ts|aac)\b", url_path.split("/")[-1]))

            if is_stream and not is_excluded and not is_segment:
                return url, request.headers
        time.sleep(0.5)
    return None, None


def _set_player_quality(driver: uc.Chrome, quality: str) -> bool:
    js_code = """
        var targetQuality = arguments[0];
        var done = arguments[arguments.length - 1];
        var playerDiv = document.querySelector('#cdnplayer');
        if (!playerDiv) return done("No player");
        playerDiv.dispatchEvent(new MouseEvent('mousemove', {bubbles: true}));
        var gear = document.querySelector('.pjs-settings') || document.querySelector('pjsdiv[title="Настройки"]');
        if (!gear) { var all = document.querySelectorAll('pjsdiv'); gear = Array.from(all).find(e => e.className && typeof e.className === 'string' && e.className.includes('pjs-settings')); }
        if (!gear) return done("No gear");
        gear.click();
        setTimeout(() => {
            var divs = document.querySelectorAll('pjsdiv');
            var qualityBtn = Array.from(divs).find(e => e.innerText && e.innerText.trim() === 'Качество');
            if (!qualityBtn) return done("No Quality button");
            qualityBtn.click();
            setTimeout(() => {
                var options = document.querySelectorAll('pjsdiv');
                var targets = Array.from(options).filter(e => e.innerText && /^\\d{3,4}p/.test(e.innerText.trim()) && e.style.visibility !== 'hidden');
                if (targets.length === 0) return done("No quality options");
                var target = targetQuality === "best" ? targets[0] : targets.find(e => e.innerText.includes(targetQuality));
                if (!target) return done("Quality not found");
                target.click();
                done("Success");
            }, 300);
        }, 300);
    """
    try:
        driver.set_script_timeout(5)
        return driver.execute_async_script(js_code, str(quality)) == "Success"
    except Exception: return False


# ---------------------------------------------------------------------------
# Download functions
# ---------------------------------------------------------------------------

def clear_trash(data: str) -> str:
    trash_list = ["@", "#", "!", "^", "$"]
    trash_codes = [base64.b64encode("".join(chars).encode("utf-8")) for i in range(2, 4) for chars in product(trash_list, repeat=i)]
    
    arr = data.replace("#h", "").split("//_//")
    trash_str = "".join(arr)
    for code in trash_codes:
        trash_str = trash_str.replace(code.decode("utf-8"), "")
    
    try:
        return base64.b64decode(trash_str + "==").decode("utf-8", errors="ignore")
    except (ValueError, base64.binascii.Error):
        return trash_str


def parse_streams(decrypted_str: str) -> dict[str, str]:
    streams: dict[str, str] = {}
    for item in decrypted_str.split(","):
        if "[" in item and "]" in item:
            parts = item.split("[", 1)[1].split("]", 1)
            if len(parts) == 2:
                q_clean = re.sub(r'<[^>]*>', '', parts[0]).strip()
                streams[q_clean] = parts[1].strip()
    return streams


def select_quality_url(streams: dict[str, str], requested_quality: str) -> str:
    if requested_quality in streams:
        links = streams[requested_quality].split(" or ")
        return next((l for l in links if ":hls:manifest.m3u8" in l), links[0])

    quality_map = []
    for key in streams:
        match = re.search(r'(\d+)', key)
        if match:
            res = int(match.group(1))
            quality_map.append((res, "ultra" in key.lower(), key))
    
    quality_map.sort(key=lambda x: (x[0], 0 if x[1] else 1), reverse=True)
    if not quality_map: raise ValueError("No video qualities found.")

    active_map = [x for x in quality_map if not x[1]] or quality_map
    if requested_quality.lower() == "ultra":
        quality_map.sort(key=lambda x: (x[0], 1 if x[1] else 0), reverse=True)
        active_map = quality_map
        
    chosen_key = active_map[0][2] if requested_quality in ("best", "ultra") else next((k for r, u, k in active_map if r <= int(re.search(r'\d+', requested_quality).group(0) if re.search(r'\d+', requested_quality) else 99999)), active_map[-1][2])
    
    links = streams[chosen_key].split(" or ")
    return next((l for l in links if ":hls:manifest.m3u8" in l), links[0])


def _get_rezka_api_response(driver: uc.Chrome, season_num: str | None = None, episode_num: str | None = None) -> dict | None:
    """Centralized method to fetch data from Rezka's internal API."""
    try:
        post_id = driver.execute_script(f"""
            var el = document.querySelector('{Selectors.POST_ID}');
            return el ? (el.value || el.getAttribute('data-id')) : null;
        """)
        translator_id = driver.execute_script(f"""
            var el = document.querySelector('{Selectors.TRANSLATOR_ACTIVE}');
            if (el) return el.getAttribute('data-translator_id');
            var scripts = Array.from(document.querySelectorAll('script'));
            for (var s of scripts) {{
                var match = s.textContent.match(/sof\\.tv\\.initCDN(?:Series|Movies)Events\\(\\s*\\d+\\s*,\\s*(\\d+)/);
                if (match) return match[1];
            }}
            return null;
        """)
        
        if not post_id or not translator_id:
            log.error("Missing post_id or translator_id.")
            return None

        params = {"id": post_id, "translator_id": translator_id}
        if season_num and episode_num:
            params.update({"season": season_num, "episode": episode_num, "action": "get_stream"})
        else:
            params["action"] = "get_movie"
            
        fetch_js = """
            var params = arguments[0];
            var callback = arguments[arguments.length - 1];
            fetch('/ajax/get_cdn_series/', {
                method: 'POST',
                headers: {'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8', 'X-Requested-With': 'XMLHttpRequest'},
                body: new URLSearchParams(params).toString()
            }).then(r => r.json()).then(data => callback(data)).catch(err => callback({success: false, error: err.toString()}));
        """
        driver.set_script_timeout(10)
        return driver.execute_async_script(fetch_js, params)
    except Exception as exc:
        log.exception("Error fetching Rezka API response")
        return None


def _get_stream_via_fetch(driver: uc.Chrome, quality: str = "best", season_num: str | None = None, episode_num: str | None = None) -> tuple[str | None, dict[str, str] | None, dict[str, str]]:
    result = _get_rezka_api_response(driver, season_num, episode_num)
    if not result or not result.get("success"):
        log.error("Fetch request failed: %s", result.get("error") if result else "No response")
        return None, None, {}
        
    url_str = result.get("url")
    if not url_str: return None, None, {}
        
    streams = parse_streams(clear_trash(url_str))
    if not streams: return None, None, {}
        
    chosen_url = select_quality_url(streams, quality)
    log.info("Fetched URL for quality %s: %s...", quality, chosen_url[:120])
    
    try:
        current_host = urlparse(driver.current_url).netloc.lower().split(":")[0]
        if current_host.startswith("www."): current_host = current_host[4:]
    except Exception: current_host = "rezka.ag"

    origin_request = next((r for r in reversed(list(driver.requests)) if r.headers and current_host in r.url), None)
    req_headers = origin_request.headers if origin_request else None
    
    subtitles_dict = parse_subtitles(result.get("subtitle"), result.get("subtitle_lns"))
    return chosen_url, req_headers, subtitles_dict


def download_with_ytdlp(stream_url: str, headers: dict[str, str], output_path: str, quality: str = "best") -> None:
    fmt = f"bestvideo[height<={quality}]+bestaudio/best[height<={quality}]/best" if quality.isdigit() else "best"
    ydl_opts = {
        "outtmpl": output_path,
        "format": fmt,
        "merge_output_format": "mp4",
        "http_headers": headers,
        "ffmpeg_location": _get_ffmpeg_path(),
        "concurrent_fragment_downloads": 3,
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        ydl.download([stream_url])


def download_with_ffmpeg(stream_url: str, headers: dict[str, str], output_path: str) -> None:
    headers_str = "".join(f"{k}: {_sanitize_header_value(v)}\r\n" for k, v in headers.items())
    cmd = [_get_ffmpeg_path(), "-y", "-headers", headers_str, "-i", stream_url, "-c", "copy", "-bsf:a", "aac_adtstoasc", output_path]
    
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"ffmpeg failed: {result.stderr[-500:]}")


def download_video(stream_url: str, headers: dict[str, str], output_path: str, max_retries: int = 3, quality: str = "best") -> None:
    for attempt in range(1, max_retries + 1):
        try:
            download_with_ytdlp(stream_url, headers, output_path, quality)
            return
        except Exception as exc:
            log.warning("yt-dlp failed (%d/%d): %s", attempt, max_retries, exc)
            if attempt < max_retries: time.sleep(5)

    try:
        download_with_ffmpeg(stream_url, headers, output_path)
    except Exception as exc:
        raise RuntimeError(f"All downloads failed for: {output_path}") from exc


# ---------------------------------------------------------------------------
# Shared episode-download helper
# ---------------------------------------------------------------------------

def _build_headers(req_headers: dict | None, referer: str | None = None) -> dict[str, str]:
    headers: dict[str, str] = {}
    if req_headers:
        for k, v in req_headers.items():
            if k.lower() in KEEP_HEADERS: headers[k.title()] = v
    if "Referer" not in headers: headers["Referer"] = referer or "https://rezka.ag/"
    return headers


def _download_episode(driver: uc.Chrome, ep_data: dict, output_dir: str, episode_file: str, quality: str = "best", season_num: str = "1") -> None:
    output_path = os.path.join(output_dir, episode_file)
    if os.path.exists(output_path): return

    if ep_data["id"]:
        ep_el = WebDriverWait(driver, 15).until(EC.element_to_be_clickable((By.CSS_SELECTOR, f"[data-episode_id='{ep_data['id']}']")))
    else:
        episodes = driver.find_elements(By.CSS_SELECTOR, Selectors.EPISODES)
        ep_el = episodes[ep_data["index"]]

    clear_requests(driver)
    driver.execute_script("arguments[0].click();", ep_el)

    try:
        WebDriverWait(driver, 10).until(EC.presence_of_element_located((By.CSS_SELECTOR, Selectors.EPISODE_ACTIVE)))
    except Exception: time.sleep(1.0)

    stream_url, req_headers, subtitles = _get_stream_via_fetch(driver, quality=quality, season_num=season_num, episode_num=ep_data["num"])
    
    if not stream_url:
        click_player(driver)
        stream_url, req_headers = get_stream_url(driver, timeout=15)
        if stream_url:
            clear_requests(driver)
            if _set_player_quality(driver, quality):
                new_url, new_headers = get_stream_url(driver, timeout=15)
                if new_url: stream_url, req_headers = new_url, new_headers

    if not stream_url: return

    headers = _build_headers(req_headers, referer=driver.current_url)
    os.makedirs(output_dir, exist_ok=True)
    download_video(stream_url, headers, output_path, max_retries=3, quality=quality)

    if subtitles:
        lang_code, sub_url = select_subtitle_url(subtitles)
        if sub_url:
            sub_output_path = f"{os.path.splitext(output_path)[0]}.{lang_code}.vtt"
            download_subtitle(sub_url, headers, sub_output_path)


# ---------------------------------------------------------------------------
# Content-type detection
# ---------------------------------------------------------------------------

def get_seasons_and_episodes(driver: uc.Chrome) -> tuple[list, list]:
    seasons = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.SEASONS))
    episodes = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.EPISODES))
    return seasons, episodes


def _fetch_available_qualities(driver: uc.Chrome) -> list[str]:
    seasons = driver.find_elements(By.CSS_SELECTOR, Selectors.SEASONS)
    episodes = driver.find_elements(By.CSS_SELECTOR, Selectors.EPISODES)
    
    season_num, episode_num = "1", None
    if seasons or episodes:
        ep_el = driver.find_element(By.CSS_SELECTOR, Selectors.EPISODES)
        match = re.search(r'\d+', ep_el.text.strip())
        episode_num = match.group(0) if match else "1"
        if seasons:
            match = re.search(r'\d+', driver.find_element(By.CSS_SELECTOR, Selectors.SEASONS).text.strip())
            season_num = match.group(0) if match else "1"
            
    result = _get_rezka_api_response(driver, season_num if episode_num else None, episode_num)
    if result and result.get("success") and result.get("url"):
        return list(parse_streams(clear_trash(result.get("url"))).keys())
    return []


# ---------------------------------------------------------------------------
# Main Orchestrators
# ---------------------------------------------------------------------------

def _handle_multi_season_series(driver: uc.Chrome, args: argparse.Namespace, sanitized_title: str, seasons: list) -> None:
    season_info = [{"id": s.get_attribute("data-season_id"), "text": s.text.strip(), "num": extract_number(s.text.strip()), "index": idx} for idx, s in enumerate(seasons)]

    selected_season_num = str(args.season) if args.season else None
    if not selected_season_num:
        choices = [s["num"] for s in season_info]
        while True:
            choice = input(f"Select season ({', '.join(choices)}, default {choices[0]}): ").strip()
            if not choice: selected_season_num = choices[0]; break
            if choice in choices: selected_season_num = choice; break

    s_data = next((s for s in season_info if s["num"] == selected_season_num), None)
    if not s_data: return

    if s_data["id"]:
        season_el = WebDriverWait(driver, 15).until(EC.element_to_be_clickable((By.CSS_SELECTOR, f"[data-season_id='{s_data['id']}']")))
    else:
        season_el = driver.find_elements(By.CSS_SELECTOR, Selectors.SEASONS)[s_data["index"]]

    driver.execute_script("arguments[0].click();", season_el)
    time.sleep(1.0)

    episodes = _deduplicate_elements(driver.find_elements(By.CSS_SELECTOR, Selectors.EPISODES))
    episode_info = [{"id": e.get_attribute("data-episode_id"), "text": e.text.strip(), "num": extract_number(e.text.strip()), "index": i} for i, e in enumerate(episodes)]

    selected_episodes = select_episode_range(episode_info, args.episode)
    for ep_data in selected_episodes:
        output_dir = os.path.join(args.output, sanitized_title, f"Season_{s_data['num']}")
        episode_file = f"{sanitized_title}_S{s_data['num']}_Ep_{ep_data['num']}.mp4"
        _download_episode(driver, ep_data, output_dir, episode_file, quality=args.quality, season_num=s_data['num'])


def _handle_single_season_series(driver: uc.Chrome, args: argparse.Namespace, sanitized_title: str, episodes: list) -> None:
    episode_info = [{"id": e.get_attribute("data-episode_id"), "text": e.text.strip(), "num": extract_number(e.text.strip()), "index": i} for i, e in enumerate(episodes)]
    selected_episodes = select_episode_range(episode_info, args.episode)
    
    for ep_data in selected_episodes:
        output_dir = os.path.join(args.output, sanitized_title, "Season_1")
        episode_file = f"{sanitized_title}_Ep_{ep_data['num']}.mp4"
        _download_episode(driver, ep_data, output_dir, episode_file, quality=args.quality)


def _handle_movie(driver: uc.Chrome, args: argparse.Namespace, sanitized_title: str) -> None:
    output_dir = os.path.join(args.output, sanitized_title)
    output_path = os.path.join(output_dir, f"{sanitized_title}.mp4")
    if os.path.exists(output_path): return

    stream_url, req_headers, subtitles = _get_stream_via_fetch(driver, quality=args.quality)
    
    if not stream_url:
        click_player(driver)
        stream_url, req_headers = get_stream_url(driver, timeout=15)
        if stream_url:
            clear_requests(driver)
            if _set_player_quality(driver, args.quality):
                new_url, new_headers = get_stream_url(driver, timeout=15)
                if new_url: stream_url, req_headers = new_url, new_headers

    if not stream_url: return

    headers = _build_headers(req_headers, referer=driver.current_url)
    os.makedirs(output_dir, exist_ok=True)
    download_video(stream_url, headers, output_path, max_retries=3, quality=args.quality)

    if subtitles:
        lang_code, sub_url = select_subtitle_url(subtitles)
        if sub_url:
            sub_output_path = f"{os.path.splitext(output_path)[0]}.{lang_code}.vtt"
            download_subtitle(sub_url, headers, sub_output_path)


def run_downloader(driver: uc.Chrome, args: argparse.Namespace) -> None:
    if not wait_for_cloudflare_bypass(driver):
        log.error("Cloudflare bypass failed.")
        return

    sanitized_title = sanitize_filename(extract_title_from_url(args.url))
    perform_pre_check(driver)
    select_translator(driver, args.translator)

    if not args.quality:
        qualities = _fetch_available_qualities(driver)
        if qualities:
            options, default_idx = [], 0
            for idx, q in enumerate(qualities):
                label = q + (" (Premium)" if "ultra" in q.lower() else " (Free)")
                options.append(label)
                if "1080p" in q and "ultra" not in q.lower(): default_idx = idx
            options.append("best (highest free quality)")
            
            choice_idx = get_user_choice(options, "Select video quality", timeout=20, default_idx=default_idx)
            args.quality = "best" if choice_idx == len(qualities) else qualities[choice_idx]
        else:
            args.quality = "best"

    seasons, episodes = get_seasons_and_episodes(driver)
    if seasons: _handle_multi_season_series(driver, args, sanitized_title, seasons)
    elif episodes: _handle_single_season_series(driver, args, sanitized_title, episodes)
    else: _handle_movie(driver, args, sanitized_title)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description="Universal rezka.ag Video Downloader")
    parser.add_argument("-u", "--url", help="Rezka.ag URL")
    parser.add_argument("-o", "--output", default="downloads", help="Output directory")
    parser.add_argument("-t", "--translator", help="Translator name substring")
    parser.add_argument("-q", "--quality", help="Video resolution (e.g., 1080, 720)")
    parser.add_argument("-s", "--season", help="Season number")
    parser.add_argument("-e", "--episode", help="Episode or range (e.g., 5 or 1-5)")
    parser.add_argument("--headless", action="store_true", help="Run headless")

    args = parser.parse_args()

    if not args.url:
        args.url = input("Enter Rezka URL: ").strip()
    if not args.url or not validate_url(args.url):
        print("Invalid URL."); sys.exit(1)

    if "--headless" not in sys.argv:
        headless_input = input("Run in background (headless)? [Y/n]: ").strip().lower()
        args.headless = headless_input not in ("n", "no")

    driver: uc.Chrome | None = None
    try:
        driver = init_driver(args.headless)
        driver.get(args.url)
        run_downloader(driver, args)
    except KeyboardInterrupt:
        log.info("Interrupted.")
    except Exception:
        log.exception("Unexpected error occurred")
    finally:
        if driver:
            try: driver.quit()
            except Exception: pass
        log.info("Finished.")

if __name__ == "__main__":
    from multiprocessing import freeze_support
    freeze_support()
    main()
