"""
Universal rezka.ag Video Downloader

Downloads movies and series from rezka.ag / hdrezka domains using
Selenium-based network interception with yt-dlp and ffmpeg backends.
"""

import os
import re
import sys
import time

try:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")
except Exception:
    pass

import atexit
import json
import shutil
import logging
import argparse
import zipfile
import subprocess
import urllib.request
from urllib.parse import urlparse

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
# Logging setup (F16)
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

# Suppress noisy third-party loggers (selenium-wire proxy logs, urllib3, etc.)
for _noisy in ("seleniumwire", "hpack", "urllib3", "selenium.webdriver"):
    logging.getLogger(_noisy).setLevel(logging.WARNING)

# ---------------------------------------------------------------------------
# Constants (F01)
# ---------------------------------------------------------------------------
STREAM_EXCLUDE_KEYWORDS: tuple[str, ...] = (
    "subtitle", "caption", "google", "analytics", "click",
    "metric", "doubleclick", "beacon", "stat.", "ima", "prebid",
)

KEEP_HEADERS: frozenset[str] = frozenset(("referer", "user-agent", "cookie", "origin"))

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def validate_url(url: str) -> bool:
    """Validates that *url* points to a known rezka mirror domain."""
    try:
        parsed = urlparse(url)
    except Exception:
        return False
    if parsed.scheme not in ("http", "https"):
        return False
    host = parsed.netloc.lower().split(":")[0]  # strip port
    if host.startswith("www."):
        host = host[4:]
    allowed = "rezka" in host
    return bool(allowed and parsed.path and parsed.path != "/")


def extract_title_from_url(url: str) -> str:
    """Extracts the name slug from a rezka URL."""
    try:
        parts = url.rstrip("/").split("/")
        last_part = parts[-1]
        if last_part.endswith(".html"):
            last_part = last_part[:-5]
        last_part = last_part.split("?")[0].split("#")[0]
        return last_part
    except Exception:
        return "rezka_video"


def sanitize_filename(name: str) -> str:
    """Sanitizes a string for use as a Windows filename (F18)."""
    name = re.sub(r'[\\/*?:"<>|]', "_", name)
    return name.strip().rstrip(". ")  # Windows forbids trailing dots/spaces


def extract_number(text: str) -> str:
    """Extracts leading digits from season/episode label text."""
    match = re.search(r"\d+", text)
    return match.group(0) if match else text


def _sanitize_header_value(value: str) -> str:
    """Strip CR, LF, and null bytes from header values to prevent CRLF injection (F04)."""
    return re.sub(r"[\r\n\x00]", "", str(value))


def _deduplicate_elements(elements: list) -> list:
    """Remove duplicate Selenium elements that share the same internal id (F27)."""
    seen: set[str] = set()
    unique: list = []
    for el in elements:
        eid = el.id
        if eid not in seen:
            seen.add(eid)
            unique.append(el)
    return unique


def parse_subtitles(subtitle_str: str | None, subtitle_lns: dict | None) -> dict[str, str]:
    """Parses raw subtitle string into a dictionary of {lang_code: url}."""
    subs: dict[str, str] = {}
    if not subtitle_str:
        return subs
    try:
        items = subtitle_str.split(",")
        for item in items:
            item = item.strip()
            if not item:
                continue
            if "[" in item and "]" in item:
                parts = item.split("[", 1)[1].split("]", 1)
                if len(parts) == 2:
                    lang = parts[0].strip()
                    url = parts[1].strip().replace(r"\/", "/")
                    code = None
                    if subtitle_lns and isinstance(subtitle_lns, dict):
                        code = subtitle_lns.get(lang)
                    if code:
                        subs[code.lower()] = url
                    else:
                        lang_lower = lang.lower()
                        if "рус" in lang_lower:
                            subs["ru"] = url
                        elif "анг" in lang_lower or "eng" in lang_lower:
                            subs["en"] = url
                        else:
                            subs[lang_lower] = url
    except Exception as e:
        log.error("Error parsing subtitles: %s", e)
    return subs


def select_subtitle_url(subtitles: dict[str, str]) -> tuple[str | None, str | None]:
    """Selects Russian subtitle URL if available, otherwise English, otherwise first available.
    Returns (lang_code, url) or (None, None)."""
    if not subtitles:
        return None, None
    if "ru" in subtitles:
        return "ru", subtitles["ru"]
    for k in subtitles:
        if "ru" in k:
            return k, subtitles[k]
    if "en" in subtitles:
        return "en", subtitles["en"]
    for k in subtitles:
        if "en" in k:
            return k, subtitles[k]
    first_lang = list(subtitles.keys())[0]
    return first_lang, subtitles[first_lang]


def download_subtitle(url: str, headers: dict[str, str], output_path: str) -> bool:
    """Downloads a subtitle VTT file using the provided headers."""
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=30) as response:
            content = response.read()
        with open(output_path, "wb") as f:
            f.write(content)
        log.info("Subtitles downloaded successfully to: %s", output_path)
        return True
    except Exception as e:
        log.error("Failed to download subtitles from %s: %s", url, e)
        return False


# ---------------------------------------------------------------------------
# Page information helpers (F26)
# ---------------------------------------------------------------------------

def collect_page_info(driver: uc.Chrome) -> tuple[list[str], list[str], list[str]]:
    """Returns (translator_names, season_texts, episode_texts) without side-effects."""
    translators = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, "#translators-list .b-translator__item, .b-translator__item")
    )
    translator_names = [t.text.strip() for t in translators if t.text.strip()]

    seasons = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, ".b-simple_seasons__item, .b-simple_season__item")
    )
    season_texts = [s.text.strip() for s in seasons if s.text.strip()]

    episodes = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
    )
    episode_texts = [e.text.strip() for e in episodes if e.text.strip()]

    return translator_names, season_texts, episode_texts


def print_page_summary(
    translator_names: list[str],
    season_texts: list[str],
    episode_texts: list[str],
) -> None:
    """Prints a human-readable summary of page contents."""
    print("\n--- PAGE CONTENT SUMMARY ---")
    print(f"Translators (Voice Actings) found: {len(translator_names)}")
    if translator_names:
        print(f"  List: {', '.join(translator_names)}")
    else:
        print("  (Using site's default voice acting)")

    if season_texts:
        print(f"Seasons found: {len(season_texts)}")
        print(f"  List: {', '.join(season_texts)}")
    else:
        print("Seasons found: 0 (Single movie or one-season/single-part video)")

    if episode_texts:
        print(f"Episodes found (currently active season): {len(episode_texts)}")
        print(f"  List: {', '.join(episode_texts)}")
    else:
        print("Episodes found: 0 (Single movie/video)")
    print("----------------------------\n")


def perform_pre_check(driver: uc.Chrome) -> tuple[int, int, int]:
    """Scans the page and prints/returns counts of translators, seasons, episodes."""
    translator_names, season_texts, episode_texts = collect_page_info(driver)
    print_page_summary(translator_names, season_texts, episode_texts)
    return len(translator_names), len(season_texts), len(episode_texts)


# ---------------------------------------------------------------------------
# Episode range selection (F09 — clamp bounds)
# ---------------------------------------------------------------------------

def select_episode_range(
    episodes_list: list[dict],
    default_range_str: str | None = None,
) -> list[dict]:
    """Prompts the user to select an episode range or uses *default_range_str*."""
    total_episodes = len(episodes_list)
    if total_episodes == 0:
        return []

    # Map episode numbers (extracted digits) to their index in the list
    ep_map: dict[int, int] = {}
    for idx, ep in enumerate(episodes_list):
        num_str = extract_number(ep["text"])
        try:
            num = int(num_str)
            ep_map[num] = idx
        except ValueError:
            ep_map[idx + 1] = idx

    min_ep = min(ep_map.keys())
    max_ep = max(ep_map.keys())

    start_num, end_num = min_ep, max_ep

    if default_range_str:
        parts = str(default_range_str).split("-")
        try:
            if len(parts) == 2:
                start_num = int(parts[0])
                end_num = int(parts[1])
            else:
                start_num = int(parts[0])
                end_num = start_num
        except ValueError:
            log.warning("Could not parse episode range '%s'. Falling back to interactive choice.", default_range_str)
            default_range_str = None

        # Validate and clamp bounds (F09)
        if default_range_str:
            if not (min_ep <= start_num <= max_ep):
                log.warning(
                    "Start episode %d is out of range (%d-%d). Clamping to %d.",
                    start_num, min_ep, max_ep, min_ep,
                )
                start_num = min_ep
            if not (min_ep <= end_num <= max_ep):
                log.warning(
                    "End episode %d is out of range (%d-%d). Clamping to %d.",
                    end_num, min_ep, max_ep, max_ep,
                )
                end_num = max_ep
            if start_num > end_num:
                log.error("Start episode (%d) > end episode (%d).", start_num, end_num)
                return []

    if not default_range_str:
        print(f"Select episode range (from {min_ep} to {max_ep}):")
        while True:
            try:
                start_input = input(f"Enter start episode ({min_ep}-{max_ep}, default {min_ep}): ").strip()
                if not start_input:
                    start_num = min_ep
                else:
                    start_num = int(start_input)
                if start_num in ep_map:
                    break
                print(f"Invalid episode number. Must be one of: {list(ep_map.keys())}")
            except ValueError:
                print("Please enter a valid number.")

        while True:
            try:
                end_input = input(f"Enter end episode ({start_num}-{max_ep}, default {max_ep}): ").strip()
                if not end_input:
                    end_num = max_ep
                else:
                    end_num = int(end_input)
                if end_num in ep_map and end_num >= start_num:
                    break
                print(f"Invalid episode number. Must be >= start episode ({start_num}) and <= {max_ep}.")
            except ValueError:
                print("Please enter a valid number.")

    selected_episodes: list[dict] = []
    for num in range(start_num, end_num + 1):
        if num in ep_map:
            selected_episodes.append(episodes_list[ep_map[num]])

    return selected_episodes


# ---------------------------------------------------------------------------
# uBlock Origin Lite auto-installer (F07, F21, F25)
# ---------------------------------------------------------------------------

def setup_ubol() -> str | None:
    """Downloads and extracts the latest uBlock Origin Lite extension if not present."""
    extension_dir = os.path.join(os.getcwd(), "ubol_extension")
    if os.path.isdir(extension_dir) and os.listdir(extension_dir):
        return extension_dir

    log.info("Setting up uBlock Origin Lite extension...")

    if os.path.exists(extension_dir):
        shutil.rmtree(extension_dir, ignore_errors=True)
    os.makedirs(extension_dir, exist_ok=True)

    api_url = "https://api.github.com/repos/uBlockOrigin/uBOL-home/releases/latest"
    http_headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        ),
    }

    try:
        req = urllib.request.Request(api_url, headers=http_headers)
        with urllib.request.urlopen(req, timeout=30) as response:  # F25
            data = json.loads(response.read().decode("utf-8"))

        zip_url: str | None = None
        for asset in data.get("assets", []):
            if asset.get("name", "").endswith(".chromium.zip"):
                zip_url = asset.get("browser_download_url")
                break

        if not zip_url:
            raise RuntimeError("Chromium zip asset not found in latest release.")

        zip_path = os.path.join(os.getcwd(), "ubol.zip")
        req_zip = urllib.request.Request(zip_url, headers=http_headers)
        with urllib.request.urlopen(req_zip, timeout=60) as response, open(zip_path, "wb") as out_file:  # F07
            shutil.copyfileobj(response, out_file)

        # Validate the zip contains a manifest.json before trusting it (F07)
        with zipfile.ZipFile(zip_path, "r") as zip_ref:
            if "manifest.json" not in zip_ref.namelist():
                raise RuntimeError("Downloaded archive does not look like a Chrome extension.")
            zip_ref.extractall(extension_dir)

        os.remove(zip_path)
        log.info("uBlock Origin Lite successfully installed.")
        return extension_dir
    except Exception as exc:
        log.error("Failed to automatically set up uBlock Origin Lite: %s", exc)
        if os.path.exists(extension_dir):
            shutil.rmtree(extension_dir, ignore_errors=True)
        return None


# ---------------------------------------------------------------------------
# Chrome version detection (F20 — removed duplicate subprocess import)
# ---------------------------------------------------------------------------

def get_chrome_main_version() -> int | None:
    """Gets Google Chrome's major version on Windows."""
    if os.name != "nt":
        return None

    # 1. Try registry
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
            except Exception:
                continue
    except Exception:
        pass

    # 2. Try common executable paths
    exe_paths = [
        os.path.expandvars(r"%ProgramFiles%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%LocalAppData%\Google\Chrome\Application\chrome.exe"),
    ]
    for path in exe_paths:
        if os.path.exists(path):
            try:
                cmd = f'(Get-Item "{path}").VersionInfo.FileVersion'
                res = subprocess.run(
                    ["powershell", "-Command", cmd],
                    capture_output=True,
                    text=True,
                )
                version_str = res.stdout.strip()
                if version_str:
                    return int(version_str.split(".")[0])
            except Exception:
                continue
    return None


# ---------------------------------------------------------------------------
# Driver initialisation (F13, F19)
# ---------------------------------------------------------------------------

_active_driver: uc.Chrome | None = None


def _safe_quit_driver() -> None:
    """atexit handler — ensures the browser is closed on interpreter shutdown (F19)."""
    global _active_driver
    if _active_driver is not None:
        try:
            _active_driver.quit()
        except Exception:
            pass
        _active_driver = None


atexit.register(_safe_quit_driver)


def init_driver(headless: bool = False) -> uc.Chrome:
    """Initialises undetected_chromedriver with selenium-wire and uBlock Origin Lite."""
    global _active_driver

    options = uc.ChromeOptions()
    if headless:
        options.add_argument("--headless")

    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")

    # Bypass certificate/SSL warnings for selenium-wire proxy (F13 — removed
    # --disable-web-security and --allow-running-insecure-content)
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--ignore-ssl-errors")
    options.add_argument("--allow-insecure-localhost")

    # Disable SafeBrowsing deceptive site warning screens
    options.add_argument("--disable-features=SafeBrowsing")
    options.add_argument("--safebrowsing-disable-download-protection")
    options.add_argument("--safebrowsing-disable-extension-blacklist")
    options.add_argument("--disable-site-isolation-trials")

    # Set up uBlock Origin Lite
    ubol_dir = setup_ubol()
    if ubol_dir:
        options.add_argument(f"--load-extension={ubol_dir}")

    seleniumwire_options = {
        "verify_ssl": False,
        "suppress_connection_errors": True,
    }

    chrome_version = get_chrome_main_version()
    if chrome_version:
        log.info("Detected Google Chrome major version: %d. Forcing ChromeDriver version match.", chrome_version)

    log.info("Starting undetected chromedriver with selenium-wire...")
    driver = uc.Chrome(
        version_main=chrome_version,
        options=options,
        seleniumwire_options=seleniumwire_options,
    )

    _active_driver = driver
    return driver


# ---------------------------------------------------------------------------
# Cloudflare bypass (F05)
# ---------------------------------------------------------------------------

def wait_for_cloudflare_bypass(
    driver: uc.Chrome,
    timeout: int = 300,
    poll_interval: float = 0.5,
) -> bool:
    """Detects and waits for the Cloudflare challenge to be solved."""
    log.info("Checking for Cloudflare challenge...")
    start_time = time.time()
    last_print = 0.0

    while True:
        elapsed = time.time() - start_time
        if elapsed >= timeout:
            return False

        try:
            elements = driver.find_elements(
                By.CSS_SELECTOR, ".b-post, #inside-main, #translators-list, #cdnplayer"
            )
            if elements:
                log.info("Rezka page elements detected. Cloudflare bypassed.")
                return True
        except Exception:
            pass

        title = ""
        try:
            title = driver.title
        except Exception:
            pass

        if "Just a moment" in title or "Cloudflare" in title:
            if elapsed - last_print >= 10:
                remaining = int(timeout - elapsed)
                log.info("  Waiting... (%ds remaining) | Page title: '%s'", remaining, title)
                last_print = elapsed
        elif elapsed - last_print >= 10:
            remaining = int(timeout - elapsed)
            log.info("  Waiting... (%ds remaining) | Page title: '%s'", remaining, title)
            last_print = elapsed

        time.sleep(poll_interval)


# ---------------------------------------------------------------------------
# Interactive user choice (F12)
# ---------------------------------------------------------------------------

def get_user_choice(
    options: list[str],
    prompt_text: str,
    timeout: int = 15,
    default_idx: int = 0,
) -> int:
    """Interactive selector with msvcrt timeout; falls back to plain input()."""
    print("\nAvailable options:")
    for idx, opt in enumerate(options):
        print(f"  [{idx + 1}] {opt}")

    prompt = f"{prompt_text} (default [{default_idx + 1}] in {timeout}s): "

    try:
        import msvcrt

        start_time = time.time()
        input_str = ""
        sys.stdout.write(prompt)
        sys.stdout.flush()
        while time.time() - start_time < timeout:
            if msvcrt.kbhit():
                char = msvcrt.getch()
                if char in (b"\r", b"\n"):
                    print()
                    val = input_str.strip()
                    if not val:
                        return default_idx
                    try:
                        choice = int(val) - 1
                        if 0 <= choice < len(options):
                            return choice
                    except ValueError:
                        pass
                    print("Invalid selection. Try again.")
                    sys.stdout.write(prompt)
                    sys.stdout.flush()
                    input_str = ""
                elif char == b"\b":
                    if len(input_str) > 0:
                        input_str = input_str[:-1]
                        sys.stdout.write("\b \b")
                        sys.stdout.flush()
                else:
                    try:
                        decoded_char = char.decode("utf-8")
                        input_str += decoded_char
                        sys.stdout.write(decoded_char)
                        sys.stdout.flush()
                    except Exception:
                        pass
            time.sleep(0.1)  # F12 — reduced from 0.05
        print(f"\nTimeout. Selecting default option: {options[default_idx]}")
        return default_idx
    except (ImportError, Exception):
        # Non-Windows or non-interactive fallback
        try:
            val = input(prompt)
            if not val.strip():
                return default_idx
            choice = int(val) - 1
            if 0 <= choice < len(options):
                return choice
        except Exception:
            pass
        return default_idx


# ---------------------------------------------------------------------------
# Translator selection
# ---------------------------------------------------------------------------

def select_translator(driver: uc.Chrome, preferred_name: str | None = None) -> str | None:
    """Identifies and selects the appropriate translator (voice acting)."""
    try:
        WebDriverWait(driver, 15).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "#translators-list, .b-translator__item, #cdnplayer"))
        )
    except Exception:
        log.info("Timeout waiting for translators list to appear.")

    translators = driver.find_elements(By.CSS_SELECTOR, "#translators-list .b-translator__item, .b-translator__item")
    if not translators:
        log.info("No voice acting (translator) list found. Using the page's default stream.")
        return None

    translator_options: list[dict] = []
    for t in translators:
        name = t.text.strip()
        translator_options.append({"element": t, "name": name})

    log.info("Detected %d translator(s).", len(translator_options))
    selected_opt: dict | None = None

    if preferred_name:
        for opt in translator_options:
            if preferred_name.lower() in opt["name"].lower():
                selected_opt = opt
                log.info("Auto-selected preferred translator: %s", opt["name"])
                break
        if not selected_opt:
            log.info("Preferred translator '%s' not found. Falling back to selection.", preferred_name)

    if not selected_opt:
        choice_idx = get_user_choice(
            [opt["name"] for opt in translator_options],
            "Select translator",
            timeout=15,
            default_idx=0,
        )
        selected_opt = translator_options[choice_idx]

    # Click selected translator if it isn't active
    is_active = "active" in selected_opt["element"].get_attribute("class")
    if not is_active:
        log.info("Switching translator to: %s", selected_opt["name"])
        driver.execute_script("arguments[0].click();", selected_opt["element"])
        time.sleep(1.0)  # Wait for page elements to reload
    else:
        log.info("Translator %s is already active.", selected_opt["name"])

    return selected_opt["name"]


# ---------------------------------------------------------------------------
# Player / network helpers (F06, F01, F22)
# ---------------------------------------------------------------------------

def click_player(driver: uc.Chrome) -> None:
    """Triggers the video player container to start video loading."""
    try:
        time.sleep(0.3)
        selectors = [
            "iframe#oframecdnplayer",
            "iframe[id*='cdnplayer']",
            "div#cdnplayer",
            "div#player",
            "div#cdnplayer-container",
            "div#videoplayer",
        ]
        player = None
        for selector in selectors:
            try:
                player = driver.find_element(By.CSS_SELECTOR, selector)
                if player.is_displayed():
                    break
            except Exception:
                continue

        if player:
            if player.tag_name == "iframe":
                driver.switch_to.frame(player)
                try:
                    play_selectors = [
                        "div.vjs-big-play-button",
                        "button.vjs-big-play-button",
                        ".play-btn",
                        "[aria-label='Play']",
                        "body",
                    ]
                    clicked = False
                    for play_sel in play_selectors:
                        try:
                            play_btn = driver.find_element(By.CSS_SELECTOR, play_sel)
                            driver.execute_script("arguments[0].click();", play_btn)
                            clicked = True
                            break
                        except Exception:
                            continue
                    if not clicked:
                        # F22 — ActionChains imported at top-level
                        ActionChains(driver).move_to_element(
                            driver.find_element(By.TAG_NAME, "body")
                        ).click().perform()
                finally:
                    driver.switch_to.default_content()
            else:
                driver.execute_script("arguments[0].click();", player)

            log.info("Video playback trigger fired.")
        else:
            log.warning("No video player elements detected.")
    except Exception as exc:
        log.error("Error triggering player click: %s", exc)


def clear_requests(driver: uc.Chrome) -> None:
    """Clears the selenium-wire network interception log (F06)."""
    try:
        del driver.requests
    except AttributeError:
        pass  # selenium-wire not active or already cleared


def get_stream_url(driver: uc.Chrome, timeout: int = 30) -> tuple[str | None, dict | None]:
    """Intercepts and extracts the direct .m3u8 or .mp4 link from network logs (F01)."""
    start_time = time.time()
    while time.time() - start_time < timeout:
        for request in list(driver.requests):
            if not request.response:
                continue
            url: str = request.url

            # Check for stream file types
            url_path = url.split("?")[0]
            is_m3u8 = ".m3u8" in url
            is_mp4 = url_path.endswith(".mp4")
            is_stream = is_m3u8 or is_mp4

            # Exclude known non-stream URLs
            is_excluded = any(k in url for k in STREAM_EXCLUDE_KEYWORDS)

            # Reject individual TS/AAC segments — only accept playlists or full MP4s
            filename = url_path.split("/")[-1]
            is_segment = bool(re.search(r"\.(ts|aac)\b", filename))

            if is_stream and not is_excluded and not is_segment:
                return url, request.headers
        time.sleep(0.5)

    # Debug output on timeout
    log.debug("Interception timed out. Sample of intercepted requests (up to 30):")
    intercepted_list = list(driver.requests)
    for idx, r in enumerate(intercepted_list[:30]):
        status_code = r.response.status_code if r.response else "No Response"
        log.debug("  [%d] %s - %s", idx + 1, status_code, r.url[:120])
    return None, None


def _set_player_quality(driver: uc.Chrome, quality: str) -> bool:
    """Attempts to switch PlayerJS quality to requested resolution via UI simulation.
    Returns True if the JS click succeeded, False otherwise."""
    js_code = """
        var targetQuality = arguments[0];
        var done = arguments[arguments.length - 1];
        
        var playerDiv = document.querySelector('#cdnplayer');
        if (!playerDiv) return done("No player");
        playerDiv.dispatchEvent(new MouseEvent('mousemove', {bubbles: true}));
        
        var gear = document.querySelector('.pjs-settings') || document.querySelector('pjsdiv[title="Настройки"]');
        if (!gear) {
            var all = document.querySelectorAll('pjsdiv');
            gear = Array.from(all).find(e => e.className && typeof e.className === 'string' && e.className.includes('pjs-settings'));
        }
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
                
                if (targets.length === 0) return done("No quality options found");
                
                var target;
                if (targetQuality === "best") {
                    target = targets[0];
                } else {
                    target = targets.find(e => e.innerText.includes(targetQuality));
                }
                
                if (!target) return done("Quality not found");
                
                target.click();
                done("Success");
            }, 300);
        }, 300);
    """
    try:
        # Increase script timeout for the async wait
        driver.set_script_timeout(5)
        res = driver.execute_async_script(js_code, str(quality))
        if res == "Success":
            return True
        log.debug("Could not switch player quality via UI: %s", res)
    except Exception as e:
        log.debug("Error during player quality switch: %s", e)
    return False


# ---------------------------------------------------------------------------
# Download functions (F04, F11, F14)
# ---------------------------------------------------------------------------

def clear_trash(data: str) -> str:
    """Decodes the obfuscated stream URL string by clearing trash characters."""
    import base64
    from itertools import product
    trash_list = ["@", "#", "!", "^", "$"]
    trash_codes = []
    for i in range(2, 4):
        for chars in product(trash_list, repeat=i):
            trash_codes.append(base64.b64encode("".join(chars).encode("utf-8")))
    
    arr = data.replace("#h", "").split("//_//")
    trash_str = "".join(arr)
    for code in trash_codes:
        temp = code.decode("utf-8")
        trash_str = trash_str.replace(temp, "")
    
    try:
        return base64.b64decode(trash_str + "==").decode("utf-8", errors="ignore")
    except Exception:
        return trash_str


def parse_streams(decrypted_str: str) -> dict[str, str]:
    """Parses decrypted qualities and stream URL options."""
    streams: dict[str, str] = {}
    for item in decrypted_str.split(","):
        if "[" in item and "]" in item:
            parts = item.split("[", 1)[1].split("]", 1)
            if len(parts) == 2:
                q = parts[0].strip()
                q_clean = re.sub(r'<[^>]*>', '', q).strip()
                url_options = parts[1].strip()
                streams[q_clean] = url_options
    return streams


def select_quality_url(streams: dict[str, str], requested_quality: str) -> str:
    """Selects the best available URL based on the requested quality."""
    if requested_quality in streams:
        raw_url_options = streams[requested_quality]
        links = raw_url_options.split(" or ")
        for link in links:
            if ":hls:manifest.m3u8" in link:
                return link
        return links[0]

    quality_map: list[tuple[int, bool, str]] = []
    for key in streams:
        match = re.search(r'(\d+)', key)
        if match:
            res = int(match.group(1))
            is_ultra = "ultra" in key.lower()
            quality_map.append((res, is_ultra, key))
    
    # Sort: resolution descending, then standard (non-ultra) first, so standard is preferred!
    quality_map.sort(key=lambda x: (x[0], 0 if x[1] else 1), reverse=True)
    if not quality_map:
        raise ValueError("No video qualities found in stream data.")
    
    # Let's filter out 'ultra' qualities if requested_quality is not explicitly 'ultra'
    # and if there are standard qualities available.
    non_ultra_map = [x for x in quality_map if not x[1]]
    active_map = non_ultra_map if non_ultra_map else quality_map
    
    if requested_quality.lower() == "ultra":
        # Sort ultra first for explicit requests
        quality_map.sort(key=lambda x: (x[0], 1 if x[1] else 0), reverse=True)
        active_map = quality_map
        
    chosen_key = None
    if requested_quality in ("best", "ultra"):
        chosen_key = active_map[0][2]
    else:
        try:
            req_res = int(re.search(r'\d+', requested_quality).group(0))
        except Exception:
            req_res = 99999
            
        for res, is_ultra, key in active_map:
            if res <= req_res:
                chosen_key = key
                break
        if not chosen_key:
            chosen_key = active_map[-1][2]
            
    raw_url_options = streams[chosen_key]
    links = raw_url_options.split(" or ")
    for link in links:
        if ":hls:manifest.m3u8" in link:
            return link
    return links[0]


def _get_stream_via_fetch(
    driver: uc.Chrome,
    quality: str = "best",
    season_num: str | None = None,
    episode_num: str | None = None,
) -> tuple[str | None, dict[str, str] | None, dict[str, str]]:
    """Retrieves stream URL and subtitles directly using browser-side fetch and local decryption."""
    try:
        post_id = driver.execute_script("""
            var el = document.querySelector('#post_id') || document.querySelector('#send-video-issue');
            return el ? (el.value || el.getAttribute('data-id')) : null;
        """)
        if not post_id:
            log.error("Could not find post_id in DOM.")
            return None, None, {}
            
        translator_id = driver.execute_script("""
            var el = document.querySelector('#translators-list .b-translator__item.active');
            if (el) return el.getAttribute('data-translator_id');
            var scripts = Array.from(document.querySelectorAll('script'));
            for (var s of scripts) {
                var txt = s.textContent;
                var match = txt.match(/sof\\.tv\\.initCDN(?:Series|Movies)Events\\(\\s*\\d+\\s*,\\s*(\\d+)/);
                if (match) return match[1];
            }
            return null;
        """)
        if not translator_id:
            log.error("Could not find active translator_id.")
            return None, None, {}
            
        fetch_js = """
            var params = arguments[0];
            var callback = arguments[arguments.length - 1];
            fetch('/ajax/get_cdn_series/', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
                    'X-Requested-With': 'XMLHttpRequest'
                },
                body: new URLSearchParams(params).toString()
            })
            .then(r => r.json())
            .then(data => callback(data))
            .catch(err => callback({success: false, error: err.toString()}));
        """
        
        params = {
            "id": post_id,
            "translator_id": translator_id,
        }
        if season_num and episode_num:
            params["season"] = str(season_num)
            params["episode"] = str(episode_num)
            params["action"] = "get_stream"
        else:
            params["action"] = "get_movie"
            
        driver.set_script_timeout(10)
        result = driver.execute_async_script(fetch_js, params)
        
        if not result or not result.get("success"):
            log.error("Fetch request failed: %s", result.get("error") if result else "No response")
            return None, None, {}
            
        url_str = result.get("url")
        if not url_str:
            log.error("No url field in fetch response.")
            return None, None, {}
            
        decrypted = clear_trash(url_str)
        streams = parse_streams(decrypted)
        if not streams:
            log.error("Failed to parse streams from decrypted data.")
            return None, None, {}
            
        chosen_url = select_quality_url(streams, quality)
        log.info("Successfully fetched direct URL for quality %s: %s", quality, chosen_url[:120] + "...")
        
        try:
            current_host = urlparse(driver.current_url).netloc.lower().split(":")[0]
            if current_host.startswith("www."):
                current_host = current_host[4:]
        except Exception:
            current_host = "rezka.ag"

        origin_request = None
        for r in reversed(list(driver.requests)):
            if r.headers and current_host in r.url:
                origin_request = r
                break
        
        subtitles_raw = result.get("subtitle")
        subtitle_lns = result.get("subtitle_lns")
        subtitles_dict = parse_subtitles(subtitles_raw, subtitle_lns)

        req_headers = origin_request.headers if origin_request else None
        return chosen_url, req_headers, subtitles_dict
        
    except Exception as exc:
        log.exception("Error fetching stream URL via AJAX")
        return None, None, {}

# ---------------------------------------------------------------------------

def download_with_ytdlp(stream_url: str, headers: dict[str, str], output_path: str, quality: str = "best") -> None:
    """Downloads HLS/MP4 streams using the yt-dlp API."""
    log.info("Downloading stream with yt-dlp to: %s (Max resolution: %s)", output_path, quality)
    
    fmt = f"bestvideo[height<={quality}]+bestaudio/best[height<={quality}]/best" if quality.isdigit() else "best"
    
    ydl_opts = {
        "outtmpl": output_path,
        "format": fmt,
        "merge_output_format": "mp4",
        "http_headers": headers,
        "quiet": False,
        "noprogress": False,
        "concurrent_fragment_downloads": 3,
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        ydl.download([stream_url])


def download_with_ffmpeg(stream_url: str, headers: dict[str, str], output_path: str) -> None:
    """Fallback stream download directly with an ffmpeg subprocess (F04)."""
    log.info("Downloading stream with ffmpeg to: %s", output_path)
    headers_str = "".join(
        f"{k}: {_sanitize_header_value(v)}\r\n" for k, v in headers.items()
    )

    cmd = [
        "ffmpeg",
        "-y",
        "-headers", headers_str,
        "-i", stream_url,
        "-c", "copy",
        "-bsf:a", "aac_adtstoasc",
        output_path,
    ]

    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"ffmpeg download failed: {result.stderr}")


def download_video(
    stream_url: str,
    headers: dict[str, str],
    output_path: str,
    max_retries: int = 3,
    quality: str = "best",
) -> None:
    """Robust download coordinator: retries yt-dlp N times, then ffmpeg as final fallback (F11)."""
    last_err: Exception | None = None
    for attempt in range(1, max_retries + 1):
        log.info("Download attempt %d/%d (yt-dlp)...", attempt, max_retries)
        try:
            download_with_ytdlp(stream_url, headers, output_path, quality)
            log.info("Downloaded successfully via yt-dlp.")
            return
        except Exception as exc:
            last_err = exc
            log.warning("yt-dlp failed (attempt %d): %s", attempt, exc)
            if attempt < max_retries:
                log.info("Retrying in 5 seconds...")
                time.sleep(5)

    log.info("yt-dlp exhausted retries. Trying ffmpeg as final fallback...")
    try:
        download_with_ffmpeg(stream_url, headers, output_path)
        log.info("Downloaded successfully via ffmpeg.")
    except Exception as exc:
        raise RuntimeError(f"All download attempts failed for: {output_path}") from (last_err or exc)


# ---------------------------------------------------------------------------
# Shared episode-download helper (F02, F10, F14)
# ---------------------------------------------------------------------------

def _build_headers(req_headers: dict | None, referer: str | None = None) -> dict[str, str]:
    """Extracts and normalises the subset of request headers needed for download (F14)."""
    headers: dict[str, str] = {}
    if req_headers:
        for k, v in req_headers.items():
            if k.lower() in KEEP_HEADERS:
                headers[k.title()] = v  # normalise capitalisation
    if "Referer" not in headers:
        headers["Referer"] = referer or "https://rezka.ag/"
    return headers


def _download_episode(
    driver: uc.Chrome,
    ep_data: dict,
    output_dir: str,
    episode_file: str,
    quality: str = "best",
    season_num: str = "1",
) -> None:
    """Clicks an episode, intercepts its stream URL, and downloads it (F02)."""
    output_path = os.path.join(output_dir, episode_file)

    # Skip if already downloaded
    if os.path.exists(output_path):
        log.info("File already exists: %s. Skipping.", output_path)
        return

    # Navigate to episode (refetching element to prevent stale references)
    if ep_data["id"]:
        ep_el = WebDriverWait(driver, 15).until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, f"[data-episode_id='{ep_data['id']}']"))
        )
    else:
        episodes = driver.find_elements(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
        ep_el = episodes[ep_data["index"]]

    clear_requests(driver)
    driver.execute_script("arguments[0].click();", ep_el)

    # F10 — wait for DOM readiness instead of magic sleep
    try:
        WebDriverWait(driver, 10).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, ".b-simple_episode__item.active, .b-simple_episodes__item.active"))
        )
    except Exception:
        time.sleep(1.0)  # graceful fallback

    log.info("Fetching stream URL via browser-side AJAX...")
    subtitles = {}
    fetch_result = _get_stream_via_fetch(driver, quality=quality, season_num=season_num, episode_num=ep_data["num"])
    stream_url, req_headers, subtitles = fetch_result

    if not stream_url:
        log.warning("AJAX fetch failed. Falling back to player network interception...")
        click_player(driver)
        log.info("Waiting for initial streaming link to trigger...")
        stream_url, req_headers = get_stream_url(driver, timeout=15)
        
        if stream_url:
            log.info("Attempting to select %s quality in player UI...", quality)
            clear_requests(driver)
            if _set_player_quality(driver, quality):
                log.info("Intercepting new streaming link for selected quality...")
                new_url, new_headers = get_stream_url(driver, timeout=15)
                if new_url:
                    stream_url, req_headers = new_url, new_headers
                    log.info("Successfully captured new stream.")
                else:
                    log.warning("Failed to capture new stream. Falling back to initial stream.")

    if not stream_url:
        log.error("Error: timed out without finding stream URL. Skipping episode.")
        return

    headers = _build_headers(req_headers, referer=driver.current_url)
    os.makedirs(output_dir, exist_ok=True)
    download_video(stream_url, headers, output_path, max_retries=3, quality=quality)

    if subtitles:
        lang_code, sub_url = select_subtitle_url(subtitles)
        if sub_url and lang_code:
            video_base_path = os.path.splitext(output_path)[0]
            sub_output_path = f"{video_base_path}.{lang_code}.vtt"
            log.info("Found subtitles for language '%s'. Downloading...", lang_code)
            download_subtitle(sub_url, headers, sub_output_path)


# ---------------------------------------------------------------------------
# Content-type detection
# ---------------------------------------------------------------------------

def get_seasons_and_episodes(driver: uc.Chrome) -> tuple[list, list]:
    """Detects available season and episode elements (F27)."""
    seasons = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, ".b-simple_seasons__item, .b-simple_season__item")
    )
    episodes = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
    )
    return seasons, episodes


# ---------------------------------------------------------------------------
# run_downloader — decomposed (F15)
# ---------------------------------------------------------------------------

def _handle_multi_season_series(
    driver: uc.Chrome,
    args: argparse.Namespace,
    sanitized_title: str,
    seasons: list,
) -> None:
    """Handles download workflow for multi-season series (F15)."""
    log.info("Content Type: Series (Multiple Seasons). Found %d season(s).", len(seasons))

    season_info: list[dict] = []
    for idx, s in enumerate(seasons):
        s_id = s.get_attribute("data-season_id")
        s_text = s.text.strip()
        season_info.append({
            "id": s_id,
            "text": s_text,
            "num": extract_number(s_text),
            "index": idx,
        })

    # Select Season
    selected_season_num: str | None = None
    if args.season:
        selected_season_num = str(args.season)
    else:
        season_choices = [s["num"] for s in season_info]
        print(f"Available seasons: {', '.join(season_choices)}")
        while True:
            choice = input(f"Select season number ({', '.join(season_choices)}, default {season_choices[0]}): ").strip()
            if not choice:
                selected_season_num = season_choices[0]
                break
            if choice in season_choices:
                selected_season_num = choice
                break
            print("Invalid season selection. Please choose from the list.")

    s_data = next((s for s in season_info if s["num"] == selected_season_num), None)
    if not s_data:
        log.error("Error: Selected season '%s' not found.", selected_season_num)
        return

    log.info("Switching to Season: %s", s_data["text"])

    # Click season (refetching to prevent stale elements)
    if s_data["id"]:
        season_el = WebDriverWait(driver, 15).until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, f"[data-season_id='{s_data['id']}']"))
        )
    else:
        seasons = driver.find_elements(By.CSS_SELECTOR, ".b-simple_seasons__item, .b-simple_season__item")
        season_el = seasons[s_data["index"]]

    driver.execute_script("arguments[0].click();", season_el)
    time.sleep(1.0)  # Wait for episode list to update

    # Detect episodes in selected season
    episodes = _deduplicate_elements(
        driver.find_elements(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
    )
    log.info("Found %d episode(s) in Season %s.", len(episodes), s_data["num"])

    episode_info: list[dict] = []
    for ep_idx, e in enumerate(episodes):
        ep_id = e.get_attribute("data-episode_id")
        ep_text = e.text.strip()
        episode_info.append({
            "id": ep_id,
            "text": ep_text,
            "num": extract_number(ep_text),
            "index": ep_idx,
        })

    selected_episodes = select_episode_range(episode_info, args.episode)
    if not selected_episodes:
        log.info("No episodes selected.")
        return

    log.info(
        "Selected %d episode(s) to download: from Episode %s to Episode %s",
        len(selected_episodes),
        selected_episodes[0]["num"],
        selected_episodes[-1]["num"],
    )

    for ep_data in selected_episodes:
        log.info("Processing Episode: %s", ep_data["text"])
        season_dir = f"Season_{s_data['num']}"
        episode_file = f"{sanitized_title}_S{s_data['num']}_Ep_{ep_data['num']}.mp4"
        output_dir = os.path.join(args.output, sanitized_title, season_dir)
        _download_episode(
            driver,
            ep_data,
            output_dir,
            episode_file,
            quality=args.quality,
            season_num=s_data['num'],
        )


def _handle_single_season_series(
    driver: uc.Chrome,
    args: argparse.Namespace,
    sanitized_title: str,
    episodes: list,
) -> None:
    """Handles download workflow for single-season series (F15)."""
    log.info("Content Type: Series (Single Season). Found %d episode(s).", len(episodes))

    episode_info: list[dict] = []
    for ep_idx, e in enumerate(episodes):
        ep_id = e.get_attribute("data-episode_id")
        ep_text = e.text.strip()
        episode_info.append({
            "id": ep_id,
            "text": ep_text,
            "num": extract_number(ep_text),
            "index": ep_idx,
        })

    selected_episodes = select_episode_range(episode_info, args.episode)
    if not selected_episodes:
        log.info("No episodes selected.")
        return

    log.info(
        "Selected %d episode(s) to download: from Episode %s to Episode %s",
        len(selected_episodes),
        selected_episodes[0]["num"],
        selected_episodes[-1]["num"],
    )

    for ep_data in selected_episodes:
        log.info("Processing Episode: %s", ep_data["text"])
        season_dir = "Season_1"
        episode_file = f"{sanitized_title}_Ep_{ep_data['num']}.mp4"
        output_dir = os.path.join(args.output, sanitized_title, season_dir)
        _download_episode(driver, ep_data, output_dir, episode_file, quality=args.quality)


def _handle_movie(
    driver: uc.Chrome,
    args: argparse.Namespace,
    sanitized_title: str,
) -> None:
    """Handles download workflow for a standalone movie (F15)."""
    log.info("Content Type: Movie.")
    output_dir = os.path.join(args.output, sanitized_title)
    output_path = os.path.join(output_dir, f"{sanitized_title}.mp4")

    if os.path.exists(output_path):
        log.info("Movie file already exists: %s. Skipping.", output_path)
        return

    log.info("Fetching stream URL via browser-side AJAX...")
    subtitles = {}
    fetch_result = _get_stream_via_fetch(driver, quality=args.quality)
    stream_url, req_headers, subtitles = fetch_result
    
    if not stream_url:
        log.warning("AJAX fetch failed. Falling back to player network interception...")
        click_player(driver)
        log.info("Waiting for initial streaming link to trigger...")
        stream_url, req_headers = get_stream_url(driver, timeout=15)
        
        if stream_url:
            log.info("Attempting to select %s quality in player UI...", args.quality)
            clear_requests(driver)
            if _set_player_quality(driver, args.quality):
                log.info("Intercepting new streaming link for selected quality...")
                new_url, new_headers = get_stream_url(driver, timeout=15)
                if new_url:
                    stream_url, req_headers = new_url, new_headers
                    log.info("Successfully captured new stream.")
                else:
                    log.warning("Failed to capture new stream. Falling back to initial stream.")

    if not stream_url:
        log.error("Error: Network interceptor timed out without finding a video stream URL.")
        return

    headers = _build_headers(req_headers, referer=driver.current_url)
    os.makedirs(output_dir, exist_ok=True)
    download_video(stream_url, headers, output_path, max_retries=3, quality=args.quality)

    if subtitles:
        lang_code, sub_url = select_subtitle_url(subtitles)
        if sub_url and lang_code:
            video_base_path = os.path.splitext(output_path)[0]
            sub_output_path = f"{video_base_path}.{lang_code}.vtt"
            log.info("Found subtitles for language '%s'. Downloading...", lang_code)
            download_subtitle(sub_url, headers, sub_output_path)


def _fetch_available_qualities(driver: uc.Chrome) -> list[str]:
    """Fetches the list of quality keys for the first episode or movie."""
    try:
        seasons = driver.find_elements(By.CSS_SELECTOR, ".b-simple_seasons__item, .b-simple_season__item")
        episodes = driver.find_elements(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
        
        season_num = "1"
        episode_num = None
        if seasons or episodes:
            ep_el = driver.find_element(By.CSS_SELECTOR, ".b-simple_episodes__item, .b-simple_episode__item")
            episode_num = ep_el.text.strip()
            match = re.search(r'\d+', episode_num)
            episode_num = match.group(0) if match else "1"
            
            if seasons:
                s_el = driver.find_element(By.CSS_SELECTOR, ".b-simple_seasons__item, .b-simple_season__item")
                s_text = s_el.text.strip()
                match = re.search(r'\d+', s_text)
                season_num = match.group(0) if match else "1"
                
        post_id = driver.execute_script("""
            var el = document.querySelector('#post_id') || document.querySelector('#send-video-issue');
            return el ? (el.value || el.getAttribute('data-id')) : null;
        """)
        translator_id = driver.execute_script("""
            var el = document.querySelector('#translators-list .b-translator__item.active');
            if (el) return el.getAttribute('data-translator_id');
            var scripts = Array.from(document.querySelectorAll('script'));
            for (var s of scripts) {
                var txt = s.textContent;
                var match = txt.match(/sof\\.tv\\.initCDN(?:Series|Movies)Events\\(\\s*\\d+\\s*,\\s*(\\d+)/);
                if (match) return match[1];
            }
            return null;
        """)
        if not post_id or not translator_id:
            return []
            
        fetch_js = """
            var params = arguments[0];
            var callback = arguments[arguments.length - 1];
            fetch('/ajax/get_cdn_series/', {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
                    'X-Requested-With': 'XMLHttpRequest'
                },
                body: new URLSearchParams(params).toString()
            })
            .then(r => r.json())
            .then(data => callback(data))
            .catch(err => callback({success: false, error: err.toString()}));
        """
        
        params = {
            "id": post_id,
            "translator_id": translator_id,
        }
        if episode_num:
            params["season"] = str(season_num)
            params["episode"] = str(episode_num)
            params["action"] = "get_stream"
        else:
            params["action"] = "get_movie"
            
        driver.set_script_timeout(10)
        result = driver.execute_async_script(fetch_js, params)
        if result and result.get("success") and result.get("url"):
            decrypted = clear_trash(result.get("url"))
            streams = parse_streams(decrypted)
            return list(streams.keys())
    except Exception:
        pass
    return []


def run_downloader(driver: uc.Chrome, args: argparse.Namespace) -> None:
    """Main orchestrator: Cloudflare bypass → pre-check → translator → download."""
    # 1. Handle Cloudflare
    if not wait_for_cloudflare_bypass(driver):
        log.error("Could not bypass Cloudflare. Program exiting.")
        return

    # 2. Extract title from link
    title_from_url = extract_title_from_url(args.url)
    sanitized_title = sanitize_filename(title_from_url)
    log.info("Extracted Title from URL: %s (Sanitized: %s)", title_from_url, sanitized_title)

    # 3. Perform Pre-check
    perform_pre_check(driver)

    # 4. Translator Selection
    select_translator(driver, args.translator)

    # 4.5 Quality Selection
    if not args.quality:
        qualities = _fetch_available_qualities(driver)
        if qualities:
            options = []
            default_idx = 0
            for idx, q in enumerate(qualities):
                label = q
                if "ultra" in q.lower():
                    label += " (Premium / True 1080p)"
                elif "1080p" in q.lower():
                    label += " (Free / 720p)"
                elif "720p" in q.lower():
                    label += " (Free / 480p)"
                elif "480p" in q.lower():
                    label += " (Free / 360p)"
                elif "360p" in q.lower():
                    label += " (Free / 240p)"
                options.append(label)
                if "1080p" in q and "ultra" not in q.lower():
                    default_idx = idx
            
            options.append("best (highest free quality)")
            if default_idx == 0 and len(qualities) > 0 and "ultra" in qualities[0].lower():
                if len(qualities) > 1:
                    default_idx = 1
                    
            choice_idx = get_user_choice(
                options,
                "Select video quality",
                timeout=20,
                default_idx=default_idx
            )
            if choice_idx == len(qualities):
                args.quality = "best"
            else:
                args.quality = qualities[choice_idx]
        else:
            args.quality = "best"

    # 5. Detect type: movie or series, then dispatch
    seasons, episodes = get_seasons_and_episodes(driver)

    if seasons:
        _handle_multi_season_series(driver, args, sanitized_title, seasons)
    elif episodes:
        _handle_single_season_series(driver, args, sanitized_title, episodes)
    else:
        _handle_movie(driver, args, sanitized_title)


# ---------------------------------------------------------------------------
# CLI entry point (F24)
# ---------------------------------------------------------------------------

def main() -> None:
    """CLI entry point."""
    parser = argparse.ArgumentParser(description="Universal rezka.ag Video Downloader")
    parser.add_argument("-u", "--url", help="Rezka.ag movie/series URL")
    parser.add_argument("-o", "--output", default="downloads", help="Output directory (default: 'downloads')")
    parser.add_argument("-t", "--translator", help="Preferred voice acting translator name (case-insensitive substring)")
    parser.add_argument("-q", "--quality", help="Preferred maximum video resolution (e.g. 1080, 720, 480, 360) or 'best'")
    parser.add_argument("-s", "--season", help="Specific season number to download (optional)")
    parser.add_argument("-e", "--episode", help="Specific episode or episode range to download, e.g. 5 or 1-5 (optional)")
    parser.add_argument("--headless", action="store_true", help="Run browser in headless mode (risk of Turnstile challenge failures)")

    args = parser.parse_args()

    if not args.url:
        args.url = input("Enter the rezka page or mirror URL (e.g. rezka.ag / rezka-ua.pub): ").strip()

    if not args.url or not validate_url(args.url):
        print("Invalid URL format. Please enter a valid rezka or hdrezka mirror URL.")
        sys.exit(1)

    # Headless prompt if not passed in CLI
    is_headless_explicit = "--headless" in sys.argv
    if not is_headless_explicit:
        headless_input = input("Run browser in background (headless mode)? [Y/n] (default Y): ").strip().lower()
        args.headless = headless_input not in ("n", "no")

    print("\nURL accepted. Initializing browser...")
    time.sleep(0.5)

    driver: uc.Chrome | None = None
    try:
        driver = init_driver(args.headless)
        driver.get(args.url)
        run_downloader(driver, args)
    except KeyboardInterrupt:
        log.info("Process interrupted by user.")
    except Exception:
        log.exception("An unexpected error occurred")  # F24 — preserves full traceback
    finally:
        if driver:
            log.info("Closing browser...")
            try:
                driver.quit()
            except Exception:
                pass
            driver = None
        log.info("Finished.")


if __name__ == "__main__":
    from multiprocessing import freeze_support
    freeze_support()
    main()
