#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Catálogo web de solo lectura para bases SQLite de addons de vídeo.
Modo reproductor externo universal (Android, TV Box, Web Desktop).
Diseño UI: Glassmorphism / Estilo Cristal.
Incluye:
  - Navegación moderna tipo pastillas (Pill Navbar) flotante
  - Hero banner interactivo con controles, segmentos y navegación fluida
  - Carruseles con flechas Glass de desplazamiento horizontal (avanzar/retroceder)
  - Badges de carátula independientes (tipo de contenido arriba a la derecha, sin colisiones)
  - Registro de avance granular con estado "Siguiendo" y "Vista Completa"
  - Botón Quick Play dinámico inteligente por capítulo
  - Mi Área unificada (Mi Lista, Ya Vistas, Historial de reproducciones)
  - Motor de lectura SQLite ultra-optimizado con indexación y pool por hilo
"""

from __future__ import annotations

import argparse
import base64
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import lru_cache
import hashlib
import hmac
import json
import mimetypes
import os
import random
import re
import requests
import subprocess
import sqlite3
import sys
import threading
import time
import unicodedata
import webbrowser
from datetime import datetime
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urlencode, urlparse, quote
from urllib.request import Request, urlopen

try:
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    _HAS_CRYPTOGRAPHY = True
except ImportError:
    _HAS_CRYPTOGRAPHY = False

try:
    from moria_downloader import (
        DEFAULT_REPOSITORY,
        MoriaDownloadError,
        GitHubRepository,
        parse_version,
        version_key,
        update_database as download_moria_database,
    )
except ModuleNotFoundError:
    import importlib.util

    _script_dir = Path(__file__).resolve().parent
    _downloader_paths = (
        _script_dir / "moria_downloader.py",
        _script_dir / "moria_downloader_1786131623710.py",
        _script_dir.parent / "moria_downloader.py",
        _script_dir.parent / "moria_downloader_1786131623710.py",
    )
    _downloader_path = next(
        (candidate for candidate in _downloader_paths if candidate.is_file()), None
    )
    _downloader_spec = (
        importlib.util.spec_from_file_location("moria_downloader", _downloader_path)
        if _downloader_path
        else None
    )
    if _downloader_spec is None or _downloader_spec.loader is None:
        DEFAULT_REPOSITORY = "https://api.github.com/repos/Maniac2017/Mipal2025"
        MoriaDownloadError = RuntimeError
        GitHubRepository = None
        parse_version = lambda name: None
        version_key = lambda v: (0,)

        def download_moria_database(*args: Any, **kwargs: Any) -> None:
            raise MoriaDownloadError(
                "No se encontró el descargador de moria.cm3 junto al script."
            )
    else:
        _downloader_module = importlib.util.module_from_spec(_downloader_spec)
        sys.modules["moria_downloader"] = _downloader_module
        _downloader_spec.loader.exec_module(_downloader_module)
        DEFAULT_REPOSITORY = _downloader_module.DEFAULT_REPOSITORY
        MoriaDownloadError = _downloader_module.MoriaDownloadError
        GitHubRepository = getattr(_downloader_module, "GitHubRepository", None)
        parse_version = getattr(_downloader_module, "parse_version", lambda name: None)
        version_key = getattr(_downloader_module, "version_key", lambda v: (0,))
        download_moria_database = _downloader_module.update_database


APP_NAME = "FlixLink Glass"
APP_VERSION = "2.5.0"
MAX_ROWS_PER_TABLE = 5000
MAX_CONTENT_ROWS = 100000
MAX_RELATED_LINKS = 5000
DEFAULT_PORT = 8765
DEFAULT_UPDATE_INTERVAL_SECONDS = 300.0
CONTENT_TABLES = ("pelis", "series", "v_pelis", "v_series")
LINK_TABLES = ("enlaces_pelis", "enlaces_series")
TMDB_IMAGE_BASE = "https://image.tmdb.org/t/p"
TMDB_API_BASE = "https://api.themoviedb.org/3"
TMDB_STREAMING_REGION = "ES"
TMDB_STREAMING_LANGUAGE = "es-ES"
TMDB_CACHE_TTL_SECONDS = 900.0
TMDB_STREAMING_PROVIDER_ALIASES = (
    ("Netflix", ("netflix",)),
    ("Amazon Prime Video", ("amazon prime video", "prime video")),
    ("Disney+", ("disney plus", "disney+")),
    ("Max", ("max", "hbo max")),
    ("Movistar Plus+", ("movistar plus", "movistarplus")),
    ("Filmin", ("filmin",)),
    ("SkyShowtime", ("skyshowtime",)),
    ("Apple TV+", ("apple tv",)),
    ("Crunchyroll", ("crunchyroll",)),
    ("Atresplayer", ("atresplayer", "atres player")),
    ("Mitele", ("mitele",)),
    ("RTVE Play", ("rtve play", "rtve")),
)
PALANTIR_AES_KEY = base64.b64decode(
    "hTh8uRnL5bX8PZC6Tc3t46nVDFfBpB6Tjw3qazQThpexpg8bLdimevNHj5vJR0nP"
)
FICHIER_API_URL = "https://api.1fichier.com/v1/download/get_token.cgi"
ALLDEBRID_API_URL = "https://api.alldebrid.com/v4"
ALLDEBRID_AGENT = "moria-catalog"
BROWSER_USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"

DEFAULT_CONFIG_PATH = Path(__file__).resolve().with_name("config.json")
LIBRARY_PATH = Path(__file__).resolve().with_name("biblioteca.json")
HISTORY_PATH = Path(__file__).resolve().with_name("historial.json")
WATCHED_PATH = Path(__file__).resolve().with_name("vistos.json")
EPISODES_WATCHED_PATH = Path(__file__).resolve().with_name("episodios_vistos.json")
VAULT_PATH = Path(__file__).resolve().with_name(".app_license.vault")
FIREBASE_PROJECT_ID = "flixlink-76e19"
FIRESTORE_URL = f"https://firestore.googleapis.com/v1/projects/{FIREBASE_PROJECT_ID}/databases/(default)/documents/licencias"
_TMDB_CACHE_LOCK = threading.RLock()
_TMDB_CACHE: dict[str, tuple[float, Any]] = {}


# ==============================================================================
# MOTOR CRIPTOGRÁFICO DE GRADO MILITAR Y PROTOCOLO DE LICENCIAS FLIXLINK
# ==============================================================================
class OfflineSecurityCore:
    _PART_A = bytes([0x4B, 0x6E, 0x39, 0x78, 0x5F, 0x41, 0x6C, 0x62])
    _PART_B = bytes([0x32, 0x30, 0x32, 0x36, 0x5F, 0x53, 0x65, 0x63])
    _PART_C = bytes([0x75, 0x72, 0x65, 0x5F, 0x50, 0x32, 0x50, 0x21])
    _XOR_KEY = 0x5A

    @classmethod
    def get_seed(cls) -> bytes:
        combined = cls._PART_A + cls._PART_B + cls._PART_C
        return bytes([b ^ cls._XOR_KEY for b in combined])

    @staticmethod
    def hash_password(password: str) -> str:
        return hashlib.sha256(f"{password}::FLIXLINK_SECURE_SALT".encode("utf-8")).hexdigest()


class Obfuscator:
    @staticmethod
    def secure_pack(payload_dict: dict, secret: bytes) -> str:
        raw_data = json.dumps(payload_dict, separators=(",", ":")).encode("utf-8")
        iv = os.urandom(12)
        keystream = b""
        c = 0
        while len(keystream) < len(raw_data):
            keystream += hashlib.sha256(secret + iv + c.to_bytes(4, "big")).digest()
            c += 1
        encrypted = bytes(a ^ b for a, b in zip(raw_data, keystream))
        mac = hmac.new(secret, iv + encrypted, hashlib.sha256).digest()
        return base64.urlsafe_b64encode(iv + mac + encrypted).decode("ascii")

    @staticmethod
    def secure_unpack(b64_str: str, secret: bytes) -> dict | None:
        try:
            raw = base64.urlsafe_b64decode(b64_str.strip().encode("ascii"))
            if len(raw) < 44:
                return None
            iv = raw[:12]
            mac_recibido = raw[12:44]
            encrypted = raw[44:]

            mac_calculado = hmac.new(secret, iv + encrypted, hashlib.sha256).digest()
            if not hmac.compare_digest(mac_recibido, mac_calculado):
                return None

            keystream = b""
            c = 0
            while len(keystream) < len(encrypted):
                keystream += hashlib.sha256(secret + iv + c.to_bytes(4, "big")).digest()
                c += 1
            decrypted = bytes(a ^ b for a, b in zip(encrypted, keystream))
            return json.loads(decrypted.decode("utf-8"))
        except Exception:
            return None


def get_firestore_user(username: str) -> tuple[str, dict[str, Any] | None]:
    """Busca el usuario de forma exacta o insensible a mayúsculas/minúsculas.
    Retorna (canonical_username, doc_json)."""
    user_clean = username.strip()
    if not user_clean:
        return ("", None)
    safe_user = quote(user_clean)
    try:
        res = requests.get(f"{FIRESTORE_URL}/{safe_user}", timeout=5)
        if res.status_code == 200:
            doc = res.json()
            doc_id = doc.get("name", "").split("/")[-1]
            return (doc_id or user_clean, doc)
    except Exception:
        pass

    # Fallback: buscar coincidencia case-insensitive en la lista de licencias
    try:
        res = requests.get(FIRESTORE_URL, timeout=5)
        if res.status_code == 200:
            docs = res.json().get("documents", [])
            target_lower = user_clean.lower()
            for doc in docs:
                doc_name = doc.get("name", "").split("/")[-1]
                if doc_name.lower() == target_lower:
                    return (doc_name, doc)
    except Exception:
        pass
    return (user_clean, None)


class InviteProtocol:
    def __init__(self):
        self._secret = OfflineSecurityCore.get_seed()

    def create_invite(self, issuer_username: str) -> str:
        exp_time = int(time.time()) + 600
        payload = {"v": 3, "act": "INVITE", "iss": issuer_username, "exp": exp_time}
        return Obfuscator.secure_pack(payload, self._secret)

    def verify_and_register(self, invite_b64: str, username: str, password_hash: str) -> tuple[bool, str]:
        data = Obfuscator.secure_unpack(invite_b64.strip(), self._secret)
        if not data:
            return False, "Código inválido o corrupto."
        if data.get("act") != "INVITE":
            return False, "Código no es de registro."
        if int(time.time()) > data.get("exp", 0):
            return False, "Código caducado (duraba 10 min)."

        existing_user, existing_doc = get_firestore_user(username)
        if existing_doc is not None:
            return False, f"El nombre de usuario '{existing_user}' ya está registrado."

        issuer_username = data.get("iss", "")
        if issuer_username != "ADMIN_CONSOLE":
            if not self._deduct_from_issuer(issuer_username, username):
                return False, "El usuario que te invitó no tiene saldo suficiente o su pase no es válido."

        try:
            self._register_on_firebase(username.strip(), password_hash, issuer_username)
            vault_data = {"username": username.strip(), "hash": password_hash, "status": "ACTIVE"}
            with open(VAULT_PATH, "w", encoding="utf-8") as f:
                json.dump(vault_data, f)
            return True, "Registro exitoso."
        except Exception:
            return False, "Error interno al guardar la sesión local."

    def _deduct_from_issuer(self, issuer_username: str, new_user: str) -> bool:
        try:
            safe_issuer = quote(issuer_username)
            res = requests.get(f"{FIRESTORE_URL}/{safe_issuer}", timeout=5)
            if res.status_code != 200:
                return False

            fields = res.json().get("fields", {})
            invites = int(fields.get("invitaciones_disponibles", {}).get("integerValue", 0))
            if invites <= 0:
                return False

            now_str = datetime.now().strftime("%d/%m/%Y %H:%M")
            new_hist = f"Has invitado a {new_user}|{now_str}"
            hist_vals = fields.get("historial", {}).get("arrayValue", {}).get("values", [])
            hist_vals.append({"stringValue": new_hist})

            amigos_vals = fields.get("amigos", {}).get("arrayValue", {}).get("values", [])
            amigos_vals.append({"stringValue": new_user})

            patch_url = f"{FIRESTORE_URL}/{safe_issuer}?updateMask.fieldPaths=invitaciones_disponibles&updateMask.fieldPaths=historial&updateMask.fieldPaths=amigos&updateMask.fieldPaths=codigo_activo&updateMask.fieldPaths=expiracion_codigo"
            body = {
                "fields": {
                    "invitaciones_disponibles": {"integerValue": str(invites - 1)},
                    "historial": {"arrayValue": {"values": hist_vals}},
                    "amigos": {"arrayValue": {"values": amigos_vals}},
                    "codigo_activo": {"stringValue": ""},
                    "expiracion_codigo": {"integerValue": "0"}
                }
            }
            requests.patch(patch_url, json=body, timeout=5)
            return True
        except Exception:
            return False

    def _register_on_firebase(self, username: str, password_hash: str, invited_by: str) -> None:
        url = f"{FIRESTORE_URL}/{quote(username)}"
        now_str = datetime.now().strftime("%d/%m/%Y %H:%M")
        body = {
            "fields": {
                "password_hash": {"stringValue": password_hash},
                "estado": {"stringValue": "ACTIVO"},
                "invitaciones_disponibles": {"integerValue": "5"},
                "invitado_por": {"stringValue": invited_by},
                "fecha_alta": {"stringValue": now_str},
                "codigo_activo": {"stringValue": ""},
                "expiracion_codigo": {"integerValue": "0"},
                "amigos": {"arrayValue": {}},
                "historial": {"arrayValue": {"values": [{"stringValue": f"Cuenta creada|{now_str}"}]}},
                "viendo_ahora": {"stringValue": "Explorando FlixLink"},
                "ultima_conexion": {"integerValue": str(int(time.time() * 1000))}
            }
        }
        requests.patch(url, json=body, timeout=5)


_licenser = InviteProtocol()


def get_local_session() -> dict[str, Any] | None:
    if os.path.exists(VAULT_PATH):
        try:
            with open(VAULT_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return None


def check_remote_status() -> str:
    try:
        res_global = requests.get(f"{FIRESTORE_URL}/GLOBAL_CONFIG", timeout=3)
        if res_global.status_code == 200:
            en_mantenimiento = res_global.json().get("fields", {}).get("modo_mantenimiento", {}).get("booleanValue", False)
            if en_mantenimiento:
                return "MANTENIMIENTO"
    except Exception:
        pass

    session = get_local_session()
    if not session:
        return "UNREGISTERED"

    username = session.get("username", "")
    pwd_hash = session.get("hash", "")
    if not username or not pwd_hash:
        return "UNREGISTERED"

    canonical_user, doc = get_firestore_user(username)
    if doc is None:
        if os.path.exists(VAULT_PATH):
            try:
                os.remove(VAULT_PATH)
            except Exception:
                pass
        return "UNREGISTERED"

    remote_hash = doc.get("fields", {}).get("password_hash", {}).get("stringValue", "")
    estado = doc.get("fields", {}).get("estado", {}).get("stringValue", "")

    if remote_hash != pwd_hash:
        if os.path.exists(VAULT_PATH):
            try:
                os.remove(VAULT_PATH)
            except Exception:
                pass
        return "UNREGISTERED"

    if estado == "BLOQUEADO":
        return "BLOQUEADO"

    return "ACTIVO"


def get_account_info() -> dict[str, Any]:
    status_str = check_remote_status()
    session = get_local_session()
    username = session.get("username", "Usuario") if session else "Usuario"
    invites_count = 0
    history_list: list[dict[str, str]] = []
    active_code = ""
    active_exp = 0

    if status_str == "ACTIVO":
        safe_user = quote(username)
        now_ms = int(time.time() * 1000)
        try:
            res = requests.get(f"{FIRESTORE_URL}/{safe_user}", timeout=3)
            if res.status_code == 200:
                fields = res.json().get("fields", {})
                invites_count = int(fields.get("invitaciones_disponibles", {}).get("integerValue", 0))
                exp_val = int(fields.get("expiracion_codigo", {}).get("integerValue", 0))
                if exp_val > now_ms:
                    active_code = fields.get("codigo_activo", {}).get("stringValue", "")
                    active_exp = exp_val

                vals = fields.get("historial", {}).get("arrayValue", {}).get("values", [])
                for v in reversed(vals):
                    texto = v.get("stringValue", "")
                    parts = texto.split("|")
                    text = parts[0] if len(parts) > 0 else "Acción Registrada"
                    date = parts[1] if len(parts) > 1 else ""
                    history_list.append({"text": text, "date": date})
        except Exception:
            pass

    return {
        "status": status_str,
        "active": (status_str == "ACTIVO"),
        "username": username,
        "nick": username,
        "invites": invites_count,
        "history": history_list,
        "active_code": active_code,
        "active_exp": active_exp,
    }


def _read_config() -> dict[str, Any]:
    try:
        payload = json.loads(DEFAULT_CONFIG_PATH.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            return payload
    except (OSError, json.JSONDecodeError):
        pass
    return {}


def _write_config(
    alldebrid_key: str | None = None,
    tmdb_key: str | None = None,
    db_update_interval_hours: int | None = None,
) -> None:
    config = _read_config()
    if alldebrid_key is not None:
        config["alldebrid_api_key"] = alldebrid_key.strip()
    if tmdb_key is not None:
        config["tmdb_api_key"] = tmdb_key.strip()
    if db_update_interval_hours is not None:
        config["db_update_interval_hours"] = int(db_update_interval_hours)

    DEFAULT_CONFIG_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = DEFAULT_CONFIG_PATH.with_name(f".{DEFAULT_CONFIG_PATH.name}.tmp")
    try:
        temporary.write_text(
            json.dumps(config, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        os.chmod(temporary, 0o600)
        os.replace(temporary, DEFAULT_CONFIG_PATH)
    except OSError as error:
        try:
            temporary.unlink()
        except OSError:
            pass
        raise RuntimeError(f"No se pudo guardar la configuración: {error}") from error


def _alldebrid_key_info() -> tuple[str, str]:
    config = _read_config()
    key = config.get("alldebrid_api_key")
    if isinstance(key, str) and key.strip():
        return key.strip(), "config"
    return "", ""


def _tmdb_key_info() -> tuple[str, str]:
    config = _read_config()
    key = config.get("tmdb_api_key")
    if isinstance(key, str) and key.strip():
        return key.strip(), "config"
    return "", ""


def _tmdb_request(
    path: str,
    params: dict[str, Any] | None = None,
    cache_ttl: float = TMDB_CACHE_TTL_SECONDS,
) -> dict[str, Any]:
    api_key, _ = _tmdb_key_info()
    if not api_key:
        raise RuntimeError("TMDB no está configurado.")

    query = {
        "api_key": api_key,
        "language": TMDB_STREAMING_LANGUAGE,
        **(params or {}),
    }
    cache_query = {key: value for key, value in query.items() if key != "api_key"}
    cache_key = f"{path}?{urlencode(sorted(cache_query.items()), doseq=True)}"
    now = time.monotonic()
    with _TMDB_CACHE_LOCK:
        cached = _TMDB_CACHE.get(cache_key)
        if cached and now - cached[0] < cache_ttl:
            value = cached[1]
            return value if isinstance(value, dict) else {}

    request = Request(
        f"{TMDB_API_BASE}/{path.lstrip('/')}?{urlencode(query, doseq=True)}",
        headers={
            "Accept": "application/json",
            "User-Agent": f"{APP_NAME}/{APP_VERSION}",
        },
    )
    try:
        with urlopen(request, timeout=12) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (HTTPError, URLError, TimeoutError, json.JSONDecodeError) as error:
        raise RuntimeError(f"No se pudo consultar TMDB: {error}") from error
    if not isinstance(payload, dict):
        raise RuntimeError("TMDB devolvió una respuesta no válida.")

    with _TMDB_CACHE_LOCK:
        _TMDB_CACHE[cache_key] = (time.monotonic(), payload)
    return payload


def _read_json_file(path: Path) -> list[dict[str, Any]]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError):
        return []
    if not isinstance(payload, list):
        return []
    return [entry for entry in payload if isinstance(entry, dict)]


def _write_json_file(path: Path, entries: list[dict[str, Any]]) -> None:
    temporary = path.with_name(f".{path.name}.tmp")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary.write_text(
        json.dumps(entries, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def safe_int(val: Any) -> int | None:
    if val in (None, "", "null", "undefined"):
        return None
    try:
        return int(val)
    except (ValueError, TypeError):
        return None


def library_key(table: str, index: int, record_id: int | None = None) -> str:
    rec = safe_int(record_id)
    idx = safe_int(index) if safe_int(index) is not None else -1
    return f"{table}:{rec if rec is not None else idx}"


@lru_cache(maxsize=32768)
def clean_key(value: str) -> str:
    text = unicodedata.normalize("NFKD", str(value))
    text = "".join(char for char in text if not unicodedata.combining(char))
    return re.sub(r"[^a-z0-9]", "", text.lower())


def json_value(value: Any) -> Any:
    if value is None:
        return None
    if isinstance(value, bytes):
        return value.hex()
    if isinstance(value, (str, int, float, bool)):
        return value
    return str(value)


def is_url(value: Any) -> bool:
    return isinstance(value, str) and bool(
        re.match(r"^(?:https?://|magnet:\?|ftp://)", value.strip(), re.I)
    )


def genre_values(value: Any) -> list[str]:
    if value in (None, ""):
        return []
    values = re.split(r"\s*(?:#|,|;|\||·)\s*", str(value).strip())
    result: list[str] = []
    seen: set[str] = set()
    for item in values:
        cleaned = re.sub(r"\s+", " ", item).strip()
        key = clean_key(cleaned)
        if cleaned and key and key not in seen:
            result.append(cleaned)
            seen.add(key)
    return result


def format_genres(value: Any) -> str:
    return ", ".join(genre_values(value))


def _alldebrid_request(action: str, params: dict[str, Any]) -> dict[str, Any]:
    api_key, _ = _alldebrid_key_info()
    if not api_key:
        raise RuntimeError("AllDebrid no está configurado.")
    query = {"agent": ALLDEBRID_AGENT, "apikey": api_key, **params}
    request = Request(
        f"{ALLDEBRID_API_URL}/{action}?{urlencode(query)}",
        headers={"Accept": "application/json", "User-Agent": ALLDEBRID_AGENT},
    )
    try:
        with urlopen(request, timeout=12) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (HTTPError, URLError, TimeoutError, json.JSONDecodeError) as error:
        raise RuntimeError(f"No se pudo consultar AllDebrid: {error}") from error
    if payload.get("status") != "success":
        error = payload.get("error") or {}
        message = error.get("message") if isinstance(error, dict) else str(error)
        raise RuntimeError(message or "AllDebrid rechazó la petición.")
    data = payload.get("data")
    return data if isinstance(data, dict) else {}


def alldebrid_status() -> dict[str, Any]:
    api_key, source = _alldebrid_key_info()
    if not api_key:
        return {"configured": False, "connected": False}
    try:
        data = _alldebrid_request("user", {})
    except RuntimeError:
        return {
            "configured": True,
            "connected": False,
            "source": source,
            "error": "No se pudo validar la clave.",
        }
    user = data.get("user") if isinstance(data.get("user"), dict) else {}
    return {
        "configured": True,
        "connected": True,
        "source": source,
        "username": user.get("username"),
        "premium": bool(user.get("isPremium") or user.get("premium")),
        "expires": user.get("premiumUntil") or user.get("expiration"),
    }


def resolve_alldebrid(link: str) -> dict[str, Any]:
    if not is_url(link):
        raise RuntimeError("AllDebrid necesita una URL válida.")
    data = _alldebrid_request("link/unlock", {"link": link})
    resolved = data.get("link")
    if not isinstance(resolved, str) or not is_url(resolved):
        raise RuntimeError("AllDebrid no devolvió un enlace reproducible.")
    return {
        "url": resolved,
        "filename": data.get("filename"),
        "source": "AllDebrid",
    }


def media_url(value: Any, size: str) -> Any:
    if not isinstance(value, str) or not value.strip():
        return value
    text = value.strip()
    if is_url(text):
        return text
    if text.startswith("/") and text.count("/") >= 1:
        return f"{TMDB_IMAGE_BASE}/{size}{text}"
    return value


def trailer_url(value: Any) -> Any:
    if not isinstance(value, str) or not value.strip() or is_url(value):
        return value
    text = value.strip()
    if re.fullmatch(r"[A-Za-z0-9_-]{6,}", text):
        return f"https://www.youtube.com/watch?v={text}"
    return value


def extract_youtube_id(value: Any) -> str | None:
    if not value or not isinstance(value, str):
        return None
    match = re.search(r"(?:v=|\/embed\/|\.be\/|\/v\/|watch\?v=)([A-Za-z0-9_-]{11})", value.strip())
    if match:
        return match.group(1)
    if re.fullmatch(r"[A-Za-z0-9_-]{11}", value.strip()):
        return value.strip()
    return None


def compact(value: Any, length: int = 180) -> str:
    if value is None:
        return ""
    text = str(value).replace("\r", " ").replace("\n", " ").strip()
    return text if len(text) <= length else text[: length - 1].rstrip() + "…"


def as_number(value: Any) -> float | int | None:
    if value is None:
        return None
    try:
        text = str(value).replace(",", ".").strip()
        match = re.search(r"-?\d+(?:\.\d+)?", text)
        if not match:
            return None
        number = float(match.group(0))
        return int(number) if number.is_integer() else round(number, 2)
    except (TypeError, ValueError):
        return None


FIELD_ALIASES = {
    "title": ("titulo", "title", "nombre", "name", "originaltitle", "originalname", "showtitle", "movie",),
    "description": ("sinopsis", "descripcion", "description", "plot", "argumento", "overview", "resumen",),
    "poster": ("poster", "posterpath", "cover", "coverurl", "caratula", "cartel", "imagen", "image", "thumb", "thumbnail",),
    "backdrop": ("backdrop", "fanart", "backdropurl", "background", "fondo",),
    "trailer": ("trailer", "trailerurl", "youtube", "youtubeurl", "teaser", "videotrailer",),
    "year": ("year", "ano", "fecha", "releaseyear", "release"),
    "rating": ("rating", "valoracion", "puntuacion", "score", "tmdbvoteaverage"),
    "genre": ("genero", "generos", "genre", "genres", "categoria", "category"),
    "language": ("idioma", "language", "lang"),
    "tmdb_id": ("tmdbid", "idtmdb", "tmdb"),
    "imdb_id": ("imdbid", "idimdb", "imdb"),
    "type": ("tipo", "type", "content", "contenido"),
    "category": ("categoria", "category", "subcategoria", "subcategory"),
    "collection": ("coleccion", "collection", "saga", "sagas"),
    "season": ("temporada", "season"),
    "episode": ("episodio", "episode"),
    "link": ("link", "url", "enlace", "enlaceurl", "fuente", "source", "stream"),
    "server": ("servidor", "server", "host", "site", "web", "provider", "label"),
    "quality": ("calidad", "quality", "resolucion", "resolution", "videoquality"),
    "audio": ("audio", "idioma", "idiomas", "language", "languages", "lang"),
    "info": ("info", "informacion", "information", "codec", "codecs", "formato"),
    "updated": ("updated", "actualizado", "fechaactualizacion", "lastupdated"),
}


def field_value(row: dict[str, Any], field: str) -> Any:
    normalized = {clean_key(key): value for key, value in row.items()}
    for alias in FIELD_ALIASES.get(field, ()):
        if alias in normalized and normalized[alias] not in (None, ""):
            return normalized[alias]
    return None


def field_column(columns: list[str], field: str) -> str | None:
    normalized = {clean_key(column): column for column in columns}
    for alias in FIELD_ALIASES.get(field, ()):
        if alias in normalized:
            return normalized[alias]
    return None


def infer_kind(table: str, row: dict[str, Any]) -> str:
    normalized_table = clean_key(table)
    values = " ".join(
        clean_key(str(value)) for value in row.values() if value is not None
    )
    if any(word in normalized_table for word in ("serie", "series", "episodio", "tv")):
        return "series"
    if any(word in normalized_table for word in ("peli", "pelicula", "movie", "film")):
        return "movies"
    if any(word in values for word in ("temporada", "episodio", "season")):
        return "series"
    return "other"


def label_for_field(key: str) -> str:
    labels = {
        "titulo": "Título", "title": "Título", "nombre": "Nombre",
        "sinopsis": "Sinopsis", "descripcion": "Descripción", "description": "Descripción", "plot": "Argumento",
        "poster": "Cartel", "fanart": "Fondo", "trailer": "Tráiler", "genero": "Género",
        "year": "Año", "ano": "Año", "rating": "Valoración",
        "temporada": "Temporada", "episodio": "Episodio",
        "link": "Enlace", "url": "URL", "enlace": "Enlace",
        "calidad": "Calidad", "quality": "Calidad",
        "audio": "Audio", "idioma": "Audio", "idiomas": "Audio",
        "info": "Información", "updated": "Actualizado",
    }
    normalized = clean_key(key)
    return labels.get(normalized, str(key).replace("_", " ").strip().title())


def display_link(value: Any) -> str:
    value = json_value(value)
    return "" if value is None else str(value).strip()


_AES_SBOX = (
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B,
    0xFE, 0xD7, 0xAB, 0x76, 0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0,
    0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0, 0xB7, 0xFD, 0x93, 0x26,
    0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2,
    0xEB, 0x27, 0xB2, 0x75, 0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0,
    0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84, 0x53, 0xD1, 0x00, 0xED,
    0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F,
    0x50, 0x3C, 0x9F, 0xA8, 0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5,
    0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2, 0xCD, 0x0C, 0x13, 0xEC,
    0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14,
    0xDE, 0x5E, 0x0B, 0xDB, 0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C,
    0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79, 0xE7, 0xC8, 0x37, 0x6D,
    0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F,
    0x4B, 0xBD, 0x8B, 0x8A, 0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E,
    0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E, 0xE1, 0xF8, 0x98, 0x11,
    0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F,
    0xB0, 0x54, 0xBB, 0x16,
)
_AES_RCON = (0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36)


def _aes_rot_word(word: list[int]) -> list[int]:
    return word[1:] + word[:1]


def _aes_expand_key(key: bytes) -> list[list[int]]:
    if len(key) != 32:
        raise ValueError("AES-256 requiere una clave de 32 bytes")
    words = [list(key[index : index + 4]) for index in range(0, 32, 4)]
    for index in range(8, 60):
        word = words[index - 1].copy()
        if index % 8 == 0:
            word = [_AES_SBOX[b] for b in _aes_rot_word(word)]
            word[0] ^= _AES_RCON[index // 8]
        elif index % 8 == 4:
            word = [_AES_SBOX[b] for b in word]
        words.append([left ^ right for left, right in zip(words[index - 8], word)])
    return [
        sum(words[index : index + 4], [])
        for index in range(0, 60, 4)
    ]


def _aes_encrypt_block(block: bytes, expanded_key: list[list[int]]) -> bytes:
    if len(block) != 16:
        raise ValueError("AES trabaja con bloques de 16 bytes")
    state = list(block)

    def add_round_key(key: list[int]) -> None:
        for index in range(16):
            state[index] ^= key[index]

    def sub_bytes() -> None:
        for index in range(16):
            state[index] = _AES_SBOX[state[index]]

    def shift_rows() -> None:
        original = state.copy()
        for row in range(4):
            for column in range(4):
                state[row + 4 * column] = original[
                    row + 4 * ((column + row) % 4)
                ]

    def xtime(value: int) -> int:
        return ((value << 1) ^ (0x11B if value & 0x80 else 0)) & 0xFF

    def mix_columns() -> None:
        for column in range(4):
            offset = 4 * column
            a0, a1, a2, a3 = state[offset : offset + 4]
            total = a0 ^ a1 ^ a2 ^ a3
            state[offset] = a0 ^ total ^ xtime(a0 ^ a1)
            state[offset + 1] = a1 ^ total ^ xtime(a1 ^ a2)
            state[offset + 2] = a2 ^ total ^ xtime(a2 ^ a3)
            state[offset + 3] = a3 ^ total ^ xtime(a3 ^ a0)

    add_round_key(expanded_key[0])
    for round_key in expanded_key[1:-1]:
        sub_bytes()
        shift_rows()
        mix_columns()
        add_round_key(round_key)
    sub_bytes()
    shift_rows()
    add_round_key(expanded_key[-1])
    return bytes(state)


def _aes_ofb_decrypt(encrypted: bytes, key: bytes, iv: bytes) -> bytes:
    if len(iv) != 16:
        raise ValueError("AES-OFB requiere un IV de 16 bytes")
    expanded_key = _aes_expand_key(key)
    feedback = iv
    output = bytearray()
    for offset in range(0, len(encrypted), 16):
        feedback = _aes_encrypt_block(feedback, expanded_key)
        chunk = encrypted[offset : offset + 16]
        output.extend(
            value ^ feedback[index]
            for index, value in enumerate(chunk)
        )
    return bytes(output)


def _decode_palantir_token_with_python(text: str) -> str:
    encoded = text.encode("ascii")
    encrypted = base64.urlsafe_b64decode(encoded + b"=" * (-len(encoded) % 4))
    if len(encrypted) < 16:
        return text
    decoded = _aes_ofb_decrypt(
        encrypted,
        PALANTIR_AES_KEY[16:],
        PALANTIR_AES_KEY[:16],
    ).decode("utf-8").strip()
    return decoded if is_url(decoded) else text


@lru_cache(maxsize=32768)
def _decode_palantir_token(value: str) -> str:
    text = value.strip()
    if not text or is_url(text):
        return text
    try:
        encoded = text.encode("ascii")
        encrypted = base64.urlsafe_b64decode(encoded + b"=" * (-len(encoded) % 4))
        if len(encrypted) < 16:
            return text
        if _HAS_CRYPTOGRAPHY:
            cipher = Cipher(
                algorithms.AES(PALANTIR_AES_KEY[16:]),
                modes.OFB(PALANTIR_AES_KEY[:16]),
            )
            decryptor = cipher.decryptor()
            decoded = (decryptor.update(encrypted) + decryptor.finalize()).decode("utf-8", errors="ignore").strip()
            if is_url(decoded):
                return decoded
        decoded = _aes_ofb_decrypt(
            encrypted,
            PALANTIR_AES_KEY[16:],
            PALANTIR_AES_KEY[:16],
        ).decode("utf-8", errors="ignore").strip()
        if is_url(decoded):
            return decoded
    except (ValueError, UnicodeError, Exception):
        pass
    return text


@lru_cache(maxsize=16384)
def discover_link(value: Any) -> tuple[str, bool]:
    original = display_link(value)
    discovered = _decode_palantir_token(original)
    return discovered, bool(discovered and discovered != original and is_url(discovered))


def link_kind(value: Any) -> str:
    text, _ = discover_link(value)
    if is_url(text):
        return "url"
    if text:
        return "identifier"
    return "empty"


def link_label(value: Any) -> str:
    _, decoded = discover_link(value)
    if decoded:
        return "URL descifrada"
    return "URL almacenada" if link_kind(value) == "url" else "Identificador almacenado"


def sort_value(value: Any) -> tuple[int, Any]:
    if value is None:
        return (0, "")
    text = str(value).strip()
    if not text:
        return (0, "")
    match = re.search(r"(\d+(?:[.,]\d+)?)", text)
    if match:
        try:
            return (2, float(match.group(1).replace(",", ".")))
        except ValueError:
            pass
    return (1, text.casefold())


def source_option(link_row: dict[str, Any], position: int) -> dict[str, Any]:
    stored_link = display_link(field_value(link_row, "link"))
    link, discovered = discover_link(stored_link)
    return {
        "number": position,
        "link": link or None,
        "stored_link": stored_link or None,
        "discovered": discovered,
        "link_kind": "url" if is_url(link) else link_kind(link),
        "link_label": "URL descifrada" if discovered else link_label(stored_link),
        "server": json_value(field_value(link_row, "server")),
        "quality": json_value(field_value(link_row, "quality")),
        "audio": json_value(field_value(link_row, "audio")),
        "info": json_value(field_value(link_row, "info")),
        "updated": json_value(field_value(link_row, "updated")),
        "season": json_value(field_value(link_row, "season")),
        "episode": json_value(field_value(link_row, "episode")),
        "fields": [
            (key, json_value(value))
            for key, value in link_row.items()
            if value not in (None, "")
        ],
    }


class CatalogStore:
    def __init__(
        self,
        db_path: str | None,
        kodi_home: str | None = None,
        auto_update: bool = True,
        repository_url: str = DEFAULT_REPOSITORY,
        requested_version: str | None = None,
        fichier_token_path: str | None = None,
        update_interval: float = DEFAULT_UPDATE_INTERVAL_SECONDS,
    ):
        self.requested_path = db_path
        self.kodi_home = kodi_home
        self.auto_update = auto_update
        self.repository_url = repository_url
        self.requested_version = requested_version
        config = _read_config()
        cfg_hours = config.get("db_update_interval_hours", 12)
        if cfg_hours <= 0:
            self.auto_update = False
            self.update_interval = 0.0
        else:
            self.update_interval = max(60.0, float(cfg_hours) * 3600.0)
        self.fichier_token_path = (
            Path(fichier_token_path).expanduser()
            if fichier_token_path
            else self._find_fichier_token(kodi_home)
        )
        self.db_path = self._find_db(db_path, kodi_home)
        if self.db_path is None:
            self.db_path = (
                Path(db_path).expanduser().resolve()
                if db_path
                else Path(__file__).resolve().parent / "moria.cm3"
            )

        self._lock = threading.RLock()
        self._update_lock = threading.Lock()
        self._update_stop = threading.Event()
        self._update_thread: threading.Thread | None = None
        self._database_revision = 0
        self._update_state = "disabled" if not self.auto_update else "idle"
        self._last_update_check_at: str | None = None
        self._last_database_update_at: str | None = None
        self.update_error: str | None = None

        has_local_database = self.db_path.is_file()
        self._db_ready = has_local_database
        self.demo = False
        self._local = threading.local()
        self._rows: dict[str, list[dict[str, Any]]] = {}
        self._table_counts: dict[str, int] = {}
        self._table_columns: dict[str, list[str]] = {}
        self._table_types: dict[str, str] = {}
        self._cached_facets: dict[str, list[str]] | None = None

        if has_local_database:
            try:
                self._ensure_indexes()
                self._load()
                if self.auto_update and check_remote_status() == "ACTIVO":
                    self._start_background_updater()
            except Exception as e:
                sys.stderr.write(f"[catalogo] Aviso al cargar base de datos existente: {e}\n")
        else:
            self._update_state = "pending_auth"

    def ensure_database_ready(self, async_download: bool = True) -> None:
        if self._db_ready and self.db_path.is_file():
            return

        def _download_task():
            with self._update_lock:
                if self._db_ready and self.db_path.is_file():
                    return
                try:
                    self._update_state = "downloading"
                    print("[catalogo] Descargando base de datos inicial moria.cm3...", file=sys.stderr)
                    changed = self._update_database()
                    self._ensure_indexes()
                    self._load()
                    self._db_ready = True
                    self._update_state = "idle"
                    if self.auto_update:
                        self._start_background_updater()
                    print("[catalogo] Base de datos descargada y cargada con éxito.", file=sys.stderr)
                except Exception as error:
                    self.update_error = str(error)
                    self._update_state = "error"
                    print(f"[catalogo] Error descargando base de datos inicial: {error}", file=sys.stderr)

        if async_download:
            t = threading.Thread(target=_download_task, name="flixlink-db-init-worker", daemon=True)
            t.start()
        else:
            _download_task()

    @staticmethod
    def _find_fichier_token(kodi_home: str | None = None) -> Path | None:
        roots: list[Path] = []
        for value in (kodi_home, os.environ.get("KODI_HOME")):
            if value:
                roots.append(Path(value).expanduser())
        roots.extend(
            [
                Path.home() / ".kodi",
                Path.cwd(),
                Path(__file__).resolve().parent,
            ]
        )
        candidates: list[Path] = []
        for root in roots:
            candidates.extend(
                [
                    root / "userdata/addon_data/plugin.video.palantir3/1fichier.txt",
                    root / "addon_data/plugin.video.palantir3/1fichier.txt",
                    root / "1fichier.txt",
                ]
            )
        for candidate in candidates:
            if candidate.is_file():
                return candidate.resolve()
        return None

    @staticmethod
    def _find_db(db_path: str | None, kodi_home: str | None = None) -> Path | None:
        candidates = []
        if db_path:
            candidates.append(Path(db_path).expanduser())
        script_dir = Path(__file__).resolve().parent
        candidates.extend(
            [
                script_dir / "moria.cm3",
                script_dir / "moria.db",
                script_dir / "MoriaDB.sqlite",
                script_dir / "MoriaDB.db",
            ]
        )
        kodi_roots: list[Path] = []
        for value in (kodi_home, os.environ.get("KODI_HOME")):
            if value:
                kodi_roots.append(Path(value).expanduser())
        home = Path.home()
        if sys.platform.startswith("win"):
            appdata = os.environ.get("APPDATA")
            if appdata:
                kodi_roots.append(Path(appdata) / "Kodi")
        elif sys.platform == "darwin":
            kodi_roots.append(home / "Library/Application Support/Kodi")
        else:
            kodi_roots.append(home / ".kodi")
        for root in kodi_roots:
            candidates.append(root / "addons/plugin.video.palantir3/moria.cm3")
            candidates.append(root / "addons/plugin.video.palantir3/moria.db")
        env_path = os.environ.get("CATALOGO_DB")
        if env_path:
            candidates.append(Path(env_path).expanduser())
        candidates.extend(
            [
                Path.cwd() / "plugin.video.palantir3/moria.cm3",
                Path.cwd() / "plugin.video.palantir3/moria.db",
                Path.cwd() / "moria.cm3",
                Path.cwd() / "moria.db",
            ]
        )
        for name in (
            "MoriaDB.sqlite",
            "MoriaDB.db",
            "moria.sqlite",
            "catalogo.db",
            "catalog.db",
        ):
            candidates.append(Path.cwd() / name)
        for candidate in candidates:
            if candidate.is_file():
                return candidate.resolve()
        return None

    @staticmethod
    def _quote(identifier: str) -> str:
        return '"' + identifier.replace('"', '""') + '"'

    def _get_connection(self) -> sqlite3.Connection:
        if self.db_path is None:
            raise sqlite3.DatabaseError("No hay una base SQLite disponible")
        conn = getattr(self._local, "connection", None)
        connection_revision = getattr(self._local, "connection_revision", -1)
        if conn is None or connection_revision != self._database_revision:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
            conn = sqlite3.connect(
                f"file:{self.db_path.as_posix()}?mode=ro", uri=True, timeout=10, check_same_thread=False
            )
            conn.row_factory = sqlite3.Row
            conn.execute("PRAGMA query_only = 1;")
            conn.execute("PRAGMA cache_size = -128000;")
            conn.execute("PRAGMA temp_store = MEMORY;")
            conn.execute("PRAGMA mmap_size = 536870912;")
            conn.execute("PRAGMA synchronous = OFF;")
            self._local.connection = conn
            self._local.connection_revision = self._database_revision
        return self._local.connection

    def _close_connections(self) -> None:
        conn = getattr(self._local, "connection", None)
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass
            self._local.connection = None
        self._local.connection_revision = -1

    def _ensure_indexes(self) -> None:
        if self.db_path is None or not self.db_path.is_file():
            return
        try:
            with sqlite3.connect(self.db_path, timeout=15) as conn:
                existing_tables = {
                    row[0]
                    for row in conn.execute(
                        "SELECT name FROM sqlite_master WHERE type IN ('table', 'view')"
                    ).fetchall()
                }
                cursor = conn.cursor()
                if "enlaces_pelis" in existing_tables:
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_enlaces_pelis_tmdb ON enlaces_pelis(tmdb);")
                if "enlaces_series" in existing_tables:
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_enlaces_series_tmdb_ep ON enlaces_series(tmdb, temporada, episodio);")
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_enlaces_series_tmdb ON enlaces_series(tmdb);")
                if "pelis" in existing_tables:
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_pelis_tmdb ON pelis(tmdb);")
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_pelis_year_rating ON pelis(year, rating);")
                if "series" in existing_tables:
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_series_tmdb ON series(tmdb);")
                    cursor.execute("CREATE INDEX IF NOT EXISTS idx_series_year_rating ON series(year, rating);")
                conn.commit()
        except (sqlite3.OperationalError, sqlite3.DatabaseError):
            pass

    def _load(self) -> None:
        assert self.db_path is not None
        try:
            conn = self._get_connection()
            tables = conn.execute(
                """
                SELECT name, type FROM sqlite_master
                WHERE type IN ('table', 'view')
                  AND name NOT LIKE 'sqlite_%'
                ORDER BY name COLLATE NOCASE
                """
            ).fetchall()
            loaded: dict[str, list[dict[str, Any]]] = {}
            table_counts: dict[str, int] = {}
            table_columns: dict[str, list[str]] = {}
            table_types: dict[str, str] = {}
            for table_row in tables:
                table = str(table_row["name"])
                try:
                    table_types[table] = str(table_row["type"])
                    columns = conn.execute(
                        f"PRAGMA table_info({self._quote(table)})"
                    ).fetchall()
                    table_columns[table] = [str(column["name"]) for column in columns]
                    count = conn.execute(
                        f"SELECT COUNT(*) FROM {self._quote(table)}"
                    ).fetchone()[0]
                    table_counts[table] = int(count)
                    if table in LINK_TABLES or table in CONTENT_TABLES:
                        loaded[table] = []
                        continue
                    row_limit = MAX_CONTENT_ROWS if table in CONTENT_TABLES else MAX_ROWS_PER_TABLE
                    rows = conn.execute(
                        f"SELECT * FROM {self._quote(table)} LIMIT ?",
                        (row_limit,),
                    ).fetchall()
                    loaded[table] = [
                        {key: json_value(row[key]) for key in row.keys()} for row in rows
                    ]
                except sqlite3.DatabaseError:
                    continue
            self._rows = loaded
            self._table_counts = table_counts
            self._table_columns = table_columns
            self._table_types = table_types
            self._cached_facets = None
            if not self._rows:
                self._rows = {}
        except sqlite3.DatabaseError as error:
            raise RuntimeError(f"No se pudo leer la base SQLite: {error}") from error

    def refresh(self) -> None:
        changed = False
        if self.auto_update and self.db_path is not None:
            with self._lock:
                self._update_state = "checking"
                self._last_update_check_at = datetime.now().astimezone().isoformat(timespec="seconds")
            changed = self._update_database()
        self._reload_catalog(changed=changed, mark_new_content=changed)
        if self.auto_update:
            with self._lock:
                self._update_state = "updated" if changed else ("error" if self.update_error else "idle")

    def _update_database(self) -> bool:
        assert self.db_path is not None
        with self._update_lock:
            try:
                changed = download_moria_database(
                    self.db_path,
                    repository_url=self.repository_url,
                    version=self.requested_version,
                )
                self.update_error = None
                if changed:
                    self.db_path = self.db_path.resolve()
                return changed
            except (MoriaDownloadError, OSError) as error:
                self.update_error = str(error)
                if self.db_path.is_file():
                    print(f"[catalogo] No se pudo actualizar la BD; se usa la copia local: {error}", file=sys.stderr)
                    return False
                raise RuntimeError(f"No se pudo descargar moria.cm3: {error}") from error

    def _reload_catalog(self, changed: bool = False, mark_new_content: bool = False) -> None:
        """Recarga el catálogo y fuerza a los hilos HTTP a renovar SQLite."""
        with self._lock:
            self._close_connections()
            self._cached_table_links.cache_clear()
            self._cached_facets = None
            self._ensure_indexes()
            self._load()
            if changed:
                # La revisión visible para el navegador cambia solo después
                # de que el catálogo nuevo se haya cargado completamente.
                self._database_revision += 1
            if changed and mark_new_content:
                self._last_database_update_at = datetime.now().astimezone().isoformat(timespec="seconds")

    def _start_background_updater(self) -> None:
        if self._update_thread is not None and self._update_thread.is_alive():
            return
        self._update_stop.clear()
        self._update_thread = threading.Thread(
            target=self._background_update_loop,
            name="flixlink-database-updater",
            daemon=True,
        )
        self._update_thread.start()

    def _background_update_loop(self) -> None:
        # Permite que el servidor atienda primero la carga inicial del navegador.
        if self._update_stop.wait(0.5):
            return
        while not self._update_stop.is_set():
            try:
                with self._lock:
                    self._update_state = "checking"
                    self._last_update_check_at = datetime.now().astimezone().isoformat(timespec="seconds")
                changed = self._update_database()
                if changed:
                    self._reload_catalog(changed=True, mark_new_content=True)
                    print("[catalogo] Nueva versión de la base de datos aplicada.", file=sys.stderr)
                with self._lock:
                    self._update_state = "updated" if changed else ("error" if self.update_error else "idle")
            except Exception as error:
                with self._lock:
                    self.update_error = str(error)
                    self._update_state = "error"
                print(f"[catalogo] Error en la actualización en segundo plano: {error}", file=sys.stderr)
            if self._update_stop.wait(self.update_interval):
                return

    def get_database_version(self) -> str:
        if self.db_path is not None:
            state_path = self.db_path.with_name(f"{self.db_path.name}.state.json")
            if state_path.is_file():
                try:
                    payload = json.loads(state_path.read_text(encoding="utf-8"))
                    if isinstance(payload, dict) and "version" in payload:
                        return str(payload["version"])
                except Exception:
                    pass
        return self.requested_version or "3.3.11"

    def set_update_interval_hours(self, hours: int) -> None:
        with self._lock:
            if hours <= 0:
                self.auto_update = False
                self.stop_background_updates()
                self._update_state = "idle"
            else:
                self.auto_update = True
                self.update_interval = float(hours) * 3600.0
                self._start_background_updater()

    def check_remote_version(self) -> dict[str, Any]:
        curr_ver = self.get_database_version()
        try:
            repo = GitHubRepository(self.repository_url, timeout=15, retries=1)
            files = repo.list_database_files()
            versions = []
            for item in files:
                name = item.get("name", "")
                v = parse_version(name)
                if v:
                    try:
                        versions.append((version_key(v), v))
                    except Exception:
                        pass
            if not versions:
                return {
                    "status": "up_to_date",
                    "current_version": curr_ver,
                    "latest_version": curr_ver,
                    "message": f"Tu base de datos está al día (v{curr_ver})",
                    "update_available": False,
                }
            versions.sort(key=lambda x: x[0], reverse=True)
            latest_ver = versions[0][1]
            try:
                is_newer = version_key(latest_ver) > version_key(curr_ver)
            except Exception:
                is_newer = latest_ver != curr_ver

            with self._lock:
                self._last_update_check_at = datetime.now().astimezone().isoformat(timespec="seconds")

            if is_newer:
                return {
                    "status": "update_available",
                    "current_version": curr_ver,
                    "latest_version": latest_ver,
                    "message": f"Nueva versión disponible: v{latest_ver} (actual: v{curr_ver})",
                    "update_available": True,
                }
            else:
                return {
                    "status": "up_to_date",
                    "current_version": curr_ver,
                    "latest_version": latest_ver,
                    "message": f"Tu base de datos está al día (v{curr_ver})",
                    "update_available": False,
                }
        except MoriaDownloadError as exc:
            err_str = str(exc)
            if "403" in err_str or "rate limit" in err_str.lower():
                return {
                    "status": "rate_limited",
                    "current_version": curr_ver,
                    "message": "Límite de peticiones de GitHub alcanzado (Rate Limit). Inténtalo más tarde.",
                    "update_available": False,
                }
            return {
                "status": "error",
                "current_version": curr_ver,
                "message": f"No se pudo comprobar: {err_str}",
                "update_available": False,
            }
        except Exception as exc:
            return {
                "status": "error",
                "current_version": curr_ver,
                "message": f"Error: {exc}",
                "update_available": False,
            }

    def stop_background_updates(self) -> None:
        self._update_stop.set()
        thread = self._update_thread
        if thread is not None and thread is not threading.current_thread():
            thread.join(timeout=2)

    def tables(self) -> list[dict[str, Any]]:
        result = []
        for table in self._table_counts or self._rows:
            rows = self._rows.get(table, [])
            first = rows[0] if rows else {}
            kind = infer_kind(table, first)
            result.append(
                {
                    "name": table,
                    "rows": self._table_counts.get(table, len(rows)),
                    "kind": kind,
                    "original": table in CONTENT_TABLES or table in LINK_TABLES,
                }
            )
        return result

    def status(self) -> dict[str, Any]:
        catalog_tables = [
            table for table in CONTENT_TABLES
            if table in self._table_counts or table in self._rows
        ]
        total = sum(
            self._table_counts.get(table, len(self._rows.get(table, [])))
            for table in catalog_tables
        )
        counts = {"movies": 0, "series": 0, "other": 0}
        for table in catalog_tables:
            rows = self._rows.get(table, [])
            kind = infer_kind(table, rows[0] if rows else {})
            counts[kind] += self._table_counts.get(table, len(rows))
        
        config = _read_config()
        return {
            "app": APP_NAME,
            "version": APP_VERSION,
            "mode": "sqlite",
            "database": str(self.db_path) if self.db_path else None,
            "total": total,
            "counts": counts,
            "tables": self.tables(),
            "facets": self.facets(),
            "tmdb_configured": bool(config.get("tmdb_api_key", "").strip()),
            "original_tables": {
                table: self._table_counts.get(table, len(self._rows.get(table, [])))
                for table in CONTENT_TABLES + LINK_TABLES
                if table in self._table_counts or table in self._rows
            },
            "updated_at": datetime.now().astimezone().isoformat(timespec="seconds"),
            "update_error": self.update_error,
            "database_revision": self._database_revision,
            "database_update": {
                "state": self._update_state,
                "in_progress": self._update_state in ("initializing", "checking"),
                "last_check_at": self._last_update_check_at,
                "last_updated_at": self._last_database_update_at,
                "error": self.update_error,
                "interval_seconds": self.update_interval if self.auto_update else None,
            },
        }

    # ==========================
    # MI ÁREA (BIBLIOTECA, HISTORIAL Y VISTOS)
    # ==========================

    def library(self) -> list[dict[str, Any]]:
        saved = _read_json_file(LIBRARY_PATH)
        result: list[dict[str, Any]] = []
        for entry in saved:
            table = str(entry.get("table") or "")
            index = int(entry.get("index", -1))
            record_id = entry.get("record_id")
            record_id = int(record_id) if record_id not in (None, "") else None
            row = self._row_at(table, index, record_id, str(entry.get("query") or ""))
            if row is None:
                continue
            summary = self._summary(table, index, row)
            summary["record_id"] = record_id
            summary["saved_at"] = entry.get("saved_at")
            summary["saved"] = True
            summary["watched"] = library_key(table, index, record_id) in self.watched_keys()
            result.append(summary)
        return result

    def is_saved_item(self, table: str, index: int = -1, record_id: int | None = None, tmdb_id: Any = None, title: Any = None) -> bool:
        saved_keys = self.library_keys()
        k = library_key(table, index, record_id)
        if k in saved_keys:
            return True
        if tmdb_id and f"tmdb:{tmdb_id}" in saved_keys:
            return True
        if title and f"title:{clean_key(str(title))}" in saved_keys:
            return True
        return False

    def is_watched_item(self, table: str, index: int = -1, record_id: int | None = None, tmdb_id: Any = None, title: Any = None) -> bool:
        watched_keys = self.watched_keys()
        k = library_key(table, index, record_id)
        if k in watched_keys:
            return True
        if tmdb_id and f"tmdb:{tmdb_id}" in watched_keys:
            return True
        if title and f"title:{clean_key(str(title))}" in watched_keys:
            return True
        return False

    def add_to_library(self, table: str, index: int, record_id: int | None = None, query: str = "") -> dict[str, Any]:
        rec_id = safe_int(record_id)
        idx = safe_int(index) if safe_int(index) is not None else 0
        row = self._row_at(table, idx, rec_id, query)
        tmdb = field_value(row, "tmdb_id") if row else None
        imdb = field_value(row, "imdb_id") if row else None
        title = field_value(row, "title") if row else None
        c_title = clean_key(title) if title else ""
        
        entries = _read_json_file(LIBRARY_PATH)
        key = library_key(table, idx, rec_id)
        
        already = False
        for e in entries:
            e_rec_id = safe_int(e.get("record_id"))
            e_idx = safe_int(e.get("index")) if safe_int(e.get("index")) is not None else -1
            e_key = library_key(str(e.get("table")), e_idx, e_rec_id)
            e_tmdb = str(e.get("tmdb") or "")
            e_title = clean_key(str(e.get("title") or ""))
            if e_key == key or (tmdb and e_tmdb == str(tmdb)) or (c_title and e_title == c_title):
                already = True
                break
                
        if not already:
            entries.append({
                "table": table, "index": idx, "record_id": rec_id, "query": query,
                "tmdb": tmdb, "imdb": imdb, "title": title,
                "saved_at": datetime.now().astimezone().isoformat(timespec="seconds")
            })
            _write_json_file(LIBRARY_PATH, entries)
        return {"saved": True, "key": key, "items": self.library()}

    def remove_from_library(self, table: str, index: int, record_id: int | None = None) -> dict[str, Any]:
        rec_id = safe_int(record_id)
        idx = safe_int(index) if safe_int(index) is not None else 0
        row = self._row_at(table, idx, rec_id)
        tmdb = field_value(row, "tmdb_id") if row else None
        title = field_value(row, "title") if row else None
        c_title = clean_key(title) if title else ""
        key = library_key(table, idx, rec_id)

        entries = []
        for e in _read_json_file(LIBRARY_PATH):
            e_rec_id = safe_int(e.get("record_id"))
            e_idx = safe_int(e.get("index")) if safe_int(e.get("index")) is not None else -1
            e_key = library_key(str(e.get("table")), e_idx, e_rec_id)
            e_tmdb = str(e.get("tmdb") or "")
            e_title = clean_key(str(e.get("title") or ""))
            if e_key == key or (tmdb and e_tmdb == str(tmdb)) or (c_title and e_title == c_title):
                continue
            entries.append(e)
        _write_json_file(LIBRARY_PATH, entries)
        return {"saved": False, "key": key, "items": self.library()}

    def library_keys(self) -> set[str]:
        keys = set()
        for e in _read_json_file(LIBRARY_PATH):
            e_rec_id = safe_int(e.get("record_id"))
            e_idx = safe_int(e.get("index")) if safe_int(e.get("index")) is not None else -1
            k = library_key(str(e.get("table")), e_idx, e_rec_id)
            keys.add(k)
            if e.get("tmdb"):
                keys.add(f"tmdb:{e['tmdb']}")
            if e.get("title"):
                keys.add(f"title:{clean_key(str(e['title']))}")
        return keys

    # HISTORIAL (CONTINUAR VIENDO)
    def history(self) -> list[dict[str, Any]]:
        entries = _read_json_file(HISTORY_PATH)
        result: list[dict[str, Any]] = []
        for entry in entries:
            table = str(entry.get("table") or "")
            index = int(entry.get("index", -1))
            record_id = entry.get("record_id")
            record_id = int(record_id) if record_id not in (None, "") else None
            row = self._row_at(table, index, record_id)
            if row is None:
                continue
            summary = self._summary(table, index, row)
            summary["record_id"] = record_id
            summary["last_played"] = entry.get("played_at")
            summary["last_season"] = entry.get("season")
            summary["last_episode"] = entry.get("episode")
            summary["saved"] = library_key(table, index, record_id) in self.library_keys()
            summary["watched"] = library_key(table, index, record_id) in self.watched_keys()
            result.append(summary)
        return result

    def add_to_history(self, table: str, index: int, record_id: int | None = None, season: Any = None, episode: Any = None) -> dict[str, Any]:
        entries = _read_json_file(HISTORY_PATH)
        key = library_key(table, index, record_id)
        entries = [
            e for e in entries
            if library_key(str(e.get("table")), int(e.get("index", -1)), int(e["record_id"]) if e.get("record_id") not in (None, "") else None) != key
        ]
        entries.insert(0, {
            "table": table, "index": index, "record_id": record_id,
            "season": season, "episode": episode,
            "played_at": datetime.now().astimezone().isoformat(timespec="seconds")
        })
        _write_json_file(HISTORY_PATH, entries[:40])

        row = self._row_at(table, index, record_id)
        tmdb = field_value(row, "tmdb_id") if row else None
        
        if season not in (None, "") and episode not in (None, ""):
            self.toggle_episode_watched(
                tmdb=str(tmdb) if tmdb else None,
                table=table,
                record_id=record_id,
                season=season,
                episode=episode,
                watched=True
            )
        else:
            self.set_watched(table, index, record_id, True)

        return {"success": True, "items": self.history()}


    def remove_from_history(self, table: str, index: int, record_id: int | None = None) -> dict[str, Any]:
        entries = _read_json_file(HISTORY_PATH)
        key = library_key(table, index, record_id)
        entries = [
            e for e in entries
            if library_key(str(e.get("table")), int(e.get("index", -1)), int(e["record_id"]) if e.get("record_id") not in (None, "") else None) != key
        ]
        _write_json_file(HISTORY_PATH, entries)
        return {"success": True, "items": self.history()}

    def clear_history(self) -> dict[str, Any]:
        _write_json_file(HISTORY_PATH, [])
        return {"success": True, "items": []}

    def categories(self) -> dict[str, Any]:
        core_categories = [
            "Acción", "Terror", "Comedia", "Ciencia ficción",
            "Animación", "Drama", "Misterio", "Aventura"
        ]
        counts: dict[str, dict[str, int]] = {}
        conn = self._get_connection()
        for cat in core_categories:
            try:
                p_cnt = int(conn.execute("SELECT COUNT(*) FROM pelis WHERE genero LIKE ? OR categoria LIKE ?", (f"%{cat}%", f"%{cat}%")).fetchone()[0])
                s_cnt = int(conn.execute("SELECT COUNT(*) FROM series WHERE genero LIKE ? OR categoria LIKE ?", (f"%{cat}%", f"%{cat}%")).fetchone()[0])
                counts[cat] = {"total": p_cnt + s_cnt, "movies": p_cnt, "series": s_cnt}
            except Exception:
                counts[cat] = {"total": 0, "movies": 0, "series": 0}
        return {"categories": counts}
    # VISTOS (WATCHED)
    def watched(self) -> list[dict[str, Any]]:
        entries = _read_json_file(WATCHED_PATH)
        result: list[dict[str, Any]] = []
        for entry in entries:
            table = str(entry.get("table") or "")
            index = int(entry.get("index", -1))
            record_id = entry.get("record_id")
            record_id = int(record_id) if record_id not in (None, "") else None
            row = self._row_at(table, index, record_id)
            if row is None:
                continue
            summary = self._summary(table, index, row)
            summary["record_id"] = record_id
            summary["watched_at"] = entry.get("watched_at")
            summary["watched"] = True
            summary["saved"] = library_key(table, index, record_id) in self.library_keys()
            result.append(summary)
        return result

    def recommendations(
        self,
        limit: int = 8,
        offset: int = 0,
        kind: str = "all",
    ) -> dict[str, Any]:
        requested_limit = max(1, min(int(limit), 48))
        requested_offset = max(0, int(offset))
        recommendation_kind = kind if kind in {"all", "movies"} else "all"
        watched_items = self.watched()
        watched_keys = self.watched_keys()
        watched_ids = self.all_watched_ids()

        def item_key(item: dict[str, Any]) -> str:
            record_id = item.get("record_id")
            return library_key(
                str(item.get("table") or ""),
                int(item.get("index", -1)),
                int(record_id) if record_id not in (None, "") else None,
            )

        def is_seen(item: dict[str, Any]) -> bool:
            if item.get("watched") or item_key(item) in watched_keys:
                return True
            tmdb = str(item.get("tmdb_id") or "")
            imdb = str(item.get("imdb_id") or "").casefold()
            title = clean_key(str(item.get("title") or ""))
            return any(
                value and value in watched_ids
                for value in (tmdb, imdb, title)
            )

        def all_catalog_items(
            section: str,
            max_items: int | None = None,
        ) -> list[dict[str, Any]]:
            collected: list[dict[str, Any]] = []
            page_size = 200
            page_offset = 0
            while True:
                page = self.catalog(
                    kind=recommendation_kind,
                    section=section,
                    limit=page_size,
                    offset=page_offset,
                )
                batch = page.get("items", [])
                if not batch:
                    break
                if max_items is not None:
                    remaining = max_items - len(collected)
                    if remaining <= 0:
                        break
                    collected.extend(batch[:remaining])
                else:
                    collected.extend(batch)
                total = int(page.get("total", 0) or 0)
                page_offset += len(batch)
                if max_items is not None and len(collected) >= max_items:
                    break
                if page_offset >= total or len(batch) < page_size:
                    break
            return collected

        if not watched_items:
            # Mezcla dinámica, fresca y variada de novedades, mejor valoradas y actualizadas
            recent_items = all_catalog_items("recent", max_items=150)
            rating_items = all_catalog_items("rating", max_items=150)
            updated_items = all_catalog_items("updated", max_items=150)
            
            seen_ids = set()
            pool: list[dict[str, Any]] = []
            for item in (recent_items + rating_items + updated_items):
                key = item_key(item)
                if key in seen_ids or is_seen(item):
                    continue
                if not (item.get("backdrop") or item.get("poster")):
                    continue
                seen_ids.add(key)
                pool.append(item)
            
            # Barajamos y ordenamos dando prioridad a títulos con tráiler y buena nota, con alta rotación aleatoria
            random.shuffle(pool)
            def fallback_weight(it: dict[str, Any]) -> float:
                score = (as_number(it.get("rating")) or 5.5)
                if it.get("youtube_id"):
                    score += 3.0
                return score + random.uniform(0.0, 16.0)

            pool.sort(key=fallback_weight, reverse=True)
            items = pool[requested_offset:requested_offset + requested_limit]
            return {
                "items": items,
                "personalized": False,
                "based_on": 0,
                "label": "Para descubrir",
                "reason": "Una selección dinámica y variada para tu próxima sesión.",
                "profile": [],
                "offset": requested_offset,
                "limit": requested_limit,
                "total": len(pool),
                "has_more": requested_offset + len(items) < len(pool),
            }

        genre_scores: dict[str, float] = {}
        genre_labels: dict[str, str] = {}
        kind_scores: dict[str, float] = {}
        for position, item in enumerate(watched_items[:24]):
            weight = max(0.65, 1.35 - position * 0.035)
            item_kind = str(item.get("kind") or "all")
            kind_scores[item_kind] = kind_scores.get(item_kind, 0) + weight
            for genre in genre_values(item.get("genre")):
                genre_key = clean_key(genre)
                if not genre_key:
                    continue
                genre_scores[genre_key] = genre_scores.get(genre_key, 0) + weight
                genre_labels.setdefault(genre_key, genre)

        profile = [
            genre_labels[key]
            for key, _ in sorted(
                genre_scores.items(),
                key=lambda pair: (-pair[1], pair[0]),
            )[:3]
        ]
        strongest_kind = max(kind_scores, key=kind_scores.get) if kind_scores else "all"
        candidate_pool_size = max(400, min(2000, requested_offset + requested_limit * 10))
        rating_items = all_catalog_items("rating", max_items=candidate_pool_size // 2)
        recent_items = all_catalog_items("recent", max_items=candidate_pool_size // 2)
        catalog_items = rating_items + recent_items
        seen_cand = set()
        candidates = []
        for it in catalog_items:
            k = item_key(it)
            if k not in seen_cand and (it.get("backdrop") or it.get("poster")) and not is_seen(it):
                seen_cand.add(k)
                candidates.append(it)

        matching_candidates = [
            item for item in candidates
            if any(clean_key(genre) in genre_scores for genre in genre_values(item.get("genre")))
        ]
        if profile and matching_candidates:
            candidates = matching_candidates

        random.shuffle(candidates)
        def score_candidate(item: dict[str, Any]) -> tuple[float, str]:
            candidate_genres = {
                clean_key(genre) for genre in genre_values(item.get("genre"))
            }
            matching_genres = [
                genre_labels[key]
                for key in candidate_genres
                if key in genre_scores
            ]
            genre_match = sum(genre_scores.get(key, 0) for key in candidate_genres)
            kind_match = 2.0 if item.get("kind") == strongest_kind else 0
            rating_match = (as_number(item.get("rating")) or 0) * 0.35
            year_match = 0.25 if as_number(item.get("year")) else 0
            trailer_bonus = 3.0 if item.get("youtube_id") else 0
            # Jitter aleatorio sustancial para rotar y variar títulos entre sesiones
            jitter = random.uniform(0.0, 14.0)
            total = genre_match * 3.5 + kind_match + rating_match + year_match + trailer_bonus + jitter
            reason = (
                f"Coincide con tus gustos: {', '.join(matching_genres[:2])}"
                if matching_genres
                else "Elegida por su buena valoración"
            )
            return total, reason

        ranked: list[tuple[float, dict[str, Any], str]] = []
        for item in candidates:
            score, reason = score_candidate(item)
            item["recommendation_reason"] = reason
            ranked.append((score, item, reason))
        ranked.sort(key=lambda entry: -entry[0])
        
        if len(ranked) < requested_offset + requested_limit:
            fallback = all_catalog_items("recent", max_items=candidate_pool_size)
            seen_result_keys = {item_key(entry[1]) for entry in ranked}
            for item in fallback:
                has_profile_match = any(
                    clean_key(genre) in genre_scores
                    for genre in genre_values(item.get("genre"))
                )
                if (
                    (item.get("backdrop") or item.get("poster"))
                    and not is_seen(item)
                    and item_key(item) not in seen_result_keys
                    and (not profile or has_profile_match)
                ):
                    item["recommendation_reason"] = "Una novedad que puede encajar contigo"
                    ranked.append((0, item, item["recommendation_reason"]))
                    seen_result_keys.add(item_key(item))
                    if len(ranked) >= requested_offset + requested_limit:
                        break

        ranked.sort(key=lambda entry: -entry[0])
        page = ranked[requested_offset:requested_offset + requested_limit]
        items = [entry[1] for entry in page]
        reason = (
            f"Basado en tus títulos vistos"
            + (f" y tu afinidad por {', '.join(profile)}" if profile else "")
        )
        return {
            "items": items[:requested_limit],
            "personalized": True,
            "based_on": len(watched_items),
            "label": "Para ti",
            "reason": reason,
            "profile": profile,
            "offset": requested_offset,
            "limit": requested_limit,
            "total": len(ranked),
            "has_more": requested_offset + len(items) < len(ranked),
        }

    def watched_keys(self) -> set[str]:
        keys = set()
        for e in _read_json_file(WATCHED_PATH):
            e_rec_id = safe_int(e.get("record_id"))
            e_idx = safe_int(e.get("index")) if safe_int(e.get("index")) is not None else -1
            k = library_key(str(e.get("table")), e_idx, e_rec_id)
            keys.add(k)
            if e.get("tmdb"):
                keys.add(f"tmdb:{e['tmdb']}")
            if e.get("title"):
                keys.add(f"title:{clean_key(str(e['title']))}")
        return keys

    def all_watched_ids(self) -> set[str]:
        ids: set[str] = set()
        for e in _read_json_file(WATCHED_PATH):
            if e.get("tmdb"):
                ids.add(str(e["tmdb"]))
            if e.get("imdb"):
                ids.add(str(e["imdb"]).lower())
            if e.get("title"):
                ids.add(clean_key(str(e["title"])))
        return ids

    def set_watched(self, table: str, index: int, record_id: int | None = None, watched: bool = True) -> dict[str, Any]:
        rec_id = safe_int(record_id)
        idx = safe_int(index) if safe_int(index) is not None else 0
        entries = _read_json_file(WATCHED_PATH)
        row = self._row_at(table, idx, rec_id)
        tmdb = field_value(row, "tmdb_id") if row else None
        imdb = field_value(row, "imdb_id") if row else None
        title = field_value(row, "title") if row else None
        c_title = clean_key(title) if title else ""
        key = library_key(table, idx, rec_id)

        new_entries = []
        for e in entries:
            e_rec_id = safe_int(e.get("record_id"))
            e_idx = safe_int(e.get("index")) if safe_int(e.get("index")) is not None else -1
            e_key = library_key(str(e.get("table")), e_idx, e_rec_id)
            e_tmdb = str(e.get("tmdb") or "")
            e_title = clean_key(str(e.get("title") or ""))
            if e_key == key or (tmdb and e_tmdb == str(tmdb)) or (c_title and e_title == c_title):
                continue
            new_entries.append(e)

        if watched:
            new_entries.insert(0, {
                "table": table, "index": idx, "record_id": rec_id,
                "tmdb": tmdb, "imdb": imdb, "title": title,
                "watched_at": datetime.now().astimezone().isoformat(timespec="seconds")
            })
        _write_json_file(WATCHED_PATH, new_entries)
        return {"watched": watched, "key": key}

    # ==========================
    # REGISTRO DE EPISODIOS VISTOS
    # ==========================

    def get_watched_episodes(self, tmdb: str | None, table: str | None = None, record_id: int | None = None) -> list[dict[str, Any]]:
        entries = _read_json_file(EPISODES_WATCHED_PATH)
        result = []
        for e in entries:
            match_tmdb = tmdb and str(e.get("tmdb")) == str(tmdb)
            match_record = table and record_id is not None and str(e.get("table")) == str(table) and str(e.get("record_id")) == str(record_id)
            if match_tmdb or match_record:
                result.append({"season": str(e.get("season")), "episode": str(e.get("episode"))})
        return result

    def toggle_episode_watched(
        self,
        tmdb: str | None,
        table: str | None,
        record_id: int | None,
        season: Any,
        episode: Any,
        watched: bool = True
    ) -> dict[str, Any]:
        entries = _read_json_file(EPISODES_WATCHED_PATH)
        s_str = str(season)
        e_str = str(episode)

        def is_same_ep(item: dict[str, Any]) -> bool:
            match_tmdb = tmdb and str(item.get("tmdb")) == str(tmdb)
            match_record = table and record_id is not None and str(item.get("table")) == str(table) and str(item.get("record_id")) == str(record_id)
            return (match_tmdb or match_record) and str(item.get("season")) == s_str and str(item.get("episode")) == e_str

        entries = [item for item in entries if not is_same_ep(item)]

        if watched:
            entries.insert(0, {
                "tmdb": tmdb,
                "table": table,
                "record_id": record_id,
                "season": s_str,
                "episode": e_str,
                "watched_at": datetime.now().astimezone().isoformat(timespec="seconds")
            })

        _write_json_file(EPISODES_WATCHED_PATH, entries)
        return {"watched": watched, "season": s_str, "episode": e_str}

    def toggle_all_episodes_watched(
        self,
        tmdb: str | None,
        table: str | None,
        record_id: int | None,
        episodes: list[dict[str, Any]],
        watched: bool = True
    ) -> dict[str, Any]:
        entries = _read_json_file(EPISODES_WATCHED_PATH)

        def match_show(item: dict[str, Any]) -> bool:
            match_tmdb = tmdb and str(item.get("tmdb")) == str(tmdb)
            match_record = table and record_id is not None and str(item.get("table")) == str(table) and str(item.get("record_id")) == str(record_id)
            return bool(match_tmdb or match_record)

        entries = [item for item in entries if not match_show(item)]

        if watched:
            now_iso = datetime.now().astimezone().isoformat(timespec="seconds")
            for ep in episodes:
                entries.insert(0, {
                    "tmdb": tmdb,
                    "table": table,
                    "record_id": record_id,
                    "season": str(ep.get("season")),
                    "episode": str(ep.get("episode")),
                    "watched_at": now_iso
                })

        _write_json_file(EPISODES_WATCHED_PATH, entries)
        
        if table:
            self.set_watched(table, -1, record_id, watched)

        return {"success": True, "watched": watched, "count": len(episodes) if watched else 0}

    # ==========================
    # RULETA INTELIGENTE "¿QUÉ VEO HOY?"
    # ==========================
    def random_smart(
        self,
        kind: str = "all",
        genre: str = "",
        era: str = "all",
        min_rating: float = 0.0,
        exclude_watched: bool = True,
    ) -> dict[str, Any] | None:
        tables = [t for t in self._catalog_tables() if not t.startswith("v_")]
        valid_tables = [t for t in tables if kind == "all" or infer_kind(t, {}) == kind]
        if not valid_tables:
            valid_tables = tables

        watched_identifiers = self.all_watched_ids() if exclude_watched else set()
        candidates: list[dict[str, Any]] = []

        conn = self._get_connection()
        for chosen_table in valid_tables:
            try:
                where_clauses = []
                params: list[Any] = []

                if genre and genre.lower() != "todos":
                    genre_col = self._column_for(chosen_table, "genre")
                    if genre_col:
                        where_clauses.append(f"{self._quote(genre_col)} LIKE ?")
                        params.append(f"%{genre}%")

                year_col = self._column_for(chosen_table, "year")
                if year_col and era != "all":
                    if era == "current":
                        where_clauses.append(f"{self._quote(year_col)} >= 2023")
                    elif era == "2010s":
                        where_clauses.append(f"{self._quote(year_col)} >= 2010 AND {self._quote(year_col)} < 2023")
                    elif era == "2000s":
                        where_clauses.append(f"{self._quote(year_col)} >= 2000 AND {self._quote(year_col)} < 2010")
                    elif era == "classic":
                        where_clauses.append(f"{self._quote(year_col)} < 2000 AND {self._quote(year_col)} > 1900")

                if min_rating > 0:
                    rating_col = self._column_for(chosen_table, "rating")
                    if rating_col:
                        where_clauses.append(f"{self._quote(rating_col)} >= ?")
                        params.append(min_rating)

                where_sql = (" WHERE " + " AND ".join(where_clauses)) if where_clauses else ""
                query = f"SELECT rowid AS __catalog_rowid, * FROM {self._quote(chosen_table)}{where_sql} ORDER BY RANDOM() LIMIT 40"
                rows = conn.execute(query, params).fetchall()

                for r in rows:
                    row_data = self._plain_row(r)
                    tmdb_id = str(field_value(row_data, "tmdb_id") or "")
                    imdb_id = str(field_value(row_data, "imdb_id") or "").lower()
                    title_key = clean_key(str(field_value(row_data, "title") or ""))

                    if exclude_watched and (tmdb_id in watched_identifiers or imdb_id in watched_identifiers or title_key in watched_identifiers):
                        continue

                    summary = self._summary(chosen_table, -1, row_data)
                    summary["record_id"] = int(r["__catalog_rowid"]) if r["__catalog_rowid"] is not None else None
                    candidates.append({"table": chosen_table, "record_id": summary["record_id"], "summary": summary})

            except sqlite3.DatabaseError:
                continue

        if candidates:
            return random.choice(candidates)
        return None

    def _column_for(self, table: str, field: str) -> str | None:
        return field_column(self._table_columns.get(table, []), field)

    @staticmethod
    def _facet_value(value: Any, field: str) -> str | None:
        if value in (None, ""):
            return None
        text = str(value).strip()
        if not text:
            return None
        if field == "year":
            match = re.search(r"\d{4}", text)
            return match.group(0) if match else None
        return text

    def facets(self) -> dict[str, list[str]]:
        if self._cached_facets is not None:
            return self._cached_facets

        values: dict[str, set[str]] = {
            "category": set(),
            "genre": set(),
            "year": set(),
            "quality": set(),
            "language": set(),
        }
        conn = self._get_connection()
        for table in self._catalog_tables():
            rows = self._rows.get(table)
            if rows:
                for row in rows:
                    category = field_value(row, "category") or field_value(row, "type")
                    for field, value in (
                        ("category", category),
                        ("genre", field_value(row, "genre")),
                        ("year", field_value(row, "year")),
                        ("quality", field_value(row, "quality")),
                        ("language", field_value(row, "language")),
                    ):
                        if field == "genre":
                            values[field].update(genre_values(value))
                            continue
                        normalized = self._facet_value(value, field)
                        if normalized:
                            values[field].add(normalized)
                continue
            if self.demo or table not in self._table_counts:
                continue
            columns = {
                field: self._column_for(table, field)
                for field in ("category", "genre", "year", "quality", "language")
            }
            selected = [column for column in columns.values() if column]
            if not selected:
                continue
            try:
                rows_from_db = conn.execute(
                    "SELECT " + ", ".join(self._quote(column) for column in selected)
                    + f" FROM {self._quote(table)}"
                ).fetchall()
                for db_row in rows_from_db:
                    for field, column in columns.items():
                        if column:
                            if field == "genre":
                                values[field].update(genre_values(db_row[column]))
                                continue
                            normalized = self._facet_value(db_row[column], field)
                            if normalized:
                                values[field].add(normalized)
            except sqlite3.DatabaseError:
                continue

        self._cached_facets = {
            field: sorted(items, key=lambda value: (clean_key(value), value))
            for field, items in values.items()
        }
        return self._cached_facets

    def _catalog_tables(self, requested_table: str = "") -> list[str]:
        if requested_table:
            return [requested_table] if requested_table in self._table_counts else []
        official = [table for table in CONTENT_TABLES if table in self._table_counts]
        if official:
            return official
        category_views = [
            table
            for table in self._table_counts
            if clean_key(table).startswith(("vpelis", "vseries"))
        ]
        return category_views or list(self._table_counts)

    @staticmethod
    def _plain_row(row: sqlite3.Row | dict[str, Any]) -> dict[str, Any]:
        return {
            str(key): json_value(value)
            for key, value in dict(row).items()
            if str(key) != "__catalog_rowid"
        }

    def _row_at(
        self,
        table: str,
        index: int,
        record_id: int | None = None,
        query: str = "",
    ) -> dict[str, Any] | None:
        rows = self._rows.get(table)
        if rows is not None and table not in CONTENT_TABLES and table not in LINK_TABLES:
            normalized_query = clean_key(query)
            matches = [
                (row_index, row)
                for row_index, row in enumerate(rows)
                if not normalized_query
                or normalized_query
                in clean_key(
                    " ".join(
                        str(value) for value in row.values() if value is not None
                    )
                )
            ]
            if 0 <= index < len(matches):
                return matches[index][1]
            return None
        
        if self.demo or table not in self._table_counts or (index < 0 and record_id is None):
            return None
        
        try:
            conn = self._get_connection()
            row = None
            if record_id is not None:
                try:
                    row = conn.execute(
                        f"SELECT rowid AS __catalog_rowid, * FROM {self._quote(table)} WHERE rowid = ?",
                        (record_id,),
                    ).fetchone()
                except sqlite3.DatabaseError:
                    pass 
            
            if row is None and index >= 0:
                where, search_values = self._search_clause(table, query)
                order = self._catalog_order(table, "all") 
                try:
                    row = conn.execute(
                        f"SELECT rowid AS __catalog_rowid, * FROM {self._quote(table)}{where}{order} LIMIT 1 OFFSET ?",
                        [*search_values, index],
                    ).fetchone()
                except sqlite3.DatabaseError:
                    row = conn.execute(
                        f"SELECT * FROM {self._quote(table)}{where}{order} LIMIT 1 OFFSET ?",
                        [*search_values, index],
                    ).fetchone()
            return self._plain_row(row) if row is not None else None
        except sqlite3.DatabaseError:
            return None

    def _search_clause(self, table: str, query: str) -> tuple[str, list[str]]:
        search_text = " ".join(str(query).split()).strip()
        if not search_text:
            return "", []
        columns = self._table_columns.get(table, [])
        if not columns:
            return "", []
        clause = " OR ".join(
            f"{self._quote(column)} LIKE ?"
            for column in columns
        )
        return f" WHERE ({clause})", [f"%{search_text}%"] * len(columns)

    def _catalog_clause(
        self,
        table: str,
        query: str = "",
        category: str = "",
        genre: str = "",
        year: str = "",
        quality: str = "",
        language: str = "",
        min_rating: float = 0.0,
        year_from: str = "",
        year_to: str = "",
        tmdb_ids: list[str] | set[str] | None = None,
    ) -> tuple[str, list[Any]]:
        clauses: list[str] = []
        values: list[Any] = []
        search_text = " ".join(str(query).split()).strip()
        columns = self._table_columns.get(table, [])
        if search_text and columns:
            clauses.append(
                "("
                + " OR ".join(
                    f"{self._quote(column)} LIKE ?"
                    for column in columns
                )
                + ")"
            )
            values.extend([f"%{search_text}%"] * len(columns))

        # Year / Period interval
        y_from = int(year_from) if str(year_from).isdigit() else None
        y_to = int(year_to) if str(year_to).isdigit() else None
        if year:
            y_str = str(year).strip()
            if "-" in y_str:
                parts = y_str.split("-")
                if parts[0].isdigit(): y_from = int(parts[0])
                if parts[1].isdigit(): y_to = int(parts[1])
            elif y_str.startswith("<=") and y_str[2:].isdigit():
                y_to = int(y_str[2:])
            elif y_str.startswith(">=") and y_str[2:].isdigit():
                y_from = int(y_str[2:])
            elif y_str.isdigit():
                y_from = int(y_str)
                y_to = int(y_str)

        date_col = self._column_for(table, "year")
        if date_col:
            if y_from is not None and y_to is not None:
                clauses.append(
                    f"CAST(SUBSTR({self._quote(date_col)}, 1, 4) AS INTEGER) >= ? AND CAST(SUBSTR({self._quote(date_col)}, 1, 4) AS INTEGER) <= ?"
                )
                values.extend([y_from, y_to])
            elif y_from is not None:
                clauses.append(
                    f"CAST(SUBSTR({self._quote(date_col)}, 1, 4) AS INTEGER) >= ?"
                )
                values.append(y_from)
            elif y_to is not None:
                clauses.append(
                    f"CAST(SUBSTR({self._quote(date_col)}, 1, 4) AS INTEGER) <= ? AND CAST(SUBSTR({self._quote(date_col)}, 1, 4) AS INTEGER) > 0"
                )
                values.append(y_to)

        # Min rating
        if min_rating and float(min_rating) > 0:
            rating_col = self._column_for(table, "rating")
            if rating_col:
                clauses.append(f"CAST({self._quote(rating_col)} AS FLOAT) >= ?")
                values.append(float(min_rating))

        # TMDB IDs (e.g. from Platform filter)
        if tmdb_ids is not None:
            tmdb_col = self._column_for(table, "tmdb_id")
            if tmdb_col:
                id_list = [str(tid) for tid in tmdb_ids if str(tid).strip()]
                if id_list:
                    chunk = id_list[:900]
                    placeholders = ",".join("?" for _ in chunk)
                    clauses.append(f"{self._quote(tmdb_col)} IN ({placeholders})")
                    values.extend(chunk)
                else:
                    clauses.append("1 = 0")

        # Category and Genre filtering
        filters = (
            ("category", category, False),
            ("genre", genre, False),
            ("quality", quality, False),
            ("language", language, False),
        )
        for field, requested, starts_with in filters:
            text = " ".join(str(requested).split()).strip()
            column = self._column_for(table, field)
            if not text or not column:
                continue
            clauses.append(
                f"{self._quote(column)} "
                + ("LIKE ?" if starts_with else "LIKE ?")
            )
            values.append(f"{text}%" if starts_with else f"%{text}%")

        return (f" WHERE {' AND '.join(clauses)}" if clauses else ""), values

    def _catalog_order(self, table: str, section: str) -> str:
        title = self._column_for(table, "title")
        updated = self._column_for(table, "updated")
        date = self._column_for(table, "year")
        rating = self._column_for(table, "rating")
        if section in ("recent", "release_desc"):
            expressions = [
                f"{self._quote(date)} DESC" if date else "",
                f"{self._quote(updated)} DESC" if updated else "",
            ]
        elif section in ("oldest", "release_asc"):
            expressions = [
                f"{self._quote(date)} ASC" if date else "",
                f"{self._quote(updated)} ASC" if updated else "",
            ]
        elif section in ("updated", "catalog_desc"):
            expressions = [f"{self._quote(updated)} DESC" if updated else ""]
        elif section == "rating":
            expressions = [
                f"CAST({self._quote(rating)} AS FLOAT) DESC" if rating else "",
                f"{self._quote(updated)} DESC" if updated else "",
            ]
        elif section in ("title_asc", "az"):
            expressions = [f"{self._quote(title)} COLLATE NOCASE ASC" if title else ""]
        elif section in ("title_desc", "za"):
            expressions = [f"{self._quote(title)} COLLATE NOCASE DESC" if title else ""]
        elif section == "random":
            return " ORDER BY RANDOM()"
        else:
            expressions = []
        expressions = [expression for expression in expressions if expression]
        if not expressions and title:
            expressions = [f"{self._quote(title)} COLLATE NOCASE ASC"]
        return " ORDER BY " + ", ".join(expressions) if expressions else ""

    @staticmethod
    def _matches_catalog_filters(
        row: dict[str, Any],
        query: str,
        category: str,
        genre: str,
        year: str,
        quality: str,
        language: str,
        min_rating: float = 0.0,
        year_from: str = "",
        year_to: str = "",
        tmdb_ids: list[str] | set[str] | None = None,
    ) -> bool:
        normalized_query = clean_key(query)
        if normalized_query and normalized_query not in clean_key(
            " ".join(str(value) for value in row.values() if value is not None)
        ):
            return False

        if tmdb_ids is not None:
            tmdb_val = str(field_value(row, "tmdb_id") or "").strip()
            if not tmdb_val or tmdb_val not in set(str(t) for t in tmdb_ids):
                return False

        if min_rating and float(min_rating) > 0:
            val_rating = as_number(field_value(row, "rating"))
            if val_rating is None or float(val_rating) < float(min_rating):
                return False

        y_from = int(year_from) if str(year_from).isdigit() else None
        y_to = int(year_to) if str(year_to).isdigit() else None
        if year:
            y_str = str(year).strip()
            if "-" in y_str:
                parts = y_str.split("-")
                if parts[0].isdigit(): y_from = int(parts[0])
                if parts[1].isdigit(): y_to = int(parts[1])
            elif y_str.startswith("<=") and y_str[2:].isdigit():
                y_to = int(y_str[2:])
            elif y_str.startswith(">=") and y_str[2:].isdigit():
                y_from = int(y_str[2:])
            elif y_str.isdigit():
                y_from = int(y_str)
                y_to = int(y_str)

        if y_from is not None or y_to is not None:
            val_year = as_number(field_value(row, "year"))
            if val_year is not None:
                val_y = int(val_year)
                if y_from is not None and val_y < y_from:
                    return False
                if y_to is not None and val_y > y_to:
                    return False

        category_value = field_value(row, "category") or field_value(row, "type")
        filters = (
            (category, category_value, False),
            (genre, field_value(row, "genre"), False),
            (quality, quality, False),
            (language, language, False),
        )
        for requested, actual, starts_with in filters:
            requested_text = clean_key(requested)
            actual_text = str(actual or "").casefold()
            if requested_text and (
                (not actual_text.startswith(requested_text))
                if starts_with
                else requested_text not in clean_key(actual_text)
            ):
                return False
        return True

    @staticmethod
    def _sort_catalog_rows(
        rows: list[tuple[int, dict[str, Any]]],
        section: str,
    ) -> list[tuple[int, dict[str, Any]]]:
        if section == "random":
            random.shuffle(rows)
            return rows
        if section in ("recent", "release_desc"):
            rows.sort(
                key=lambda pair: (
                    str(field_value(pair[1], "year") or ""),
                    str(field_value(pair[1], "updated") or ""),
                ),
                reverse=True,
            )
        elif section in ("oldest", "release_asc"):
            rows.sort(
                key=lambda pair: (
                    str(field_value(pair[1], "year") or "9999"),
                    str(field_value(pair[1], "updated") or "9999"),
                ),
                reverse=False,
            )
        elif section in ("updated", "catalog_desc"):
            rows.sort(
                key=lambda pair: str(field_value(pair[1], "updated") or ""),
                reverse=True,
            )
        elif section == "rating":
            rows.sort(
                key=lambda pair: (
                    as_number(field_value(pair[1], "rating")) or -1,
                    str(field_value(pair[1], "updated") or ""),
                ),
                reverse=True,
            )
        elif section in ("title_desc", "za"):
            rows.sort(
                key=lambda pair: str(field_value(pair[1], "title") or "").casefold(),
                reverse=True,
            )
        else: # title_asc, az, all
            rows.sort(key=lambda pair: str(field_value(pair[1], "title") or "").casefold())
        return rows
    def trending(self, kind: str, limit: int = 20) -> dict[str, Any]:
        config = _read_config()
        tmdb_key = config.get("tmdb_api_key", "").strip() or "35ba90a85ecdc69c7962a68b363ef5ef"
        items = []
        seen_keys = set()
        
        if tmdb_key:
            endpoint = "movie" if kind == "movies" else "tv"
            url = f"https://api.themoviedb.org/3/{endpoint}/popular?api_key={tmdb_key}&language=es-ES&page=1"
            try:
                request = Request(url, headers={"Accept": "application/json"})
                with urlopen(request, timeout=4) as response:
                    data = json.loads(response.read().decode("utf-8"))
                tmdb_ids: list[str] = [
                    str(r["id"]) for r in data.get("results", []) if r.get("id")
                ]
                
                if tmdb_ids:
                    found_items = []
                    saved_keys = self.library_keys()
                    watched_keys = self.watched_keys()
                    conn = self._get_connection()
                    for table_name in self._catalog_tables():
                        if table_name.startswith("v_"):
                            continue
                            
                        table_kind = infer_kind(table_name, {})
                        if kind != table_kind:
                            continue
                        
                        tmdb_column = self._column_for(table_name, "tmdb_id")
                        if not tmdb_column:
                            continue
                        
                        placeholders = ",".join("?" for _ in tmdb_ids)
                        try:
                            query = f"SELECT rowid AS __catalog_rowid, * FROM {self._quote(table_name)} WHERE {self._quote(tmdb_column)} IN ({placeholders})"
                            rows = conn.execute(query, tmdb_ids).fetchall()

                            for row in rows:
                                row_data = self._plain_row(row)
                                record_id = row["__catalog_rowid"]
                                summary = self._summary(table_name, -1, row_data)
                                summary["record_id"] = int(record_id) if record_id is not None else None
                                summary["index"] = -1 
                                summary["saved"] = self.is_saved_item(table_name, -1, summary["record_id"], summary.get("tmdb_id"), summary.get("title"))
                                summary["watched"] = self.is_watched_item(table_name, -1, summary["record_id"], summary.get("tmdb_id"), summary.get("title"))
                                summary["_tmdb_id"] = str(row_data.get(tmdb_column))
                                found_items.append(summary)
                        except sqlite3.DatabaseError:
                            continue
                    
                    id_to_item = {item["_tmdb_id"]: item for item in found_items}
                    for tid in tmdb_ids:
                        if tid in id_to_item:
                            item = id_to_item[tid]
                            key = (item.get("table"), item.get("record_id"), item.get("title"))
                            if key not in seen_keys:
                                items.append(item)
                                seen_keys.add(key)
                                if len(items) >= limit:
                                    break

            except Exception as e:
                print(f"[catalogo] Error en tendencias TMDB: {e}", file=sys.stderr)

        if len(items) < limit:
            try:
                fallback_data = self.catalog(kind=kind, section="recent", limit=limit * 2)
                for fb_item in fallback_data.get("items", []):
                    key = (fb_item.get("table"), fb_item.get("record_id"), fb_item.get("title"))
                    if key not in seen_keys:
                        items.append(fb_item)
                        seen_keys.add(key)
                        if len(items) >= limit:
                            break
            except Exception as e:
                print(f"[catalogo] Error en fallback de tendencias: {e}", file=sys.stderr)

        return {"items": items[:limit], "total": len(items[:limit])}

    @lru_cache(maxsize=4096)
    def _cached_table_links(self, link_table: str, tmdb: str) -> tuple[dict[str, Any], ...]:
        try:
            conn = self._get_connection()
            link_rows = conn.execute(
                f"SELECT * FROM {self._quote(link_table)} WHERE tmdb = ?",
                (tmdb,),
            ).fetchall()
            return tuple(dict(r) for r in link_rows)
        except sqlite3.DatabaseError:
            return ()

    def _related_links(
        self,
        row: dict[str, Any],
        kind: str,
        season: Any = None,
        episode: Any = None,
    ) -> list[dict[str, Any]]:
        tmdb = field_value(row, "tmdb_id")
        if tmdb in (None, ""):
            return []
        link_table = "enlaces_series" if kind == "series" else "enlaces_pelis"
        if self.demo or self.db_path is None or link_table not in self._table_counts:
            return []
        try:
            raw_rows = list(self._cached_table_links(link_table, str(tmdb)))
            if kind == "series":
                if season not in (None, ""):
                    raw_rows = [
                        r for r in raw_rows 
                        if str(field_value(r, "season") or r.get("temporada")) == str(season)
                    ]
                if episode not in (None, ""):
                    raw_rows = [
                        r for r in raw_rows 
                        if str(field_value(r, "episode") or r.get("episodio")) == str(episode)
                    ]
                raw_rows.sort(
                    key=lambda candidate: (
                        sort_value(field_value(candidate, "season")),
                        sort_value(field_value(candidate, "episode")),
                        sort_value(field_value(candidate, "quality")),
                    )
                )
            else:
                raw_rows.sort(
                    key=lambda candidate: (
                        sort_value(field_value(candidate, "quality")),
                        sort_value(field_value(candidate, "updated")),
                    ),
                    reverse=True,
                )
            return [
                {
                    "table": link_table,
                    **source_option(link_row, position),
                    "fichier_resolvable": self._can_resolve_fichier(link_row),
                }
                for position, link_row in enumerate(raw_rows[:MAX_RELATED_LINKS], start=1)
            ]
        except sqlite3.DatabaseError:
            return []

    def _can_resolve_fichier(self, link_row: dict[str, Any]) -> bool:
        link, _ = discover_link(field_value(link_row, "link"))
        server = clean_key(str(field_value(link_row, "server") or ""))
        return bool(
            self.fichier_token_path
            and self.fichier_token_path.is_file()
            and link
            and (
                "1fichier" in server
                or "1fichier.com" in urlparse(link).netloc.casefold()
            )
        )

    def resolve_fichier(
        self,
        tmdb: Any,
        kind: str,
        season: Any = None,
        episode: Any = None,
        number: int = 0,
    ) -> dict[str, Any]:
        if not self.fichier_token_path or not self.fichier_token_path.is_file():
            raise RuntimeError(
                "No se encontró la clave de acceso de descarga rápida."
            )
        row = {"tmdb": tmdb}
        entries = self._related_links(row, kind, season, episode)
        if number < 1 or number > len(entries):
            raise RuntimeError("La fuente indicada ya no está disponible.")
        entry = entries[number - 1]
        link = str(entry.get("link") or "")
        if "1fichier.com" not in urlparse(link).netloc.casefold():
            raise RuntimeError("La fuente seleccionada no es una fuente válida.")
        token = self.fichier_token_path.read_text(encoding="utf-8").strip()
        if not token:
            raise RuntimeError("La clave de acceso está vacía.")
        request = Request(
            FICHIER_API_URL,
            data=json.dumps({"url": link}).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
            },
            method="POST",
        )
        try:
            with urlopen(request, timeout=10) as response:
                payload = json.loads(response.read().decode("utf-8"))
        except (HTTPError, URLError, TimeoutError, json.JSONDecodeError) as error:
            raise RuntimeError(f"No se pudo realizar la petición de streaming: {error}") from error
        if payload.get("status") not in (None, "OK"):
            raise RuntimeError(str(payload.get("message") or "Petición rechazada por el servidor."))
        resolved = payload.get("url")
        if not isinstance(resolved, str) or not is_url(resolved):
            raise RuntimeError("El servidor no devolvió una URL válida.")
        return {"url": resolved, "source": "Directo", "expires": payload.get("expires")}

    def resolve_fichier_for_item(
        self,
        table: str,
        index: int,
        record_id: int | None,
        query: str,
        number: int,
    ) -> dict[str, Any]:
        row = self._row_at(table, index, record_id, query)
        if row is None:
            raise RuntimeError("Registro no encontrado.")
        kind = infer_kind(table, row)
        tmdb = field_value(row, "tmdb_id")
        return self.resolve_fichier(
            tmdb,
            kind,
            field_value(row, "season"),
            field_value(row, "episode"),
            number,
        )

    def _summary(self, table: str, index: int, row: dict[str, Any]) -> dict[str, Any]:
        kind = infer_kind(table, row)
        explicit_type = field_value(row, "type")
        trailer_raw = trailer_url(field_value(row, "trailer"))
        return {
            "table": table,
            "index": index,
            "kind": kind,
            "type": explicit_type or ("Serie" if kind == "series" else "Película" if kind == "movies" else "Otro"),
            "title": field_value(row, "title") or f"Registro {index + 1}",
            "description": compact(field_value(row, "description")),
            "poster": media_url(field_value(row, "poster"), "w500"),
            "backdrop": media_url(field_value(row, "backdrop"), "w1280"),
            "trailer": trailer_raw,
            "youtube_id": extract_youtube_id(trailer_raw),
            "year": as_number(field_value(row, "year")),
            "rating": as_number(field_value(row, "rating")),
            "genre": format_genres(field_value(row, "genre")),
            "language": json_value(field_value(row, "language")),
            "tmdb_id": field_value(row, "tmdb_id"),
            "imdb_id": field_value(row, "imdb_id"),
            "fields": len(row),
        }

    def _streaming_local_items(
        self,
        tmdb_ids_by_kind: dict[str, set[str]],
    ) -> dict[tuple[str, str], dict[str, Any]]:
        """Indexa los títulos locales encontrados por el descubrimiento de TMDB."""
        wanted = {
            (kind, str(tmdb_id))
            for kind, ids in tmdb_ids_by_kind.items()
            for tmdb_id in ids
            if str(tmdb_id).strip()
        }
        if not wanted or self.demo or self.db_path is None:
            return {}

        found: dict[tuple[str, str], dict[str, Any]] = {}
        saved_keys = self.library_keys()
        watched_keys = self.watched_keys()
        conn = self._get_connection()
        for table_name in self._catalog_tables():
            table_kind = infer_kind(
                table_name, (self._rows.get(table_name) or [{}])[0]
            )
            if table_kind not in {"movies", "series"}:
                continue
            tmdb_column = self._column_for(table_name, "tmdb_id")
            if not tmdb_column:
                continue
            ids = [
                tmdb_id
                for kind, tmdb_id in wanted
                if kind == table_kind
            ]
            if not ids:
                continue
            placeholders = ",".join("?" for _ in ids)
            try:
                rows = conn.execute(
                    f"SELECT rowid AS __catalog_rowid, * FROM "
                    f"{self._quote(table_name)} "
                    f"WHERE {self._quote(tmdb_column)} IN ({placeholders})",
                    ids,
                ).fetchall()
            except sqlite3.DatabaseError:
                continue

            for row in rows:
                row_data = self._plain_row(row)
                tmdb_id = str(field_value(row_data, "tmdb_id") or "").strip()
                key = (table_kind, tmdb_id)
                if key not in wanted or key in found:
                    continue
                record_id = row["__catalog_rowid"] if "__catalog_rowid" in row.keys() else None
                record_id = int(record_id) if record_id is not None else None
                summary = self._summary(table_name, -1, row_data)
                summary["record_id"] = record_id
                summary["saved"] = self.is_saved_item(table_name, -1, record_id, summary.get("tmdb_id"), summary.get("title"))
                summary["watched"] = self.is_watched_item(table_name, -1, record_id, summary.get("tmdb_id"), summary.get("title"))
                found[key] = summary
        return found

    def streaming_platforms(self, region: str = TMDB_STREAMING_REGION) -> dict[str, Any]:
        """Devuelve plataformas de streaming activas en España con títulos locales."""
        api_key, _ = _tmdb_key_info()
        if not api_key:
            return {
                "configured": False,
                "region": region,
                "providers": [],
                "message": "Configura tu clave de TMDB en Ajustes para explorar por plataforma.",
            }

        provider_lists = [
            _tmdb_request(
                "watch/providers/movie",
                {"watch_region": region},
            ),
            _tmdb_request(
                "watch/providers/tv",
                {"watch_region": region},
            ),
        ]
        available: dict[str, dict[str, Any]] = {}
        for payload in provider_lists:
            for provider in payload.get("results", []):
                if not isinstance(provider, dict) or not provider.get("provider_id"):
                    continue
                provider_id = str(provider["provider_id"])
                current = available.get(provider_id)
                if current is None or int(provider.get("display_priority") or 999) < int(
                    current.get("display_priority") or 999
                ):
                    available[provider_id] = provider

        selected: list[dict[str, Any]] = []
        used_ids: set[str] = set()
        for label, aliases in TMDB_STREAMING_PROVIDER_ALIASES:
            matching = [
                provider
                for provider in available.values()
                if any(
                    clean_key(alias) in clean_key(str(provider.get("provider_name") or ""))
                    for alias in aliases
                )
            ]
            matching.sort(
                key=lambda provider: int(provider.get("display_priority") or 999)
            )
            if matching and str(matching[0]["provider_id"]) not in used_ids:
                provider = dict(matching[0])
                provider["display_name"] = label
                selected.append(provider)
                used_ids.add(str(provider["provider_id"]))

        # Si TMDB cambia los nombres regionales, conservamos algunas plataformas
        # con mejor prioridad para que la sección no quede vacía.
        if not selected:
            fallback = sorted(
                available.values(),
                key=lambda provider: int(provider.get("display_priority") or 999),
            )
            selected = [dict(provider) for provider in fallback[:8]]

        def discover_provider(provider: dict[str, Any]) -> dict[str, Any]:
            discovered: dict[str, list[str]] = {"movies": [], "series": []}
            provider_id = str(provider["provider_id"])
            for endpoint, kind in (("movie", "movies"), ("tv", "series")):
                try:
                    payload = _tmdb_request(
                        f"discover/{endpoint}",
                        {
                            "watch_region": region,
                            "with_watch_providers": provider_id,
                            "with_watch_monetization_types": "flatrate|free|ads",
                            "sort_by": "popularity.desc",
                            "include_adult": "false",
                            "page": 1,
                        },
                        cache_ttl=600.0,
                    )
                except RuntimeError:
                    continue
                for result in payload.get("results", []):
                    if isinstance(result, dict) and result.get("id"):
                        tmdb_id = str(result["id"])
                        if tmdb_id not in discovered[kind]:
                            discovered[kind].append(tmdb_id)
            return discovered

        discovered_by_provider: dict[str, dict[str, Any]] = {}
        with ThreadPoolExecutor(max_workers=min(6, max(1, len(selected)))) as executor:
            futures = {
                executor.submit(discover_provider, provider): str(provider["provider_id"])
                for provider in selected
            }
            for future in as_completed(futures):
                provider_id = futures[future]
                try:
                    discovered_by_provider[provider_id] = future.result()
                except (RuntimeError, ValueError):
                    discovered_by_provider[provider_id] = {"movies": [], "series": []}

        all_ids_by_kind = {"movies": set(), "series": set()}
        for discovered in discovered_by_provider.values():
            for kind in all_ids_by_kind:
                all_ids_by_kind[kind].update(discovered.get(kind, []))
        local_items = self._streaming_local_items(all_ids_by_kind)

        providers: list[dict[str, Any]] = []
        for provider in selected:
            provider_id = str(provider["provider_id"])
            discovered = discovered_by_provider.get(
                provider_id, {"movies": [], "series": []}
            )
            items: list[dict[str, Any]] = []
            seen_local_keys: set[tuple[str, str]] = set()
            # Primero películas y luego series, manteniendo el orden de popularidad
            # devuelto por TMDB en cada tipo.
            for kind in ("movies", "series"):
                for tmdb_id in discovered.get(kind, []):
                    local_key = (kind, str(tmdb_id))
                    item = local_items.get(local_key)
                    if item is not None and local_key not in seen_local_keys:
                        items.append(item)
                        seen_local_keys.add(local_key)
                    if len(items) >= 15:
                        break
                if len(items) >= 15:
                    break
            if not items:
                continue
            providers.append(
                {
                    "id": provider_id,
                    "name": provider.get("display_name") or provider.get("provider_name"),
                    "logo": media_url(provider.get("logo_path"), "w92"),
                    "items": items,
                }
            )

        return {
            "configured": True,
            "region": region,
            "providers": providers,
            "message": (
                "No hay títulos locales con proveedor de streaming en España."
                if not providers
                else None
            ),
        }

    def _resolve_platform_provider_id(self, platform_name_or_id: str, region: str = TMDB_STREAMING_REGION) -> str | None:
        p_clean = clean_key(platform_name_or_id)
        if not p_clean:
            return None
        if platform_name_or_id.isdigit():
            return platform_name_or_id
        for label, aliases in TMDB_STREAMING_PROVIDER_ALIASES:
            if clean_key(label) == p_clean or any(clean_key(a) == p_clean or p_clean in clean_key(a) or clean_key(a) in p_clean for a in aliases):
                try:
                    providers = _tmdb_request("watch/providers/movie", {"watch_region": region}, cache_ttl=3600.0).get("results", [])
                    for p in providers:
                        p_name = clean_key(str(p.get("provider_name") or ""))
                        if any(clean_key(a) in p_name for a in aliases):
                            return str(p.get("provider_id"))
                except Exception:
                    pass
        return None

    def _platform_tmdb_ids(self, platform: str, region: str = TMDB_STREAMING_REGION) -> dict[str, set[str]]:
        provider_id = self._resolve_platform_provider_id(platform, region)
        if not provider_id:
            return {"movies": set(), "series": set()}
        discovered: dict[str, set[str]] = {"movies": set(), "series": set()}
        for endpoint, kind in (("movie", "movies"), ("tv", "series")):
            for page in range(1, 4):
                try:
                    payload = _tmdb_request(
                        f"discover/{endpoint}",
                        {
                            "watch_region": region,
                            "with_watch_providers": provider_id,
                            "with_watch_monetization_types": "flatrate|free|ads",
                            "sort_by": "popularity.desc",
                            "include_adult": "false",
                            "page": page,
                        },
                        cache_ttl=600.0,
                    )
                    for r in payload.get("results", []):
                        if r.get("id"):
                            discovered[kind].add(str(r["id"]))
                except Exception:
                    break
        return discovered

    def catalog(
        self,
        query: str = "",
        kind: str = "all",
        table: str = "",
        section: str = "recent",
        category: str = "",
        genre: str = "",
        year: str = "",
        quality: str = "",
        language: str = "",
        min_rating: float = 0.0,
        year_from: str = "",
        year_to: str = "",
        platform: str = "",
        limit: int = 60,
        offset: int = 0,
    ) -> dict[str, Any]:
        requested_limit = max(1, min(int(limit), 200))
        requested_offset = max(0, int(offset))
        valid_sections = {"all", "recent", "oldest", "updated", "rating", "title_asc", "title_desc", "random"}
        section = section if section in valid_sections else "recent"
        items: list[dict[str, Any]] = []
        total = 0
        remaining_offset = requested_offset
        saved_keys = self.library_keys()
        watched_keys = self.watched_keys()
        conn = self._get_connection()

        platform_tmdb: dict[str, set[str]] | None = None
        if platform:
            platform_tmdb = self._platform_tmdb_ids(platform)

        target_tables = [
            t for t in self._catalog_tables(table)
            if (kind == "all" or infer_kind(t, (self._rows.get(t) or [{}])[0]) == kind)
        ]

        if len(target_tables) > 1:
            all_candidates: list[dict[str, Any]] = []
            total = 0
            candidate_fetch_limit = requested_offset + requested_limit * 3

            for table_name in target_tables:
                table_kind = infer_kind(table_name, (self._rows.get(table_name) or [{}])[0])
                table_tmdb_ids = platform_tmdb.get(table_kind, set()) if platform_tmdb is not None else None

                rows = self._rows.get(table_name)
                if rows:
                    matches = [
                        (index, row)
                        for index, row in enumerate(rows)
                        if self._matches_catalog_filters(
                            row, query, category, genre, year, quality, language,
                            min_rating=float(min_rating or 0.0),
                            year_from=year_from, year_to=year_to,
                            tmdb_ids=table_tmdb_ids
                        )
                    ]
                    total += len(matches)
                    matches = self._sort_catalog_rows(matches, section)[:candidate_fetch_limit]
                    for index, row in matches:
                        summary = self._summary(table_name, index, row)
                        summary["record_id"] = None
                        summary["saved"] = self.is_saved_item(table_name, index, None, summary.get("tmdb_id"), summary.get("title"))
                        summary["watched"] = self.is_watched_item(table_name, index, None, summary.get("tmdb_id"), summary.get("title"))
                        all_candidates.append(summary)
                    continue

                if self.demo or table_name not in self._table_counts:
                    continue

                where, search_values = self._catalog_clause(
                    table_name, query, category, genre, year, quality, language,
                    min_rating=float(min_rating or 0.0),
                    year_from=year_from, year_to=year_to,
                    tmdb_ids=table_tmdb_ids
                )
                try:
                    table_total = int(
                        conn.execute(
                            f"SELECT COUNT(*) FROM {self._quote(table_name)}{where}",
                            search_values,
                        ).fetchone()[0]
                    )
                    total += table_total

                    try:
                        fetched = conn.execute(
                            f"SELECT rowid AS __catalog_rowid, * FROM "
                            f"{self._quote(table_name)}{where}"
                            f"{self._catalog_order(table_name, section)} LIMIT ?",
                            [*search_values, candidate_fetch_limit],
                        ).fetchall()
                    except sqlite3.DatabaseError:
                        fetched = conn.execute(
                            f"SELECT * FROM {self._quote(table_name)}{where} "
                            f"{self._catalog_order(table_name, section)} LIMIT ?",
                            [*search_values, candidate_fetch_limit],
                        ).fetchall()

                    for position, row in enumerate(fetched):
                        row_data = self._plain_row(row)
                        summary = self._summary(table_name, position, row_data)
                        record_id = row["__catalog_rowid"] if "__catalog_rowid" in row.keys() else None
                        rec_id_val = int(record_id) if record_id is not None else None
                        summary["record_id"] = rec_id_val
                        summary["saved"] = self.is_saved_item(table_name, position, rec_id_val, summary.get("tmdb_id"), summary.get("title"))
                        summary["watched"] = self.is_watched_item(table_name, position, rec_id_val, summary.get("tmdb_id"), summary.get("title"))
                        all_candidates.append(summary)
                except sqlite3.DatabaseError:
                    continue

            # Sort combined multi-table list according to section
            def item_year(item):
                try:
                    y = str(item.get("year") or "").strip()[:4]
                    return int(y) if y.isdigit() else 0
                except Exception:
                    return 0

            def item_rating(item):
                try:
                    r = item.get("rating")
                    return float(r) if r is not None else 0.0
                except Exception:
                    return 0.0

            if section in ("recent", "release_desc"):
                all_candidates.sort(key=lambda x: (item_year(x), x.get("record_id") or 0), reverse=True)
            elif section in ("oldest", "release_asc"):
                all_candidates.sort(key=lambda x: (item_year(x) if item_year(x) > 0 else 9999, x.get("record_id") or 0))
            elif section in ("updated", "catalog_desc"):
                all_candidates.sort(key=lambda x: x.get("record_id") or 0, reverse=True)
            elif section == "rating":
                all_candidates.sort(key=lambda x: item_rating(x), reverse=True)
            elif section in ("title_asc", "az"):
                all_candidates.sort(key=lambda x: str(x.get("title") or "").casefold())
            elif section in ("title_desc", "za"):
                all_candidates.sort(key=lambda x: str(x.get("title") or "").casefold(), reverse=True)
            elif section == "random":
                import random
                random.shuffle(all_candidates)

            items = all_candidates[requested_offset : requested_offset + requested_limit]
            return {
                "items": items,
                "total": total,
                "offset": requested_offset,
                "limit": requested_limit,
                "has_more": requested_offset + len(items) < total,
                "section": section,
                "filters": {
                    "query": query,
                    "kind": kind,
                    "section": section,
                    "category": category,
                    "genre": genre,
                    "year": year,
                    "quality": quality,
                    "language": language,
                    "min_rating": min_rating,
                    "year_from": year_from,
                    "year_to": year_to,
                    "platform": platform,
                },
            }

        for table_name in self._catalog_tables(table):
            table_kind = infer_kind(
                table_name, (self._rows.get(table_name) or [{}])[0]
            )
            if kind != "all" and table_kind != kind:
                continue

            table_tmdb_ids = None
            if platform_tmdb is not None:
                table_tmdb_ids = platform_tmdb.get(table_kind, set())

            rows = self._rows.get(table_name)
            if rows:
                matches = [
                    (index, row)
                    for index, row in enumerate(rows)
                    if self._matches_catalog_filters(
                        row, query, category, genre, year, quality, language,
                        min_rating=float(min_rating or 0.0),
                        year_from=year_from, year_to=year_to,
                        tmdb_ids=table_tmdb_ids
                    )
                ]
                matches = self._sort_catalog_rows(matches, section)
                table_total = len(matches)
                page_matches = matches[remaining_offset : remaining_offset + requested_limit]
                remaining_offset = max(0, remaining_offset - table_total)
                total += table_total
                for index, row in page_matches:
                    summary = self._summary(table_name, index, row)
                    summary["record_id"] = None
                    summary["saved"] = self.is_saved_item(table_name, index, None, summary.get("tmdb_id"), summary.get("title"))
                    summary["watched"] = self.is_watched_item(table_name, index, None, summary.get("tmdb_id"), summary.get("title"))
                    items.append(summary)
                continue

            if self.demo or table_name not in self._table_counts:
                continue
            where, search_values = self._catalog_clause(
                table_name, query, category, genre, year, quality, language,
                min_rating=float(min_rating or 0.0),
                year_from=year_from, year_to=year_to,
                tmdb_ids=table_tmdb_ids
            )
            try:
                table_total = int(
                    conn.execute(
                        f"SELECT COUNT(*) FROM {self._quote(table_name)}{where}",
                        search_values,
                    ).fetchone()[0]
                )
                total += table_total
                if remaining_offset >= table_total:
                    remaining_offset -= table_total
                    continue
                try:
                    fetched = conn.execute(
                        f"SELECT rowid AS __catalog_rowid, * FROM "
                        f"{self._quote(table_name)}{where}"
                        f"{self._catalog_order(table_name, section)} LIMIT ? OFFSET ?",
                        [*search_values, requested_limit, remaining_offset],
                    ).fetchall()
                except sqlite3.DatabaseError:
                    fetched = conn.execute(
                        f"SELECT rowid AS __catalog_rowid, * FROM {self._quote(table_name)}{where} "
                        f"{self._catalog_order(table_name, section)} "
                        "LIMIT ? OFFSET ?",
                        [*search_values, requested_limit, remaining_offset],
                    ).fetchall()
                start_index = remaining_offset
                remaining_offset = 0
                for position, row in enumerate(fetched):
                    row_data = self._plain_row(row)
                    summary = self._summary(
                        table_name,
                        start_index + position,
                        row_data,
                    )
                    record_id = row["__catalog_rowid"] if "__catalog_rowid" in row.keys() else None
                    rec_id_val = int(record_id) if record_id is not None else None
                    summary["record_id"] = rec_id_val
                    summary["saved"] = self.is_saved_item(
                        table_name,
                        start_index + position,
                        rec_id_val,
                        summary.get("tmdb_id"),
                        summary.get("title")
                    )
                    summary["watched"] = self.is_watched_item(
                        table_name,
                        start_index + position,
                        rec_id_val,
                        summary.get("tmdb_id"),
                        summary.get("title")
                    )
                    items.append(summary)
            except sqlite3.DatabaseError:
                continue

        return {
            "items": items[:requested_limit],
            "total": total,
            "offset": requested_offset,
            "limit": requested_limit,
            "has_more": requested_offset + len(items) < total,
            "section": section,
            "filters": {
                "query": query,
                "kind": kind,
                "category": category,
                "genre": genre,
                "platform": platform,
                "year": year,
                "year_from": year_from,
                "year_to": year_to,
                "min_rating": min_rating,
                "quality": quality,
                "language": language,
            },
        }
    def item(
        self,
        table: str,
        index: int,
        record_id: int | None = None,
        query: str = "",
    ) -> dict[str, Any] | None:
        row = self._row_at(table, index, record_id, query)
        if row is None:
            return None
        item_kind = infer_kind(table, row)
        tmdb = field_value(row, "tmdb_id")
        related = self._related_links(
            row,
            item_kind,
            field_value(row, "season"),
            field_value(row, "episode"),
        )
        watched_episodes = []
        if item_kind == "series":
            watched_episodes = self.get_watched_episodes(tmdb, table, record_id)
        actual_record_id = record_id if record_id is not None else row.get("__catalog_rowid")
        actual_record_id = safe_int(actual_record_id)
        is_saved = self.is_saved_item(table, index, actual_record_id, tmdb, field_value(row, "title"))
        is_watched = self.is_watched_item(table, index, actual_record_id, tmdb, field_value(row, "title"))
        summary_obj = self._summary(table, index, row)
        summary_obj["record_id"] = actual_record_id
        summary_obj["saved"] = is_saved
        summary_obj["watched"] = is_watched
        return {
            "table": table,
            "index": index,
            "record_id": actual_record_id,
            "kind": item_kind,
            "summary": summary_obj,
            "fields": [
                {
                    "key": key,
                    "label": label_for_field(key),
                    "value": format_genres(value) if clean_key(key) in {"genero", "generos", "genre", "genres"} else value,
                    "url": link_kind(value) == "url",
                }
                for key, value in row.items()
            ],
            "related": related,
            "watched_episodes": watched_episodes,
            "saved": is_saved,
            "watched": is_watched,
        }

    def resolve_alldebrid_for_item(
        self,
        table: str,
        index: int,
        record_id: int | None,
        query: str,
        number: int,
    ) -> dict[str, Any]:
        row = self._row_at(table, index, record_id, query)
        if row is None:
            raise RuntimeError("Registro no encontrado.")
        kind = infer_kind(table, row)
        entries = self._related_links(
            row,
            kind,
            field_value(row, "season"),
            field_value(row, "episode"),
        )
        if number < 1 or number > len(entries):
            raise RuntimeError("La fuente seleccionada ya no está disponible.")
        link = str(entries[number - 1].get("link") or "")
        return resolve_alldebrid(link)



_index_file = Path(__file__).resolve().parent / "index.html"
HTML = _index_file.read_text(encoding="utf-8", errors="ignore") if _index_file.is_file() else "<!DOCTYPE html><html><body><h1>FlixLink</h1></body></html>"



class CatalogHandler(BaseHTTPRequestHandler):
    store: CatalogStore

    def log_message(self, format: str, *args: Any) -> None:
        sys.stderr.write("[catalogo] " + (format % args) + "\n")

    def _send_cors_headers(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Authorization, X-Requested-With")

    def do_OPTIONS(self) -> None:
        self.send_response(HTTPStatus.OK)
        self._send_cors_headers()
        self.send_header("Content-Length", "0")
        self.end_headers()

    def _send_json(self, payload: Any, status: int = HTTPStatus.OK) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        try:
            self.send_response(status)
            self._send_cors_headers()
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            return

    def _send_html(self) -> None:
        candidates = [
            Path(__file__).resolve().parent / "templates" / "index.html",
            Path(__file__).resolve().parent / "index.html",
        ]
        html_bytes: bytes | None = None
        for candidate in candidates:
            if candidate.is_file():
                try:
                    html_bytes = candidate.read_bytes()
                    break
                except OSError:
                    pass

        if html_bytes is None:
            html_bytes = HTML.encode("utf-8")

        try:
            self.send_response(HTTPStatus.OK)
            self._send_cors_headers()
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(html_bytes)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(html_bytes)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            return

    def _handle_stream_proxy(self, params: dict[str, list[str]]) -> None:
        target_url = params.get("url", [""])[0]
        if not target_url or not is_url(target_url):
            self._send_json({"error": "URL inválida"}, HTTPStatus.BAD_REQUEST)
            return
        req_headers = {"User-Agent": BROWSER_USER_AGENT}
        if "Range" in self.headers:
            req_headers["Range"] = self.headers["Range"]
        try:
            upstream = requests.get(target_url, headers=req_headers, stream=True, timeout=15)
            self.send_response(upstream.status_code)
            self._send_cors_headers()
            for h in ["Content-Type", "Content-Range", "Content-Length", "Accept-Ranges"]:
                if h in upstream.headers:
                    self.send_header(h, upstream.headers[h])
            self.end_headers()
            for chunk in upstream.iter_content(chunk_size=65536):
                if chunk:
                    self.wfile.write(chunk)
        except Exception:
            return

    def _send_static_file(self, relative_path: str, content_type: str, extra_headers: dict[str, str] | None = None) -> None:
        target = (Path(__file__).resolve().parent / relative_path).resolve()
        script_dir = Path(__file__).resolve().parent
        if not str(target).startswith(str(script_dir)) or not target.is_file():
            self._send_json({"error": "Archivo no encontrado"}, HTTPStatus.NOT_FOUND)
            return
        try:
            data = target.read_bytes()
            self.send_response(HTTPStatus.OK)
            self._send_cors_headers()
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "public, max-age=86400")
            if extra_headers:
                for k, v in extra_headers.items():
                    self.send_header(k, v)
            self.end_headers()
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            return

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path in ("/", "/index.html"):
            self._send_html()
            return
        if parsed.path == "/manifest.json":
            self._send_static_file("manifest.json", "application/manifest+json; charset=utf-8")
            return
        if parsed.path == "/sw.js":
            self._send_static_file("sw.js", "application/javascript; charset=utf-8", extra_headers={"Service-Worker-Allowed": "/"})
            return
        if parsed.path in ("/favicon.ico", "/icons/favicon.ico"):
            self._send_static_file("icons/favicon.ico", "image/x-icon")
            return
        if parsed.path.startswith("/icons/"):
            rel = parsed.path.lstrip("/")
            ctype = "image/png"
            if rel.endswith(".svg"):
                ctype = "image/svg+xml"
            elif rel.endswith(".ico"):
                ctype = "image/x-icon"
            self._send_static_file(rel, ctype)
            return
        params = parse_qs(parsed.query)
        if parsed.path == "/api/proxy/stream":
            self._handle_stream_proxy(params)
            return
        try:
            routes = {
                "/api/status": self._handle_status,
                "/api/license/status": lambda p: get_account_info(),
                "/api/create-invite": self._handle_license_create_invite,
                "/api/license/create-invite": self._handle_license_create_invite,
                "/api/friends": self._handle_get_friends,
                "/api/alldebrid/status": lambda p: alldebrid_status(),
                "/api/alldebrid/pin/get": self._handle_alldebrid_pin_get,
                "/api/alldebrid/pin/check": self._handle_alldebrid_pin_check,
                "/api/app/check-update": lambda p: {"has_update": False, "version": "web"},
                "/api/trending": lambda p: self.store.trending(
                    p.get("kind", ["movies"])[0],
                    limit=int(p.get("limit", ["20"])[0])
                ) if self.store._db_ready else [],
                "/api/recommendations": self._handle_recommendations,
                "/api/catalog": self._handle_catalog,
                "/api/categories": lambda p: self.store.categories() if self.store._db_ready else {},
                "/api/streaming": self._handle_streaming,
                "/api/library": lambda p: {"items": self.store.library()},
                "/api/history": lambda p: {"items": self.store.history()},
                "/api/watched": lambda p: {"items": self.store.watched()},
                "/api/episodes/watched": self._handle_episodes_watched,
                "/api/random-smart": self._handle_random_smart,
                "/api/item": self._handle_item,
                "/api/item/fichier": self._handle_resolve_fichier,
                "/api/item/alldebrid": self._handle_resolve_alldebrid,
                "/api/resolve-alldebrid": self._handle_resolve_alldebrid,
                "/api/resolve-fichier": self._handle_resolve_fichier,
                "/api/refresh": self._handle_refresh,
                "/api/database/status": self._handle_database_status,
            }
            handler = routes.get(parsed.path)
            if handler is None:
                self._send_json({"error": "Ruta no encontrada"}, HTTPStatus.NOT_FOUND)
                return
            result = handler(params)
            if result is not None:
                self._send_json(result)
        except (ValueError, RuntimeError) as error:
            self._send_json({"error": str(error)}, HTTPStatus.BAD_REQUEST)

    def _handle_database_status(self, params: dict[str, list[str]]) -> dict[str, Any]:
        config = _read_config()
        hours = config.get("db_update_interval_hours", 12)
        return {
            "version": self.store.get_database_version(),
            "auto_update": self.store.auto_update,
            "update_interval_hours": hours,
            "update_state": self.store._update_state,
            "last_check_at": self.store._last_update_check_at,
            "last_updated_at": self.store._last_database_update_at,
            "error": self.store.update_error,
            "db_ready": self.store._db_ready,
        }

    def _handle_status(self, params: dict[str, list[str]]) -> dict[str, Any]:
        result = self.store.status()
        ad_key, _ = _alldebrid_key_info()
        tmdb_key, _ = _tmdb_key_info()
        result["alldebrid_configured"] = bool(ad_key)
        result["tmdb_configured"] = bool(tmdb_key)
        result["db_ready"] = self.store._db_ready
        result["license_status"] = check_remote_status()
        return result

    def _handle_get_friends(self, params: dict[str, list[str]]) -> list[dict[str, Any]]:
        session = get_local_session()
        if not session:
            return []
        safe_user = quote(session.get("username", ""))
        try:
            res_me = requests.get(f"{FIRESTORE_URL}/{safe_user}", timeout=4)
            if res_me.status_code != 200:
                return []
            friends_array = res_me.json().get("fields", {}).get("amigos", {}).get("arrayValue", {}).get("values", [])
            if not friends_array:
                return []

            friends_data = []
            now = int(time.time() * 1000)
            for f in friends_array:
                fname = f.get("stringValue")
                if not fname:
                    continue
                try:
                    f_res = requests.get(f"{FIRESTORE_URL}/{quote(fname)}", timeout=3)
                    if f_res.status_code == 200:
                        fields = f_res.json().get("fields", {})
                        f_team = fields.get("equipo_favorito", {}).get("stringValue", "")
                        f_watch = fields.get("viendo_ahora", {}).get("stringValue", "")
                        f_last = int(fields.get("ultima_conexion", {}).get("integerValue", 0))
                        is_online = (now - f_last) < 40000
                        friends_data.append({
                            "nick": fname,
                            "equipo": f_team,
                            "viendo": f_watch if is_online else "",
                            "online": is_online
                        })
                except Exception:
                    pass
            return friends_data
        except Exception:
            return []

    def _handle_license_create_invite(self, params: dict[str, list[str]]) -> dict[str, Any]:
        info = get_account_info()
        if not info.get("active"):
            raise RuntimeError("Licencia bloqueada o no activada.")
        if info.get("invites", 0) <= 0:
            raise RuntimeError("Has agotado tus invitaciones disponibles.")

        username = info.get("username", "Usuario")
        safe_user = quote(username)
        exp_time_ms = int(time.time() * 1000) + 600000
        new_code = _licenser.create_invite(username)

        try:
            patch_url = f"{FIRESTORE_URL}/{safe_user}?updateMask.fieldPaths=codigo_activo&updateMask.fieldPaths=expiracion_codigo"
            patch_body = {
                "fields": {
                    "codigo_activo": {"stringValue": new_code},
                    "expiracion_codigo": {"integerValue": exp_time_ms}
                }
            }
            requests.patch(patch_url, json=patch_body, timeout=5)
        except Exception:
            pass

        return {"invite_code": new_code, "remaining": info.get("invites", 0), "exp": exp_time_ms}

    def _handle_episodes_watched(self, params: dict[str, list[str]]) -> dict[str, Any]:
        tmdb = params.get("tmdb", [None])[0]
        table = params.get("table", [None])[0]
        record_id = params.get("record_id", [None])[0]
        rec_id = int(record_id) if record_id not in (None, "", "null") else None
        return {"items": self.store.get_watched_episodes(tmdb, table, rec_id)}

    def _handle_random_smart(self, params: dict[str, list[str]]) -> dict[str, Any] | None:
        kind = params.get("kind", ["all"])[0]
        genre = params.get("genre", [""])[0]
        era = params.get("era", ["all"])[0]
        min_rating = float(params.get("min_rating", ["0"])[0])
        exclude_watched = params.get("exclude_watched", ["1"])[0] == "1"
        return self.store.random_smart(kind, genre, era, min_rating, exclude_watched)

    def _handle_catalog(self, params: dict[str, list[str]]) -> dict[str, Any]:
        return self.store.catalog(
            query=params.get("q", [""])[0],
            kind=params.get("kind", params.get("type", ["all"]))[0],
            table=params.get("table", [""])[0],
            section=params.get("section", params.get("sort", ["recent"]))[0],
            category=params.get("category", [""])[0],
            genre=params.get("genre", [""])[0],
            year=params.get("year", [""])[0],
            year_from=params.get("year_from", [""])[0],
            year_to=params.get("year_to", [""])[0],
            min_rating=float(params.get("min_rating", ["0"])[0] or 0),
            platform=params.get("platform", [""])[0],
            quality=params.get("quality", [""])[0],
            language=params.get("language", [""])[0],
            limit=int(params.get("limit", ["60"])[0]),
            offset=int(params.get("offset", ["0"])[0]),
        )

    def _handle_streaming(self, params: dict[str, list[str]]) -> dict[str, Any]:
        region = (params.get("region", [TMDB_STREAMING_REGION])[0] or TMDB_STREAMING_REGION).upper()
        if not re.fullmatch(r"[A-Z]{2}", region):
            region = TMDB_STREAMING_REGION
        return self.store.streaming_platforms(region)

    def _handle_recommendations(self, params: dict[str, list[str]]) -> dict[str, Any]:
        return self.store.recommendations(
            limit=int(params.get("limit", ["8"])[0]),
            offset=int(params.get("offset", ["0"])[0]),
            kind=params.get("kind", ["all"])[0],
        )

    def _handle_item(self, params: dict[str, list[str]]) -> dict[str, Any] | None:
        table = params.get("table", [""])[0]
        index = safe_int(params.get("index", ["-1"])[0]) if safe_int(params.get("index", ["-1"])[0]) is not None else -1
        record_id = safe_int(params.get("record_id", [None])[0])
        item = self.store.item(
            table,
            index,
            record_id,
            params.get("q", [""])[0],
        )
        if item is None:
            self._send_json({"error": "Registro no encontrado"}, HTTPStatus.NOT_FOUND)
            return None
        return item

    def _handle_resolve_fichier(self, params: dict[str, list[str]]) -> dict[str, Any]:
        table = params.get("table", [""])[0]
        index = safe_int(params.get("index", ["-1"])[0]) or 0
        number = safe_int(params.get("number", ["0"])[0]) or 0
        record_id = safe_int(params.get("record_id", [None])[0])
        return self.store.resolve_fichier_for_item(
            table,
            index,
            record_id,
            params.get("q", [""])[0],
            number,
        )

    def _handle_resolve_alldebrid(self, params: dict[str, list[str]]) -> dict[str, Any]:
        table = params.get("table", [""])[0]
        index = safe_int(params.get("index", ["-1"])[0]) or 0
        number = safe_int(params.get("number", ["0"])[0]) or 0
        record_id = safe_int(params.get("record_id", [None])[0])
        return self.store.resolve_alldebrid_for_item(
            table,
            index,
            record_id,
            params.get("q", [""])[0],
            number,
        )

    def _handle_refresh(self, params: dict[str, list[str]]) -> dict[str, Any]:
        self.store.refresh()
        return self.store.status()

    def _handle_alldebrid_pin_get(self, params: dict[str, list[str]]) -> dict[str, Any]:
        try:
            r = requests.get(f"{ALLDEBRID_API_URL}/pin/get?agent={ALLDEBRID_AGENT}", timeout=5)
            if r.status_code == 200:
                data = r.json().get("data", {})
                pin = data.get("pin", "")
                check = data.get("check", "")
                user_url = data.get("user_url") or f"https://alldebrid.es/pin?pin={pin}"
                return {
                    "status": "success",
                    "pin": pin,
                    "check": check,
                    "user_url": user_url,
                    "base_url": "https://alldebrid.es/pin"
                }
        except Exception as e:
            sys.stderr.write(f"[catalogo] Error en AllDebrid PIN get: {e}\n")
        return {"status": "error", "error": "No se pudo generar el código PIN de AllDebrid"}

    def _handle_alldebrid_pin_check(self, params: dict[str, list[str]]) -> dict[str, Any]:
        pin = params.get("pin", [""])[0]
        check = params.get("check", [""])[0]
        if not pin or not check:
            return {"status": "error", "error": "Faltan parámetros pin y check"}
        try:
            r = requests.get(f"{ALLDEBRID_API_URL}/pin/check?check={check}&pin={pin}&agent={ALLDEBRID_AGENT}", timeout=5)
            if r.status_code == 200:
                data = r.json().get("data", {})
                if data.get("activated"):
                    apikey = data.get("apikey", "")
                    if apikey:
                        _write_config(alldebrid_key=apikey)
                        sys.stderr.write("[catalogo] AllDebrid vinculado exitosamente vía PIN!\n")
                        return {"status": "success", "activated": True, "apikey": apikey}
                return {"status": "success", "activated": False, "expires_in": data.get("expires_in", 0)}
        except Exception as e:
            sys.stderr.write(f"[catalogo] Error en AllDebrid PIN check: {e}\n")
        return {"status": "error", "error": "Error al verificar PIN de AllDebrid"}

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        valid_paths = {
            "/api/login", "/api/register", "/api/logout",
            "/api/friends/add", "/api/status/update",
            "/api/alldebrid/config", "/api/database/check", "/api/database/update", "/api/database/config",
            "/api/library/add", "/api/library/remove",
            "/api/history/add", "/api/history/remove", "/api/history/clear", "/api/watched/toggle",
            "/api/episodes/toggle", "/api/episodes/toggle-all"
        }
        if parsed.path not in valid_paths:
            self._send_json({"error": "Ruta no encontrada"}, HTTPStatus.NOT_FOUND)
            return
        try:
            length = int(self.headers.get("Content-Length", "0"))
            if length > 32_768:
                raise RuntimeError("La petición es demasiado grande.")
            raw_body = self.rfile.read(max(0, length)).decode("utf-8")
            params = parse_qs(raw_body, keep_blank_values=True)

            if parsed.path == "/api/login":
                user = ""
                pwd = ""
                try:
                    data = json.loads(raw_body)
                    user = data.get("user", "").strip()
                    pwd = data.get("pass", "").strip()
                except Exception:
                    user = params.get("user", [""])[0].strip()
                    pwd = params.get("pass", [""])[0].strip()
                if not user or not pwd:
                    sys.stderr.write("[catalogo] [LOGIN] Rechazado: faltan datos de usuario o contraseña.\n")
                    self._send_json({"success": False, "error": "Faltan datos de usuario y contraseña."}, HTTPStatus.BAD_REQUEST)
                    return
                try:
                    canonical_user, doc = get_firestore_user(user)
                    if doc is None:
                        sys.stderr.write(f"[catalogo] [LOGIN] Usuario '{user}' no existe en Firestore.\n")
                        self._send_json({"success": False, "error": "El usuario no existe."}, HTTPStatus.BAD_REQUEST)
                        return
                    remote_hash = doc.get("fields", {}).get("password_hash", {}).get("stringValue", "")
                    estado = doc.get("fields", {}).get("estado", {}).get("stringValue", "")
                    local_hash = OfflineSecurityCore.hash_password(pwd)
                    if remote_hash != local_hash:
                        sys.stderr.write(f"[catalogo] [LOGIN] Contraseña incorrecta para '{canonical_user}'.\n")
                        self._send_json({"success": False, "error": "Contraseña incorrecta."}, HTTPStatus.BAD_REQUEST)
                        return
                    if estado == "BLOQUEADO":
                        sys.stderr.write(f"[catalogo] [LOGIN] Cuenta bloqueada para '{canonical_user}'.\n")
                        self._send_json({"success": False, "error": "Tu cuenta está bloqueada."}, HTTPStatus.FORBIDDEN)
                        return
                    vault_data = {"username": canonical_user, "hash": local_hash, "status": "ACTIVE"}
                    with open(VAULT_PATH, "w", encoding="utf-8") as f:
                        json.dump(vault_data, f)

                    sys.stderr.write(f"[catalogo] [LOGIN] ¡Usuario '{canonical_user}' autenticado correctamente!\n")
                    self.store.ensure_database_ready(async_download=True)
                    self._send_json({"success": True})
                except Exception as ex:
                    sys.stderr.write(f"[catalogo] [LOGIN] Error de conexión: {ex}\n")
                    self._send_json({"success": False, "error": f"Error de conexión: {ex}"}, HTTPStatus.INTERNAL_SERVER_ERROR)
                return

            if parsed.path == "/api/register":
                user = ""
                pwd = ""
                invite = ""
                try:
                    data = json.loads(raw_body)
                    user = data.get("user", "").strip()
                    pwd = data.get("pass", "").strip()
                    invite = data.get("invite", "").strip()
                except Exception:
                    user = params.get("user", [""])[0].strip()
                    pwd = params.get("pass", [""])[0].strip()
                    invite = params.get("invite", [""])[0].strip()
                if not user or not pwd or not invite:
                    self._send_json({"success": False, "error": "Faltan datos para el registro."}, HTTPStatus.BAD_REQUEST)
                    return
                try:
                    res_global = requests.get(f"{FIRESTORE_URL}/GLOBAL_CONFIG", timeout=3)
                    if res_global.status_code == 200:
                        if res_global.json().get("fields", {}).get("modo_mantenimiento", {}).get("booleanValue", False):
                            self._send_json({"success": False, "error": "La app está en mantenimiento."}, HTTPStatus.FORBIDDEN)
                            return
                except Exception:
                    pass
                pwd_hash = OfflineSecurityCore.hash_password(pwd)
                success, msg = _licenser.verify_and_register(invite, user, pwd_hash)
                if success:
                    self.store.ensure_database_ready(async_download=True)
                    self._send_json({"success": True})
                else:
                    self._send_json({"success": False, "error": msg}, HTTPStatus.BAD_REQUEST)
                return

            if parsed.path == "/api/logout":
                if os.path.exists(VAULT_PATH):
                    try:
                        os.remove(VAULT_PATH)
                    except Exception:
                        pass
                self._send_json({"success": True})
                return

            if parsed.path == "/api/status/update":
                session = get_local_session()
                if not session:
                    self._send_json({"success": False})
                    return
                safe_user = quote(session.get("username", ""))
                watching = "Explorando FlixLink"
                try:
                    data = json.loads(raw_body)
                    watching = data.get("watching", data.get("viendo_ahora", "Explorando FlixLink"))
                except Exception:
                    watching = params.get("watching", ["Explorando FlixLink"])[0]
                body = {
                    "fields": {
                        "ultima_conexion": {"integerValue": int(time.time() * 1000)},
                        "viendo_ahora": {"stringValue": watching}
                    }
                }
                url = f"{FIRESTORE_URL}/{safe_user}?updateMask.fieldPaths=ultima_conexion&updateMask.fieldPaths=viendo_ahora"
                try:
                    requests.patch(url, json=body, timeout=3)
                except Exception:
                    pass
                self._send_json({"success": True})
                return

            if parsed.path == "/api/friends/add":
                session = get_local_session()
                if not session:
                    self._send_json({"error": "No has iniciado sesión."}, HTTPStatus.UNAUTHORIZED)
                    return
                safe_user = quote(session.get("username", ""))
                new_friend = ""
                try:
                    data = json.loads(raw_body)
                    new_friend = data.get("nick", "").strip()
                except Exception:
                    new_friend = params.get("nick", [""])[0].strip()
                if not new_friend or new_friend.lower() == session.get("username", "").lower():
                    self._send_json({"error": "Nick no válido."}, HTTPStatus.BAD_REQUEST)
                    return
                try:
                    res_check = requests.get(f"{FIRESTORE_URL}/{quote(new_friend)}", timeout=3)
                    if res_check.status_code != 200:
                        self._send_json({"error": "El usuario no existe."}, HTTPStatus.BAD_REQUEST)
                        return
                    res_me = requests.get(f"{FIRESTORE_URL}/{safe_user}", timeout=3)
                    me_doc = res_me.json()
                    friends_array = me_doc.get("fields", {}).get("amigos", {}).get("arrayValue", {}).get("values", [])
                    if friends_array is None:
                        friends_array = []
                    if any(f.get("stringValue", "").lower() == new_friend.lower() for f in friends_array):
                        self._send_json({"error": "Ya tienes a este usuario en tu lista."}, HTTPStatus.BAD_REQUEST)
                        return
                    friends_array.append({"stringValue": new_friend})
                    body = {"fields": {"amigos": {"arrayValue": {"values": friends_array}}}}
                    url = f"{FIRESTORE_URL}/{safe_user}?updateMask.fieldPaths=amigos"
                    requests.patch(url, json=body, timeout=3)
                    self._send_json({"success": True})
                except Exception:
                    self._send_json({"error": "Error de conexión."}, HTTPStatus.INTERNAL_SERVER_ERROR)
                return

            if parsed.path == "/api/database/check":
                now_iso = datetime.now().astimezone().isoformat(timespec="seconds")
                self.store._last_update_check_at = now_iso
                res = self.store.check_remote_version()
                if isinstance(res, dict):
                    res["last_check_at"] = now_iso
                self._send_json(res)
                return
            if parsed.path == "/api/database/update":
                self.store.refresh()
                self._send_json({
                    "status": "ok",
                    "version": self.store.get_database_version(),
                    "message": "Base de datos actualizada con éxito.",
                })
                return
            if parsed.path == "/api/database/config":
                raw_hours = params.get("db_update_interval_hours", ["12"])[0]
                try:
                    hours = int(raw_hours)
                except ValueError:
                    hours = 12
                _write_config(db_update_interval_hours=hours)
                self.store.set_update_interval_hours(hours)
                self._send_json({
                    "status": "ok",
                    "db_update_interval_hours": hours,
                    "auto_update": hours > 0,
                })
                return
            if parsed.path == "/api/library/add":
                table = params.get("table", [""])[0]
                index = safe_int(params.get("index", ["-1"])[0]) or 0
                record_id = safe_int(params.get("record_id", [None])[0])
                self._send_json(
                    self.store.add_to_library(
                        table,
                        index,
                        record_id,
                        params.get("q", [""])[0],
                    )
                )
                return
            if parsed.path == "/api/library/remove":
                table = params.get("table", [""])[0]
                index = safe_int(params.get("index", ["-1"])[0]) or 0
                record_id = safe_int(params.get("record_id", [None])[0])
                self._send_json(
                    self.store.remove_from_library(
                        table,
                        index,
                        record_id,
                    )
                )
                return
            if parsed.path == "/api/history/add":
                table = params.get("table", [""])[0]
                index = safe_int(params.get("index", ["-1"])[0]) or 0
                record_id = safe_int(params.get("record_id", [None])[0])
                season = params.get("season", [None])[0]
                episode = params.get("episode", [None])[0]
                self._send_json(
                    self.store.add_to_history(
                        table,
                        index,
                        record_id,
                        season,
                        episode,
                    )
                )
                return
            if parsed.path == "/api/history/remove":
                table = params.get("table", [""])[0]
                index = safe_int(params.get("index", ["-1"])[0]) or 0
                record_id = safe_int(params.get("record_id", [None])[0])
                self._send_json(
                    self.store.remove_from_history(
                        table,
                        index,
                        record_id,
                    )
                )
                return
            if parsed.path == "/api/history/clear":
                self._send_json(self.store.clear_history())
                return
            if parsed.path == "/api/watched/toggle":
                table = params.get("table", [""])[0]
                index = safe_int(params.get("index", ["-1"])[0]) or 0
                record_id = safe_int(params.get("record_id", [None])[0])
                watched = params.get("watched", ["1"])[0] == "1"
                self._send_json(
                    self.store.set_watched(
                        table,
                        index,
                        record_id,
                        watched,
                    )
                )
                return
            if parsed.path == "/api/episodes/toggle":
                tmdb = params.get("tmdb", [None])[0]
                table = params.get("table", [None])[0]
                record_id = safe_int(params.get("record_id", [None])[0])
                season = params.get("season", [None])[0]
                episode = params.get("episode", [None])[0]
                watched = params.get("watched", ["1"])[0] == "1"
                self._send_json(
                    self.store.toggle_episode_watched(
                        tmdb=tmdb if tmdb else None,
                        table=table if table else None,
                        record_id=record_id,
                        season=season,
                        episode=episode,
                        watched=watched,
                    )
                )
                return
            if parsed.path == "/api/episodes/toggle-all":
                tmdb = params.get("tmdb", [None])[0]
                table = params.get("table", [None])[0]
                record_id = params.get("record_id", [None])[0]
                watched = params.get("watched", ["1"])[0] == "1"
                episodes_raw = params.get("episodes", ["[]"])[0]
                try:
                    episodes = json.loads(episodes_raw)
                except Exception:
                    episodes = []
                rec_id = int(record_id) if record_id not in (None, "", "null") else None
                self._send_json(
                    self.store.toggle_all_episodes_watched(
                        tmdb=tmdb if tmdb else None,
                        table=table if table else None,
                        record_id=rec_id,
                        episodes=episodes,
                        watched=watched
                    )
                )
                return

            _write_config(
                alldebrid_key=params.get("api_key", [None])[0],
                tmdb_key=params.get("tmdb_key", [None])[0],
            )
            self._send_json(alldebrid_status())
        except (ValueError, RuntimeError, UnicodeDecodeError) as error:
            self._send_json({"error": str(error)}, HTTPStatus.BAD_REQUEST)


def make_server(host: str, port: int, store: CatalogStore) -> ThreadingHTTPServer:
    CatalogHandler.store = store
    return ThreadingHTTPServer((host, port), CatalogHandler)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Catálogo web de solo lectura para bases SQLite de addons de vídeo.",
    )
    parser.add_argument(
        "--db",
        dest="db_path",
        help="Ruta al archivo moria.cm3 o .db (opcional, se detecta automáticamente).",
    )
    parser.add_argument(
        "--kodi-home",
        dest="kodi_home",
        help="Ruta base de Kodi para buscar bases de datos y tokens de 1fichier.",
    )
    parser.add_argument(
        "--port",
        type=int,
        default=DEFAULT_PORT,
        help=f"Puerto HTTP del servidor local (por defecto: {DEFAULT_PORT}).",
    )
    parser.add_argument(
        "--host",
        default="0.0.0.0",
        help="Host al que vincular el servidor (por defecto: 0.0.0.0 para acceso en red local y TV Box).",
    )
    parser.add_argument(
        "--no-browser",
        action="store_true",
        help="No abrir automáticamente el navegador.",
    )
    parser.add_argument(
        "--no-update",
        action="store_true",
        help="Desactiva la comprobación y descarga automática periódica de moria.cm3.",
    )
    parser.add_argument(
        "--update-interval",
        type=float,
        default=DEFAULT_UPDATE_INTERVAL_SECONDS,
        help=(
            "Intervalo en segundos para consultar nuevas versiones de moria.cm3 "
            f"(por defecto: {int(DEFAULT_UPDATE_INTERVAL_SECONDS)}s)."
        ),
    )
    args = parser.parse_args()

    try:
        store = CatalogStore(
            db_path=args.db_path,
            kodi_home=args.kodi_home,
            auto_update=not args.no_update,
            update_interval=args.update_interval,
        )
    except MoriaDownloadError as error:
        sys.stderr.write(f"[catalogo] Error descargando base de datos: {error}\n")
        sys.exit(1)
    except FileNotFoundError as error:
        sys.stderr.write(f"[catalogo] {error}\n")
        sys.exit(1)

    server = make_server(args.host, args.port, store)
    url = f"http://localhost:{args.port}/"
    print(f"[catalogo] Servidor iniciado en {url}")
    print(f"[catalogo] Accesible en red local: http://{args.host}:{args.port}/")

    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[catalogo] Servidor detenido por el usuario.")
    finally:
        store.stop_background_updates()
        server.server_close()


if __name__ == "__main__":
    main()
