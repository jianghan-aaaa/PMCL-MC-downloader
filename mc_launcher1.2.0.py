#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MC 启动器 —— 从社区镜像(BMCLAPI)拉取 Minecraft 版本，可选组件下载，装模组加载器，下 Modrinth 模组，离线启动。

特点
  * 纯标准库实现，不需要 pip 安装任何东西
  * 本地网页界面（http://127.0.0.1:端口），双击 启动.bat 即可
  * 镜像：BMCLAPI 国内镜像（默认）/ Mojang 官方源，逐个 URL 自动回退
  * 选择性下载：客户端核心 / 依赖库 / 资源文件 / 日志配置，可跳过音效
  * 断点友好：已存在且大小一致的文件直接跳过；下载失败自动重试并换源
  * 多线程并发 + 实时进度/速度/剩余时间
  * 模组加载器：Fabric / Quilt / Legacy Fabric（元数据安装）、Forge / NeoForge（官方 installer 安装）
  * 模组：Modrinth 搜索 + 一键下载到 .minecraft/mods，自动补装必需前置
  * 目录布局与 HMCL / 官方启动器一致：mods、saves、resourcepacks 都在 .minecraft 下，
    本启动器下的东西可以直接给 HMCL 用（想每版本隔离就开 version_isolation）
  * 离线启动（离线用户名 + 离线 UUID），自动挑选匹配的 Java

命令行
  python mc_launcher.py                     # 启动网页界面（默认）
  python mc_launcher.py --selftest          # 自检：镜像连通性 + Java 检测
  python mc_launcher.py --list              # 列出全部版本
  python mc_launcher.py --download 1.20.1 --only client,libraries
  python mc_launcher.py --print-cmd 1.20.1  # 只打印启动命令，不启动游戏
  python mc_launcher.py --loaders 1.20.1    # 查看该版本可用的加载器
  python mc_launcher.py --install-loader 1.20.1 fabric
  python mc_launcher.py --install-java 17       # 下载 Adoptium JDK 17 到 java/ 下
  python mc_launcher.py --search-mod sodium --vid fabric-loader-0.16.9-1.20.1
  python mc_launcher.py --install-mod sodium --vid fabric-loader-0.16.9-1.20.1

目录结构（全部在脚本所在文件夹内，绿色免安装）
  mc_launcher.py
  launcher.json            配置文件
  .minecraft/versions/<id>/<id>.json|.jar
  .minecraft/libraries/...
  .minecraft/assets/indexes|objects/...
  .minecraft/natives/<id>/...
  .minecraft/mods|saves|resourcepacks/...            默认与 HMCL 共用（version_isolation=false）
  .minecraft/instances/<id>/mods|saves|...           开了版本隔离才用
  logs/latest.log          游戏输出
  cache/                   安装器 jar 缓存
"""

from __future__ import annotations

import atexit
import hashlib
import json
import os
import platform
import re
import shutil
import socket
import subprocess
import sys
import tarfile
import threading
import time
import uuid
import webbrowser
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, urlencode, urlparse
from urllib.request import Request, urlopen

# --------------------------------------------------------------------------- #
# 基础配置
# --------------------------------------------------------------------------- #

APP_NAME = "PMCL-MC-downloader"
APP_VER = "1.1.0"
BASE_DIR = Path(__file__).resolve().parent
GAME_DIR = BASE_DIR / ".minecraft"
VERSIONS_DIR = GAME_DIR / "versions"
LIBRARIES_DIR = GAME_DIR / "libraries"
ASSETS_DIR = GAME_DIR / "assets"
NATIVES_DIR = GAME_DIR / "natives"
INSTANCES_DIR = GAME_DIR / "instances"
JAVA_DIR = BASE_DIR / "java"
CACHE_DIR = BASE_DIR / "cache"
LOG_DIR = BASE_DIR / "logs"
CONFIG_FILE = BASE_DIR / "launcher.json"
AUTH_INJECTOR_JAR = BASE_DIR / "authlib-injector.jar"

# ---- frp 内网穿透（一键开服） ----
FRP_DIR = BASE_DIR / "frp"
FRP_EXE = FRP_DIR / "frpc.exe"
FRP_CONF = FRP_DIR / "frpc.toml"
FRP_VER_API = "https://api.github.com/repos/fatedier/frp/releases/latest"
FRP_MIRRORS = ["https://ghfast.top/", "https://ghproxy.net/"]

# ---- 陶瓦联机（Terracotta，基于 EasyTier 的 P2P 联机） ----
# 版本与哈希来自 HMCL 官方维护的 terracotta.json（github.com/HMCL-dev/HMCL）
TERRACOTTA_DIR = BASE_DIR / "terracotta"
TERRACOTTA_VER = "0.4.2"
TERRACOTTA_CLASSIFIER = "windows-x86_64"
TERRACOTTA_EXE = TERRACOTTA_DIR / f"terracotta-{TERRACOTTA_VER}-{TERRACOTTA_CLASSIFIER}.exe"
TERRACOTTA_PKG_NAME = f"terracotta-{TERRACOTTA_VER}-{TERRACOTTA_CLASSIFIER}-pkg.tar.gz"
TERRACOTTA_URLS = [
    f"https://gitee.com/burningtnt/Terracotta/releases/download/v{TERRACOTTA_VER}/{TERRACOTTA_PKG_NAME}",
    f"https://cnb.cool/HMCL-Terracotta/Terracotta/-/releases/download/v{TERRACOTTA_VER}/{TERRACOTTA_PKG_NAME}",
    f"https://alist.8mi.tech/d/mirror/HMCL-Terracotta/Auto/v{TERRACOTTA_VER}/{TERRACOTTA_PKG_NAME}",
    f"https://github.com/burningtnt/Terracotta/releases/download/v{TERRACOTTA_VER}/{TERRACOTTA_PKG_NAME}",
]
# windows-x86_64 包内文件 SHA-512
TERRACOTTA_FILES = {
    "VCRUNTIME140.DLL": "3d4b24061f72c0e957c7b04a0c4098c94c8f1afb4a7e159850b9939c7210d73398be6f27b5ab85073b4e8c999816e7804fef0f6115c39cd061f4aaeb4dcda8cf",
    f"terracotta-{TERRACOTTA_VER}-{TERRACOTTA_CLASSIFIER}.exe":
        "6e98d1f2380ed22fb5a2dd4aafce6c773e9cf69100c8bb8e49e7d6983756bdb9a31f80e06bcfbe5a2742144fe806d3d687dec54d8f09d87c659341f99dd9fd80",
}

ADOPTIUM_API = "https://api.adoptium.net/v3"

UA = "MCLauncher/1.1 (Windows; local launcher)"
HDRS = {"User-Agent": UA, "Accept": "*/*"}

MIRRORS = {
    "bmcl": {"label": "BMCLAPI 国内镜像", "base": "https://bmclapi2.bangbang93.com"},
    "mojang": {"label": "Mojang 官方源", "base": ""},
}
OFFICIAL_MANIFEST = "https://piston-meta.mojang.com/mc/game/version_manifest_v2.json"

FABRIC_META = "https://meta.fabricmc.net/v2"
QUILT_META = "https://meta.quiltmc.org/v3"
FORGE_PROMO = "https://files.minecraftforge.net/net/minecraftforge/forge/promotions_slim.json"
FORGE_MAVEN = "https://maven.minecraftforge.net/net/minecraftforge/forge"
MODRINTH_API = "https://api.modrinth.com/v2"

TYPE_LABEL = {
    "release": "正式版",
    "snapshot": "快照",
    "old_beta": "远古 Beta",
    "old_alpha": "远古 Alpha",
}

LOADERS = {
    "fabric": {
        "label": "Fabric", "kind": "meta", "modrinth": "fabric",
        "meta": "https://meta.fabricmc.net/v2",
        "note": "轻量、更新快，现代模组主流",
    },
    "quilt": {
        "label": "Quilt", "kind": "meta", "modrinth": "quilt",
        "meta": "https://meta.quiltmc.org/v3",
        "note": "Fabric 的衍生版，兼容大部分 Fabric 模组",
    },
    "legacyfabric": {
        "label": "Legacy Fabric", "kind": "meta", "modrinth": "fabric",
        "meta": "https://meta.legacyfabric.net/v2",
        "note": "给 1.13 及更早版本的 Fabric",
    },
    "forge": {
        "label": "Forge", "kind": "installer", "modrinth": "forge",
        "note": "老牌加载器，1.12.2 生态最大",
    },
    "neoforge": {
        "label": "NeoForge", "kind": "installer", "modrinth": "neoforge",
        "note": "Forge 分叉，1.20.2 之后的社区主流",
    },
}
LOADER_LABEL = {k: v["label"] for k, v in LOADERS.items()}
# 走模块化启动的加载器：classpath 里不能再放原版 jar，否则模块撞包
MODULE_LOADERS = ("forge", "neoforge")   # 老版 Forge/NeoForge 走模块化启动（-p + BootstrapLauncher）

DEFAULT_CONFIG = {
    "mirror": "bmcl",
    "username": "Steve",
    "memory": 2048,
    "java": "",
    "workers": 16,
    "verify_sha1": False,
    "mod_mirror": "",
    "version_isolation": False,   # False = 用 .minecraft/mods 通用布局
    "servers": [],                # 联机服务器列表，每项 {name,address,port,authlib,note}
    "frp": {                      # frp 内网穿透配置
        "server": "", "port": 7000, "token": "",
        "local_port": 25565, "remote_port": 0,   # remote_port=0 表示与本地端口相同
    },
}

# authlib-injector（第三方登录/外置登录）：
# 直链版本号会变，先查 GitHub API 拿最新 release 的 jar 直链，再用这些镜像前缀做加速回退
AUTH_INJECTOR_API = "https://api.github.com/repos/yushijinhun/authlib-injector/releases/latest"
AUTH_INJECTOR_MIRRORS = [
    "https://ghfast.top/",
    "https://ghproxy.net/",
]


def human_size(n) -> str:
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024.0
    return f"{n:.1f} TB"


def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def instance_dir(vid: str) -> Path:
    """游戏工作目录（存档 / options.txt / mods 的父目录）。

    默认就是 .minecraft，跟官方启动器、HMCL 的通用布局一致；
    把 launcher.json 里的 version_isolation 改成 true 才会按版本隔离到 instances/<版本>/。
    """
    if load_config().get("version_isolation"):
        return INSTANCES_DIR / vid
    return GAME_DIR


def mods_dir(vid: str) -> Path:
    return instance_dir(vid) / "mods"


# --------------------------------------------------------------------------- #
# 网络层
# --------------------------------------------------------------------------- #

class FetchError(RuntimeError):
    pass


def fetch_bytes(urls, timeout=45, retries=2):
    """按候选 URL 顺序尝试，任何一个成功即返回 (bytes, 最终 url)。"""
    if isinstance(urls, str):
        urls = [urls]
    last = None
    for url in urls:
        if not url:
            continue
        for attempt in range(retries + 1):
            try:
                with urlopen(Request(url, headers=HDRS), timeout=timeout) as resp:
                    return resp.read(), url
            except Exception as exc:  # noqa: BLE001
                last = exc
                if attempt < retries:
                    time.sleep(0.5 * (attempt + 1))
    raise FetchError(f"请求失败 {urls[0]} -> {last}")


def fetch_json(urls, timeout=45, retries=2):
    data, _ = fetch_bytes(urls, timeout=timeout, retries=retries)
    return json.loads(data.decode("utf-8"))


# --------------------------------------------------------------------------- #
# 镜像 / URL 构造
# --------------------------------------------------------------------------- #

def mirror_base(key: str) -> str:
    return MIRRORS.get(key, MIRRORS["bmcl"])["base"].rstrip("/")


def url_manifest(mirror: str):
    base = mirror_base(mirror)
    if not base:
        return [OFFICIAL_MANIFEST]
    return [f"{base}/mc/game/version_manifest.json", OFFICIAL_MANIFEST]


def url_version_json(mirror: str, vid: str, official: str = ""):
    base = mirror_base(mirror)
    out = []
    if base:
        out.append(f"{base}/version/{vid}/json")
    if official:
        out.append(official)
    elif base:
        out.append(f"{base}/version/{vid}/json")
    return out


def url_client(mirror: str, vid: str, official: str = ""):
    base = mirror_base(mirror)
    out = []
    if base:
        out.append(f"{base}/version/{vid}/client")
    if official:
        out.append(official)
    return out


def url_library(mirror: str, path: str, official: str = ""):
    base = mirror_base(mirror)
    out = []
    if base:
        out.append(f"{base}/maven/{path}")
    if official:
        out.append(official)
    return out


def url_asset(mirror: str, h: str):
    base = mirror_base(mirror)
    sub = h[:2]
    out = []
    if base:
        out.append(f"{base}/assets/{sub}/{h}")
    out.append(f"https://resources.download.minecraft.net/{sub}/{h}")
    return out


def url_piston_file(mirror: str, sha1: str, name: str, official: str = ""):
    """piston-meta 上的 /v1/packages/<sha1>/<name> 类文件（资源索引等）。"""
    base = mirror_base(mirror)
    out = []
    if base and sha1:
        out.append(f"{base}/v1/packages/{sha1}/{name}")
    if official:
        out.append(official)
    return out


# --------------------------------------------------------------------------- #
# 版本清单 / 版本 JSON
# --------------------------------------------------------------------------- #

_MANIFEST_CACHE = {}
_VJ_CACHE = {}
_INDEX_CACHE = {}


def get_manifest(mirror: str) -> dict:
    if mirror in _MANIFEST_CACHE:
        return _MANIFEST_CACHE[mirror]
    data = fetch_json(url_manifest(mirror))
    data["_mirror"] = mirror
    _MANIFEST_CACHE[mirror] = data
    return data


def save_version_json(vid: str, data: dict) -> Path:
    d = VERSIONS_DIR / vid
    d.mkdir(parents=True, exist_ok=True)
    p = d / f"{vid}.json"
    p.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    return p


def get_version_json(mirror: str, vid: str) -> dict:
    """先看本地（加载器安装出来的 profile），再回源到镜像/官方。"""
    key = (mirror, vid)
    if key in _VJ_CACHE:
        return _VJ_CACHE[key]
    local = VERSIONS_DIR / vid / f"{vid}.json"
    if local.exists():
        try:
            vj = json.loads(local.read_text(encoding="utf-8"))
            _VJ_CACHE[key] = vj
            return vj
        except Exception:  # noqa: BLE001
            pass
    official = ""
    try:
        for v in get_manifest(mirror).get("versions", []):
            if v["id"] == vid:
                official = v.get("url", "")
                break
    except Exception:  # noqa: BLE001
        pass
    vj = fetch_json(url_version_json(mirror, vid, official))
    try:
        save_version_json(vid, vj)
    except Exception:  # noqa: BLE001
        pass
    _VJ_CACHE[key] = vj
    return vj


def get_asset_index(mirror: str, vj: dict, persist: bool = False) -> dict:
    info = vj.get("assetIndex") or {}
    idx_id = str(info.get("id") or "legacy")
    if idx_id in _INDEX_CACHE:
        idx = _INDEX_CACHE[idx_id]
    else:
        disk = ASSETS_DIR / "indexes" / f"{idx_id}.json"
        if disk.exists():
            idx = json.loads(disk.read_text(encoding="utf-8"))
        else:
            urls = url_piston_file(mirror, info.get("sha1", ""), f"{idx_id}.json", info.get("url", ""))
            raw, _ = fetch_bytes(urls, timeout=60)
            idx = json.loads(raw.decode("utf-8"))
            if persist:
                disk.parent.mkdir(parents=True, exist_ok=True)
                disk.write_bytes(raw)
        if len(_INDEX_CACHE) > 3:
            _INDEX_CACHE.clear()
        _INDEX_CACHE[idx_id] = idx
    if persist:
        disk = ASSETS_DIR / "indexes" / f"{idx_id}.json"
        if not disk.exists():
            disk.parent.mkdir(parents=True, exist_ok=True)
            disk.write_text(json.dumps(idx, ensure_ascii=False), encoding="utf-8")
    return idx


# --------------------------------------------------------------------------- #
# 规则判断（库 / 启动参数）
# --------------------------------------------------------------------------- #

IS_WIN = os.name == "nt"
OS_NAME = {"nt": "windows", "posix": "linux"}.get(os.name, "windows")
ARCH = "x86" if platform.architecture()[0] == "32bit" else "x86_64"


def rules_allow(rules) -> bool:
    if not rules:
        return True
    allowed = False
    for rule in rules:
        action = rule.get("action")
        ok = True
        os_rule = rule.get("os")
        if os_rule:
            if "name" in os_rule and os_rule["name"] != OS_NAME:
                ok = False
            if "arch" in os_rule:
                want = os_rule["arch"]
                if want == "x86" and ARCH != "x86":
                    ok = False
                if want in ("x86_64", "arm64") and ARCH != want:
                    ok = False
            if "version" in os_rule:
                try:
                    if not re.search(os_rule["version"], platform.version()):
                        ok = False
                except re.error:
                    pass
        feats = rule.get("features")
        if feats:
            # 我们没有开启任何特性（demo / 自定义分辨率等）
            if any(bool(v) for v in feats.values()):
                ok = False
        if ok:
            allowed = action == "allow"
    return allowed


# --------------------------------------------------------------------------- #
# 版本继承（Forge / Fabric 的 profile 都靠 inheritsFrom 挂到原版上）
# --------------------------------------------------------------------------- #

def _collect_args(vj: dict, kind: str) -> list:
    args = vj.get("arguments") or {}
    raw = args.get(kind)
    if raw is None:
        if kind == "game":
            legacy = vj.get("minecraftArguments") or ""
            return legacy.split() if legacy else []
        return []
    out = []
    for item in raw:
        if isinstance(item, str):
            out.append(item)
        elif isinstance(item, dict):
            if not rules_allow(item.get("rules")):
                continue
            val = item.get("value")
            if isinstance(val, list):
                out.extend(val)
            elif isinstance(val, str):
                out.append(val)
    return out


def _lib_key(lib: dict) -> str:
    """去重键：group:artifact + classifier。

    必须带上 classifier，否则 natives-windows 变体会被基础 jar 挤掉（LWJGL 就是同名不同 classifier）。
    """
    name = lib.get("name") or ""
    parts = name.split(":")
    if len(parts) < 2:
        return name
    key = ":".join(parts[:2])
    cls = parts[3] if len(parts) >= 4 else ""
    if not cls and lib.get("natives"):
        cls = "natives"
    return key + ("|" + cls if cls else "")


def _merge_libraries(child, parent):
    out = []
    seen = set()
    for lib in list(child) + list(parent):
        k = _lib_key(lib)
        if k and k in seen:
            continue
        if k:
            seen.add(k)
        out.append(lib)
    return out


def detect_loader(vj: dict) -> str:
    """从 mainClass / libraries 里认加载器（json 里没写 _loader 时兜底）。

    安装器产出的 json 不带我们的 _loader 标记，靠这个认，避免把 NeoForge
    当成 Forge（或反过来），进而用错 classpath 策略。
    """
    if vj.get("_loader"):
        return vj["_loader"]
    main = (vj.get("mainClass") or "").lower()
    names = " ".join(str(l.get("name") or "") for l in (vj.get("libraries") or [])).lower()
    blob = main + " " + names
    if "neoforged" in blob or "neoforge" in blob:
        return "neoforge"
    if "minecraftforge" in blob or "forge" in main:
        return "forge"
    if "quiltmc" in blob or "quilt" in main:
        return "quilt"
    if "legacyfabric" in blob:
        return "legacyfabric"
    if "fabricmc" in blob or "fabric" in main:
        return "fabric"
    return ""


def resolve_version(mirror: str, vid: str, _depth: int = 0) -> dict:
    """把 inheritsFrom 链合并成一个可直接启动的版本对象。

    返回的 dict 额外带：_jar_id（该用哪个版本的 client.jar）、_base_id（原版号）、
    _loader / _loader_version（fabric/quilt/forge/空）。
    """
    if _depth > 4:
        raise RuntimeError("版本继承链过深，无法解析")
    vj = get_version_json(mirror, vid)
    vj_id = vj.get("id", vid)
    parent_id = vj.get("inheritsFrom")
    if not parent_id:
        out = dict(vj)
        out["id"] = vj_id
        out["_jar_id"] = vj_id
        out["_base_id"] = vj_id
        out["_loader"] = detect_loader(vj)
        out["_loader_version"] = vj.get("_loader_version", "")
        return out

    parent = resolve_version(mirror, parent_id, _depth + 1)
    merged = dict(parent)
    merged["id"] = vj_id
    merged["_jar_id"] = parent.get("_jar_id", parent_id)
    merged["_base_id"] = parent.get("_base_id", parent_id)
    merged["mainClass"] = vj.get("mainClass") or parent.get("mainClass")
    merged["type"] = vj.get("type") or parent.get("type")
    merged["releaseTime"] = vj.get("releaseTime") or parent.get("releaseTime")
    merged["libraries"] = _merge_libraries(vj.get("libraries") or [], parent.get("libraries") or [])
    merged["arguments"] = {
        "game": _collect_args(vj, "game") + _collect_args(parent, "game"),
        "jvm": _collect_args(vj, "jvm") + _collect_args(parent, "jvm"),
    }
    merged.pop("minecraftArguments", None)
    merged["_loader"] = detect_loader(vj) or parent.get("_loader", "")
    merged["_loader_version"] = vj.get("_loader_version") or parent.get("_loader_version", "")
    return merged


def list_local_versions() -> list:
    """本地已装/已安装加载器的版本（versions 目录里能解析出 json 的）。"""
    out = []
    if not VERSIONS_DIR.exists():
        return out
    for d in sorted(VERSIONS_DIR.iterdir(), key=lambda p: p.name.lower()):
        if not d.is_dir():
            continue
        jp = d / f"{d.name}.json"
        if not jp.exists():
            continue
        try:
            meta = json.loads(jp.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            continue
        jar = d / f"{d.name}.jar"
        out.append({
            "id": d.name,
            "inheritsFrom": meta.get("inheritsFrom", ""),
            "loader": meta.get("_loader", ""),
            "loaderVersion": meta.get("_loader_version", ""),
            "jar": jar.exists(),
        })
    return out


# --------------------------------------------------------------------------- #
# 下载计划
# --------------------------------------------------------------------------- #

class Task:
    __slots__ = ("urls", "dest", "sha1", "size", "kind")

    def __init__(self, urls, dest: Path, sha1="", size=0, kind="file"):
        self.urls = [u for u in urls if u]
        self.dest = dest
        self.sha1 = sha1 or ""
        self.size = int(size or 0)
        self.kind = kind


def _maven_rel(group: str, artifact: str, version: str, classifier: str = "") -> str:
    fn = f"{artifact}-{version}" + (f"-{classifier}" if classifier else "") + ".jar"
    return "/".join(group.split(".") + [artifact, version, fn])


def _maven_rel_from_name(name: str, classifier: str = "") -> str:
    parts = (name or "").split(":")
    if len(parts) < 3:
        return ""
    if len(parts) >= 4 and not classifier:
        classifier = parts[3]
    return _maven_rel(parts[0], parts[1], parts[2], classifier)


def lib_files(lib: dict):
    """列出某个库要落盘的文件：[(相对路径, [候选url], sha1, size, 是否natives)]

    兼容两种格式：
      * 新式（原版 1.7+）：downloads.artifact / downloads.classifiers
      * 老式（Fabric/Quilt/Forge 的 profile）：只有 name(maven 坐标) + url
    """
    dl = lib.get("downloads") or {}
    base = (lib.get("url") or "https://libraries.minecraft.net/").rstrip("/")
    out = []
    art = dl.get("artifact")
    if art and art.get("path"):
        out.append((art["path"], [art.get("url", "")], art.get("sha1", ""), int(art.get("size") or 0),
                    "natives" in art["path"]))
    else:
        rel = _maven_rel_from_name(lib.get("name", ""))
        if rel:
            out.append((rel, [f"{base}/{rel}"], lib.get("sha1", ""), int(lib.get("size") or 0),
                        "natives" in rel))
    natives_map = lib.get("natives") or {}
    if natives_map and IS_WIN:
        key = natives_map.get("windows")
        if key:
            cls = (dl.get("classifiers") or {}).get(key)
            if cls and cls.get("path"):
                out.append((cls["path"], [cls.get("url", "")], cls.get("sha1", ""),
                            int(cls.get("size") or 0), True))
            else:
                rel = _maven_rel_from_name(lib.get("name", ""), key)
                if rel:
                    out.append((rel, [f"{base}/{rel}"], "", 0, True))
    return out


def _lib_targets(lib: dict):
    """返回 (artifact_tasks, natives_tasks)，dest 用相对路径占位，由调用方替换。"""
    tasks = []
    natives = []
    for rel, urls, sha1, size, is_native in lib_files(lib):
        t = Task(urls, LIBRARIES_DIR / rel, sha1, size)
        (natives if is_native else tasks).append(t)
    return tasks, natives


def build_plan(vj: dict, mirror: str, components, skip_sounds: bool):
    """构造下载任务列表。vj 必须是 resolve_version() 的结果。"""
    vid = vj["id"]
    jar_id = vj.get("_jar_id") or vid
    tasks: list[Task] = []
    seen = set()

    def add(t: Task):
        key = str(t.dest).lower()
        if key in seen:
            return
        seen.add(key)
        tasks.append(t)

    if "client" in components:
        dl = (vj.get("downloads") or {}).get("client")
        if dl:
            add(Task(url_client(mirror, jar_id, dl.get("url", "")),
                     VERSIONS_DIR / jar_id / f"{jar_id}.jar", dl.get("sha1", ""), dl.get("size", 0), "client"))

    if "libraries" in components:
        for lib in vj.get("libraries") or []:
            if not rules_allow(lib.get("rules")):
                continue
            arts, nats = _lib_targets(lib)
            for t in arts + nats:
                rel = t.dest.relative_to(LIBRARIES_DIR).as_posix()
                add(Task(url_library(mirror, rel) + t.urls, t.dest, t.sha1, t.size, "library"))

    if "assets" in components:
        idx = get_asset_index(mirror, vj, persist=True)
        for name, obj in (idx.get("objects") or {}).items():
            if skip_sounds and name.startswith("minecraft/sounds/"):
                continue
            h = obj["hash"]
            add(Task(url_asset(mirror, h), ASSETS_DIR / "objects" / h[:2] / h, h, obj.get("size", 0), "asset"))

    if "logging" in components:
        lg = ((vj.get("logging") or {}).get("client") or {}).get("file")
        if lg:
            add(Task([lg.get("url", "")], ASSETS_DIR / "log_configs" / lg["id"],
                     lg.get("sha1", ""), lg.get("size", 0), "logging"))

    return tasks


def plan_stats(vj: dict, mirror: str, skip_sounds: bool = False) -> dict:
    """返回各组件的估算体积（用于界面展示）。"""
    out = {"client": {"count": 0, "size": 0}, "libraries": {"count": 0, "size": 0},
           "assets": {"count": 0, "size": 0}, "logging": {"count": 0, "size": 0}}
    dl = (vj.get("downloads") or {}).get("client") or {}
    if dl:
        out["client"] = {"count": 1, "size": int(dl.get("size") or 0)}
    for lib in vj.get("libraries") or []:
        if not rules_allow(lib.get("rules")):
            continue
        arts, nats = _lib_targets(lib)
        for t in arts + nats:
            out["libraries"]["count"] += 1
            out["libraries"]["size"] += t.size
    try:
        idx = get_asset_index(mirror, vj)
        total = 0
        cnt = 0
        for name, obj in (idx.get("objects") or {}).items():
            if skip_sounds and name.startswith("minecraft/sounds/"):
                continue
            cnt += 1
            total += int(obj.get("size") or 0)
        out["assets"] = {"count": cnt, "size": total}
    except Exception:  # noqa: BLE001
        out["assets"] = {"count": 0, "size": 0}
    lg = ((vj.get("logging") or {}).get("client") or {}).get("file")
    if lg:
        out["logging"] = {"count": 1, "size": int(lg.get("size") or 0)}
    return out


# --------------------------------------------------------------------------- #
# 下载器
# --------------------------------------------------------------------------- #

class StopRequested(Exception):
    pass


class DownloadJob:
    def __init__(self, vid: str, mirror: str, tasks: list, workers: int = 16, verify: bool = False):
        self.id = uuid.uuid4().hex[:12]
        self.vid = vid
        self.mirror = mirror
        self.tasks = tasks
        self.workers = max(1, min(48, int(workers or 16)))
        self.verify = verify
        self.stop = threading.Event()
        self.lock = threading.Lock()
        self.done_bytes = 0
        self.total_bytes = sum(t.size or 0 for t in tasks)
        self.done_files = 0
        self.total_files = len(tasks)
        self.skipped = 0
        self.errors: list[str] = []
        self.status = "pending"
        self.message = ""
        self.logs: list[str] = []
        self.started = time.time()
        self._speed = 0.0
        self._sample_t = time.time()
        self._sample_b = 0
        self.thread = None

    # ---- 进度 ----
    def _add(self, n: int, files: int = 0):
        with self.lock:
            self.done_bytes += n
            if self.done_bytes < 0:
                self.done_bytes = 0
            if self.done_bytes > self.total_bytes > 0:
                self.done_bytes = self.total_bytes
            self.done_files += files
        now = time.time()
        if now - self._sample_t >= 0.5:
            with self.lock:
                db = self.done_bytes - self._sample_b
                self._sample_b = self.done_bytes
            self._speed = db / max(1e-6, now - self._sample_t)
            self._sample_t = now

    def note(self, text: str):
        with self.lock:
            self.logs.append(text)
            if len(self.logs) > 200:
                del self.logs[:100]

    def snapshot(self) -> dict:
        with self.lock:
            total = self.total_bytes
            done = self.done_bytes
            pct = (done / total * 100.0) if total else (
                self.done_files / self.total_files * 100.0 if self.total_files else 0.0)
            eta = ((total - done) / self._speed) if (total and self._speed > 1024) else -1
            return {
                "id": self.id, "vid": self.vid, "status": self.status, "message": self.message,
                "done": done, "total": total, "percent": round(min(100.0, pct), 1),
                "files": self.done_files, "files_total": self.total_files, "skipped": self.skipped,
                "speed": round(self._speed), "eta": int(eta), "errors": self.errors[-5:],
                "logs": self.logs[-40:], "elapsed": int(time.time() - self.started),
            }

    # ---- 执行 ----
    def start(self):
        self.thread = threading.Thread(target=self.run, name=f"job-{self.id}", daemon=True)
        self.thread.start()

    def run(self):
        try:
            self.status = "running"
            self.note(f"开始下载 {self.vid}：{self.total_files} 个文件，共 {human_size(self.total_bytes)}")
            with ThreadPoolExecutor(max_workers=self.workers) as ex:
                futures = [ex.submit(self._one, t) for t in self.tasks]
                for fut in as_completed(futures):
                    try:
                        fut.result()
                    except StopRequested:
                        pass
                    except Exception as exc:  # noqa: BLE001
                        self.errors.append(str(exc))
            if self.stop.is_set():
                self.status = "cancelled"
                self.message = "已取消"
                self.note("下载已取消")
            elif self.errors and self.done_files == 0:
                self.status = "error"
                self.message = f"{len(self.errors)} 个文件下载失败"
                self.note(f"失败：{self.errors[0]}")
            else:
                self.status = "done"
                self.message = f"完成：{self.done_files} 个文件（跳过已存在 {self.skipped} 个）"
                self.note(self.message)
                if self.errors:
                    self.note(f"有 {len(self.errors)} 个文件失败，可重试")
        except Exception as exc:  # noqa: BLE001
            self.status = "error"
            self.message = f"异常：{exc}"
            self.note(self.message)

    def _one(self, task: Task):
        if self.stop.is_set():
            raise StopRequested()
        dest = task.dest
        if dest.exists():
            size = dest.stat().st_size
            if (task.size and size == task.size) or (not task.size and size > 0):
                with self.lock:
                    self.skipped += 1
                self._add(task.size or size, 1)
                return
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.with_name(dest.name + ".part")
        last_err = None
        for url in task.urls:
            for attempt in range(2):
                if self.stop.is_set():
                    raise StopRequested()
                got = 0
                try:
                    got = self._fetch(url, tmp, task)
                    if dest.exists():
                        dest.unlink()
                    tmp.replace(dest)
                    self._add(0, 1)
                    return
                except StopRequested:
                    raise
                except Exception as exc:  # noqa: BLE001
                    last_err = exc
                    self._add(-got)
                    try:
                        tmp.unlink()
                    except OSError:
                        pass
                    time.sleep(0.5)
        raise RuntimeError(f"{dest.name}: {last_err}")

    def _fetch(self, url: str, tmp: Path, task: Task) -> int:
        h = hashlib.sha1() if (task.sha1 or self.verify) else None
        got = 0
        with urlopen(Request(url, headers=HDRS), timeout=45) as resp, open(tmp, "wb") as fh:
            while True:
                if self.stop.is_set():
                    raise StopRequested()
                chunk = resp.read(262144)
                if not chunk:
                    break
                fh.write(chunk)
                if h is not None:
                    h.update(chunk)
                got += len(chunk)
                self._add(len(chunk))
        if h is not None and task.sha1 and h.hexdigest() != task.sha1:
            raise RuntimeError("SHA1 校验不通过")
        if task.size and got != task.size:
            raise RuntimeError(f"大小不符（{got} != {task.size}）")
        return got


class OpJob:
    """给「装加载器 / 装模组」这类不定长操作复用的进度对象（同样走 SSE）。"""

    def __init__(self, title: str):
        self.id = uuid.uuid4().hex[:12]
        self.title = title
        self.status = "running"
        self.message = title
        self.logs = [title]
        self.errors: list[str] = []
        self.started = time.time()
        self.stop = threading.Event()
        self.lock = threading.Lock()
        self.percent = 0.0
        self.speed = 0
        self.result = None

    def note(self, text: str):
        with self.lock:
            self.logs.append(text)
            if len(self.logs) > 200:
                del self.logs[:100]

    def snapshot(self) -> dict:
        with self.lock:
            done = self.status in ("done", "error", "cancelled")
            return {
                "id": self.id, "vid": "", "status": self.status, "message": self.message,
                "done": 1 if done else 0, "total": 1,
                "percent": 100.0 if done else round(self.percent, 1),
                "files": 0, "files_total": 0, "skipped": 0,
                "speed": self.speed, "eta": -1,
                "errors": self.errors[-5:], "logs": self.logs[-40:],
                "result": self.result,
                "elapsed": int(time.time() - self.started),
            }

    def run(self, fn):
        def wrapper():
            try:
                self.result = fn(self)
                self.status = "done"
                self.message = self.message or "完成"
                self.note("完成")
            except Exception as exc:  # noqa: BLE001
                self.status = "error"
                self.message = str(exc)
                self.errors.append(str(exc))
                self.note(f"失败：{exc}")
        threading.Thread(target=wrapper, daemon=True).start()


# --------------------------------------------------------------------------- #
# natives 解压
# --------------------------------------------------------------------------- #

def natives_dir(vid: str) -> Path:
    return NATIVES_DIR / vid


def extract_natives(vj: dict, quiet=True) -> int:
    """把 natives jar 里的 dll 解压到 .minecraft/natives/<id>。"""
    vid = vj["id"]
    out = natives_dir(vid)
    out.mkdir(parents=True, exist_ok=True)
    count = 0
    for lib in vj.get("libraries") or []:
        if not rules_allow(lib.get("rules")):
            continue
        for rel, _urls, _sha1, _size, is_native in lib_files(lib):
            if not is_native:
                continue
            jar = LIBRARIES_DIR / rel
            if not jar.exists():
                continue
            try:
                with zipfile.ZipFile(jar) as zf:
                    for info in zf.infolist():
                        if info.is_dir():
                            continue
                        low = info.filename.lower()
                        if low.startswith("meta-inf/") or low.endswith(".git") or low.endswith(".sha1"):
                            continue
                        if not (low.endswith(".dll") or low.endswith(".so") or low.endswith(".dylib")):
                            continue
                        target = out / Path(info.filename).name
                        with zf.open(info) as src, open(target, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        count += 1
            except zipfile.BadZipFile:
                continue
    if not quiet:
        log(f"natives 解压完成：{count} 个动态库 -> {out}")
    return count


# --------------------------------------------------------------------------- #
# Java 检测
# --------------------------------------------------------------------------- #

_JAVA_CACHE = {"list": None, "at": 0.0}


def java_major(java_path: str) -> int:
    try:
        flags = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
        p = subprocess.run([java_path, "-version"], capture_output=True, text=True,
                           timeout=12, creationflags=flags)
        text = (p.stderr or "") + (p.stdout or "")
        m = re.search(r'version "(\d+)(?:\.(\d+))?', text)
        if not m:
            return 0
        major = int(m.group(1))
        if major == 1 and m.group(2):
            major = int(m.group(2))
        return major
    except Exception:  # noqa: BLE001
        return 0


def find_javas(force=False):
    if not force and _JAVA_CACHE["list"] is not None and time.time() - _JAVA_CACHE["at"] < 120:
        return _JAVA_CACHE["list"]
    found: dict[str, int] = {}
    exe = "java.exe" if IS_WIN else "java"

    def consider(p):
        if not p:
            return
        p = Path(p)
        if not p.exists():
            return
        key = str(p.resolve()).lower()
        if key in found:
            return
        major = java_major(str(p))
        if major:
            found[key] = major

    cfg = load_config().get("java")
    if cfg:
        consider(cfg)
    jh = os.environ.get("JAVA_HOME")
    if jh:
        consider(Path(jh) / "bin" / exe)
    which = shutil.which("java")
    if which:
        consider(which)
    patterns = [
        str(JAVA_DIR / "**" / "bin") + "/" + exe,     # 本启动器自己下的 JDK
        r"C:/Program Files/Java/*/bin/" + exe,
        r"C:/Program Files/Eclipse Adoptium/*/bin/" + exe,
        r"C:/Program Files/Microsoft/jdk*/bin/" + exe,
        r"C:/Program Files/Zulu/*/bin/" + exe,
        r"C:/Program Files/Amazon Corretto/*/bin/" + exe,
        r"C:/Program Files/BellSoft/*/bin/" + exe,
        r"C:/Program Files/Common Files/Oracle/Java/javapath/" + exe,
        r"C:/Program Files (x86)/Java/*/bin/" + exe,
        str(Path.home() / "AppData/Local/Programs/**/bin") + "/" + exe,
    ]
    import glob as _glob
    for pat in patterns:
        for hit in _glob.glob(pat, recursive=True):
            consider(hit)
    items = sorted(({"path": k, "major": v} for k, v in found.items()),
                   key=lambda x: (x["major"], x["path"]), reverse=True)
    _JAVA_CACHE["list"] = items
    _JAVA_CACHE["at"] = time.time()
    return items


def pick_java(required_major: int, prefer: str = "") -> str:
    if prefer and Path(prefer).exists():
        return prefer
    javas = find_javas()
    if not javas:
        return ""
    exact = [j for j in javas if j["major"] == required_major]
    if exact:
        return exact[0]["path"]
    higher = sorted([j for j in javas if j["major"] >= required_major], key=lambda x: x["major"])
    if higher:
        return higher[0]["path"]
    return javas[0]["path"]


# --------------------------------------------------------------------------- #
# Java 运行时下载（Adoptium Temurin）
# --------------------------------------------------------------------------- #

def _os_arch() -> tuple:
    sysname = {"windows": "windows", "linux": "linux", "darwin": "mac"}.get(
        platform.system().lower(), "linux")
    machine = platform.machine().lower()
    arch = {"amd64": "x64", "x86_64": "x64", "aarch64": "aarch64", "arm64": "aarch64"}.get(machine, "x64")
    return sysname, arch


def java_package(major: int) -> dict:
    """问 Adoptium 要某个大版本的最新 JDK 包信息（不下载）。

    返回的 urls 是国内镜像优先：清华 TUNA 的 Adoptium 镜像和官方 GitHub 是同一个文件
    （文件名、大小都一样），GitHub 在国内经常几十 KB/s，所以先试镜像。
    """
    osname, arch = _os_arch()
    url = (f"{ADOPTIUM_API}/assets/latest/{int(major)}/hotspot"
           f"?architecture={arch}&image_type=jdk&os={osname}&vendor=eclipse")
    data = json.loads(fetch_bytes([url], timeout=60, retries=2)[0].decode("utf-8"))
    if not data:
        raise RuntimeError(f"Adoptium 上没有 Java {major} 的 {osname}/{arch} 包")
    pkg = data[0]["binary"]["package"]
    link = pkg["link"]
    fname = link.rsplit("/", 1)[-1]
    urls = []
    if osname == "windows" and fname.lower().endswith(".zip"):
        urls.append(f"https://mirrors.tuna.tsinghua.edu.cn/Adoptium/{int(major)}/jdk/{arch}/{osname}/{fname}")
    urls.append(link)
    return {
        "major": int(major),
        "name": data[0].get("release_name") or f"jdk-{major}",
        "link": link,
        "urls": urls,
        "size": int(pkg.get("size") or 0),
        "ext": ".zip" if fname.lower().endswith(".zip") else ".tar.gz",
    }


def _stream_download(urls, dest: Path, job=None, label: str = "", expect: int = 0) -> Path:
    """带进度的单文件下载（Java 包一百多 MB，不能用 fetch_bytes 一把梭），支持换源。"""
    if isinstance(urls, str):
        urls = [urls]
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(dest.suffix + ".part")
    last_err = None
    for url in urls:
        started = time.time()
        got = 0
        try:
            req = Request(url, headers=dict(HDRS, **{"Accept-Encoding": "identity"}))
            with urlopen(req, timeout=30) as r, open(tmp, "wb") as fh:
                total = int(r.headers.get("Content-Length") or 0) or expect
                last = 0.0
                while True:
                    if job is not None and job.stop.is_set():
                        raise RuntimeError("已取消")
                    chunk = r.read(262144)
                    if not chunk:
                        break
                    fh.write(chunk)
                    got += len(chunk)
                    now = time.time()
                    if job is not None and now - last > 0.4:
                        last = now
                        with job.lock:
                            job.percent = (got * 100.0 / total) if total else 0.0
                            job.speed = int(got / max(now - started, 0.001))
                            job.message = (f"{label} {human_size(got)} / {human_size(total)}"
                                           if total else f"{label} {human_size(got)}")
            size = tmp.stat().st_size
            if expect and size != expect:
                raise RuntimeError(f"大小不对（{size} != {expect}）")
            tmp.replace(dest)
            if job is not None:
                with job.lock:
                    job.speed = 0
            return dest
        except Exception as exc:  # noqa: BLE001
            last_err = exc
            try:
                tmp.unlink()
            except OSError:
                pass
            if job is not None and job.stop.is_set():
                raise
            if len(urls) > 1:
                _note(job, f"  源 {url.split('/')[2]} 不行（{str(exc)[:70]}），换下一个")
    raise RuntimeError(f"下载失败：{last_err}")


def _extract_java(archive: Path, out_dir: Path, expect_name: str = "") -> Path:
    """解压 JDK 包，返回 bin/java(.exe) 路径。

    注意：out_dir 下可能已经躺着别的 JDK（比如先下了 17 又下 25），
    所以不能直接 glob **/bin/java 取第一个，否则会拿到老版本。
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    before = {p.name for p in out_dir.iterdir() if p.is_dir()}
    if archive.suffix.lower() == ".zip":
        with zipfile.ZipFile(archive) as z:
            z.extractall(out_dir)
    else:
        import tarfile
        with tarfile.open(archive) as t:
            try:
                t.extractall(out_dir, filter="data")   # py3.12+ 防路径穿越
            except TypeError:
                t.extractall(out_dir)
    exe = "java.exe" if IS_WIN else "java"
    if expect_name and (out_dir / expect_name / "bin" / exe).exists():
        return out_dir / expect_name / "bin" / exe
    fresh = [p for p in out_dir.iterdir() if p.is_dir() and p.name not in before]
    hits = []
    for d in fresh:
        hits += sorted(d.glob(f"**/bin/{exe}"))
    if not hits:
        hits = sorted(out_dir.glob(f"**/bin/{exe}"))
    if not hits:
        raise RuntimeError(f"解压后没找到 bin/{exe}，压缩包可能不完整")
    return hits[0]


def install_java(major: int, job: OpJob = None) -> dict:
    """下载并解压一个 JDK 到 java/ 目录，返回 {path, major}。"""
    pkg = java_package(major)
    target = JAVA_DIR / pkg["name"]
    exe = target / "bin" / ("java.exe" if IS_WIN else "java")
    if not exe.exists():
        _note(job, f"准备 Java {major}：{pkg['name']}（{human_size(pkg['size'])}）")
        archive = CACHE_DIR / (pkg["name"] + pkg["ext"])
        if archive.exists() and pkg["size"] and archive.stat().st_size == pkg["size"]:
            _note(job, "压缩包已在缓存里，跳过下载")
        else:
            _note(job, f"下载 {pkg['name']}（{human_size(pkg['size'])}，先试国内镜像）")
            _stream_download(pkg["urls"], archive, job, f"Java {major}", pkg["size"])
        _note(job, "解压中…")
        exe = _extract_java(archive, JAVA_DIR, pkg["name"])
        try:                      # 解压完就没必要留着 180MB 的包
            archive.unlink()
        except OSError:
            pass
    _JAVA_CACHE["list"] = None
    ver = java_major(str(exe))
    _note(job, f"Java {ver or major} 就绪：{exe}")
    return {"path": str(exe), "major": ver or int(major), "name": pkg["name"]}


# --------------------------------------------------------------------------- #
# 启动游戏
# --------------------------------------------------------------------------- #

def ensure_authlib_injector() -> Path:
    """确保 authlib-injector.jar 就位（第三方登录 / 外置登录用），缺了就下。"""
    p = AUTH_INJECTOR_JAR
    if p.exists() and p.stat().st_size >= 50_000:
        return p
    log("正在下载 authlib-injector.jar（外置登录组件）…")
    # 1) 查 GitHub API 拿最新 release 的 jar 直链
    direct = ""
    try:
        d = fetch_json([AUTH_INJECTOR_API], timeout=20, retries=1)
        for a in d.get("assets") or []:
            name = a.get("name", "")
            if name.endswith(".jar") and "sources" not in name.lower():
                direct = a.get("browser_download_url", "")
                break
    except Exception as exc:  # noqa: BLE001
        log(f"查询 authlib-injector 版本失败（{exc}），尝试固定直链")
        direct = "https://github.com/yushijinhun/authlib-injector/releases/latest/download/authlib-injector-1.2.8.jar"
    if not direct:
        raise RuntimeError("无法获取 authlib-injector 下载地址，请手动下载后放到 " + str(p))
    # 2) 原直链 + 加速镜像依次尝试
    candidates = [direct] + [f"{m}{direct}" for m in AUTH_INJECTOR_MIRRORS]
    try:
        data, _ = fetch_bytes(candidates, timeout=60, retries=1)
    except Exception as exc:  # noqa: BLE001
        raise RuntimeError(
            f"下载 authlib-injector.jar 失败（{exc}）。"
            f"可手动下载后放到 {p}，或检查网络/镜像连通性") from exc
    if len(data) < 50_000:
        raise RuntimeError("authlib-injector.jar 下载内容异常（文件过小），请检查来源")
    tmp = p.with_suffix(".jar.part")
    tmp.write_bytes(data)
    tmp.replace(p)
    log("authlib-injector.jar 已就绪：" + str(p))
    return p


def offline_uuid(name: str) -> str:
    digest = bytearray(hashlib.md5(("OfflinePlayer:" + name).encode("utf-8")).digest())
    digest[6] = (digest[6] & 0x0F) | 0x30
    digest[8] = (digest[8] & 0x3F) | 0x80
    return str(uuid.UUID(bytes=bytes(digest)))


def uses_module_path(vj: dict) -> bool:
    """这个版本是不是模块化启动（`-p` + BootstrapLauncher）。

    老版 Forge / NeoForge（1.17~1.21 那几代）是模块化的，classpath 里放原版 jar 会
    多出一个 `_1.20.1` 自动模块跟 `minecraft` 模块撞包；新版 NeoForge（26.x，
    mainClass = net.neoforged.fml.startup.Client）又回到普通 classpath 启动了，
    所以按实际参数判断，别按加载器名字猜。
    """
    main = (vj.get("mainClass") or "").lower()
    if "bootstraplauncher" in main:
        return True
    jvm = _collect_args(vj, "jvm")
    return any(a in ("-p", "--module-path") for a in jvm)


def classpath_entries(vj: dict, jar_id: str, include_client: bool = True):
    entries = []
    for lib in vj.get("libraries") or []:
        if not rules_allow(lib.get("rules")):
            continue
        for rel, _urls, _sha1, _size, _nat in lib_files(lib):
            entries.append(str(LIBRARIES_DIR / rel))
    # Forge 走模块化启动，游戏类由 client-srg.jar / forge-client.jar 提供；
    # 再把原版 jar 塞进 classpath 会多出一个 _1.xx.x 自动模块，和 minecraft 模块撞包直接崩。
    if include_client:
        entries.append(str(VERSIONS_DIR / jar_id / f"{jar_id}.jar"))
    return entries


def build_command(vj: dict, username: str, memory_mb: int, java_path: str,
                  server: str = "", server_port: int = 0, authlib: str = "") -> list:
    """拼 java 启动命令。

    server:  联机服务器地址，非空时启动后自动加入该服务器（--server/--port）
    authlib: 第三方登录（外置登录）yggdrasil API，非空时挂 authlib-injector
    """
    vid = vj.get("id", "")
    jar_id = vj.get("_jar_id") or vid
    required = int(((vj.get("javaVersion") or {}).get("majorVersion")) or 8)
    java = java_path or pick_java(required)
    if not java:
        raise RuntimeError("未找到 Java，请安装 Java 或手动指定 java.exe 路径")
    major = java_major(java)
    if major and major < required:
        raise RuntimeError(f"该版本需要 Java {required} 或更高，当前选中的是 Java {major}，请在设置里换一个 Java")
    if authlib and not re.match(r"^https?://", authlib):
        raise RuntimeError("第三方登录 API 必须以 http(s):// 开头")
    jar = VERSIONS_DIR / jar_id / f"{jar_id}.jar"
    if not jar.exists():
        raise RuntimeError(f"缺少客户端核心 {jar.name}，请先下载“客户端核心”")

    asset_index_id = str((vj.get("assetIndex") or {}).get("id") or "legacy")
    if not (ASSETS_DIR / "indexes" / f"{asset_index_id}.json").exists():
        raise RuntimeError("缺少资源索引文件，请勾选「资源文件」重新下载一次")

    extract_natives(vj, quiet=True)
    nat = natives_dir(vid)
    nat.mkdir(parents=True, exist_ok=True)
    gdir = instance_dir(vid)
    gdir.mkdir(parents=True, exist_ok=True)
    mods_dir(vid).mkdir(parents=True, exist_ok=True)

    sep = ";" if IS_WIN else ":"
    # 模块化启动（-p + BootstrapLauncher）时 classpath 里不能放原版 jar，
    # 否则会多出一个 _1.20.1 自动模块跟 minecraft 模块撞包。
    # 新版 NeoForge（26.x）已经改成普通 classpath 启动，所以按参数判断而不是按加载器名。
    is_module_loader = uses_module_path(vj)
    cp = sep.join(classpath_entries(vj, jar_id, include_client=not is_module_loader))
    subs = {
        "auth_player_name": username or "Steve",
        "version_name": vid,
        "game_directory": str(gdir),
        "assets_root": str(ASSETS_DIR),
        "game_assets": str(ASSETS_DIR / "virtual" / "legacy"),
        "assets_index_name": asset_index_id,
        "auth_uuid": offline_uuid(username or "Steve"),
        "auth_access_token": "0" * 32,
        "auth_session": "0" * 32,
        "clientid": "",
        "auth_xuid": "",
        "user_type": "legacy",
        "version_type": vj.get("type", "release"),
        "natives_directory": str(nat),
        "launcher_name": "MCLauncher",
        "launcher_version": APP_VER,
        "classpath": cp,
        "classpath_separator": sep,
        "library_directory": str(LIBRARIES_DIR),
        "resolution_width": "854",
        "resolution_height": "480",
        "user_properties": "{}",
    }

    def sub(arg: str) -> str:
        for k, v in subs.items():
            arg = arg.replace("${" + k + "}", v)
        return arg

    jvm = [sub(a) for a in _collect_args(vj, "jvm")]
    game = [sub(a) for a in _collect_args(vj, "game")]

    cmd = [java]
    if authlib:
        # 第三方登录：用 authlib-injector 拦截 yggdrasil 验证，进外置登录服务器
        inj = ensure_authlib_injector()
        cmd.append(f"-javaagent:{inj}={authlib}")
    if memory_mb:
        cmd.append(f"-Xmx{int(memory_mb)}M")
        cmd.append(f"-Xms{min(int(memory_mb), 1024)}M")
    log_cfg = ((vj.get("logging") or {}).get("client") or {}).get("file")
    if log_cfg:
        p = ASSETS_DIR / "log_configs" / log_cfg["id"]
        if p.exists():
            cmd.append(f"-Dlog4j.configurationFile={p}")
    cmd.extend(jvm)
    if not any(a.startswith("-cp") or a == "-classpath" for a in jvm):
        cmd.extend(["-cp", cp])
    cmd.append(vj.get("mainClass", "net.minecraft.client.main.Main"))
    cmd.extend(game)
    if "--versionType" not in game:
        cmd.extend(["--versionType", vj.get("type", "release")])
    if server:
        # 一键进服：启动后自动加入该服务器
        cmd.extend(["--server", server, "--port", str(int(server_port) or 25565)])
    return cmd


def launch_game(vj: dict, username: str, memory_mb: int, java_path: str,
                server: str = "", server_port: int = 0, authlib: str = "") -> subprocess.Popen:
    cmd = build_command(vj, username, memory_mb, java_path,
                        server=server, server_port=server_port, authlib=authlib)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    logfile = LOG_DIR / "latest.log"
    fh = open(logfile, "wb")
    flags = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
    proc = subprocess.Popen(cmd, cwd=str(instance_dir(vj["id"])), stdout=fh, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL, creationflags=flags)
    log("已启动游戏，日志：" + str(logfile))
    return proc


# --------------------------------------------------------------------------- #
# frp 内网穿透（一键开服）
# --------------------------------------------------------------------------- #

FRP_PROC: subprocess.Popen | None = None
FRP_PROC_LOCK = threading.Lock()


def frp_config() -> dict:
    cfg = load_config().get("frp") or {}
    return {
        "server": (cfg.get("server") or "").strip(),
        "port": int(cfg.get("port") or 7000),
        "token": cfg.get("token") or "",
        "local_port": int(cfg.get("local_port") or 25565),
        "remote_port": int(cfg.get("remote_port") or 0),
    }


def frp_status() -> dict:
    running = FRP_PROC is not None and FRP_PROC.poll() is None
    return {
        "cfg": frp_config(),
        "exe_exists": FRP_EXE.exists(),
        "running": running,
        "pid": FRP_PROC.pid if running else None,
    }


def ensure_frpc(job=None) -> Path:
    """下载 frpc.exe（Windows amd64）到 frp/ 目录，已存在且够大就跳过。"""
    if FRP_EXE.exists() and FRP_EXE.stat().st_size >= 2_000_000:
        return FRP_EXE
    _note(job, "正在获取 frp 最新版本…")
    ver, direct = "", ""
    try:
        d = fetch_json([FRP_VER_API], timeout=20, retries=1)
        ver = str(d.get("tag_name", "")).lstrip("v")
        for a in d.get("assets") or []:
            if a.get("name") == f"frp_{ver}_windows_amd64.zip":
                direct = a.get("browser_download_url", "")
                break
    except Exception as exc:  # noqa: BLE001
        raise RuntimeError(f"获取 frp 版本失败：{exc}") from exc
    if not direct:
        raise RuntimeError("frp 发布页没有找到 windows_amd64 安装包")
    candidates = [direct] + [f"{m}{direct}" for m in FRP_MIRRORS]
    _note(job, f"正在下载 frp v{ver}（约 15 MB，GitHub + 加速镜像）…")
    data, _ = fetch_bytes(candidates, timeout=180, retries=1)
    FRP_DIR.mkdir(parents=True, exist_ok=True)
    ztmp = FRP_DIR / "frp.zip.part"
    ztmp.write_bytes(data)
    try:
        with zipfile.ZipFile(ztmp) as z:
            names = [n for n in z.namelist() if n.endswith("frpc.exe")]
            if not names:
                raise RuntimeError("frp 压缩包里没有 frpc.exe")
            with z.open(names[0]) as src, open(FRP_EXE, "wb") as dst:
                shutil.copyfileobj(src, dst)
    finally:
        ztmp.unlink(missing_ok=True)
    _note(job, "frpc.exe 已就绪：" + str(FRP_EXE))
    return FRP_EXE


def start_frp(job=None) -> dict:
    """写 frpc.toml 并启动穿透，返回公网连接地址。"""
    cfg = frp_config()
    if not cfg["server"]:
        raise ValueError("请先填 frp 服务器地址（你 frps 的公网 IP 或域名）")
    if not 1 <= cfg["port"] <= 65535 or not 1 <= cfg["local_port"] <= 65535:
        raise ValueError("端口必须在 1~65535 之间")
    stop_frp()
    ensure_frpc(job)
    remote_port = cfg["remote_port"] or cfg["local_port"]
    if not 1 <= remote_port <= 65535:
        raise ValueError("远程端口必须在 1~65535 之间")
    conf_lines = [
        f'serverAddr = "{cfg["server"]}"',
        f'serverPort = {cfg["port"]}',
    ]
    if cfg["token"]:
        conf_lines.append('auth.method = "token"')
        conf_lines.append(f'auth.token = "{cfg["token"]}"')
    conf_lines += [
        "",
        "[[proxies]]",
        'name = "minecraft"',
        'type = "tcp"',
        'localIP = "127.0.0.1"',
        f'localPort = {cfg["local_port"]}',
        f'remotePort = {remote_port}',
    ]
    FRP_DIR.mkdir(parents=True, exist_ok=True)
    FRP_CONF.write_text("\n".join(conf_lines) + "\n", encoding="utf-8")
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    logfile = open(LOG_DIR / "frp.log", "ab")
    flags = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
    global FRP_PROC
    with FRP_PROC_LOCK:
        FRP_PROC = subprocess.Popen([str(FRP_EXE), "-c", str(FRP_CONF)],
                                    cwd=str(FRP_DIR), stdout=logfile, stderr=subprocess.STDOUT,
                                    stdin=subprocess.DEVNULL, creationflags=flags)
    _note(job, f"frpc 已启动（PID {FRP_PROC.pid}），日志：logs/frp.log")
    return {"ok": True, "pid": FRP_PROC.pid,
            "public": f"{cfg['server']}:{remote_port}",
            "log": str(LOG_DIR / "frp.log")}


def stop_frp() -> dict:
    with FRP_PROC_LOCK:
        global FRP_PROC
        if FRP_PROC is not None and FRP_PROC.poll() is None:
            FRP_PROC.terminate()
            try:
                FRP_PROC.wait(timeout=5)
            except subprocess.TimeoutExpired:
                FRP_PROC.kill()
            FRP_PROC = None
            return {"ok": True, "stopped": True}
        FRP_PROC = None
        return {"ok": True, "stopped": False}


# --------------------------------------------------------------------------- #
# 陶瓦联机（Terracotta，基于 EasyTier 的 P2P 联机）
# --------------------------------------------------------------------------- #

TC_PROC: subprocess.Popen | None = None
TC_PROC_LOCK = threading.Lock()


def _sha512_file(p: Path) -> str:
    h = hashlib.sha512()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def terracotta_status() -> dict:
    exe_ok = TERRACOTTA_EXE.exists()
    dll_ok = (TERRACOTTA_DIR / "VCRUNTIME140.DLL").exists()
    running = TC_PROC is not None and TC_PROC.poll() is None
    return {
        "installed": exe_ok,
        "complete": exe_ok and dll_ok,
        "version": TERRACOTTA_VER,
        "dir": str(TERRACOTTA_DIR),
        "running": running,
        "pid": TC_PROC.pid if running else None,
    }


def install_terracotta(job=None) -> dict:
    """下载陶瓦联机包（gitee 等国内镜像优先）→ 解压 → SHA-512 校验。"""
    if terracotta_status()["complete"]:
        _note(job, "陶瓦联机已就绪，无需重复下载")
        return {"ok": True, "already": True, "version": TERRACOTTA_VER}
    _note(job, f"正在下载陶瓦联机 v{TERRACOTTA_VER}（国内镜像）…")
    data, _ = fetch_bytes(TERRACOTTA_URLS, timeout=300, retries=1)
    TERRACOTTA_DIR.mkdir(parents=True, exist_ok=True)
    pkg = TERRACOTTA_DIR / ("_" + TERRACOTTA_PKG_NAME)
    pkg.write_bytes(data)
    try:
        with tarfile.open(pkg, "r:gz") as tf:
            for m in tf.getmembers():
                if m.isfile():
                    base = os.path.basename(m.name)
                    if base in TERRACOTTA_FILES:
                        out = TERRACOTTA_DIR / base
                        src = tf.extractfile(m)
                        with open(out, "wb") as dst:
                            shutil.copyfileobj(src, dst)  # type: ignore[arg-type]
        for name, expect in TERRACOTTA_FILES.items():
            p = TERRACOTTA_DIR / name
            if not p.exists():
                raise RuntimeError(f"陶瓦联机包缺少文件 {name}")
            actual = _sha512_file(p)
            if actual.lower() != expect.lower():
                raise RuntimeError(f"{name} SHA-512 校验失败（下载可能损坏），请重试")
    finally:
        pkg.unlink(missing_ok=True)
    _note(job, "陶瓦联机安装完成（SHA-512 校验通过）")
    return {"ok": True, "version": TERRACOTTA_VER}


def launch_terracotta(job=None) -> dict:
    """启动陶瓦联机图形界面（房主创建房间 / 房客输房间码加入）。

    HMCL 深度集成会传 `--hmcl <IPC文件>`；独立使用直接启动 GUI 即可。
    """
    if not terracotta_status()["complete"]:
        install_terracotta(job)
    global TC_PROC
    with TC_PROC_LOCK:
        if TC_PROC is not None and TC_PROC.poll() is None:
            return {"ok": True, "pid": TC_PROC.pid, "already": True}
        flags = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
        TC_PROC = subprocess.Popen([str(TERRACOTTA_EXE)], cwd=str(TERRACOTTA_DIR), creationflags=flags)
    _note(job, f"陶瓦联机已启动（PID {TC_PROC.pid}）")
    return {"ok": True, "pid": TC_PROC.pid}


# --------------------------------------------------------------------------- #
# 模组加载器安装（Fabric / Quilt / Legacy Fabric / Forge / NeoForge）
# --------------------------------------------------------------------------- #

NEOFORGE_MAVEN = "https://maven.neoforged.net/releases"


def _maven_metadata(group_path: str, mirror: str) -> list:
    """读 maven-metadata.xml 的版本列表（先镜像后官方）。"""
    base = mirror_base(mirror)
    urls = []
    if base:
        urls.append(f"{base}/maven/{group_path}/maven-metadata.xml")
    urls.append(f"{NEOFORGE_MAVEN}/{group_path}/maven-metadata.xml")
    raw, _ = fetch_bytes(urls, timeout=40)
    return re.findall(r"<version>([^<]+)</version>", raw.decode("utf-8", "replace"))


def loader_versions(mc: str, loader: str, mirror: str = "bmcl") -> list:
    info = LOADERS.get(loader)
    if not info:
        raise ValueError(f"不支持的加载器：{loader}")
    if info["kind"] == "meta":
        try:
            data = fetch_json([f"{info['meta']}/versions/loader/{quote(mc)}"])
        except FetchError as exc:
            # meta 对不支持的 MC 版本回 400/404（比如 Legacy Fabric 只有老版本），当成「没有」而不是报错
            if "400" in str(exc) or "404" in str(exc):
                return []
            raise
        out = []
        for it in data:
            l = it.get("loader") or {}
            if l.get("version"):
                out.append({"version": l["version"], "stable": bool(l.get("stable"))})
        return out
    if loader == "forge":
        promos = fetch_json([FORGE_PROMO]).get("promos", {})
        out = []
        rec = promos.get(f"{mc}-recommended")
        latest = promos.get(f"{mc}-latest")
        if rec:
            out.append({"version": rec, "stable": True})
        if latest and latest != rec:
            out.append({"version": latest, "stable": False})
        return out
    if loader == "neoforge":
        if mc == "1.20.1":
            # 1.20.1 那代还是 net.neoforged:forge，版本号形如 1.20.1-47.1.106
            vs = _maven_metadata("net/neoforged/forge", mirror)
            out = [{"version": v.split("-", 1)[1], "stable": "beta" not in v.lower()}
                   for v in vs if v.startswith("1.20.1-")]
        else:
            # NeoForge 版本号跟 MC 走，但历史上有两套写法：
            #   1.21.1 → 21.1.x（去掉开头的 "1."），1.20.6 → 20.6.x
            #   26.3   → 26.3.0.x（新命名直接照抄）
            parts = mc.split(".")
            cands = []
            if parts[0] == "1" and len(parts) >= 2:
                patch = parts[2] if len(parts) > 2 else "0"
                cands.append(f"{parts[1]}.{patch}.")
            cands.append(f"{mc}.")
            vs = _maven_metadata("net/neoforged/neoforge", mirror)
            out = []
            for pre in cands:
                out = [{"version": v, "stable": "beta" not in v.lower()}
                       for v in vs if v.startswith(pre)]
                if out:
                    break
        out.reverse()   # metadata 是升序，翻过来新的在前
        return out
    raise ValueError(f"不支持的加载器：{loader}")


def _first_stable(items):
    for it in items:
        if it.get("stable"):
            return it["version"]
    return items[0]["version"] if items else ""


def install_loader(mirror: str, mc: str, loader: str, loader_ver: str = "", job: OpJob = None) -> dict:
    """装加载器，返回 {id, loader, loaderVersion}。

    Fabric / Quilt / Legacy Fabric 走 meta 的 profile json；
    Forge / NeoForge 下载官方 installer 跑 --installClient。
    """
    info = LOADERS.get(loader)
    if not info:
        raise ValueError(f"不支持的加载器：{loader}")
    _note(job, f"准备安装 {info['label']} 到 Minecraft {mc}")

    if info["kind"] == "meta":
        ver = loader_ver
        if not ver:
            items = loader_versions(mc, loader, mirror)
            if not items:
                raise RuntimeError(f"{info['label']} 没有适配 {mc} 的版本")
            ver = _first_stable(items)
        _note(job, f"使用 {info['label']} {ver}，正在获取 profile…")
        prof = fetch_json([f"{info['meta']}/versions/loader/{quote(mc)}/{quote(ver)}/profile/json"])
        vid = prof.get("id") or f"{loader}-loader-{ver}-{mc}"
        prof["id"] = vid
        prof["_loader"] = loader
        prof["_loader_version"] = ver
        if not prof.get("inheritsFrom"):
            prof["inheritsFrom"] = mc
        save_version_json(vid, prof)
        _VJ_CACHE.clear()
        _note(job, f"已写入 versions/{vid}/{vid}.json")
        # 加载器自己的库（fabric-loader / mixin 等）顺手补上，省得用户还要再点一次「下载所选」
        try:
            vj = resolve_version(mirror, vid)
            tasks = build_plan(vj, mirror, ["libraries"], False)
            if tasks:
                _download_tasks(tasks, job, 8, f"{info['label']} 依赖库")
        except Exception as exc:  # noqa: BLE001
            _note(job, f"依赖库补齐失败（可稍后在版本页点下载）：{exc}")
        return {"id": vid, "loader": loader, "loaderVersion": ver, "base": mc}

    return _install_via_installer(mirror, mc, loader, loader_ver, job)


def _note(job, msg: str):
    if job:
        job.note(msg)
    else:
        log(msg)


def _download_tasks(tasks, job, workers: int = 8, label: str = "依赖库") -> int:
    """给装加载器用的小下载器：并发拉取，进度写进 job 的日志（job 为空就打印）。"""
    if not tasks:
        return 0
    _note(job, f"补齐{label}：{len(tasks)} 个文件")
    done = [0]
    errors = []
    lock = threading.Lock()

    def one(t: Task):
        if t.dest.exists() and ((t.size and t.dest.stat().st_size == t.size) or not t.size):
            with lock:
                done[0] += 1
            return
        t.dest.parent.mkdir(parents=True, exist_ok=True)
        raw, _ = fetch_bytes(t.urls, timeout=180, retries=1)
        t.dest.write_bytes(raw)
        with lock:
            done[0] += 1
            if done[0] % 5 == 0:
                _note(job, f"  {label} {done[0]}/{len(tasks)}")

    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(one, t) for t in tasks]
        for f in as_completed(futs):
            try:
                f.result()
            except Exception as exc:  # noqa: BLE001
                errors.append(str(exc))
    if errors:
        _note(job, f"  {len(errors)} 个文件失败，可稍后在版本页点「下载所选」重试")
    else:
        _note(job, f"  {label}就绪（{len(tasks)} 个）")
    return len(errors)


def _read_install_profile(installer: Path) -> dict:
    try:
        with zipfile.ZipFile(installer) as z:
            return json.loads(z.read("install_profile.json").decode("utf-8"))
    except Exception:  # noqa: BLE001
        return {}


def _preseed_installer_libs(installer: Path, mirror: str, job) -> None:
    """先把安装器自己要用的库下好（走镜像回退）。

    Forge / NeoForge 安装器自己下载库经常失败（国内直连 maven.minecraftforge.net /
    maven.neoforged.net 基本不通），一失败就整包中止，连反混淆都不跑，最后缺
    client-srg.jar 而启动不了。提前喂给它就不会翻车。

    要喂两批：install_profile.json 的（跑 processors 用的）+ version.json 的
    （装到 libraries 里给游戏用的），少一批安装器都会报 "These libraries failed to download"。
    """
    prof = _read_install_profile(installer)
    libs = list(prof.get("libraries") or [])
    try:
        with zipfile.ZipFile(installer) as z:
            vp = str(prof.get("json") or "").lstrip("/")
            if vp and vp in z.namelist():
                libs += json.loads(z.read(vp).decode("utf-8")).get("libraries") or []
    except Exception:  # noqa: BLE001
        pass
    seen, tasks = set(), []
    for lib in libs:
        try:
            entries = lib_files(lib)
        except Exception:  # noqa: BLE001
            continue
        for rel, offs, sha1, size, _nat in entries:
            if rel in seen:
                continue
            seen.add(rel)
            tasks.append(Task(url_library(mirror, rel, offs[0] if offs else ""),
                              LIBRARIES_DIR / rel, sha1, size))
    if tasks:
        _download_tasks(tasks, job, 8, "安装器依赖")


def _installer_rel_path(mc: str, loader: str, ver: str):
    """返回 (maven 相对路径, 官方源基址, 猜的版本目录名)。"""
    if loader == "forge":
        full = f"{mc}-{ver}"
        return (f"net/minecraftforge/forge/{full}/forge-{full}-installer.jar",
                "https://maven.minecraftforge.net", f"{mc}-forge-{ver}")
    if mc == "1.20.1":
        # NeoForge 在 1.20.1 上还是 net.neoforged:forge 这条线
        full = f"{mc}-{ver}"
        return (f"net/neoforged/forge/{full}/forge-{full}-installer.jar",
                NEOFORGE_MAVEN, f"{mc}-neoforge-{ver}")
    return (f"net/neoforged/neoforge/{ver}/neoforge-{ver}-installer.jar",
            NEOFORGE_MAVEN, f"neoforge-{ver}")


def _install_via_installer(mirror: str, mc: str, loader: str, ver: str = "", job: OpJob = None) -> dict:
    label = LOADERS[loader]["label"]
    if not ver:
        items = loader_versions(mc, loader, mirror)
        if not items:
            raise RuntimeError(f"{label} 没有适配 {mc} 的版本")
        ver = _first_stable(items)
    rel, official_base, _vid_guess = _installer_rel_path(mc, loader, ver)
    urls = url_library(mirror, rel, f"{official_base}/{rel}")
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    installer = CACHE_DIR / Path(rel).name
    if not installer.exists() or installer.stat().st_size < 100000:
        _note(job, f"下载 {label} 安装器：{Path(rel).name}")
        raw, _ = fetch_bytes(urls, timeout=300, retries=2)
        installer.write_bytes(raw)
    _note(job, f"安装器已就绪（{human_size(installer.stat().st_size)}），执行 --installClient（可能要几分钟）")
    prof = _read_install_profile(installer)
    _preseed_installer_libs(installer, mirror, job)

    # 安装器要拿原版 version json + client.jar 来打补丁，缺了它自己会去 piston 下（国内常失败），先替它备好
    req_java = 17
    try:
        base = resolve_version(mirror, mc)
        req_java = int(((base.get("javaVersion") or {}).get("majorVersion")) or 17)
        jar_id = base.get("_jar_id") or mc
        jar = VERSIONS_DIR / jar_id / f"{jar_id}.jar"
        if not jar.exists():
            _note(job, "先补下原版客户端核心（安装器要用它打补丁）")
            _download_tasks(build_plan(base, mirror, ["client"], False), job, 4, "客户端核心")
    except Exception as exc:  # noqa: BLE001
        _note(job, f"原版核心检查失败（安装器可能会自己下）：{exc}")

    # 安装器自己也要能跑：老版本要 17，26.x 要 25
    java = pick_java(req_java) or pick_java(17) or pick_java(8)
    if not java:
        raise RuntimeError("未找到 Java，无法运行安装器")
    jmaj = java_major(java)
    if jmaj and jmaj < req_java:
        _note(job, f"注意：{label} 建议 Java {req_java}+，当前只有 Java {jmaj}，安装可能失败")
    GAME_DIR.mkdir(parents=True, exist_ok=True)
    # 安装器要求目标目录里存在 launcher_profiles.json（官方启动器才会生成），缺了会直接报错退出
    profiles = GAME_DIR / "launcher_profiles.json"
    if not profiles.exists():
        profiles.write_text(json.dumps({
            "profiles": {}, "selectedProfile": "", "clientToken": "",
            "authenticationDatabase": {},
            "launcherVersion": {"name": "MCLauncher", "format": 21},
        }, ensure_ascii=False), encoding="utf-8")
    before = {p.name for p in VERSIONS_DIR.iterdir() if p.is_dir()} if VERSIONS_DIR.exists() else set()
    flags = subprocess.CREATE_NO_WINDOW if IS_WIN else 0
    # 关键：必须显式给出目标目录。NeoForge / Forge 安装器不认 cwd，
    # 会去 %APPDATA%\.minecraft（Linux 是 ~/.minecraft），不传就装到别处去了。
    target = str(GAME_DIR.resolve())
    _note(job, f"安装目标：{target}")
    proc = subprocess.run([java, "-jar", str(installer), "--installClient", target],
                          cwd=target, capture_output=True, text=True,
                          timeout=1800, creationflags=flags,
                          encoding="utf-8", errors="replace")
    tail = ((proc.stdout or "") + (proc.stderr or "")).strip().splitlines()[-8:]
    for line in tail:
        _note(job, line[:200])
    # 安装器会在 cwd 留一个 <jar>.log，挪到 logs/ 里方便排查
    try:
        ilog = GAME_DIR / f"{installer.name}.log"
        if ilog.exists():
            LOG_DIR.mkdir(parents=True, exist_ok=True)
            shutil.move(str(ilog), str(LOG_DIR / f"{loader}-install.log"))
    except Exception:  # noqa: BLE001
        pass

    # 认安装器产出的版本目录：优先用 install_profile 里写明的 id（最准），
    # 其次才看这次新冒出来的目录。任何情况下都不碰别的加载器的目录。
    expected = str(prof.get("version") or "").strip()
    found = ""
    created = []
    if VERSIONS_DIR.exists():
        created = [p for p in VERSIONS_DIR.iterdir() if p.is_dir() and p.name not in before]
    order = []
    if expected:
        order.append(VERSIONS_DIR / expected)
    order += [d for d in created if d.name != expected]
    for d in order:
        jp = d / f"{d.name}.json"
        if not jp.exists():
            continue
        try:
            meta = json.loads(jp.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            continue
        if meta.get("inheritsFrom") != mc:
            continue
        # 已被别的加载器占用的目录（比如老 Forge 的 1.20.1-forge-47.4.28）绝不改写
        if detect_loader(meta) not in ("", loader):
            continue
        found = d.name
        break
    if not found:
        hint = "；".join(tail[-3:]) if tail else "无输出"
        raise RuntimeError(f"{label} 安装器没有产出可用的版本文件（{hint}）")

    p = VERSIONS_DIR / found / f"{found}.json"
    meta = json.loads(p.read_text(encoding="utf-8"))
    meta["_loader"] = loader
    meta["_loader_version"] = ver
    p.write_text(json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8")
    _VJ_CACHE.clear()
    _note(job, f"{label} 版本已生成：versions/{found}")
    srg = list((LIBRARIES_DIR / "net" / "minecraft" / "client").glob("*/client-*-srg.jar")) \
        if (LIBRARIES_DIR / "net" / "minecraft" / "client").exists() else []
    if not srg:
        _note(job, "注意：没找到 client-srg.jar，反混淆步骤可能没跑成功，启动会报 Invalid paths")
    # 安装器偶尔会有几个库拉不下来（网络抖动），用我们自己的镜像回退再补一遍
    try:
        vj = resolve_version(mirror, found)
        tasks = build_plan(vj, mirror, ["libraries"], False)
        _download_tasks(tasks, job, 8, f"{label} 依赖库")
    except Exception as exc:  # noqa: BLE001
        _note(job, f"依赖库补齐失败（可稍后在版本页点下载）：{exc}")
    _note(job, f"{label} 安装完成")
    return {"id": found, "loader": loader, "loaderVersion": ver, "base": mc}


# --------------------------------------------------------------------------- #
# Modrinth 模组
# --------------------------------------------------------------------------- #

def _q(params: dict) -> str:
    return urlencode({k: v for k, v in params.items() if v not in (None, "")})


def modrinth_search(query: str, loader: str, mc: str, offset: int = 0, limit: int = 20,
                    sort: str = "relevance") -> dict:
    facets = [["project_type:mod"]]
    if loader:
        facets.append([f"categories:{loader}"])
    if mc:
        facets.append([f"versions:{mc}"])
    params = {
        "query": query or "",
        "limit": limit,
        "offset": offset,
        "index": sort if sort in ("relevance", "downloads", "follows", "newest", "updated") else "relevance",
        "facets": json.dumps(facets, separators=(",", ":")),
    }
    data = fetch_json([f"{MODRINTH_API}/search?" + _q(params)], timeout=30)
    hits = []
    for h in data.get("hits", []):
        hits.append({
            "id": h.get("project_id"),
            "slug": h.get("slug"),
            "title": h.get("title"),
            "author": h.get("author"),
            "description": h.get("description"),
            "downloads": h.get("downloads", 0),
            "icon": h.get("icon_url") or "",
            "categories": (h.get("categories") or [])[:4],
            "versions": h.get("versions") or [],
        })
    return {"hits": hits, "total": data.get("total_hits", len(hits))}


def modrinth_versions(project_id: str, loader: str, mc: str) -> list:
    params = {}
    if loader:
        params["loaders"] = json.dumps([loader])
    if mc:
        params["game_versions"] = json.dumps([mc])
    url = f"{MODRINTH_API}/project/{quote(project_id)}/version"
    if params:
        url += "?" + _q(params)
    return fetch_json([url], timeout=30)


def mod_loader_name(loader: str) -> str:
    """Modrinth 的加载器名（Legacy Fabric 的模组在 Modrinth 上标的是 fabric）。"""
    return LOADERS.get(loader, {}).get("modrinth", loader)


def install_mod(vid: str, project_id: str, job: OpJob = None) -> list:
    """把某个模组装到 vid 这个实例的 mods 目录，并递归补装 required 前置。"""
    vj = resolve_version(load_config().get("mirror", "bmcl"), vid)
    loader = vj.get("_loader") or ""
    mc = vj.get("_base_id") or vj["id"]
    if not loader:
        raise RuntimeError("这个版本没有模组加载器，请先安装 Fabric / Quilt / Legacy Fabric / Forge / NeoForge")
    mods_dir(vid).mkdir(parents=True, exist_ok=True)
    out = []
    visited = set()
    ml = mod_loader_name(loader)

    def one(pid: str, depth: int):
        if not pid or pid in visited or depth > 2 or len(visited) > 12:
            return
        visited.add(pid)
        vers = modrinth_versions(pid, ml, mc)
        if not vers:
            raise RuntimeError(f"{pid} 没有适配 {mc} + {ml} 的文件")
        v = vers[0]
        files = [f for f in v.get("files", []) if f.get("primary")] or v.get("files", [])
        if not files:
            raise RuntimeError("该版本没有可下载文件")
        f = files[0]
        name = f.get("filename") or f"{pid}.jar"
        dest = mods_dir(vid) / name
        if not dest.exists():
            if job:
                job.note(f"下载 {name}（{human_size(f.get('size') or 0)}）")
            urls = [f["url"]]
            mir = (load_config().get("mod_mirror") or "").rstrip("/")
            if mir:
                urls.append(mir + urlparse(f["url"]).path)
            try:
                raw, _ = fetch_bytes(urls, timeout=180, retries=2)
            except FetchError as exc:
                raise RuntimeError(
                    f"下载 {name} 失败：{exc}。cdn.modrinth.com 在国内经常连不上，"
                    f"可在 launcher.json 里设置 mod_mirror 指向加速镜像后重试")
            dest.write_bytes(raw)
        else:
            if job:
                job.note(f"{name} 已存在，跳过")
        out.append({"file": name, "size": f.get("size") or 0, "project": pid,
                    "title": v.get("name") or name})
        for dep in v.get("dependencies") or []:
            if dep.get("dependency_type") == "required" and dep.get("project_id"):
                one(dep["project_id"], depth + 1)

    one(project_id, 0)
    return out


def installed_mods(vid: str) -> list:
    d = mods_dir(vid)
    if not d.exists():
        return []
    items = []
    for p in sorted(d.glob("*.jar"), key=lambda x: x.name.lower()):
        st = p.stat()
        items.append({"file": p.name, "size": st.st_size,
                      "time": time.strftime("%Y-%m-%d %H:%M", time.localtime(st.st_mtime))})
    return items


# --------------------------------------------------------------------------- #
# 配置
# --------------------------------------------------------------------------- #

def load_config() -> dict:
    cfg = dict(DEFAULT_CONFIG)
    try:
        if CONFIG_FILE.exists():
            cfg.update(json.loads(CONFIG_FILE.read_text(encoding="utf-8")))
    except Exception:  # noqa: BLE001
        pass
    return cfg


def save_config(cfg: dict) -> None:
    merged = dict(DEFAULT_CONFIG)
    merged.update(load_config())          # 保留界面上没暴露的键（例如 mod_mirror）
    merged.update({k: v for k, v in cfg.items() if v is not None})
    CONFIG_FILE.write_text(json.dumps(merged, ensure_ascii=False, indent=2), encoding="utf-8")


# --------------------------------------------------------------------------- #
# 任务注册表
# --------------------------------------------------------------------------- #

JOBS: dict = {}
JOBS_LOCK = threading.Lock()


def _register(job):
    with JOBS_LOCK:
        for old in list(JOBS):
            if JOBS[old].status in ("done", "error", "cancelled"):
                JOBS.pop(old, None)
        JOBS[job.id] = job
    return job


def start_download(vid: str, mirror: str, components, skip_sounds: bool, workers: int, verify: bool) -> DownloadJob:
    vj = resolve_version(mirror, vid)
    comps = [c for c in components if c in ("client", "libraries", "assets", "logging")]
    if not comps:
        raise ValueError("请至少选择一个下载组件")
    tasks = build_plan(vj, mirror, comps, skip_sounds)
    job = _register(DownloadJob(vid, mirror, tasks, workers=workers, verify=verify))
    job.start()
    return job


# --------------------------------------------------------------------------- #
# HTTP 服务
# --------------------------------------------------------------------------- #

class Api:
    @staticmethod
    def versions(q):
        mirror = q.get("mirror", ["bmcl"])[0]
        if mirror not in MIRRORS:
            mirror = "bmcl"
        if q.get("refresh"):
            _MANIFEST_CACHE.pop(mirror, None)
        man = get_manifest(mirror)
        items = [{"id": v["id"], "type": v.get("type", ""), "releaseTime": v.get("releaseTime", ""),
                  "local": False} for v in man.get("versions", [])]
        known = {i["id"] for i in items}
        for loc in list_local_versions():
            if loc["id"] in known:
                for i in items:
                    if i["id"] == loc["id"]:
                        i["local"] = True
                        break
            else:
                items.insert(0, {"id": loc["id"], "type": "modded",
                                 "releaseTime": "", "local": True,
                                 "loader": loc.get("loader", ""),
                                 "loaderVersion": loc.get("loaderVersion", "")})
        return {"versions": items, "latest": man.get("latest", {}), "source": MIRRORS[mirror]["label"]}

    @staticmethod
    def version(q):
        vid = q.get("id", [""])[0]
        mirror = q.get("mirror", ["bmcl"])[0]
        if not vid:
            raise ValueError("缺少版本 id")
        vj = resolve_version(mirror, vid)
        stats = plan_stats(vj, mirror, skip_sounds=False)
        jar_id = vj.get("_jar_id") or vid
        jar = VERSIONS_DIR / jar_id / f"{jar_id}.jar"
        req_java = int(((vj.get("javaVersion") or {}).get("majorVersion")) or 8)
        return {
            "id": vj.get("id", vid),
            "baseId": vj.get("_base_id", vid),
            "loader": vj.get("_loader", ""),
            "loaderLabel": LOADER_LABEL.get(vj.get("_loader", ""), ""),
            "loaderVersion": vj.get("_loader_version", ""),
            "type": vj.get("type", ""),
            "typeLabel": TYPE_LABEL.get(vj.get("type", ""), "模组版" if vj.get("_loader") else ""),
            "releaseTime": vj.get("releaseTime", ""),
            "javaVersion": req_java,
            "mainClass": vj.get("mainClass", ""),
            "components": stats,
            "installed": jar.exists(),
            "jarSize": jar.stat().st_size if jar.exists() else 0,
            "gameDir": str(instance_dir(vj.get("id", vid))),
            "mods": len(installed_mods(vj.get("id", vid))),
        }

    @staticmethod
    def instances(q):
        out = []
        for loc in list_local_versions():
            out.append(loc)
        return {"list": out}

    @staticmethod
    def java(q):
        return {"list": find_javas()}

    @staticmethod
    def settings(q):
        return {"config": load_config(),
                "mirrors": [{"key": k, "label": v["label"]} for k, v in MIRRORS.items()],
                "loaders": [{"key": k, "label": v["label"], "note": v.get("note", "")}
                            for k, v in LOADERS.items()]}

    @staticmethod
    def loaders(q):
        mc = q.get("mc", [""])[0]
        loader = q.get("loader", ["fabric"])[0]
        if not mc:
            raise ValueError("缺少 mc 参数")
        items = loader_versions(mc, loader, load_config().get("mirror", "bmcl"))
        return {"loader": loader, "versions": items, "recommended": _first_stable(items) if items else ""}

    @staticmethod
    def download(body):
        vid = body.get("id") or ""
        mirror = body.get("mirror") or "bmcl"
        comps = body.get("components") or []
        cfg = load_config()
        job = start_download(vid, mirror, comps, bool(body.get("skipSounds")),
                             int(body.get("workers") or cfg.get("workers") or 16),
                             bool(body.get("verify")))
        return {"job": job.id, "total": job.total_bytes, "files": job.total_files}

    @staticmethod
    def cancel(body):
        job = JOBS.get(body.get("job") or "")
        if job:
            job.stop.set()
            return {"ok": True}
        return {"ok": False, "error": "任务不存在"}

    @staticmethod
    def launch(body):
        vid = body.get("id") or ""
        mirror = body.get("mirror") or "bmcl"
        cfg = load_config()
        username = body.get("username") or cfg.get("username") or "Steve"
        memory = int(body.get("memory") or cfg.get("memory") or 2048)
        java = body.get("java") or cfg.get("java") or ""
        server = (body.get("server") or "").strip()
        try:
            port = int(body.get("port") or 25565)
        except (TypeError, ValueError):
            port = 25565
        authlib = (body.get("authlib") or "").strip()
        vj = resolve_version(mirror, vid)
        proc = launch_game(vj, username, memory, java,
                           server=server, server_port=port, authlib=authlib)
        return {"ok": True, "pid": proc.pid, "log": str(LOG_DIR / "latest.log"), "server": server}

    @staticmethod
    def install_loader(body):
        mc = body.get("mc") or ""
        loader = body.get("loader") or "fabric"
        ver = body.get("version") or ""
        mirror = body.get("mirror") or "bmcl"
        if not mc:
            raise ValueError("缺少 Minecraft 版本")
        job = _register(OpJob(f"安装 {LOADER_LABEL.get(loader, loader)} 到 {mc}"))
        job.run(lambda j: install_loader(mirror, mc, loader, ver, j))
        return {"job": job.id}

    @staticmethod
    def java_install(body):
        major = int(body.get("major") or 17)
        job = _register(OpJob(f"下载 Java {major}"))

        def work(j):
            r = install_java(major, j)
            j.message = f"Java {r['major']} 已就绪"
            return r

        job.run(work)
        return {"job": job.id}

    @staticmethod
    def mods_search(q):
        vid = q.get("vid", [""])[0]
        query = q.get("q", [""])[0]
        offset = int(q.get("offset", ["0"])[0] or 0)
        sort = q.get("sort", ["relevance"])[0]
        loader, mc = "", ""
        if vid:
            vj = resolve_version(load_config().get("mirror", "bmcl"), vid)
            loader = vj.get("_loader") or ""
            mc = vj.get("_base_id") or vj["id"]
        data = modrinth_search(query, mod_loader_name(loader), mc, offset=offset, sort=sort)
        data.update({"loader": loader, "mc": mc, "offset": offset})
        return data

    @staticmethod
    def mods_install(body):
        vid = body.get("vid") or ""
        project = body.get("project") or ""
        if not vid or not project:
            raise ValueError("缺少参数")
        job = _register(OpJob("安装模组"))
        job.run(lambda j: install_mod(vid, project, j))
        return {"job": job.id}

    @staticmethod
    def mods_installed(q):
        vid = q.get("vid", [""])[0]
        return {"list": installed_mods(vid), "dir": str(mods_dir(vid))}

    @staticmethod
    def mods_delete(body):
        vid = body.get("vid") or ""
        name = os.path.basename(body.get("file") or "")
        if not vid or not name:
            raise ValueError("缺少参数")
        p = mods_dir(vid) / name
        if p.exists() and p.suffix.lower() == ".jar":
            p.unlink()
            return {"ok": True}
        return {"ok": False, "error": "文件不存在"}

    @staticmethod
    def servers(q):
        return {"list": load_config().get("servers") or []}

    @staticmethod
    def server_save(body):
        cfg = load_config()
        servers = list(cfg.get("servers") or [])
        idx = body.get("index")
        name = (body.get("name") or "").strip()
        address = (body.get("address") or "").strip()
        try:
            port = int(body.get("port") or 25565)
        except (TypeError, ValueError):
            port = 25565
        if not 1 <= port <= 65535:
            raise ValueError("端口必须在 1~65535 之间")
        authlib = (body.get("authlib") or "").strip()
        if authlib and not re.match(r"^https?://", authlib):
            raise ValueError("第三方登录 API 必须以 http(s):// 开头")
        if not address:
            raise ValueError("服务器地址不能为空")
        item = {
            "name": name or address,
            "address": address,
            "port": port,
            "authlib": authlib,
            "note": (body.get("note") or "").strip(),
        }
        if isinstance(idx, int) and 0 <= idx < len(servers):
            servers[idx] = item
        else:
            servers.append(item)
        save_config({"servers": servers})
        return {"ok": True, "list": servers}

    @staticmethod
    def server_delete(body):
        cfg = load_config()
        servers = list(cfg.get("servers") or [])
        idx = body.get("index")
        if not isinstance(idx, int) or not 0 <= idx < len(servers):
            raise ValueError("服务器不存在")
        removed = servers.pop(idx)
        save_config({"servers": servers})
        return {"ok": True, "name": removed.get("name", "")}

    # ---- frp 内网穿透 ----
    @staticmethod
    def frp_info(q):
        return frp_status()

    @staticmethod
    def frp_start(body):
        cfg = frp_config()
        if (body.get("server") or "").strip():
            cfg["server"] = (body.get("server") or "").strip()
        cfg["port"] = int(body.get("port") or cfg["port"] or 7000)
        cfg["token"] = body.get("token") or ""
        cfg["local_port"] = int(body.get("local_port") or cfg["local_port"] or 25565)
        cfg["remote_port"] = int(body.get("remote_port") or 0)
        save_config({"frp": cfg})
        job = _register(OpJob("启动 frp 内网穿透"))
        job.run(lambda j: start_frp(j))
        return {"job": job.id}

    @staticmethod
    def frp_stop(body):
        return stop_frp()

    # ---- 陶瓦联机（Terracotta） ----
    @staticmethod
    def tc_info(q):
        return terracotta_status()

    @staticmethod
    def tc_install(body):
        job = _register(OpJob("下载陶瓦联机"))
        job.run(lambda j: install_terracotta(j))
        return {"job": job.id}

    @staticmethod
    def tc_launch(body):
        job = _register(OpJob("启动陶瓦联机"))
        job.run(lambda j: launch_terracotta(j))
        return {"job": job.id}

    @staticmethod
    def log_tail(q):
        p = LOG_DIR / "latest.log"
        if not p.exists():
            return {"text": "还没有启动过游戏。"}
        try:
            return {"text": p.read_bytes()[-8000:].decode("utf-8", "replace")}
        except Exception:  # noqa: BLE001
            return {"text": "读取日志失败"}


class Handler(BaseHTTPRequestHandler):
    server_version = f"MCLauncher/{APP_VER}"
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):  # 静音访问日志
        pass

    # ---- 工具 ----
    def _json(self, obj, code=200):
        raw = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def _html(self, text: str):
        raw = text.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")   # 防止浏览器缓存旧版页面
        self.end_headers()
        self.wfile.write(raw)

    def _body(self) -> dict:
        try:
            n = int(self.headers.get("Content-Length") or 0)
            if not n:
                return {}
            return json.loads(self.rfile.read(n).decode("utf-8"))
        except Exception:  # noqa: BLE001
            return {}

    # ---- GET ----
    def do_GET(self):  # noqa: N802
        parsed = urlparse(self.path)
        path = parsed.path
        q = parse_qs(parsed.query)
        try:
            if path in ("/", "/index.html"):
                return self._html(PAGE)
            if path == "/api/versions":
                return self._json(Api.versions(q))
            if path == "/api/version":
                return self._json(Api.version(q))
            if path == "/api/instances":
                return self._json(Api.instances(q))
            if path == "/api/java":
                return self._json(Api.java(q))
            if path == "/api/settings":
                return self._json(Api.settings(q))
            if path == "/api/loaders":
                return self._json(Api.loaders(q))
            if path == "/api/mods/search":
                return self._json(Api.mods_search(q))
            if path == "/api/mods/installed":
                return self._json(Api.mods_installed(q))
            if path == "/api/servers":
                return self._json(Api.servers(q))
            if path == "/api/frp/status":
                return self._json(Api.frp_info(q))
            if path == "/api/terracotta/status":
                return self._json(Api.tc_info(q))
            if path == "/api/log":
                return self._json(Api.log_tail(q))
            if path == "/api/progress":
                return self._sse(q.get("job", [""])[0])
            if path == "/favicon.ico":
                self.send_response(204)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            return self._json({"error": "not found"}, 404)
        except Exception as exc:  # noqa: BLE001
            return self._json({"error": str(exc)}, 500)

    # ---- POST ----
    def do_POST(self):  # noqa: N802
        path = urlparse(self.path).path
        body = self._body()
        try:
            if path == "/api/download":
                return self._json(Api.download(body))
            if path == "/api/cancel":
                return self._json(Api.cancel(body))
            if path == "/api/launch":
                return self._json(Api.launch(body))
            if path == "/api/install_loader":
                return self._json(Api.install_loader(body))
            if path == "/api/java_install":
                return self._json(Api.java_install(body))
            if path == "/api/mods/install":
                return self._json(Api.mods_install(body))
            if path == "/api/mods/delete":
                return self._json(Api.mods_delete(body))
            if path == "/api/server_save":
                return self._json(Api.server_save(body))
            if path == "/api/server_delete":
                return self._json(Api.server_delete(body))
            if path == "/api/frp/start":
                return self._json(Api.frp_start(body))
            if path == "/api/frp/stop":
                return self._json(Api.frp_stop(body))
            if path == "/api/terracotta/install":
                return self._json(Api.tc_install(body))
            if path == "/api/terracotta/launch":
                return self._json(Api.tc_launch(body))
            if path == "/api/settings":
                save_config(body.get("config") or {})
                return self._json({"ok": True, "config": load_config()})
            if path == "/api/open":
                target = body.get("path") or ""
                p = (BASE_DIR / target).resolve()
                if BASE_DIR not in p.parents and p != BASE_DIR:
                    return self._json({"error": "路径不合法"}, 400)
                p.mkdir(parents=True, exist_ok=True)
                if IS_WIN:
                    os.startfile(str(p))  # noqa: S606
                else:
                    subprocess.Popen(["xdg-open", str(p)])
                return self._json({"ok": True, "path": str(p)})
            if path == "/api/shutdown":
                self._json({"ok": True})
                threading.Thread(target=lambda: (time.sleep(0.4), os._exit(0)), daemon=True).start()
                return
            return self._json({"error": "not found"}, 404)
        except Exception as exc:  # noqa: BLE001
            return self._json({"error": str(exc)}, 500)

    # ---- SSE 进度流 ----
    def _sse(self, job_id: str):
        job = JOBS.get(job_id)
        if not job:
            return self._json({"error": "任务不存在"}, 404)
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream; charset=utf-8")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True
        try:
            while True:
                snap = job.snapshot()
                self.wfile.write(b"data: " + json.dumps(snap, ensure_ascii=False).encode("utf-8") + b"\n\n")
                self.wfile.flush()
                if snap["status"] in ("done", "error", "cancelled"):
                    break
                time.sleep(0.3)
        except (BrokenPipeError, ConnectionResetError, OSError):
            pass


# --------------------------------------------------------------------------- #
# 前端页面
# --------------------------------------------------------------------------- #

PAGE = r"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>MC 启动器</title>
<style>
:root{
  --bg:#f4f6f8; --panel:#ffffff; --line:#e3e8ee; --text:#1b2430; --dim:#6b7a8d;
  --accent:#2ea043; --accent-dark:#1f7a33; --accent-soft:#e8f6ec; --warn:#d9822b; --err:#d64545;
}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;background:var(--bg);color:var(--text);
  font:14px/1.55 "Segoe UI","Microsoft YaHei UI","Microsoft YaHei",system-ui,sans-serif;
  -webkit-font-smoothing:antialiased}
.app{display:grid;grid-template-columns:320px 1fr;height:100vh;overflow:hidden}
.side{background:var(--panel);border-right:1px solid var(--line);display:flex;flex-direction:column;min-height:0}
.brand{padding:18px 18px 12px;display:flex;align-items:center;gap:9px;font-weight:700;font-size:17px;letter-spacing:.2px}
.brand .dot{width:10px;height:10px;border-radius:3px;background:var(--accent);box-shadow:0 0 0 3px var(--accent-soft)}
.brand small{margin-left:auto;font-weight:500;color:var(--dim);font-size:12px}
.filters{padding:0 14px 10px;display:flex;flex-direction:column;gap:8px}
input,select,button{font-family:inherit;font-size:13px;color:var(--text)}
input[type=text],input[type=number],select{
  width:100%;padding:8px 10px;border:1px solid var(--line);border-radius:8px;background:#fff;outline:none}
input:focus,select:focus{border-color:var(--accent);box-shadow:0 0 0 3px var(--accent-soft)}
.row{display:flex;gap:8px}
.vlist{flex:1;overflow-y:auto;padding:2px 8px 8px}
.vrow{display:flex;align-items:center;gap:8px;padding:9px 10px;border-radius:8px;cursor:pointer;border:1px solid transparent}
.vrow:hover{background:#f7f9fb}
.vrow.on{background:var(--accent-soft);border-color:#bfe6ca}
.vrow .nm{font-weight:600;font-size:13.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.vrow .tag{margin-left:auto;font-size:11px;color:var(--dim);background:#f0f3f6;padding:2px 7px;border-radius:20px;white-space:nowrap}
.vrow .tag.rel{color:var(--accent-dark);background:#e9f7ee}
.vrow .tag.mod{color:#7a4bd0;background:#f1ecfd}
.side-foot{padding:10px 16px;border-top:1px solid var(--line);color:var(--dim);font-size:12px}
.main{display:flex;flex-direction:column;min-width:0;overflow-y:auto}
.tabs{display:flex;gap:6px;padding:12px 28px 0;border-bottom:1px solid var(--line);background:var(--panel);
  position:sticky;top:0;z-index:6}
.tab{border:none;background:transparent;padding:9px 16px;border-radius:8px 8px 0 0;color:var(--dim);
  font-weight:600;border-bottom:2px solid transparent;cursor:pointer}
.tab.on{color:var(--accent-dark);background:var(--accent-soft);border-bottom-color:var(--accent)}
.main-inner{padding:20px 28px 40px;max-width:980px;width:100%}
h1{margin:0 0 6px;font-size:24px;letter-spacing:.2px}
h1 span{font-weight:500;color:var(--dim);font-size:15px;margin-left:8px}
.meta{color:var(--dim);font-size:12.5px;display:flex;gap:14px;flex-wrap:wrap;margin-bottom:16px}
.meta b{color:var(--text);font-weight:600}
.sec-title{font-size:13px;font-weight:700;color:var(--dim);letter-spacing:.6px;text-transform:uppercase;margin:22px 0 10px}
.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:12px}
.card{border:1px solid var(--line);border-radius:12px;padding:13px 14px;background:var(--panel);cursor:pointer;
  transition:.15s;display:flex;gap:10px;align-items:flex-start}
.card:hover{border-color:#cdd7e2;box-shadow:0 2px 10px rgba(27,36,48,.05)}
.card.on{border-color:var(--accent);background:#fbfffc;box-shadow:0 0 0 3px var(--accent-soft)}
.card input{margin:3px 0 0;accent-color:var(--accent);width:15px;height:15px}
.card .ct{font-weight:600;font-size:13.5px}
.card .cd{color:var(--dim);font-size:12px;margin-top:2px}
.card .cs{color:var(--accent-dark);font-size:12px;margin-top:5px;font-weight:600}
.loader-bar{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-top:16px;padding:12px 14px;
  border:1px solid var(--line);border-radius:12px;background:var(--panel)}
.loader-bar .t{font-weight:600;font-size:13px;color:var(--dim);margin-right:2px}
.loader-bar select{width:auto;min-width:132px}
.loader-bar .tip{color:var(--dim);font-size:12px;margin-left:auto}
.actions{display:flex;gap:10px;flex-wrap:wrap;margin-top:20px;align-items:center}
button{border:1px solid var(--line);background:#fff;padding:9px 16px;border-radius:9px;cursor:pointer;font-weight:600;transition:.15s}
button:hover{border-color:#c3cedb;background:#fafcfe}
button:disabled{opacity:.5;cursor:not-allowed}
button.primary{background:var(--accent);border-color:var(--accent);color:#fff}
button.primary:hover{background:var(--accent-dark);border-color:var(--accent-dark)}
button.ghost{color:var(--accent-dark)}
.hint{color:var(--dim);font-size:12px}
.progress{margin-top:22px;border:1px solid var(--line);border-radius:12px;background:var(--panel);padding:16px 18px}
.progress.hidden{display:none}
.bar{height:9px;background:#eef2f6;border-radius:99px;overflow:hidden}
.fill{height:100%;width:0;background:linear-gradient(90deg,#35b558,#2ea043);transition:width .25s ease}
.pinfo{display:flex;justify-content:space-between;margin-top:9px;font-size:12.5px;color:var(--dim);gap:12px}
.pinfo b{color:var(--text)}
.log{margin:12px 0 0;max-height:150px;overflow:auto;background:#f7f9fb;border:1px solid var(--line);
  border-radius:8px;padding:10px;font:12px/1.6 Consolas,"Courier New",monospace;color:#3d4b5c;white-space:pre-wrap}
.settings{margin-top:26px;border-top:1px solid var(--line);padding-top:18px;display:grid;
  grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:14px;align-items:end}
.field label{display:block;font-size:12px;color:var(--dim);margin-bottom:5px;font-weight:600}
.field .row select{flex:1 1 auto;min-width:0}
.field .row button{flex:0 0 auto;white-space:nowrap;padding:8px 12px}
.toast{position:fixed;right:20px;bottom:20px;background:#1b2430;color:#fff;padding:11px 16px;border-radius:10px;
  font-size:13px;opacity:0;transform:translateY(8px);transition:.25s;pointer-events:none;max-width:420px;z-index:20}
.toast.on{opacity:1;transform:none}
.toast.err{background:#a32626}
.empty{color:var(--dim);padding:40px 0;text-align:center}
.placeholder{grid-column:1/-1;color:var(--dim);font-size:13px;padding:26px 14px;text-align:center;
  border:1px dashed var(--line);border-radius:12px;background:#fbfcfd}
.badge{display:inline-block;padding:1px 8px;border-radius:20px;font-size:11.5px;background:var(--accent-soft);
  color:var(--accent-dark);font-weight:600;margin-left:6px}
.badge.mod{background:#f1ecfd;color:#6a3fc0}
.mod-head{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:12px}
.mod-head select{width:auto;min-width:150px}
.mod-head input{flex:1;min-width:190px}
.mod-grid{display:grid;gap:10px}
.modrow{display:flex;gap:12px;align-items:center;border:1px solid var(--line);border-radius:12px;
  padding:11px 13px;background:var(--panel)}
.modrow .ico{width:44px;height:44px;border-radius:9px;background:#eef2f6;flex:0 0 auto;object-fit:cover}
.modrow .body{min-width:0;flex:1}
.modrow .mt{font-weight:600;font-size:13.5px}
.modrow .mt em{font-style:normal;color:var(--dim);font-weight:500;font-size:12px;margin-left:6px}
.modrow .md{color:var(--dim);font-size:12px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;
  overflow:hidden;margin-top:2px}
.modrow .ms{color:var(--dim);font-size:11.5px;margin-top:3px}
.modrow button{margin-left:6px;white-space:nowrap;padding:7px 13px}
.modrow .pill{display:inline-block;background:#f0f3f6;color:var(--dim);border-radius:20px;padding:1px 7px;
  font-size:11px;margin-right:5px}
.mods-list .item{display:flex;gap:10px;align-items:center;padding:8px 12px;border:1px solid var(--line);
  border-radius:9px;margin-bottom:8px;background:var(--panel);font-size:12.5px}
.mods-list .item .nm{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mods-list .item .sz{color:var(--dim);margin-left:auto;white-space:nowrap}
.mods-list .item .del{color:#d64545;background:none;border:none;padding:2px 6px;cursor:pointer;font-weight:600}
/* ---- 联机 ---- */
.net-list{display:grid;gap:10px}
.netrow{display:flex;gap:12px;align-items:center;border:1px solid var(--line);border-radius:12px;
  padding:12px 14px;background:var(--panel);cursor:pointer;transition:.15s}
.netrow:hover{border-color:#cdd7e2;box-shadow:0 2px 10px rgba(27,36,48,.05)}
.netrow.on{border-color:var(--accent);background:#fbfffc;box-shadow:0 0 0 3px var(--accent-soft)}
.netrow .dot{width:10px;height:10px;border-radius:50%;background:#e3e8ee;flex:0 0 auto;margin:0 2px}
.netrow.on .dot{background:var(--accent);box-shadow:0 0 0 3px var(--accent-soft)}
.netrow .nm{font-weight:600;font-size:14px}
.netrow .addr{color:var(--dim);font-size:12.5px;margin-top:1px}
.netrow .flags{margin-left:auto;display:flex;gap:6px;align-items:center;flex-wrap:wrap}
.netrow .pill{display:inline-block;background:#f0f3f6;color:var(--dim);border-radius:20px;padding:2px 9px;font-size:11px}
.netrow .pill.auth{background:#f1ecfd;color:#6a3fc0}
.netrow .ops{display:flex;gap:4px;align-items:center;flex-wrap:wrap}
.netrow .ops button{padding:5px 11px;font-size:12px;white-space:nowrap}
.net-form{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:12px;align-items:end;
  border:1px solid var(--line);border-radius:12px;padding:14px;background:var(--panel)}
.net-form .field input{width:100%}
.net-form .wide{grid-column:1/-1}
.net-help{border:1px solid var(--line);border-radius:12px;background:var(--panel);padding:14px 16px;
  font-size:12.5px;color:var(--dim);line-height:1.8}
.net-help b{color:var(--text)}
.hidden{display:none}
</style>
</head>
<body>
<div class="app">
  <aside class="side">
    <div class="brand"><span class="dot"></span>MC 启动器 <small>v1.1</small></div>
    <div class="filters">
      <div class="row">
        <input type="text" id="search" placeholder="搜索版本号，例如 1.20">
        <button id="btnRefresh" style="white-space:nowrap;padding:8px 12px" title="重新获取版本清单">刷新</button>
      </div>
      <div class="row">
        <select id="typeFilter">
          <option value="">全部类型</option>
          <option value="release">正式版</option>
          <option value="snapshot">快照</option>
          <option value="modded">已装加载器</option>
          <option value="old">远古版</option>
        </select>
        <select id="mirror">
          <option value="bmcl">BMCLAPI 镜像</option>
          <option value="mojang">Mojang 官方</option>
        </select>
      </div>
    </div>
    <div class="vlist" id="vlist"><div class="empty">正在获取版本清单…</div></div>
    <div class="side-foot" id="count">—</div>
  </aside>

  <main class="main">
    <div class="tabs">
      <button class="tab on" data-tab="ver">版本与启动</button>
      <button class="tab" data-tab="mod">模组</button>
      <button class="tab" data-tab="net">联机</button>
    </div>
    <div class="main-inner">
      <section id="tab-ver">
        <h1 id="vtitle">选择一个版本</h1>
        <div class="meta" id="vmeta"></div>

        <div class="sec-title">选择要下载的内容</div>
        <div class="cards" id="components"><div class="placeholder">← 先在左侧选择一个版本</div></div>

        <div class="loader-bar">
          <span class="t">模组加载器</span>
          <select id="loaderType">
            <option value="fabric">Fabric</option>
            <option value="quilt">Quilt</option>
            <option value="legacyfabric">Legacy Fabric</option>
            <option value="forge">Forge</option>
            <option value="neoforge">NeoForge</option>
          </select>
          <select id="loaderVer"><option value="">默认版本</option></select>
          <button id="btnLoader" disabled>安装加载器</button>
          <span class="tip" id="loaderTip">装好加载器后才能在「模组」页下载 mod</span>
        </div>

        <div class="actions">
          <button class="primary" id="btnDownload" disabled>下载所选</button>
          <button id="btnCancel" disabled>取消</button>
          <button id="btnFolder">打开游戏目录</button>
          <button class="ghost" id="btnLaunch" disabled>启动游戏</button>
          <span class="hint" id="actionHint"></span>
          <span class="hint" id="joinHint"></span>
        </div>

        <div class="progress hidden" id="progressBox">
          <div class="bar"><div class="fill" id="fill"></div></div>
          <div class="pinfo"><span id="pstat">准备中…</span><span id="pspeed"></span></div>
          <pre class="log" id="plog"></pre>
        </div>

        <div class="settings">
          <div class="field"><label>离线用户名</label><input type="text" id="username" value="Steve"></div>
          <div class="field"><label>最大内存 (MB)</label><input type="number" id="memory" value="2048" min="512" step="512"></div>
          <div class="field" style="grid-column:span 2"><label>Java 路径</label><select id="java"></select></div>
          <div class="field"><label>下载 Java（Adoptium）</label>
            <span class="row">
              <select id="javaMajor">
                <option value="25">Java 25（26.x 及以后）</option>
                <option value="21">Java 21（1.20.5~1.21.x）</option>
                <option value="17">Java 17（1.17~1.20.4）</option>
                <option value="8">Java 8（1.12.2 及更早）</option>
              </select>
              <button id="btnJava" class="ghost">下载</button>
            </span>
          </div>
          <div class="field"><label>并发线程</label><input type="number" id="workers" value="16" min="1" max="48"></div>
        </div>
      </section>

      <section id="tab-mod" class="hidden">
        <h1>模组 <span id="modSub">Modrinth</span></h1>
        <div class="meta" id="modMeta"><span>先选一个装了 Fabric / Quilt / Forge 的版本</span></div>
        <div class="mod-head">
          <select id="modInstance"></select>
          <input type="text" id="modSearch" placeholder="搜索模组，例如 sodium / jei / 小地图">
          <select id="modSort">
            <option value="relevance">相关度</option>
            <option value="downloads">下载量</option>
            <option value="follows">收藏数</option>
            <option value="newest">最新发布</option>
          </select>
          <button id="btnModSearch" class="primary">搜索</button>
        </div>
        <div class="mod-grid" id="modList"><div class="placeholder">搜索后在这里选模组，点「下载」即可</div></div>
        <div class="sec-title">已安装模组 <span id="modCount"></span></div>
        <div class="mods-list" id="modInstalled"><div class="hint">—</div></div>
      </section>

      <section id="tab-net" class="hidden">
        <h1>联机 <span>一键进服 & 第三方登录</span></h1>
        <div class="meta" id="netMeta"><span>选中服务器后，回到「版本与启动」点「启动游戏」就会自动加入</span></div>

        <div class="sec-title">服务器列表</div>
        <div class="net-list" id="netList"><div class="placeholder">还没有添加服务器，下面添加一个吧</div></div>

        <div class="sec-title">添加 / 编辑服务器</div>
        <div class="net-form" id="netForm">
          <div class="field"><label>服务器名称</label><input type="text" id="srvName" placeholder="例如 花雨庭"></div>
          <div class="field"><label>服务器地址</label><input type="text" id="srvAddr" placeholder="play.example.com 或 IP / IPv6"></div>
          <div class="field"><label>端口</label><input type="number" id="srvPort" value="25565" min="1" max="65535"></div>
          <div class="field"><label>第三方登录 API（可选）</label><input type="text" id="srvAuth" placeholder="https://…/api/yggdrasil"></div>
          <div class="field wide"><label>备注（可选）</label><input type="text" id="srvNote" placeholder="版本要求 / 群号等"></div>
          <div class="field"><button class="primary" id="btnSrvSave">保存服务器</button>
            <button id="btnSrvClear" style="margin-left:8px">清空表单</button></div>
        </div>

        <div class="sec-title">内网穿透开服（frp）<span class="hint">把本地房间映射到公网，跨网也能连</span></div>
        <div class="net-form" id="frpForm">
          <div class="field"><label>frp 服务器地址</label><input type="text" id="frpServer" placeholder="你的 frps 公网 IP 或域名"></div>
          <div class="field"><label>服务器端口</label><input type="number" id="frpPort" value="7000" min="1" max="65535"></div>
          <div class="field"><label>Token（无则留空）</label><input type="text" id="frpToken" placeholder="auth.token"></div>
          <div class="field"><label>本地端口</label><input type="number" id="frpLocal" value="25565" min="1" max="65535"></div>
          <div class="field"><label>远程端口（留空=同本地）</label><input type="number" id="frpRemote" value="" min="1" max="65535"></div>
          <div class="field">
            <button class="primary" id="btnFrpStart">下载并启动穿透</button>
            <button id="btnFrpStop" style="margin-left:8px">停止</button>
          </div>
        </div>
        <div class="hint" id="frpStatus" style="margin-top:10px"></div>

        <div class="sec-title">陶瓦联机（Terracotta）<span class="hint">P2P 直连 · 免公网 IP · 房间码加入</span></div>
        <div class="net-help" style="display:flex;align-items:center;gap:14px;flex-wrap:wrap">
          <span id="tcStatus">检查中…</span>
          <span style="margin-left:auto">
            <button class="primary" id="btnTcInstall">下载陶瓦联机</button>
            <button id="btnTcLaunch" style="margin-left:8px">启动陶瓦联机</button>
          </span>
        </div>
        <div class="hint" id="tcHint" style="margin-top:10px"></div>

        <div class="sec-title">联机说明</div>
        <div class="net-help" id="netHelp"></div>
      </section>
    </div>
  </main>
</div>
<div class="toast" id="toast"></div>

<script>
var state = { versions: [], current: null, job: null, es: null, detail: null,
              instances: [], modOffset: 0, modLoading: false,
              servers: [], selServer: -1, srvEditing: -1 };

function $(id){ return document.getElementById(id); }
function fmt(n){
  n = n || 0;
  if (n < 1024) return n + ' B';
  var u = ['KB','MB','GB','TB'], i = -1;
  do { n = n / 1024; i++; } while (n >= 1024 && i < u.length - 1);
  return n.toFixed(1) + ' ' + u[i];
}
function fmtTime(s){
  if (s < 0) return '';
  if (s < 60) return s + ' 秒';
  return Math.floor(s / 60) + ' 分 ' + (s % 60) + ' 秒';
}
function esc(s){
  return String(s == null ? '' : s).replace(/[&<>"']/g, function(c){
    return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c];
  });
}
function toast(msg, isErr){
  var t = $('toast');
  t.textContent = msg;
  t.className = 'toast on' + (isErr ? ' err' : '');
  clearTimeout(t._t);
  t._t = setTimeout(function(){ t.className = 'toast'; }, 3600);
}
function api(path, opt){
  return fetch(path, opt).then(function(r){
    return r.json().then(function(j){
      if (!r.ok) throw new Error(j.error || ('HTTP ' + r.status));
      return j;
    });
  });
}
function post(path, body){
  return api(path, {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(body)});
}

/* ---------- 版本清单 ---------- */
function loadVersions(force){
  var mirror = $('mirror').value;
  $('vlist').innerHTML = '<div class="empty">正在获取版本清单…</div>';
  api('/api/versions?mirror=' + mirror + (force ? '&refresh=1' : '')).then(function(d){
    state.versions = d.versions || [];
    renderList();
    $('count').textContent = state.versions.length + ' 个版本 · ' + d.source;
    var last = d.latest || {};
    if (last.release) $('actionHint').textContent = '最新正式版 ' + last.release;
    if (!state.current){
      var want = null;
      try { want = new URLSearchParams(location.search).get('v'); } catch (e) {}
      if (want) selectVersion(want);
    }
  }).catch(function(e){
    $('vlist').innerHTML = '<div class="empty">获取失败：' + esc(e.message) + '</div>';
  });
}

function renderList(){
  var kw = $('search').value.trim().toLowerCase();
  var tf = $('typeFilter').value;
  var box = $('vlist');
  var frag = document.createDocumentFragment();
  var n = 0;
  for (var i = 0; i < state.versions.length; i++){
    var v = state.versions[i];
    if (kw && v.id.toLowerCase().indexOf(kw) < 0) continue;
    if (tf === 'old'){ if (v.type.indexOf('old') !== 0) continue; }
    else if (tf && v.type !== tf) continue;
    var row = document.createElement('div');
    row.className = 'vrow' + (state.current === v.id ? ' on' : '');
    var label = {release:'正式版', snapshot:'快照', old_beta:'远古 Beta', old_alpha:'远古 Alpha',
                 modded:'模组'}[v.type] || v.type;
    var cls = v.type === 'release' ? 'tag rel' : (v.type === 'modded' ? 'tag mod' : 'tag');
    row.innerHTML = '<span class="nm">' + esc(v.id) + '</span><span class="' + cls + '">' + esc(label) + '</span>';
    row.onclick = (function(id){ return function(){ selectVersion(id); }; })(v.id);
    frag.appendChild(row);
    n++;
    if (n > 2000) break;
  }
  box.innerHTML = '';
  if (!n) box.innerHTML = '<div class="empty">没有匹配的版本</div>';
  else {
    box.appendChild(frag);
    var sel = box.querySelector('.vrow.on');
    if (sel && sel.scrollIntoView) sel.scrollIntoView({ block: 'nearest' });
  }
}

/* ---------- 版本详情 ---------- */
function pickJavaFor(required){
  // 版本需要 Java N：优先精确匹配，其次选 >= N 里最小的，别拿 Java 24 去跑 1.20.1
  var sel = $('java');
  if (!sel || !sel.options.length || !required) return;
  var best = -1, bestMajor = 1e9, maxMajor = 0;
  for (var i = 0; i < sel.options.length; i++){
    var m = /^Java (\d+)/.exec(sel.options[i].textContent);
    if (!m) continue;
    var major = parseInt(m[1]);
    if (major > maxMajor) maxMajor = major;
    if (major === required){ best = i; break; }
    if (major > required && major < bestMajor){ bestMajor = major; best = i; }
  }
  if (best >= 0){ sel.selectedIndex = best; return; }
  // 一个都不够新：提醒去下对应大版本
  if (required > maxMajor && state.javaHinted !== required){
    state.javaHinted = required;
    toast('这个版本需要 Java ' + required + '，下面「下载 Java」选 ' + required + ' 装一个');
  }
}

function selectVersion(id){
  state.current = id;
  renderList();
  var mirror = $('mirror').value;
  $('vtitle').textContent = id;
  $('vmeta').innerHTML = '<span>加载中…</span>';
  $('components').innerHTML = '';
  $('btnDownload').disabled = true;
  api('/api/version?id=' + encodeURIComponent(id) + '&mirror=' + mirror).then(function(d){
    state.detail = d;
    var c = d.components;
    var t = d.releaseTime ? new Date(d.releaseTime).toLocaleDateString() : '—';
    var title = d.id + '<span>' + (d.typeLabel || '') + '</span>';
    if (d.loader) title += '<span class="badge mod">' + d.loaderLabel + ' ' + esc(d.loaderVersion) + '</span>';
    $('vtitle').innerHTML = title;
    $('vmeta').innerHTML =
      '<span>发布时间 <b>' + t + '</b></span>' +
      (d.loader ? '<span>基于 <b>' + esc(d.baseId) + '</b></span>' : '') +
      '<span>需要 Java <b>' + d.javaVersion + '+</b></span>' +
      '<span>依赖库 <b>' + c.libraries.count + '</b> 个</span>' +
      '<span>资源 <b>' + c.assets.count + '</b> 个</span>' +
      (d.loader ? '<span>已装模组 <b>' + d.mods + '</b> 个</span>' : '') +
      (d.installed ? '<span class="badge">已下载核心</span>' : '');
    renderComponents(c);
    pickJavaFor(d.javaVersion);
    $('btnDownload').disabled = false;
    $('btnLaunch').disabled = false;
    $('btnLoader').disabled = false;
    $('loaderTip').textContent = '装好加载器后才能在「模组」页下载 mod';
    loadLoaderVersions(d.baseId);
  }).catch(function(e){
    $('vmeta').innerHTML = '<span style="color:#d64545">加载失败：' + esc(e.message) + '</span>';
  });
}

function renderComponents(c){
  var defs = [
    {k:'client', t:'客户端核心', d:'版本 jar 文件，运行必需', s:c.client},
    {k:'libraries', t:'依赖库', d:'运行所需的第三方 jar', s:c.libraries},
    {k:'assets', t:'资源文件', d:'音效、语言、贴图等', s:c.assets},
    {k:'logging', t:'日志配置', d:'log4j 配置（可选）', s:c.logging}
  ];
  var box = $('components');
  box.innerHTML = '';
  defs.forEach(function(x){
    var checked = (x.k === 'client' || x.k === 'libraries' || x.k === 'assets');
    if (!x.s || !x.s.count) checked = false;
    var el = document.createElement('label');
    el.className = 'card' + (checked ? ' on' : '');
    el.innerHTML = '<input type="checkbox" data-k="' + x.k + '"' + (checked ? ' checked' : '') + '>' +
      '<div><div class="ct">' + x.t + '</div><div class="cd">' + x.d + '</div>' +
      '<div class="cs">' + (x.s && x.s.count ? (x.s.count + ' 个文件 · ' + fmt(x.s.size)) : '无') + '</div></div>';
    var cb = el.querySelector('input');
    cb.onchange = function(){ el.className = 'card' + (cb.checked ? ' on' : ''); };
    box.appendChild(el);
  });
  var extra = document.createElement('label');
  extra.className = 'card';
  extra.innerHTML = '<input type="checkbox" id="skipSounds"><div><div class="ct">跳过音效</div>' +
    '<div class="cd">不下载 minecraft/sounds 下的音频</div><div class="cs">可省下约 200 MB</div></div>';
  box.appendChild(extra);
  $('skipSounds').onchange = function(){ extra.className = 'card' + (this.checked ? ' on' : ''); };
}

function picked(){
  var out = [];
  document.querySelectorAll('#components input[data-k]').forEach(function(cb){
    if (cb.checked) out.push(cb.getAttribute('data-k'));
  });
  return out;
}

/* ---------- 加载器 ---------- */
function loadLoaderVersions(mc){
  var loader = $('loaderType').value;
  var sel = $('loaderVer');
  var note = (state.loaderNotes || {})[loader];
  $('loaderTip').textContent = note || '装好加载器后才能在「模组」页下载 mod';
  sel.innerHTML = '<option value="">加载中…</option>';
  api('/api/loaders?mc=' + encodeURIComponent(mc) + '&loader=' + loader).then(function(d){
    sel.innerHTML = '';
    if (!d.versions.length){
      sel.innerHTML = '<option value="">该版本无可用 ' + loader + '</option>';
      return;
    }
    d.versions.slice(0, 25).forEach(function(v){
      var o = document.createElement('option');
      o.value = v.version;
      o.textContent = v.version + (v.stable ? '（稳定）' : '');
      if (v.version === d.recommended) o.selected = true;
      sel.appendChild(o);
    });
  }).catch(function(e){
    sel.innerHTML = '<option value="">获取失败</option>';
  });
}

function installLoader(){
  var d = state.detail;
  if (!d) return;
  var loader = $('loaderType').value;
  var ver = $('loaderVer').value;
  if (loader === 'forge' || loader === 'neoforge'){
    if (!confirm(loader + ' 需要运行官方安装器，会下载几十 MB 并可能耗时几分钟，继续吗？')) return;
  }
  showProgress('准备安装 ' + loader + '…');
  $('btnLoader').disabled = true;
  post('/api/install_loader', {mc: d.baseId, loader: loader, version: ver, mirror: $('mirror').value})
    .then(function(r){ watchJob(r.job, 'loader'); })
    .catch(function(e){
      toast('安装失败：' + e.message, true);
      $('btnLoader').disabled = false;
    });
}

/* ---------- 下载 ---------- */
function showProgress(text){
  $('progressBox').className = 'progress';
  $('fill').style.width = '0%';
  $('pstat').textContent = text || '正在准备…';
  $('pspeed').textContent = '';
  $('plog').textContent = '';
  $('btnCancel').disabled = false;
}
function hideProgress(){ $('progressBox').className = 'progress hidden'; }

function startDownload(){
  if (!state.current) return;
  var comps = picked();
  if (!comps.length){ toast('请至少勾选一个组件', true); return; }
  showProgress('正在准备…');
  $('btnDownload').disabled = true;
  post('/api/download', {
    id: state.current, mirror: $('mirror').value, components: comps,
    skipSounds: $('skipSounds') ? $('skipSounds').checked : false,
    workers: parseInt($('workers').value) || 16, verify: false
  }).then(function(d){ watchJob(d.job, 'download'); })
    .catch(function(e){
      toast('启动下载失败：' + e.message, true);
      $('btnDownload').disabled = false;
      $('btnCancel').disabled = true;
    });
}

function watchJob(jobId, kind){
  state.job = jobId;
  if (state.es) state.es.close();
  state.es = new EventSource('/api/progress?job=' + jobId);
  state.es.onmessage = function(ev){ onProgress(JSON.parse(ev.data), kind); };
  state.es.onerror = function(){ if (state.es) state.es.close(); };
}

function onProgress(p, kind){
  $('fill').style.width = p.percent + '%';
  if (p.status === 'running'){
    $('pstat').innerHTML = kind === 'download'
      ? '已下载 <b>' + fmt(p.done) + '</b> / ' + fmt(p.total) + '（' + p.percent + '%）· 文件 ' +
        p.files + '/' + p.files_total + (p.skipped ? ' · 跳过 ' + p.skipped : '')
      : (p.message || '处理中…');
    $('pspeed').textContent = kind === 'download'
      ? (fmt(p.speed) + '/s' + (p.eta > 0 ? ' · 剩余 ' + fmtTime(p.eta) : ''))
      : ('用时 ' + fmtTime(p.elapsed));
  } else {
    $('pstat').innerHTML = '<b>' + esc(p.message || p.status) + '</b>';
    $('pspeed').textContent = '用时 ' + fmtTime(p.elapsed);
  }
  if (p.logs && p.logs.length){
    $('plog').textContent = p.logs.join('\n');
    $('plog').scrollTop = $('plog').scrollHeight;
  }
  if (p.status !== 'running'){
    $('btnDownload').disabled = false;
    $('btnCancel').disabled = true;
    $('btnLoader').disabled = false;
    $('btnJava').disabled = false;
    if (state.es) state.es.close();
    if (p.status === 'done'){
      if (kind === 'loader'){
        toast('加载器安装完成');
        loadVersions();
        loadInstances();
        if (p.result && p.result.id) selectVersion(p.result.id);
      } else if (kind === 'java'){
        toast('Java 已就绪');
        refreshJava(p.result && p.result.path).then(function(){ saveSettings(); });
      } else if (kind === 'frp'){
        toast('穿透已启动' + (p.result && p.result.public ? '，公网地址 ' + p.result.public : ''));
        loadFrp();
      } else if (kind === 'tc'){
        toast('陶瓦联机已就绪');
        loadTc();
      } else {
        toast('下载完成，可以启动游戏了');
        if (state.current) selectVersion(state.current);
      }
    } else if (p.status === 'error'){
      toast('失败：' + (p.errors && p.errors[0] ? p.errors[0] : p.message), true);
    }
  }
}

/* ---------- 启动 ---------- */
function launch(){
  if (!state.current) return;
  var body = {
    id: state.current, mirror: $('mirror').value,
    username: $('username').value.trim() || 'Steve',
    memory: parseInt($('memory').value) || 2048,
    java: $('java').value || ''
  };
  var sv = (state.selServer >= 0 && state.servers[state.selServer]) ? state.servers[state.selServer] : null;
  if (sv){
    body.server = sv.address;
    body.port = sv.port;
    body.authlib = sv.authlib || '';
  }
  saveSettings();
  $('btnLaunch').disabled = true;
  $('btnLaunch').textContent = '启动中…';
  post('/api/launch', body).then(function(d){
    toast('游戏已启动（PID ' + d.pid + '）' + (d.server ? '，将自动加入 ' + d.server : '') + '，日志：logs/latest.log');
  }).catch(function(e){
    toast('启动失败：' + e.message, true);
  }).finally(function(){
    $('btnLaunch').disabled = false;
    $('btnLaunch').textContent = '启动游戏';
  });
}

/* ---------- 模组 ---------- */
function loadInstances(){
  return api('/api/instances').then(function(d){
    state.instances = (d.list || []).filter(function(x){ return x.loader; });
    var sel = $('modInstance');
    var keep = sel.value;
    sel.innerHTML = '';
    if (!state.instances.length){
      sel.innerHTML = '<option value="">还没有装加载器的版本</option>';
      $('modMeta').innerHTML = '<span>请先到「版本与启动」页，选中一个原版版本，点「安装加载器」</span>';
      return;
    }
    state.instances.forEach(function(x){
      var o = document.createElement('option');
      o.value = x.id;
      o.textContent = x.id + '（' + (x.loader || '') + '）';
      sel.appendChild(o);
    });
    if (keep){ for (var i = 0; i < sel.options.length; i++) if (sel.options[i].value === keep) sel.selectedIndex = i; }
    onModInstanceChange();
  });
}

function onModInstanceChange(){
  var vid = $('modInstance').value;
  if (!vid){ $('modList').innerHTML = '<div class="placeholder">没有可用的模组版本</div>'; return; }
  var inst = null;
  state.instances.forEach(function(x){ if (x.id === vid) inst = x; });
  $('modMeta').innerHTML = '<span>目标实例 <b>' + esc(vid) + '</b></span>' +
    '<span>加载器 <b>' + esc(inst ? inst.loader : '') + '</b></span>' +
    '<span>游戏版本 <b>' + esc(inst ? inst.inheritsFrom : '') + '</b></span>' +
    '<span>只显示适配该版本 + 该加载器的模组</span>';
  loadInstalled();
  doSearch(0);
}

function doSearch(offset){
  var vid = $('modInstance').value;
  if (!vid) return;
  state.modOffset = offset || 0;
  $('modList').innerHTML = '<div class="placeholder">搜索中…</div>';
  var url = '/api/mods/search?vid=' + encodeURIComponent(vid) +
            '&q=' + encodeURIComponent($('modSearch').value.trim()) +
            '&sort=' + $('modSort').value + '&offset=' + state.modOffset;
  api(url).then(function(d){
    var list = $('modList');
    list.innerHTML = '';
    if (!d.hits.length){
      list.innerHTML = '<div class="placeholder">没有找到模组，换个关键词试试</div>';
      return;
    }
    d.hits.forEach(function(h){
      var el = document.createElement('div');
      el.className = 'modrow';
      var icon = h.icon ? '<img class="ico" src="' + esc(h.icon) + '" onerror="this.style.visibility=\'hidden\'">'
                        : '<div class="ico"></div>';
      el.innerHTML = icon +
        '<div class="body"><div class="mt">' + esc(h.title) + '<em>' + esc(h.author) + '</em></div>' +
        '<div class="md">' + esc(h.description) + '</div>' +
        '<div class="ms">' + (h.categories || []).map(function(c){ return '<span class="pill">' + esc(c) + '</span>'; }).join('') +
        fmt(h.downloads) + ' 次下载</div></div>' +
        '<button class="primary">下载</button>';
      el.querySelector('button').onclick = function(){ installMod(h.id, h.title, this); };
      list.appendChild(el);
    });
    if (d.hits.length >= 20){
      var more = document.createElement('div');
      more.style.textAlign = 'center';
      more.innerHTML = '<button>加载更多</button>';
      more.querySelector('button').onclick = function(){ doSearch(state.modOffset + 20); };
      list.appendChild(more);
    }
  }).catch(function(e){
    $('modList').innerHTML = '<div class="placeholder">搜索失败：' + esc(e.message) + '</div>';
  });
}

function installMod(project, title, btn){
  var vid = $('modInstance').value;
  if (!vid) return;
  btn.disabled = true;
  btn.textContent = '下载中…';
  showProgress('安装模组：' + title);
  post('/api/mods/install', {vid: vid, project: project}).then(function(r){
    watchJob(r.job, 'mod');
    setTimeout(function(){ btn.disabled = false; btn.textContent = '下载'; }, 1500);
    setTimeout(function(){ loadInstalled(); }, 3000);
  }).catch(function(e){
    toast('安装失败：' + e.message, true);
    btn.disabled = false;
    btn.textContent = '下载';
  });
}

function loadInstalled(){
  var vid = $('modInstance').value;
  if (!vid) return;
  api('/api/mods/installed?vid=' + encodeURIComponent(vid)).then(function(d){
    var box = $('modInstalled');
    $('modCount').textContent = d.list.length ? '（' + d.list.length + ' 个）' : '';
    if (!d.list.length){
      box.innerHTML = '<div class="hint">这个版本还没有装模组。上面的搜索结果点「下载」就会装到这里。</div>';
      return;
    }
    box.innerHTML = '';
    d.list.forEach(function(m){
      var el = document.createElement('div');
      el.className = 'item';
      el.innerHTML = '<span class="nm">' + esc(m.file) + '</span>' +
        '<span class="sz">' + fmt(m.size) + '</span>' +
        '<button class="del">删除</button>';
      el.querySelector('.del').onclick = function(){
        if (!confirm('删除 ' + m.file + ' ？')) return;
        post('/api/mods/delete', {vid: vid, file: m.file}).then(function(){ loadInstalled(); })
          .catch(function(e){ toast(e.message, true); });
      };
      box.appendChild(el);
    });
  }).catch(function(){});
}

/* ---------- 联机 ---------- */
function updateJoinHint(){
  var h = $('joinHint');
  if (!h) return;
  var s = (state.selServer >= 0 && state.servers[state.selServer]) ? state.servers[state.selServer] : null;
  h.textContent = s ? '将自动加入 ' + s.name + '（' + s.address + ':' + s.port + '）' : '';
  h.style.color = s ? 'var(--accent-dark)' : '';
}
function loadServers(){
  return api('/api/servers').then(function(d){
    state.servers = d.list || [];
    if (state.selServer >= state.servers.length) state.selServer = -1;
    renderServers();
  }).catch(function(e){
    $('netList').innerHTML = '<div class="placeholder">加载失败：' + esc(e.message) + '</div>';
  });
}
function renderServers(){
  var box = $('netList');
  box.innerHTML = '';
  if (!state.servers.length){
    box.innerHTML = '<div class="placeholder">还没有添加服务器，下面添加一个吧</div>';
    updateJoinHint();
    return;
  }
  state.servers.forEach(function(s, i){
    var el = document.createElement('div');
    el.className = 'netrow' + (state.selServer === i ? ' on' : '');
    el.innerHTML = '<span class="dot"></span>' +
      '<div style="min-width:0"><div class="nm">' + esc(s.name) + '</div>' +
      '<div class="addr">' + esc(s.address) + ':' + s.port + (s.note ? ' · ' + esc(s.note) : '') + '</div></div>' +
      '<div class="flags">' +
      (s.authlib ? '<span class="pill auth">外置登录</span>' : '<span class="pill">离线</span>') +
      '<span class="ops">' +
      '<button title="编辑">编辑</button>' +
      '<button class="del" title="删除" style="color:#d64545;border-color:#f0d4d4">删除</button>' +
      '</span></div>';
    el.onclick = function(){ selectServer(i); };
    var btns = el.querySelectorAll('.ops button');
    btns[0].onclick = function(e){ e.stopPropagation(); fillServerForm(i); };
    btns[1].onclick = function(e){ e.stopPropagation(); deleteServer(i); };
    box.appendChild(el);
  });
  updateJoinHint();
}
function selectServer(i){
  state.selServer = (state.selServer === i) ? -1 : i;
  renderServers();
  var s = (state.selServer >= 0 && state.servers[state.selServer]) ? state.servers[state.selServer] : null;
  $('netMeta').innerHTML = s
    ? '<span>将加入 <b>' + esc(s.name) + '</b>（' + esc(s.address) + ':' + s.port + '）</span>' +
      '<span>回「版本与启动」页点「启动游戏」即自动进服</span>'
    : '<span>选中服务器后，回到「版本与启动」点「启动游戏」就会自动加入</span>';
}
function fillServerForm(i){
  var s = state.servers[i];
  if (!s) return;
  state.srvEditing = i;
  $('srvName').value = s.name || '';
  $('srvAddr').value = s.address || '';
  $('srvPort').value = s.port || 25565;
  $('srvAuth').value = s.authlib || '';
  $('srvNote').value = s.note || '';
  $('btnSrvSave').textContent = '保存修改';
  $('netForm').scrollIntoView({behavior: 'smooth', block: 'nearest'});
}
function clearSrvForm(){
  state.srvEditing = -1;
  $('btnSrvSave').textContent = '保存服务器';
  $('srvName').value = ''; $('srvAddr').value = ''; $('srvAuth').value = ''; $('srvNote').value = '';
  $('srvPort').value = 25565;
}
function saveServerForm(){
  var body = {
    name: $('srvName').value.trim(),
    address: $('srvAddr').value.trim(),
    port: parseInt($('srvPort').value) || 25565,
    authlib: $('srvAuth').value.trim(),
    note: $('srvNote').value.trim()
  };
  if (state.srvEditing >= 0) body.index = state.srvEditing;
  post('/api/server_save', body).then(function(d){
    state.servers = d.list || [];
    clearSrvForm();
    renderServers();
    toast('服务器已保存');
  }).catch(function(e){ toast('保存失败：' + e.message, true); });
}
function deleteServer(i){
  var s = state.servers[i];
  if (!s) return;
  if (!confirm('删除服务器「' + s.name + '」？')) return;
  post('/api/server_delete', {index: i}).then(function(){
    if (state.selServer === i) state.selServer = -1;
    if (state.srvEditing === i) clearSrvForm();
    loadServers();
  }).catch(function(e){ toast(e.message, true); });
}
function renderNetHelp(){
  $('netHelp').innerHTML =
    '<b>① 局域网联机（同一个 WiFi / 网线）</b>：房主进游戏 → 按 <code>Esc</code> → 「对局域网开放」→ 记下端口号；' +
    '朋友在本页添加服务器，地址填房主电脑的局域网 IP（<code>ipconfig</code> 查 IPv4 地址），端口填刚才的端口，保存后启动即进服。<br>' +
    '<b>② 不在同一网络（跨网联机）</b>：需要内网穿透（frp / natapp / 花生壳）把端口映射到公网；' +
    '双方都有公网 IPv6 时也可直接用 IPv6 地址连，地址要带方括号，如 <code>[240e:1234::1]:25565</code>。<br>' +
    '<b>③ 第三方登录（外置登录）</b>：服务器要求外置登录（如花雨庭、LittleSkin 生态）时，' +
    '把它的 yggdrasil API 地址填进「第三方登录 API」框，启动器首次使用时自动下载 authlib-injector 组件；' +
    '普通离线服务器留空即可。<br>' +
    '<b>④ frp 开服流程</b>：房主进游戏对局域网开放（或本地起独立服务端）→ 填 frps 参数点「下载并启动穿透」→ ' +
    '把状态栏显示的公网地址（<code>服务器IP:远程端口</code>）发给朋友，朋友在服务器列表添加该地址即可进服。<br>' +
    '<b>⑤ 陶瓦联机（免费 P2P，推荐小规模开黑）</b>：所有玩家各自下载并启动陶瓦联机 → 房主进游戏对局域网开放后，' +
    '在陶瓦联机里「创建房间」拿到房间码 → 朋友在陶瓦联机里输入房间码加入 → 游戏多人列表里出现房主的房间，直接进。' +
    '不需要公网 IP，不依赖第三方服务器中转。';
}

/* ---------- frp 内网穿透 ---------- */
function loadFrp(){
  return api('/api/frp/status').then(function(d){
    state.frp = d;
    if (d.cfg){
      $('frpServer').value = d.cfg.server || '';
      $('frpPort').value = d.cfg.port || 7000;
      $('frpToken').value = d.cfg.token || '';
      $('frpLocal').value = d.cfg.local_port || 25565;
      $('frpRemote').value = d.cfg.remote_port || '';
    }
    renderFrp(d);
  }).catch(function(){});
}
function renderFrp(d){
  var s = d || state.frp;
  if (!s) return;
  var parts = [];
  parts.push(s.exe_exists ? 'frpc 已就绪' : 'frpc 未下载（首次启动自动下载，约 15 MB）');
  parts.push(s.running ? '穿透运行中（PID ' + s.pid + '）' : '穿透未运行');
  $('frpStatus').textContent = parts.join(' · ');
  $('btnFrpStart').textContent = s.running ? '重新启动穿透' : '下载并启动穿透';
}
function frpStart(){
  var body = {
    server: $('frpServer').value.trim(),
    port: parseInt($('frpPort').value) || 7000,
    token: $('frpToken').value,
    local_port: parseInt($('frpLocal').value) || 25565,
    remote_port: parseInt($('frpRemote').value) || 0
  };
  if (!body.server){ toast('请先填 frp 服务器地址', true); return; }
  showProgress('正在启动 frp 穿透…');
  post('/api/frp/start', body).then(function(r){ watchJob(r.job, 'frp'); })
    .catch(function(e){ toast('启动失败：' + e.message, true); });
}
function frpStop(){
  post('/api/frp/stop', {}).then(function(d){
    toast(d.stopped ? '已停止穿透' : '穿透本来就没在运行');
    loadFrp();
  }).catch(function(e){ toast(e.message, true); });
}

/* ---------- 陶瓦联机 ---------- */
function loadTc(){
  return api('/api/terracotta/status').then(function(d){
    state.tc = d;
    renderTc(d);
  }).catch(function(){});
}
function renderTc(d){
  if (!d) return;
  var st = d.complete ? '陶瓦联机 v' + d.version + ' 已就绪' :
           (d.installed ? '陶瓦联机已下载但文件不完整' : '陶瓦联机未下载');
  if (d.running) st += ' · 运行中（PID ' + d.pid + '）';
  $('tcStatus').textContent = st;
  $('btnTcLaunch').textContent = d.running ? '已运行' : '启动陶瓦联机';
  $('tcHint').textContent = d.complete
    ? '点击「启动陶瓦联机」打开图形界面：房主点「创建房间」拿房间码，朋友点「加入房间」输房间码'
    : '点击「下载陶瓦联机」安装官方联机组件（约 30 MB，国内镜像，含 SHA-512 校验）';
}
function tcInstall(){
  showProgress('正在下载陶瓦联机…');
  post('/api/terracotta/install', {}).then(function(r){ watchJob(r.job, 'tc'); })
    .catch(function(e){ toast('下载失败：' + e.message, true); });
}
function tcLaunch(){
  showProgress('正在启动陶瓦联机…');
  post('/api/terracotta/launch', {}).then(function(r){ watchJob(r.job, 'tc'); })
    .catch(function(e){ toast('启动失败：' + e.message, true); });
}

/* ---------- 设置 ---------- */
function saveSettings(){
  post('/api/settings', {config:{
    mirror: $('mirror').value,
    username: $('username').value.trim() || 'Steve',
    memory: parseInt($('memory').value) || 2048,
    java: $('java').value || '',
    workers: parseInt($('workers').value) || 16
  }}).catch(function(){});
}

function refreshJava(pick){
  return api('/api/java').then(function(d){
    var sel = $('java');
    sel.innerHTML = '';
    var list = (d && d.list) || [];
    if (!list.length){ sel.innerHTML = '<option value="">未检测到 Java</option>'; return; }
    list.forEach(function(j){
      var o = document.createElement('option');
      o.value = j.path;
      o.textContent = 'Java ' + j.major + ' · ' + j.path;
      if (pick && j.path === pick) o.selected = true;
      sel.appendChild(o);
    });
  });
}

function loadSettings(){
  api('/api/settings').then(function(d){
    var c = d.config || {};
    state.loaderNotes = {};
    (d.loaders || []).forEach(function(x){ state.loaderNotes[x.key] = x.note; });
    if (c.username) $('username').value = c.username;
    if (c.memory) $('memory').value = c.memory;
    if (c.workers) $('workers').value = c.workers;
    if (c.mirror) $('mirror').value = c.mirror;
    return api('/api/java');
  }).then(function(d){
    var sel = $('java');
    sel.innerHTML = '';
    var list = (d && d.list) || [];
    if (!list.length){ sel.innerHTML = '<option value="">未检测到 Java</option>'; return; }
    list.forEach(function(j){
      var o = document.createElement('option');
      o.value = j.path;
      o.textContent = 'Java ' + j.major + ' · ' + j.path;
      sel.appendChild(o);
    });
    return api('/api/settings').then(function(s){
      var want = (s.config || {}).java;
      if (want){ for (var i = 0; i < sel.options.length; i++) if (sel.options[i].value === want) sel.selectedIndex = i; }
    });
  }).catch(function(){}).finally(function(){ loadVersions(); loadInstances(); loadServers(); loadFrp(); loadTc(); renderNetHelp(); });
}

/* ---------- 绑定 ---------- */
$('search').oninput = renderList;
$('typeFilter').onchange = renderList;
$('btnRefresh').onclick = function(){ loadVersions(true); };
$('mirror').onchange = function(){ saveSettings(); state.current = null; loadVersions(); };
$('btnDownload').onclick = startDownload;
$('btnLaunch').onclick = launch;
$('btnLoader').onclick = installLoader;
$('btnJava').onclick = function(){
  var major = parseInt($('javaMajor').value) || 17;
  if (!confirm('下载 Adoptium JDK ' + major + '？约 180 MB，装到启动器目录的 java/ 下。')) return;
  showProgress('准备下载 Java ' + major + '…');
  $('btnJava').disabled = true;
  post('/api/java_install', {major: major})
    .then(function(r){ watchJob(r.job, 'java'); })
    .catch(function(e){ toast('下载失败：' + e.message, true); $('btnJava').disabled = false; });
};
$('loaderType').onchange = function(){ if (state.detail) loadLoaderVersions(state.detail.baseId); };
$('btnFolder').onclick = function(){
  var p = state.detail ? state.detail.gameDir : '.minecraft';
  post('/api/open', {path: p.replace(/\\/g, '/')}).catch(function(e){ toast(e.message, true); });
};
$('btnCancel').onclick = function(){
  if (!state.job) return;
  post('/api/cancel', {job: state.job}).catch(function(){});
};
$('btnModSearch').onclick = function(){ doSearch(0); };
$('modSearch').onkeydown = function(e){ if (e.key === 'Enter') doSearch(0); };
$('modSort').onchange = function(){ doSearch(0); };
$('modInstance').onchange = onModInstanceChange;
$('btnSrvSave').onclick = saveServerForm;
$('btnSrvClear').onclick = clearSrvForm;
$('btnFrpStart').onclick = frpStart;
$('btnFrpStop').onclick = frpStop;
$('btnTcInstall').onclick = tcInstall;
$('btnTcLaunch').onclick = tcLaunch;
function switchTab(name){
  document.querySelectorAll('.tab').forEach(function(x){
    x.className = 'tab' + (x.getAttribute('data-tab') === name ? ' on' : '');
  });
  $('tab-ver').className = name === 'ver' ? '' : 'hidden';
  $('tab-mod').className = name === 'mod' ? '' : 'hidden';
  $('tab-net').className = name === 'net' ? '' : 'hidden';
  if (name === 'mod') loadInstances();
  if (name === 'net'){ loadServers(); loadFrp(); loadTc(); }
}
document.querySelectorAll('.tab').forEach(function(t){
  t.onclick = function(){ switchTab(t.getAttribute('data-tab')); };
});
loadSettings();
try {
  if (new URLSearchParams(location.search).get('tab') === 'mod') setTimeout(function(){ switchTab('mod'); }, 900);
} catch (e) {}
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------- #
# 入口
# --------------------------------------------------------------------------- #

def find_free_port(start=8765):
    for port in range(start, start + 60):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                s.bind(("127.0.0.1", port))
                return port
            except OSError:
                continue
    return 0


def run_server(host="127.0.0.1", port=0, open_browser=True):
    if not port:
        port = find_free_port()
    httpd = ThreadingHTTPServer((host, port), Handler)
    httpd.daemon_threads = True
    url = f"http://{host}:{port}/"
    log(f"{APP_NAME} v{APP_VER} 已启动：{url}")
    log(f"游戏目录：{GAME_DIR}")
    if open_browser:
        threading.Thread(target=lambda: (time.sleep(0.6), webbrowser.open(url)), daemon=True).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        log("已退出")


def cli_list(mirror="bmcl"):
    man = get_manifest(mirror)
    print(f"{'版本':<24}{'类型':<12}{'发布时间'}")
    for v in man.get("versions", [])[:60]:
        print(f"{v['id']:<24}{TYPE_LABEL.get(v.get('type'), v.get('type')):<12}{v.get('releaseTime', '')[:10]}")
    print(f"... 共 {len(man.get('versions', []))} 个版本")


def cli_download(vid, only, skip_sounds=False, mirror="bmcl", workers=16):
    cfg = load_config()
    vj = resolve_version(mirror, vid)
    comps = [c.strip() for c in only.split(",") if c.strip()] if only else ["client", "libraries", "assets"]
    tasks = build_plan(vj, mirror, comps, skip_sounds)
    job = DownloadJob(vid, mirror, tasks, workers=workers, verify=cfg.get("verify_sha1", False))
    job.start()
    last = -1
    while job.status in ("pending", "running"):
        snap = job.snapshot()
        if int(snap["percent"]) != last:
            last = int(snap["percent"])
            sys.stdout.write(f"\r  {snap['percent']:5.1f}%  {human_size(snap['done'])}/{human_size(snap['total'])}"
                             f"  {human_size(snap['speed'])}/s  {snap['files']}/{snap['files_total']}   ")
            sys.stdout.flush()
        time.sleep(0.3)
    print()
    snap = job.snapshot()
    print(f"  {snap['status']}: {snap['message']}")
    for e in snap["errors"][:5]:
        print("  ! " + e)
    return 0 if snap["status"] == "done" else 1


def cli_selftest():
    print(f"{APP_NAME} v{APP_VER} 自检")
    print(f"  脚本目录 : {BASE_DIR}")
    print(f"  游戏目录 : {GAME_DIR}")
    print(f"  Python   : {sys.version.split()[0]}  ({sys.executable})")
    ok = True
    for key in MIRRORS:
        label = MIRRORS[key]["label"]
        t0 = time.time()
        try:
            man = get_manifest(key)
            n = len(man.get("versions", []))
            latest = (man.get("latest") or {}).get("release", "?")
            print(f"  [OK]   {label}: {n} 个版本，最新 {latest}，耗时 {time.time()-t0:.1f}s")
        except Exception as exc:  # noqa: BLE001
            ok = False
            print(f"  [FAIL] {label}: {exc}")
    for name, url in (("Fabric Meta", f"{FABRIC_META}/versions/loader/1.20.1"),
                      ("Modrinth", f"{MODRINTH_API}/search?query=sodium&limit=1")):
        try:
            fetch_json([url], timeout=20)
            print(f"  [OK]   {name}")
        except Exception as exc:  # noqa: BLE001
            ok = False
            print(f"  [FAIL] {name}: {exc}")
    javas = find_javas(force=True)
    if javas:
        for j in javas[:5]:
            print(f"  [JAVA] {j['major']:>3}  {j['path']}")
    else:
        print("  [JAVA] 未检测到 Java，请安装 Java 17 或 21")
    return 0 if ok else 1


def main(argv):
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        except Exception:  # noqa: BLE001
            pass
    args = argv[1:]
    if not args:
        return run_server()

    def opt(name, default=None):
        if name in args:
            i = args.index(name)
            if i + 1 < len(args):
                return args[i + 1]
        return default

    port = int(opt("--port", "0") or 0)
    host = opt("--host", "127.0.0.1")
    no_browser = "--no-browser" in args

    cmd = args[0]
    if cmd in ("--selftest", "-t"):
        return cli_selftest()
    if cmd in ("--list", "-l"):
        return cli_list() or 0
    if cmd == "--download":
        vid = args[1] if len(args) > 1 else ""
        if not vid:
            print("用法: --download <版本> [--only client,libraries,assets,logging] [--skip-sounds]")
            return 2
        only = "client,libraries,assets"
        if "--only" in args:
            only = args[args.index("--only") + 1]
        return cli_download(vid, only, "--skip-sounds" in args)
    if cmd == "--print-cmd":
        vid = args[1] if len(args) > 1 else ""
        if not vid:
            print("用法: --print-cmd <版本> [--server 地址 --port 端口 --authlib API]")
            return 2
        cfg = load_config()
        vj = resolve_version(cfg.get("mirror", "bmcl"), vid)
        server = opt("--server", "")
        port = int(opt("--port", "25565") or 25565)
        authlib = opt("--authlib", "")
        cmdline = build_command(vj, cfg.get("username", "Steve"), cfg.get("memory", 2048), cfg.get("java", ""),
                                server=server, server_port=port, authlib=authlib)
        print("\n".join(cmdline))
        return 0
    if cmd == "--servers":
        servers = load_config().get("servers") or []
        if not servers:
            print("还没有保存的服务器，在网页「联机」页添加")
            return 0
        for i, s in enumerate(servers):
            auth = "外置登录" if s.get("authlib") else "离线"
            print(f"  [{i}] {s.get('name','')}  {s.get('address','')}:{s.get('port',25565)}  {auth}")
        return 0
    if cmd == "--loaders":
        mc = args[1] if len(args) > 1 else ""
        if not mc:
            print("用法: --loaders <mc版本> [loader]")
            return 2
        loader = args[2] if len(args) > 2 else "fabric"
        items = loader_versions(mc, loader, load_config().get("mirror", "bmcl"))
        print(f"{mc} 可用的 {LOADER_LABEL.get(loader, loader)}：")
        for it in items[:20]:
            print(f"  {it['version']}{'（稳定）' if it['stable'] else ''}")
        return 0
    if cmd == "--install-loader":
        mc = args[1] if len(args) > 1 else ""
        loader = args[2] if len(args) > 2 else "fabric"
        if not mc:
            print("用法: --install-loader <mc版本> [fabric|quilt|legacyfabric|forge|neoforge] [loader版本]")
            return 2
        ver = args[3] if len(args) > 3 else ""
        info = install_loader(load_config().get("mirror", "bmcl"), mc, loader, ver)
        print(f"已安装：{info['id']}（{info['loader']} {info['loaderVersion']}）")
        return 0
    if cmd == "--install-java":
        major = args[1] if len(args) > 1 else "17"
        if not str(major).isdigit():
            print("用法: --install-java <8|17|21>")
            return 2
        info = install_java(int(major))
        print(f"Java {info['major']} 已就绪：{info['path']}")
        return 0
    if cmd == "--search-mod":
        name = args[1] if len(args) > 1 else ""
        vid = opt("--vid", "")
        if not name or not vid:
            print("用法: --search-mod <关键词> --vid <实例id>")
            return 2
        vj = resolve_version(load_config().get("mirror", "bmcl"), vid)
        data = modrinth_search(name, mod_loader_name(vj.get("_loader", "")), vj.get("_base_id", vid))
        for h in data["hits"][:15]:
            print(f"  {h['title']:<30} {h['id']}  {fmt_dl(h['downloads'])}")
        return 0
    if cmd == "--install-mod":
        name = args[1] if len(args) > 1 else ""
        vid = opt("--vid", "")
        if not name or not vid:
            print("用法: --install-mod <项目id或slug> --vid <实例id>")
            return 2
        pid = name
        if not re.fullmatch(r"[A-Za-z0-9]{8}", name):
            hits = modrinth_search(name, "", "")["hits"]
            if not hits:
                print("没有搜到该模组")
                return 1
            pid = hits[0]["id"]
            print(f"匹配到：{hits[0]['title']}（{pid}）")
        files = install_mod(vid, pid)
        for f in files:
            print(f"  + {f['file']}")
        return 0
    if cmd in ("--help", "-h"):
        print(__doc__)
        return 0
    if cmd.startswith("--"):
        if cmd in ("--port", "--host", "--no-browser"):
            return run_server(host=host, port=port, open_browser=not no_browser)
    print(f"未知参数 {cmd}，用 --help 查看用法")
    return 2


def fmt_dl(n):
    n = float(n or 0)
    for u in ("", "K", "M", "B"):
        if n < 1000 or u == "B":
            return f"{n:.0f}{u}"
        n /= 1000.0
    return f"{n:.0f}"


if __name__ == "__main__":
    atexit.register(stop_frp)   # 启动器退出时顺手关掉 frpc，不留后台进程
    sys.exit(main(sys.argv))
