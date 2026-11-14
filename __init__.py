"""PocketComfy: ComfyUI server extension for the PocketComfy mobile app. GPL-3.0."""
import asyncio
import base64
import gzip
import hashlib
import heapq
import ipaddress
import json
import logging
import os
import queue
import re
import shutil
import socket
import sqlite3
import struct
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zlib

from aiohttp import web
from PIL import Image
from server import PromptServer
import folder_paths

POCKET_VERSION = "2.0.0"
NODE_CLASS_MAPPINGS = {}
NODE_DISPLAY_NAME_MAPPINGS = {}

HERE = os.path.dirname(os.path.abspath(__file__))
WEB_DIR = os.path.join(HERE, "web")
THUMB_DIR = os.path.join(tempfile.gettempdir(), "comfyui_pocket_thumbs")
IMAGE_EXT = {".png", ".jpg", ".jpeg", ".webp", ".gif", ".bmp"}
VIDEO_EXT = {".mp4", ".webm", ".mov", ".mkv"}
TYPES = {
    ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
    ".css": "text/css; charset=utf-8", ".svg": "image/svg+xml",
    ".webmanifest": "application/manifest+json", ".json": "application/json",
    ".png": "image/png",
}
_cache = {"at": 0.0, "items": []}
DURATIONS = {}


def inside(base, path):
    base = os.path.normcase(os.path.realpath(base))
    path = os.path.normcase(os.path.realpath(path))
    try:
        return os.path.commonpath([base, path]) == base
    except ValueError:
        return False


def scan_outputs():
    now = time.time()
    if now - _cache["at"] < 3:
        return _cache["items"]
    root = folder_paths.get_output_directory()
    items = []
    for folder, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        rel = os.path.relpath(folder, root).replace("\\", "/")
        rel = "" if rel == "." else rel
        for name in files:
            if os.path.splitext(name)[1].lower() not in IMAGE_EXT | VIDEO_EXT:
                continue
            try:
                st = os.stat(os.path.join(folder, name))
            except OSError:
                continue
            items.append({"filename": name, "subfolder": rel, "type": "output",
                          "mtime": st.st_mtime, "size": st.st_size,
                          "duration": DURATIONS.get(f"{rel}/{name}")})
    items.sort(key=lambda x: x["mtime"], reverse=True)
    _cache.update(at=now, items=items)
    return items


def video_frame(path):
    """Первый кадр ролика. ComfyUI ставит PyAV для своих видеонод; без него будет заглушка."""
    try:
        import av
        with av.open(path) as container:
            for frame in container.decode(video=0):
                return frame.to_image()
    except Exception:
        pass
    return Image.new("RGB", (480, 704), (29, 29, 26))


def video_text(path):
    """Настройки, которые SaveVideo записывает в метаданные файла."""
    out = {}
    try:
        import av
        with av.open(path) as container:
            for key in ("prompt", "workflow"):
                value = container.metadata.get(key)
                if isinstance(value, str):
                    out[key] = value
    except Exception:
        pass
    return out


def make_thumb(path, width):
    st = os.stat(path)
    key = hashlib.sha1(f"{path}|{st.st_mtime}|{width}".encode("utf-8")).hexdigest()
    os.makedirs(THUMB_DIR, exist_ok=True)
    target = os.path.join(THUMB_DIR, key + ".webp")
    if not os.path.exists(target):
        is_video = os.path.splitext(path)[1].lower() in VIDEO_EXT
        with (video_frame(path) if is_video else Image.open(path)) as im:
            im = im.convert("RGB")
            im.thumbnail((width, width * 3))
            tmp = target + f".{os.getpid()}.tmp"
            im.save(tmp, "WEBP", quality=72)
            os.replace(tmp, target)
    return target


routes = PromptServer.instance.routes


# --- Прогресс генерации для всех устройств --------------------------------
# ComfyUI шлёт шаги, превью и начало генерации только тому, кто её запустил.
# Эти события дублируются всем подключённым устройствам, чтобы на каждом было
# видно ход чужой генерации (шаги, превью) и её можно было прервать.

_broadcast_patched = False
# Адресные события, которые дублируем всем. Завершение и ошибку НЕ дублируем:
# иначе на чужом устройстве выскочит «картинка готова» или окно ошибки.
_FANOUT_EVENTS = {"execution_start", "executing", "progress", "progress_state"}


def _running_node_title(server, prompt_id, node_id):
    """Название ноды из выполняемого задания: у чужого устройства нет этого графа."""
    try:
        running = getattr(server.prompt_queue, "currently_running", {}) or {}
        for item in list(running.values()):
            if prompt_id and item[1] != prompt_id:
                continue
            node = (item[2] or {}).get(str(node_id)) or {}
            title = (node.get("_meta") or {}).get("title") or node.get("class_type")
            if title:
                return str(title)
    except Exception:
        pass
    return None


# Текущий ход генерации. Приложение опрашивает его, если пропустило события по сокету:
# так прогресс и превью видны всегда, кто бы ни запустил генерацию.
LIVE = {"id": None, "node": None, "title": None, "value": 0, "max": 0, "at": 0.0, "preview": None, "seq": 0}
LIVE_LOCK = threading.Lock()


def _preview_jpeg(preview):
    """Превью из ComfyUI (формат, картинка PIL, размер) в JPEG-байты."""
    image = preview[1] if isinstance(preview, (tuple, list)) and len(preview) > 1 else preview
    if not hasattr(image, "save"):
        return None
    import io
    buf = io.BytesIO()
    image.convert("RGB").save(buf, format="JPEG", quality=80)
    return buf.getvalue()


def live_record(server, event, data, preview_events):
    now = time.time()
    if event in preview_events:
        preview = data[0] if isinstance(data, (tuple, list)) and len(data) == 2 and isinstance(data[1], dict) else data
        jpeg = _preview_jpeg(preview)
        if jpeg:
            with LIVE_LOCK:
                LIVE["preview"] = jpeg
                LIVE["seq"] += 1
                LIVE["at"] = now
        return
    if not isinstance(data, dict):
        return
    with LIVE_LOCK:
        if event == "execution_start":
            LIVE.update(id=data.get("prompt_id"), node=None, title=None, value=0, max=0, preview=None, at=now)
        elif event == "executing":
            node = data.get("node")
            if node is None:
                if data.get("prompt_id") in (None, LIVE["id"]):
                    LIVE.update(id=None, node=None, title=None, value=0, max=0, preview=None, at=now)
            else:
                LIVE["id"] = data.get("prompt_id") or LIVE["id"]
                LIVE["node"] = str(node)
                LIVE["title"] = _running_node_title(server, data.get("prompt_id"), node)
                LIVE["value"], LIVE["max"], LIVE["at"] = 0, 0, now
        elif event == "progress":
            LIVE["id"] = data.get("prompt_id") or LIVE["id"]
            LIVE["value"] = int(data.get("value") or 0)
            LIVE["max"] = int(data.get("max") or 0)
            LIVE["at"] = now
        elif event in ("execution_success", "execution_error", "execution_interrupted"):
            if data.get("prompt_id") in (None, LIVE["id"]):
                LIVE.update(id=None, node=None, title=None, value=0, max=0, preview=None, at=now)


def broadcast_install(server):
    """Оборачивает server.send так, чтобы прогресс шёл на все устройства, а не только запустившему."""
    global _broadcast_patched
    if _broadcast_patched or getattr(server, "_pocket_original_send", None) is not None:
        return
    try:
        from protocol import BinaryEventTypes
        from server import send_socket_catch_exception
    except Exception as error:
        logging.warning("[PocketComfy] progress forwarding unavailable: %s", error)
        return
    original_send = server.send
    preview_events = {BinaryEventTypes.UNENCODED_PREVIEW_IMAGE, BinaryEventTypes.PREVIEW_IMAGE_WITH_METADATA}

    async def send(event, data, sid=None):
        await original_send(event, data, sid)
        try:
            live_record(server, event, data, preview_events)
        except Exception as error:
            logging.debug("[PocketComfy] live progress: %s", error)
        if sid is None:
            return  # уже ушло всем
        try:
            targets = [(k, ws) for k, ws in server.sockets.items() if k != sid]
            if not targets:
                return
            if event in _FANOUT_EVENTS:
                extra = {"pocket_foreign": True}
                if event == "executing" and isinstance(data, dict) and data.get("node") is not None:
                    title = _running_node_title(server, data.get("prompt_id"), data.get("node"))
                    if title:
                        extra["pocket_title"] = title
                message = {"type": event, "data": {**data, **extra} if isinstance(data, dict) else data}
                for _, ws in targets:
                    await send_socket_catch_exception(ws.send_json, message)
            elif event in preview_events:
                # Приводим превью к простому формату PREVIEW_IMAGE, понятному всем клиентам.
                preview = data[0] if event == BinaryEventTypes.PREVIEW_IMAGE_WITH_METADATA else data
                for k, _ in targets:
                    await server.send_image(preview, sid=k)
        except Exception as error:
            logging.debug("[PocketComfy] progress forwarding: %s", error)

    server.send = send
    server._pocket_original_send = original_send
    _broadcast_patched = True


broadcast_install(PromptServer.instance)


@routes.get("/pocket/api/live")
async def pocket_live(request):
    """Ход текущей генерации: id, нода, шаги и номер последнего превью."""
    running = []
    try:
        running, _ = PromptServer.instance.prompt_queue.get_current_queue_volatile()
    except Exception:
        pass
    ids = [x[1] for x in running]
    with LIVE_LOCK:
        live = {k: LIVE[k] for k in ("id", "node", "title", "value", "max", "seq")}
        live["has_preview"] = LIVE["preview"] is not None
    if live["id"] is None and ids:
        live["id"] = ids[0]
    live["running"] = ids
    return web.json_response(live)


@routes.get("/pocket/api/live/preview")
async def pocket_live_preview(request):
    with LIVE_LOCK:
        jpeg = LIVE["preview"]
    if not jpeg:
        return web.Response(status=204)
    return web.Response(body=jpeg, headers={"Content-Type": "image/jpeg", "Cache-Control": "no-store"})


@routes.get("/pocket/api/outputs")
async def pocket_outputs(request):
    try:
        offset = max(0, int(request.query.get("offset", 0)))
        limit = min(200, max(1, int(request.query.get("limit", 60))))
    except ValueError:
        return web.json_response({"error": "bad paging"}, status=400)
    folder = request.query.get("folder")
    loop = asyncio.get_running_loop()
    items = await loop.run_in_executor(None, scan_outputs)
    folders = {}
    for it in items:
        folders[it["subfolder"]] = folders.get(it["subfolder"], 0) + 1
    if folder is not None:
        items = [i for i in items if i["subfolder"] == folder]
    return web.json_response({
        "total": len(items), "items": items[offset:offset + limit],
        "folders": [{"name": k, "count": v} for k, v in sorted(folders.items())],
    })


@routes.get("/pocket/api/thumb")
async def pocket_thumb(request):
    root = folder_paths.get_directory_by_type(request.query.get("type", "output"))
    if not root:
        return web.Response(status=404)
    path = os.path.join(root, request.query.get("subfolder", ""), request.query.get("filename", ""))
    if not inside(root, path) or not os.path.isfile(path):
        return web.Response(status=404)
    try:
        width = min(1024, max(64, int(request.query.get("w", 384))))
        loop = asyncio.get_running_loop()
        target = await loop.run_in_executor(None, make_thumb, path, width)
    except Exception:
        return web.Response(status=415)
    return web.FileResponse(target, headers={
        "Content-Type": "image/webp", "Cache-Control": "public, max-age=604800"})


@routes.get("/pocket")
async def pocket_redirect(request):
    raise web.HTTPFound("/pocket/")


@routes.get("/pocket/")
async def pocket_index(request):
    index = os.path.join(WEB_DIR, "index.html")
    if os.path.isfile(index):
        return web.FileResponse(index, headers={"Content-Type": TYPES[".html"], "Cache-Control": "no-cache"})
    return web.Response(text="PocketComfy extension is running. Open the PocketComfy app on your phone and connect to this computer.",
                        headers={"Cache-Control": "no-cache"})


# История генераций. ComfyUI хранит её только до перезапуска, поэтому копия пишется в файл.
HISTORY = []
HISTORY_IDS = set()
HISTORY_LOCK = threading.Lock()
SYNC_LOCK = threading.Lock()
RUN_SEEN = {}
PROMPTS = {}
MAX_HISTORY = 5000


def history_file():
    return os.path.join(folder_paths.get_user_directory(), "pocket_history.jsonl")


def prompt_text(prompt):
    """Текст позитивного промта из задания."""
    if not isinstance(prompt, dict):
        return ""
    for node in prompt.values():
        link = (node.get("inputs") or {}).get("positive")
        for _ in range(6):
            if not (isinstance(link, list) and link):
                break
            src = prompt.get(str(link[0])) or {}
            text = (src.get("inputs") or {}).get("text")
            if isinstance(text, str):
                return text[:400]
            link = (src.get("inputs") or {}).get("conditioning") or (src.get("inputs") or {}).get("positive")
    texts = [n["inputs"]["text"] for n in prompt.values() if isinstance((n.get("inputs") or {}).get("text"), str)]
    return (max(texts, key=len) if texts else "")[:400]


def summarize(prompt_id, entry):
    item = entry.get("prompt") or (0, prompt_id, {}, {}, [])
    status = entry.get("status") or {}
    times = {}
    error = None
    for ev, data in status.get("messages") or []:
        data = data or {}
        if "timestamp" in data:
            times[ev] = data["timestamp"]
        if ev == "execution_error":
            error = f"{data.get('node_type', '')}: {data.get('exception_message', '')}".strip(": \n")[:400]
    start = times.get("execution_start")
    end = times.get("execution_success") or times.get("execution_error") or times.get("execution_interrupted")
    images = []
    for out in (entry.get("outputs") or {}).values():
        for im in (out or {}).get("images") or []:
            if im.get("type") == "output":
                images.append({"filename": im.get("filename"), "subfolder": str(im.get("subfolder", "")).replace("\\", "/"), "type": "output"})
    if not images:
        for out in (entry.get("outputs") or {}).values():
            for im in (out or {}).get("images") or []:
                images.append({"filename": im.get("filename"), "subfolder": str(im.get("subfolder", "")).replace("\\", "/"), "type": im.get("type", "temp")})
    state = "done" if status.get("completed", True) and "execution_error" not in times and "execution_interrupted" not in times else ("stopped" if "execution_interrupted" in times else "error")
    packed = ""
    try:
        packed = base64.b64encode(gzip.compress(json.dumps(item[2]).encode("utf-8"), 6)).decode("ascii")
    except (TypeError, ValueError):
        pass
    return {"id": prompt_id, "number": item[0], "state": state, "start": start, "end": end,
            "duration": round((end - start) / 1000, 1) if start and end else None,
            "images": images, "text": prompt_text(item[2]), "error": error, "p": packed}


def remember(sm):
    packed = sm.pop("p", None)
    with HISTORY_LOCK:
        if sm["id"] in HISTORY_IDS:
            return False
        HISTORY_IDS.add(sm["id"])
        if packed:
            PROMPTS[sm["id"]] = packed
        HISTORY.append(sm)
        if sm["duration"] is not None:
            for im in sm["images"]:
                DURATIONS[f"{im['subfolder']}/{im['filename']}"] = sm["duration"]
        if len(HISTORY) > MAX_HISTORY:
            old = HISTORY.pop(0)["id"]
            HISTORY_IDS.discard(old)
            PROMPTS.pop(old, None)
    return True


def load_history():
    try:
        with open(history_file(), encoding="utf-8") as f:
            lines = f.readlines()[-MAX_HISTORY:]
    except OSError:
        return
    for line in lines:
        try:
            remember(json.loads(line))
        except (ValueError, KeyError, TypeError):
            continue


def sync_history():
    """Переносит завершённые задания из памяти ComfyUI в постоянную историю."""
    queue_obj = getattr(PromptServer.instance, "prompt_queue", None)
    if queue_obj is None:
        return
    with SYNC_LOCK:
        running, _ = queue_obj.get_current_queue_volatile()
        ids = {x[1] for x in running}
        now = time.time()
        for i in ids:
            RUN_SEEN.setdefault(i, now)
        for i in [k for k in RUN_SEEN if k not in ids]:
            RUN_SEEN.pop(i, None)
        fresh = []
        for pid, entry in queue_obj.get_history(max_items=64, map_function=lambda p: p).items():
            if pid not in HISTORY_IDS and entry.get("status") is not None:
                sm = summarize(pid, entry)
                line = json.dumps(sm, ensure_ascii=False)
                if remember(sm):
                    fresh.append((sm.get("number") or 0, line))
        if fresh:
            fresh.sort(key=lambda x: x[0])
            _cache["at"] = 0.0
            path = history_file()
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "a", encoding="utf-8") as f:
                for _, line in fresh:
                    f.write(line + "\n")


def history_worker():
    load_history()
    while True:
        time.sleep(2)
        try:
            sync_history()
        except Exception as e:  # поток истории не должен ронять ComfyUI
            print(f"[PocketComfy] history: {type(e).__name__}: {e}")
            time.sleep(5)


threading.Thread(target=history_worker, daemon=True, name="pocket-history").start()


# Очередь: порядок, пауза и оценка времени поверх стандартной очереди ComfyUI.
HELD = []
QUEUE_PAUSED = False
QUEUE_LOCK = threading.RLock()
_queue_patched = None


def queue_install(q):
    """На время паузы новые задания откладываются сразу, ещё до того, как их заберёт рабочий поток."""
    global _queue_patched
    if _queue_patched is q:
        return
    original = q.put

    def put(item):
        with QUEUE_LOCK:
            if QUEUE_PAUSED:
                HELD.append(item)
                q.server.queue_updated()
                return
        original(item)

    q.put = put
    q._pocket_original_put = original
    _queue_patched = q


def queue_set_paused(q, paused):
    global QUEUE_PAUSED
    queue_install(q)
    with q.mutex:
        with QUEUE_LOCK:
            if paused and not QUEUE_PAUSED:
                QUEUE_PAUSED = True
                HELD.extend(q.queue)
                q.queue.clear()
            elif not paused and QUEUE_PAUSED:
                QUEUE_PAUSED = False
                held = list(HELD)
                HELD.clear()
                for item in held:
                    q._pocket_original_put(item)
            q.server.queue_updated()


def _reorder(items, prompt_id, where):
    """Меняет порядок, сохраняя набор номеров. Возвращает новый список или None."""
    ordered = sorted(items, key=lambda x: x[0])
    ids = [x[1] for x in ordered]
    if prompt_id not in ids:
        return None
    i = ids.index(prompt_id)
    target = {"top": 0, "bottom": len(ordered) - 1, "up": max(0, i - 1), "down": min(len(ordered) - 1, i + 1)}.get(where)
    if target is None:
        return None
    numbers = [x[0] for x in ordered]
    ordered.insert(target, ordered.pop(i))
    return [(numbers[n],) + tuple(item[1:]) for n, item in enumerate(ordered)]


def queue_move(q, prompt_id, where):
    with q.mutex:
        with QUEUE_LOCK:
            if QUEUE_PAUSED:
                new = _reorder(HELD, prompt_id, where)
                if new is None:
                    return False
                HELD[:] = new
            else:
                new = _reorder(q.queue, prompt_id, where)
                if new is None:
                    return False
                q.queue[:] = new
                heapq.heapify(q.queue)
            q.server.queue_updated()
    return True


def queue_remove(q, prompt_id):
    with q.mutex:
        with QUEUE_LOCK:
            removed = [x for x in HELD if x[1] == prompt_id]
            HELD[:] = [x for x in HELD if x[1] != prompt_id]
            kept = [x for x in q.queue if x[1] != prompt_id]
            removed += [x for x in q.queue if x[1] == prompt_id]
            if len(kept) != len(q.queue):
                q.queue[:] = kept
                heapq.heapify(q.queue)
            q.server.queue_updated()
    return len(removed)


def queue_clear(q):
    with q.mutex:
        with QUEUE_LOCK:
            count = len(HELD) + len(q.queue)
            HELD.clear()
            q.queue.clear()
            q.server.queue_updated()
    return count


def median_duration(items, count=20):
    values = sorted(i["duration"] for i in items[:count] if i.get("state") == "done" and i.get("duration"))
    if not values:
        return None
    middle = len(values) // 2
    return round(values[middle] if len(values) % 2 else (values[middle - 1] + values[middle]) / 2, 1)


@routes.post("/pocket/api/queue/move")
async def pocket_queue_move(request):
    data = await request.json()
    moved = queue_move(PromptServer.instance.prompt_queue, data.get("id"), data.get("where"))
    return web.json_response({"moved": moved}, status=200 if moved else 404)


@routes.post("/pocket/api/queue/remove")
async def pocket_queue_remove(request):
    data = await request.json()
    return web.json_response({"removed": queue_remove(PromptServer.instance.prompt_queue, data.get("id"))})


@routes.post("/pocket/api/queue/clear")
async def pocket_queue_clear(request):
    return web.json_response({"removed": queue_clear(PromptServer.instance.prompt_queue)})


@routes.post("/pocket/api/queue/pause")
async def pocket_queue_pause(request):
    data = await request.json()
    queue_set_paused(PromptServer.instance.prompt_queue, bool(data.get("paused")))
    return web.json_response({"paused": QUEUE_PAUSED})


@routes.get("/pocket/api/history")
async def pocket_history(request):
    try:
        offset = max(0, int(request.query.get("offset", 0)))
        limit = min(500, max(1, int(request.query.get("limit", 60))))
    except ValueError:
        return web.json_response({"error": "bad paging"}, status=400)
    state = request.query.get("state")
    loop = asyncio.get_running_loop()
    await loop.run_in_executor(None, sync_history)
    queue_obj = PromptServer.instance.prompt_queue
    running, queued = queue_obj.get_current_queue_volatile()
    with QUEUE_LOCK:
        queued = list(queued) + list(HELD)
    now = time.time()
    with HISTORY_LOCK:
        items = list(HISTORY)
    items.sort(key=lambda x: (x.get("end") or x.get("start") or 0, x.get("number") or 0), reverse=True)
    avg = median_duration(items)
    counts = {"done": 0, "stopped": 0, "error": 0}
    for i in items:
        counts[i.get("state")] = counts.get(i.get("state"), 0) + 1
    if state == "done":
        items = [i for i in items if i["state"] == "done"]
    elif state == "failed":
        items = [i for i in items if i["state"] != "done"]
    queued = sorted(queued, key=lambda x: x[0])
    return web.json_response({
        "running": [{"id": x[1], "number": x[0], "text": prompt_text(x[2]),
                     "elapsed": round(now - RUN_SEEN.get(x[1], now), 1)} for x in running],
        "pending": [{"id": x[1], "number": x[0], "text": prompt_text(x[2]), "position": i + 1}
                    for i, x in enumerate(queued)],
        "items": items[offset:offset + limit], "total": len(items), "paused": QUEUE_PAUSED, "avg": avg,
        "counts": counts,
    })


@routes.get("/pocket/api/history/prompt")
async def pocket_history_prompt(request):
    packed = PROMPTS.get(request.query.get("id", ""))
    if not packed:
        return web.json_response({"error": "Settings were not saved for this entry."}, status=404)
    return web.json_response({"prompt": json.loads(gzip.decompress(base64.b64decode(packed)).decode("utf-8"))})


def rewrite_history():
    path = history_file()
    tmp = path + ".tmp"
    with HISTORY_LOCK:
        items = [dict(i, p=PROMPTS.get(i["id"], "")) for i in HISTORY]
    with open(tmp, "w", encoding="utf-8") as f:
        for it in items:
            f.write(json.dumps(it, ensure_ascii=False) + "\n")
    os.replace(tmp, path)


@routes.post("/pocket/api/history/delete")
async def pocket_history_delete(request):
    """Убирает записи истории. Картинки переносятся в корзину, только если об этом попросили."""
    data = await request.json()
    with HISTORY_LOCK:
        states = set(data.get("states") or [])
        if data.get("all") is True:
            ids = {i["id"] for i in HISTORY}
        elif states:
            ids = {i["id"] for i in HISTORY if i.get("state") in states}
        else:
            ids = set(data.get("ids") or [])
        gone = [i for i in HISTORY if i["id"] in ids]
        HISTORY[:] = [i for i in HISTORY if i["id"] not in ids]
        for i in gone:
            PROMPTS.pop(i["id"], None)
    loop = asyncio.get_running_loop()
    with SYNC_LOCK:
        await loop.run_in_executor(None, rewrite_history)
    trashed = []
    if data.get("with_images") is True:
        images = [im for i in gone for im in i.get("images", []) if im.get("type") == "output"]
        trashed = await loop.run_in_executor(None, trash_items, images)
    return web.json_response({"deleted": len(gone), "trash": trashed})


# Каталог: поиск, избранное, оценки и корзина
TRASH = ".pocket_trash"
DB_LOCK = threading.RLock()
_db = None
KNOWN = {}
INDEX_WAKE = threading.Event()
_like = lambda s: "%" + s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%"


def catalog_db():
    global _db
    with DB_LOCK:
        if _db is None:
            root = folder_paths.get_user_directory()
            os.makedirs(root, exist_ok=True)
            _db = sqlite3.connect(os.path.join(root, "pocket_catalog.sqlite"), check_same_thread=False)
            _db.execute("PRAGMA journal_mode=WAL")
            _db.executescript("""
                CREATE TABLE IF NOT EXISTS images(
                    key TEXT PRIMARY KEY, subfolder TEXT, filename TEXT, mtime REAL, size INTEGER,
                    positive TEXT DEFAULT '', negative TEXT DEFAULT '', models TEXT DEFAULT '', loras TEXT DEFAULT '',
                    favorite INTEGER DEFAULT 0, rating INTEGER DEFAULT 0, indexed INTEGER DEFAULT 0);
                CREATE INDEX IF NOT EXISTS images_mtime ON images(mtime DESC);
                CREATE INDEX IF NOT EXISTS images_pending ON images(indexed);
                CREATE TABLE IF NOT EXISTS trash(
                    id TEXT PRIMARY KEY, file TEXT, subfolder TEXT, filename TEXT, deleted_at REAL, size INTEGER,
                    favorite INTEGER DEFAULT 0, rating INTEGER DEFAULT 0);
                CREATE TABLE IF NOT EXISTS collections(
                    id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, created REAL);
                CREATE TABLE IF NOT EXISTS collection_items(
                    cid INTEGER NOT NULL, key TEXT NOT NULL, added REAL, PRIMARY KEY(cid, key));
                CREATE INDEX IF NOT EXISTS collection_items_key ON collection_items(key);
            """)
            _db.commit()
        return _db


def read_png_text(path):
    out = {}
    with open(path, "rb") as f:
        if f.read(8) != b"\x89PNG\r\n\x1a\n":
            return out
        while True:
            head = f.read(8)
            if len(head) < 8:
                return out
            size = struct.unpack(">I", head[:4])[0]
            kind = head[4:]
            if kind in (b"IDAT", b"IEND"):
                return out
            if kind in (b"tEXt", b"zTXt", b"iTXt") and size < 16 * 1024 * 1024:
                data = f.read(size)
                f.seek(4, 1)
                key, _, rest = data.partition(b"\0")
                name = key.decode("latin-1")
                if name not in ("prompt", "parameters"):
                    continue
                try:
                    if kind == b"tEXt":
                        out[name] = rest.decode("utf-8", "replace")
                    elif kind == b"zTXt":
                        out[name] = zlib.decompress(rest[1:]).decode("utf-8", "replace")
                    else:
                        compressed = rest[0] == 1
                        body = rest[2:].split(b"\0", 2)[2]
                        out[name] = (zlib.decompress(body) if compressed else body).decode("utf-8", "replace")
                except (ValueError, IndexError, zlib.error):
                    pass
            else:
                f.seek(size + 4, 1)


def read_other_text(path):
    out = {}
    with Image.open(path) as im:
        for key in ("prompt", "parameters"):
            if isinstance(im.info.get(key), str):
                out[key] = im.info[key]
        exif = im.getexif()
        for tag in (0x010F, 0x0110):
            value = exif.get(tag)
            if isinstance(value, str) and value.lower().startswith("prompt:"):
                out["prompt"] = value[7:].strip()
        comment = exif.get_ifd(0x8769).get(0x9286)
        if isinstance(comment, bytes):
            body = comment[8:] if comment[:8] in (b"UNICODE\0", b"ASCII\0\0\0", b"\0" * 8) else comment
            zeros = sum(1 for c in body[:200:2] if c == 0)
            encoding = "utf-16-be" if zeros > 20 else "utf-16-le" if comment[:7] == b"UNICODE" else "utf-8"
            out.setdefault("parameters", body.decode(encoding, "replace"))
    return out


def linked_text(prompt, key):
    for node in prompt.values():
        if not isinstance(node, dict):
            continue
        link = (node.get("inputs") or {}).get(key)
        for _ in range(6):
            if not (isinstance(link, list) and link):
                break
            src = prompt.get(str(link[0])) or {}
            inputs = src.get("inputs") or {}
            if isinstance(inputs.get("text"), str):
                return inputs["text"]
            link = inputs.get("conditioning") or inputs.get(key)
    return ""


def describe_image(path):
    """Промт, негативный промт, модели и LoRA из настроек внутри файла."""
    if os.path.splitext(path)[1].lower() in VIDEO_EXT:
        raw = video_text(path)
    else:
        raw = read_png_text(path) if path.lower().endswith(".png") else read_other_text(path)
    positive = negative = ""
    models, loras = set(), set()
    if raw.get("prompt"):
        try:
            prompt = json.loads(raw["prompt"].replace("NaN", "null"))
        except ValueError:
            prompt = None
        if isinstance(prompt, dict):
            positive = linked_text(prompt, "positive")
            negative = linked_text(prompt, "negative")
            if not positive:
                positive = prompt_text(prompt)
            for node in prompt.values():
                inputs = (node.get("inputs") if isinstance(node, dict) else None) or {}
                for key in ("ckpt_name", "unet_name"):
                    if isinstance(inputs.get(key), str):
                        models.add(inputs[key])
                if isinstance(inputs.get("lora_name"), str):
                    loras.add(inputs["lora_name"])
    elif raw.get("parameters"):
        text = raw["parameters"]
        head, _, tail = text.rpartition("\nSteps:")
        positive, _, negative = head.partition("\nNegative prompt:")
        match = re.search(r"Model:\s*([^,\n]+)", tail)
        if match:
            models.add(match.group(1).strip())
        loras.update(re.findall(r"<lora:([^:>]+)", text))
    pack = lambda names: "|" + "|".join(sorted(names)) + "|" if names else ""
    return positive, negative, pack(models), pack(loras)


def catalog_sync():
    """Сверяет таблицу с файлами на диске."""
    items = scan_outputs()
    db = catalog_db()
    with DB_LOCK:
        if not KNOWN:
            KNOWN.update(db.execute("SELECT key, mtime FROM images").fetchall())
        seen = set()
        fresh = []
        for it in items:
            key = f"{it['subfolder']}/{it['filename']}"
            seen.add(key)
            if KNOWN.get(key) != it["mtime"]:
                fresh.append((key, it["subfolder"], it["filename"], it["mtime"], it["size"]))
                KNOWN[key] = it["mtime"]
        gone = [k for k in KNOWN if k not in seen]
        if fresh:
            db.executemany("""INSERT INTO images(key, subfolder, filename, mtime, size) VALUES(?,?,?,?,?)
                              ON CONFLICT(key) DO UPDATE SET mtime=excluded.mtime, size=excluded.size, indexed=0""", fresh)
        if gone:
            db.executemany("DELETE FROM images WHERE key=?", [(k,) for k in gone])
            for k in gone:
                KNOWN.pop(k, None)
        if fresh or gone:
            db.commit()


def catalog_index_batch(limit=100):
    db = catalog_db()
    root = folder_paths.get_output_directory()
    with DB_LOCK:
        rows = db.execute("SELECT key, subfolder, filename FROM images WHERE indexed=0 ORDER BY mtime DESC LIMIT ?", (limit,)).fetchall()
    done = []
    for key, sub, name in rows:
        try:
            info = describe_image(os.path.join(root, sub, name))
        except Exception:
            info = ("", "", "", "")
        done.append((*info, key))
        time.sleep(0.002)
    with DB_LOCK:
        db.executemany("UPDATE images SET positive=?, negative=?, models=?, loras=?, indexed=1 WHERE key=?", done)
        db.commit()
    return len(rows)


def clean_mask_uploads():
    """Убирает временные фрагменты масок старше недели."""
    box = os.path.join(folder_paths.get_input_directory(), "pocket_mask")
    limit = time.time() - 7 * 86400
    try:
        for name in os.listdir(box):
            path = os.path.join(box, name)
            if os.path.isfile(path) and os.path.getmtime(path) < limit:
                os.remove(path)
    except OSError:
        pass


def catalog_worker():
    clean_mask_uploads()
    while True:
        try:
            catalog_sync()
            while catalog_index_batch():
                pass
        except Exception as e:  # индекс не должен мешать ComfyUI
            print(f"[PocketComfy] catalog: {type(e).__name__}: {e}")
        INDEX_WAKE.wait(20)
        INDEX_WAKE.clear()


threading.Thread(target=catalog_worker, daemon=True, name="pocket-catalog").start()


def catalog_query(q):
    where, args = [], []
    fields = {"prompt": ["positive"], "model": ["models"], "lora": ["loras"]}.get(q.get("in"), ["positive", "models", "loras", "filename"])
    for token in (q.get("q") or "").split():
        where.append("(" + " OR ".join(f"{f} LIKE ? ESCAPE '\\'" for f in fields) + ")")
        args += [_like(token)] * len(fields)
    if q.get("favorite") == "1":
        where.append("favorite=1")
    if (q.get("min_rating") or "").isdigit() and int(q["min_rating"]) > 0:
        where.append("rating>=?")
        args.append(int(q["min_rating"]))
    if q.get("model"):
        where.append("models LIKE ? ESCAPE '\\'")
        args.append(_like("|" + q["model"] + "|"))
    if q.get("lora"):
        where.append("loras LIKE ? ESCAPE '\\'")
        args.append(_like("|" + q["lora"] + "|"))
    if q.get("folder") is not None:
        where.append("subfolder=?")
        args.append(q["folder"])
    if q.get("collection"):
        where.append("key IN (SELECT key FROM collection_items WHERE cid=?)")
        args.append(int(q["collection"]))
    if q.get("similar"):
        return catalog_similar(q["similar"], max(0, int(q.get("offset", 0))), min(200, max(1, int(q.get("limit", 60)))))
    clause = (" WHERE " + " AND ".join(where)) if where else ""
    order = {"rating": "rating DESC, mtime DESC", "oldest": "mtime ASC"}.get(q.get("sort"), "mtime DESC")
    offset, limit = max(0, int(q.get("offset", 0))), min(200, max(1, int(q.get("limit", 60))))
    db = catalog_db()
    with DB_LOCK:
        total = db.execute("SELECT COUNT(*) FROM images" + clause, args).fetchone()[0]
        rows = db.execute("SELECT subfolder, filename, mtime, size, favorite, rating, positive, models, loras FROM images" + clause
                          + f" ORDER BY {order} LIMIT ? OFFSET ?", args + [limit, offset]).fetchall()
        folders = db.execute("SELECT subfolder, COUNT(*) FROM images GROUP BY subfolder ORDER BY subfolder").fetchall()
        pending = db.execute("SELECT COUNT(*) FROM images WHERE indexed=0").fetchone()[0]
    return {
        "total": total,
        "items": [{"filename": r[1], "subfolder": r[0], "type": "output", "mtime": r[2], "size": r[3], "favorite": bool(r[4]),
                   "rating": r[5], "text": r[6][:300], "models": r[7], "loras": r[8],
                   "duration": DURATIONS.get(f"{r[0]}/{r[1]}")} for r in rows],
        "folders": [{"name": a, "count": b} for a, b in folders if not a.split("/")[-1].startswith("_tmp")],
        "indexing": pending,
    }


def prompt_tokens(text):
    """Теги промта без весов и скобок: по ним сравниваются похожие картинки."""
    out = set()
    for part in re.split(r"[,\n]+", (text or "").lower()):
        part = re.sub(r":\s*-?\d+(\.\d+)?", "", part)
        part = re.sub(r"[()\[\]{}]", " ", part)
        part = " ".join(part.split())
        if len(part) > 2:
            out.add(part)
    return out


def similar_score(a, b):
    if not a or not b:
        return 0.0
    both = len(a & b)
    return both / (len(a) + len(b) - both)


def catalog_similar(key, offset, limit):
    db = catalog_db()
    with DB_LOCK:
        row = db.execute("SELECT positive FROM images WHERE key=?", (key,)).fetchone()
        rows = db.execute("SELECT subfolder, filename, mtime, size, favorite, rating, positive, models, loras, key FROM images "
                          "WHERE positive<>'' AND key<>?", (key,)).fetchall()
        folders = db.execute("SELECT subfolder, COUNT(*) FROM images GROUP BY subfolder ORDER BY subfolder").fetchall()
    target = prompt_tokens(row[0]) if row else set()
    scored = []
    for r in rows:
        score = similar_score(target, prompt_tokens(r[6]))
        if score >= 0.2:
            scored.append((score, r))
    scored.sort(key=lambda x: (x[0], x[1][2]), reverse=True)
    scored = scored[:500]
    return {
        "total": len(scored),
        "items": [{"filename": r[1], "subfolder": r[0], "type": "output", "mtime": r[2], "size": r[3], "favorite": bool(r[4]),
                   "rating": r[5], "text": r[6][:300], "models": r[7], "loras": r[8], "duration": DURATIONS.get(f"{r[0]}/{r[1]}")}
                  for _, r in scored[offset:offset + limit]],
        "folders": [{"name": a, "count": b} for a, b in folders if not a.split("/")[-1].startswith("_tmp")],
        "indexing": 0,
    }


def collections_list():
    db = catalog_db()
    with DB_LOCK:
        rows = db.execute("SELECT c.id, c.name, COUNT(i.key) FROM collections c "
                          "LEFT JOIN collection_items i ON i.cid=c.id AND i.key IN (SELECT key FROM images) "
                          "GROUP BY c.id ORDER BY c.name COLLATE NOCASE").fetchall()
        out = []
        for cid, name, count in rows:
            cover = db.execute("SELECT m.subfolder, m.filename FROM collection_items i JOIN images m ON m.key=i.key "
                               "WHERE i.cid=? ORDER BY i.added DESC LIMIT 1", (cid,)).fetchone()
            out.append({"id": cid, "name": name, "count": count,
                        "cover": {"subfolder": cover[0], "filename": cover[1], "type": "output"} if cover else None})
    return out


def collection_clean_name(value):
    name = " ".join(str(value or "").split())[:80]
    if not name:
        raise ValueError("Empty name")
    return name


@routes.get("/pocket/api/collections")
async def pocket_collections(request):
    return web.json_response({"items": await asyncio.get_running_loop().run_in_executor(None, collections_list)})


@routes.post("/pocket/api/collections")
async def pocket_collection_create(request):
    data = await request.json()
    try:
        name = collection_clean_name(data.get("name"))
    except ValueError as error:
        return web.json_response({"error": str(error)}, status=400)
    db = catalog_db()
    with DB_LOCK:
        try:
            cur = db.execute("INSERT INTO collections(name, created) VALUES(?, ?)", (name, time.time()))
            cid = cur.lastrowid
            db.commit()
        except sqlite3.IntegrityError:
            cid = db.execute("SELECT id FROM collections WHERE name=?", (name,)).fetchone()[0]
    return web.json_response({"id": cid, "name": name})


@routes.post("/pocket/api/collections/rename")
async def pocket_collection_rename(request):
    data = await request.json()
    try:
        name = collection_clean_name(data.get("name"))
        cid = int(data["id"])
    except (KeyError, TypeError, ValueError) as error:
        return web.json_response({"error": str(error)}, status=400)
    db = catalog_db()
    with DB_LOCK:
        try:
            changed = db.execute("UPDATE collections SET name=? WHERE id=?", (name, cid)).rowcount
            db.commit()
        except sqlite3.IntegrityError:
            return web.json_response({"error": "A collection with this name already exists"}, status=409)
    return web.json_response({"renamed": changed})


@routes.post("/pocket/api/collections/delete")
async def pocket_collection_delete(request):
    data = await request.json()
    try:
        cid = int(data["id"])
    except (KeyError, TypeError, ValueError):
        return web.json_response({"error": "bad id"}, status=400)
    db = catalog_db()
    with DB_LOCK:
        db.execute("DELETE FROM collection_items WHERE cid=?", (cid,))
        removed = db.execute("DELETE FROM collections WHERE id=?", (cid,)).rowcount
        db.commit()
    return web.json_response({"deleted": removed})


@routes.post("/pocket/api/collections/items")
async def pocket_collection_items(request):
    data = await request.json()
    try:
        cid = int(data["id"])
    except (KeyError, TypeError, ValueError):
        return web.json_response({"error": "bad id"}, status=400)
    def key_of(item):
        return f"{item.get('subfolder', '')}/{item.get('filename', '')}"
    db = catalog_db()
    now = time.time()
    with DB_LOCK:
        if not db.execute("SELECT 1 FROM collections WHERE id=?", (cid,)).fetchone():
            return web.json_response({"error": "No such collection"}, status=404)
        add = [key_of(i) for i in data.get("add", []) if isinstance(i, dict)]
        remove = [key_of(i) for i in data.get("remove", []) if isinstance(i, dict)]
        db.executemany("INSERT OR REPLACE INTO collection_items(cid, key, added) VALUES(?, ?, ?)", [(cid, k, now) for k in add])
        db.executemany("DELETE FROM collection_items WHERE cid=? AND key=?", [(cid, k) for k in remove])
        db.commit()
    return web.json_response({"added": len(add), "removed": len(remove)})


@routes.get("/pocket/api/catalog")
async def pocket_catalog(request):
    q = dict(request.query)
    try:
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(None, catalog_sync)
        return web.json_response(await loop.run_in_executor(None, catalog_query, q))
    except ValueError:
        return web.json_response({"error": "bad paging"}, status=400)


def catalog_facets():
    db = catalog_db()
    with DB_LOCK:
        rows = db.execute("SELECT models, loras FROM images WHERE models<>'' OR loras<>''").fetchall()
    models, loras = {}, {}
    for m, l in rows:
        for name in m.strip("|").split("|") if m else ():
            models[name] = models.get(name, 0) + 1
        for name in l.strip("|").split("|") if l else ():
            loras[name] = loras.get(name, 0) + 1
    order = lambda d: [{"name": k, "count": v} for k, v in sorted(d.items(), key=lambda x: (-x[1], x[0].lower()))]
    return {"models": order(models), "loras": order(loras)}


@routes.get("/pocket/api/catalog/facets")
async def pocket_catalog_facets(request):
    return web.json_response(await asyncio.get_running_loop().run_in_executor(None, catalog_facets))


@routes.get("/pocket/api/catalog/item")
async def pocket_catalog_item(request):
    key = f"{request.query.get('subfolder', '')}/{request.query.get('filename', '')}"
    db = catalog_db()
    with DB_LOCK:
        row = db.execute("SELECT favorite, rating FROM images WHERE key=?", (key,)).fetchone()
    return web.json_response({"favorite": bool(row[0]) if row else False, "rating": row[1] if row else 0, "known": bool(row)})


@routes.post("/pocket/api/catalog/mark")
async def pocket_catalog_mark(request):
    data = await request.json()
    key = f"{data.get('subfolder', '')}/{data.get('filename', '')}"
    sets, args = [], []
    if isinstance(data.get("favorite"), bool):
        sets.append("favorite=?")
        args.append(int(data["favorite"]))
    if isinstance(data.get("rating"), int) and 0 <= data["rating"] <= 5:
        sets.append("rating=?")
        args.append(data["rating"])
    if not sets:
        return web.json_response({"error": "Nothing to change."}, status=400)
    db = catalog_db()
    with DB_LOCK:
        changed = db.execute(f"UPDATE images SET {', '.join(sets)} WHERE key=?", args + [key]).rowcount
        db.commit()
    return web.json_response({"ok": bool(changed)}, status=200 if changed else 404)


def trash_items(items):
    """Переносит картинки в скрытую папку, откуда их можно вернуть."""
    root = folder_paths.get_output_directory()
    box = os.path.join(root, TRASH)
    os.makedirs(box, exist_ok=True)
    db = catalog_db()
    done = []
    for it in items:
        sub = str(it.get("subfolder", "")).replace("\\", "/")
        name = str(it.get("filename", ""))
        path = os.path.join(root, sub, name)
        if not name or TRASH in sub.split("/") or not inside(root, path) or not os.path.isfile(path):
            continue
        tid = uuid.uuid4().hex
        stored = tid + os.path.splitext(name)[1].lower()
        size = os.path.getsize(path)
        shutil.move(path, os.path.join(box, stored))
        key = f"{sub}/{name}"
        with DB_LOCK:
            row = db.execute("SELECT favorite, rating FROM images WHERE key=?", (key,)).fetchone() or (0, 0)
            db.execute("INSERT INTO trash VALUES(?,?,?,?,?,?,?,?)", (tid, stored, sub, name, time.time(), size, row[0], row[1]))
            db.execute("DELETE FROM images WHERE key=?", (key,))
            db.commit()
            KNOWN.pop(key, None)
        done.append(tid)
    _cache["at"] = 0.0
    return done


def trash_restore(ids):
    root = folder_paths.get_output_directory()
    db = catalog_db()
    with DB_LOCK:
        rows = db.execute("SELECT id, file, subfolder, filename, favorite, rating FROM trash").fetchall()
    restored = 0
    for tid, stored, sub, name, favorite, rating in rows:
        if ids is not None and tid not in ids:
            continue
        src = os.path.join(root, TRASH, stored)
        folder = os.path.join(root, sub)
        if not inside(root, folder) or not os.path.isfile(src):
            continue
        os.makedirs(folder, exist_ok=True)
        stem, ext = os.path.splitext(name)
        target, n = name, 1
        while os.path.exists(os.path.join(folder, target)):
            target, n = f"{stem}_{n}{ext}", n + 1
        shutil.move(src, os.path.join(folder, target))
        st = os.stat(os.path.join(folder, target))
        key = f"{sub}/{target}"
        with DB_LOCK:
            db.execute("""INSERT OR REPLACE INTO images(key, subfolder, filename, mtime, size, favorite, rating)
                          VALUES(?,?,?,?,?,?,?)""", (key, sub, target, st.st_mtime, st.st_size, favorite, rating))
            db.execute("DELETE FROM trash WHERE id=?", (tid,))
            db.commit()
            KNOWN[key] = st.st_mtime
        restored += 1
    _cache["at"] = 0.0
    INDEX_WAKE.set()
    return restored


def trash_empty():
    root = folder_paths.get_output_directory()
    db = catalog_db()
    with DB_LOCK:
        rows = db.execute("SELECT id, file FROM trash").fetchall()
    removed = 0
    for tid, stored in rows:
        path = os.path.join(root, TRASH, stored)
        if inside(root, path) and os.path.isfile(path):
            os.remove(path)
        with DB_LOCK:
            db.execute("DELETE FROM trash WHERE id=?", (tid,))
            db.commit()
        removed += 1
    return removed


@routes.post("/pocket/api/catalog/delete")
async def pocket_catalog_delete(request):
    data = await request.json()
    ids = await asyncio.get_running_loop().run_in_executor(None, trash_items, data.get("items") or [])
    return web.json_response({"trash": ids})


@routes.post("/pocket/api/catalog/restore")
async def pocket_catalog_restore(request):
    data = await request.json()
    ids = None if data.get("all") is True else set(data.get("ids") or [])
    return web.json_response({"restored": await asyncio.get_running_loop().run_in_executor(None, trash_restore, ids)})


@routes.get("/pocket/api/catalog/trash")
async def pocket_catalog_trash(request):
    db = catalog_db()
    with DB_LOCK:
        rows = db.execute("SELECT id, file, filename, subfolder, deleted_at, size FROM trash ORDER BY deleted_at DESC LIMIT 500").fetchall()
        count, size = db.execute("SELECT COUNT(*), COALESCE(SUM(size), 0) FROM trash").fetchone()
    return web.json_response({
        "count": count, "size": size,
        "items": [{"id": r[0], "file": r[1], "filename": r[2], "subfolder": r[3], "deleted_at": r[4], "size": r[5]} for r in rows],
    })


@routes.post("/pocket/api/catalog/trash/empty")
async def pocket_catalog_trash_empty(request):
    data = await request.json()
    if data.get("confirm") is not True:
        return web.json_response({"error": "Confirmation required."}, status=400)
    return web.json_response({"removed": await asyncio.get_running_loop().run_in_executor(None, trash_empty)})


@routes.get("/pocket/api/info")
async def pocket_info(request):
    return web.json_response({"app": "karman", "api": 3, "version": POCKET_VERSION,
                              "features": ["live", "history_states", "history_counts"]})


# Добавление моделей
MODEL_KINDS = {"loras", "checkpoints", "vae", "controlnet", "upscale_models", "embeddings", "diffusion_models", "text_encoders"}
# Только форматы без исполняемого кода: .ckpt, .pt и .bin могут запустить код при загрузке.
MODEL_EXT = {".safetensors", ".sft", ".gguf"}
CIVITAI_TYPES = {"lora": "loras", "locon": "loras", "dora": "loras", "checkpoint": "checkpoints", "vae": "vae",
                 "controlnet": "controlnet", "upscaler": "upscale_models", "textualinversion": "embeddings"}
RESERVE = 2 * 1024 ** 3
CHUNK = 1024 * 1024


class ModelError(Exception):
    """Ошибка с текстом для пользователя."""


def host_allowed(host):
    try:
        infos = socket.getaddrinfo(host, None)
    except OSError:
        raise ModelError("Could not reach this site. Check the link and the computer's internet connection.")
    for info in infos:
        ip = ipaddress.ip_address(info[4][0])
        if not ip.is_global:
            return False
    return True


def check_url(url):
    parts = urllib.parse.urlsplit(url)
    if parts.scheme not in ("http", "https") or not parts.hostname:
        raise ModelError("The link must start with https://")
    if not host_allowed(parts.hostname):
        raise ModelError("Links to local network addresses are not allowed.")


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        check_url(newurl)
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is not None and urllib.parse.urlsplit(newurl).hostname != urllib.parse.urlsplit(req.full_url).hostname:
            # Ключ доступа нельзя передавать другому сайту.
            new.headers.pop("Authorization", None)
            new.unredirected_hdrs.pop("Authorization", None)
        return new


OPENER = urllib.request.build_opener(SafeRedirect)
USER_AGENT = "ComfyUI-Pocket/1.0"


def open_url(url, token=None):
    check_url(url)
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    if token and (urllib.parse.urlsplit(url).hostname or "").endswith("civitai.com"):
        req.add_header("Authorization", f"Bearer {token}")
    return OPENER.open(req, timeout=60)


def resolve_link(url, kind, token):
    """Страницу модели превращает в прямую ссылку и по возможности определяет тип."""
    parts = urllib.parse.urlsplit(url)
    host = (parts.hostname or "").lower()
    if host.endswith("huggingface.co"):
        return url.replace("/blob/", "/resolve/", 1), kind
    if not host.endswith("civitai.com"):
        return url, kind
    query = urllib.parse.parse_qs(parts.query)
    version = (query.get("modelVersionId") or [None])[0]
    direct = re.search(r"/api/download/models/(\d+)", parts.path)
    if direct:
        return url, kind
    page = re.search(r"/models/(\d+)", parts.path)
    if not page:
        raise ModelError("Open the model page on Civitai and copy its link.")
    if kind == "auto" or not version:
        try:
            with open_url(f"https://civitai.com/api/v1/models/{page.group(1)}", token) as r:
                info = json.loads(r.read(5 * 1024 * 1024))
        except (OSError, ValueError):
            info = {}
        if kind == "auto":
            kind = CIVITAI_TYPES.get(str(info.get("type", "")).lower(), "auto")
        if not version and info.get("modelVersions"):
            version = info["modelVersions"][0].get("id")
    if not version:
        raise ModelError("Could not detect the model version. Copy the link to a specific version.")
    return f"https://civitai.com/api/download/models/{version}", kind


def clean_name(name):
    name = os.path.basename(str(name).replace("\\", "/")).strip()
    name = re.sub(r'[<>:"|?*\x00-\x1f]', "_", name)
    if not name or name.startswith("."):
        raise ModelError("The file has no name.")
    if os.path.splitext(name)[1].lower() not in MODEL_EXT:
        raise ModelError("Only .safetensors, .sft and .gguf files are allowed. .ckpt, .pt and .bin files can run code on your computer.")
    return name


def name_from_response(resp, url):
    cd = resp.headers.get("Content-Disposition", "")
    m = re.search(r"filename\*=(?:UTF-8|utf-8)''([^;]+)", cd)
    if m:
        return urllib.parse.unquote(m.group(1).strip())
    m = re.search(r'filename="?([^";]+)"?', cd)
    if m:
        return m.group(1).strip()
    return urllib.parse.unquote(urllib.parse.urlsplit(resp.geturl() or url).path)


def target_path(kind, name):
    if kind not in MODEL_KINDS:
        raise ModelError("Choose the file type.")
    folders = folder_paths.get_folder_paths(kind)
    if not folders:
        raise ModelError("There is no folder for this file type on the computer.")
    folder = folders[0]
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, name)
    if not inside(folder, path):
        raise ModelError("Invalid file name.")
    if os.path.exists(path):
        raise ModelError(f"The file {name} already exists on the computer.")
    return path


def check_space(path, size):
    free = shutil.disk_usage(os.path.dirname(path)).free
    if size and free - size < RESERVE:
        raise ModelError(f"Not enough disk space: the file needs {size / 1024 ** 3:.1f} GB, {free / 1024 ** 3:.1f} GB free.")


def verify_model(path):
    with open(path, "rb") as f:
        head = f.read(9)
        size = os.fstat(f.fileno()).st_size
    if head[:4] == b"GGUF":
        return
    if len(head) == 9 and head[8:9] == b"{" and 2 <= struct.unpack("<Q", head[:8])[0] <= size - 8:
        return
    raise ModelError("The file is damaged or not a model. The site may have returned a web page instead of the file.")


JOBS = {}
JOB_QUEUE = queue.Queue()
JOB_LOCK = threading.Lock()


def public_job(j):
    return {k: j[k] for k in ("id", "kind", "name", "done", "total", "status", "error", "source")}


def download_job(job, url, token):
    part = None
    try:
        link, kind = resolve_link(url, job["kind"], token)
        job["kind"] = kind
        try:
            resp = open_url(link, token)
        except urllib.error.HTTPError as e:
            if e.code in (401, 403):
                raise ModelError("The site requires sign-in. Add a Civitai key or download the file from the model page.")
            if e.code == 404:
                raise ModelError("Nothing found at this link.")
            raise ModelError(f"The site returned error {e.code}.")
        with resp:
            if "text/html" in resp.headers.get("Content-Type", "").lower():
                raise ModelError("The site returned a page, not a file. You probably need to sign in or use a direct link.")
            name = clean_name(name_from_response(resp, link))
            job["name"] = name
            if kind == "auto":
                raise ModelError("Could not detect the file type. Choose it manually.")
            path = target_path(kind, name)
            total = int(resp.headers.get("Content-Length") or 0)
            job["total"] = total
            check_space(path, total)
            part = f"{path}.{job['id']}.part"
            with open(part, "wb") as f:
                while True:
                    if job["cancel"]:
                        raise ModelError("Cancelled")
                    chunk = resp.read(CHUNK)
                    if not chunk:
                        break
                    f.write(chunk)
                    job["done"] += len(chunk)
        if total and job["done"] != total:
            raise ModelError("The connection dropped and the file was not fully downloaded. Try again.")
        verify_model(part)
        if os.path.exists(path):
            raise ModelError(f"The file {name} already exists on the computer.")
        os.replace(part, path)
        part = None
        job["status"] = "done"
    except ModelError as e:
        job["status"] = "cancelled" if job["cancel"] else "error"
        job["error"] = str(e)
    except (OSError, ValueError) as e:
        job["status"] = "error"
        job["error"] = f"Could not download the file: {type(e).__name__}"
    finally:
        if part and os.path.exists(part):
            try:
                os.remove(part)
            except OSError:
                pass


def job_worker():
    while True:
        job, url, token = JOB_QUEUE.get()
        if job["cancel"]:
            job["status"] = "cancelled"
            continue
        job["status"] = "running"
        download_job(job, url, token)


threading.Thread(target=job_worker, daemon=True, name="pocket-downloads").start()


@routes.post("/pocket/api/models/download")
async def pocket_model_download(request):
    try:
        data = await request.json()
    except ValueError:
        return web.json_response({"error": "Bad request."}, status=400)
    url = str(data.get("url", "")).strip()
    kind = str(data.get("kind", "auto"))
    token = str(data.get("token") or "").strip() or None
    if kind != "auto" and kind not in MODEL_KINDS:
        return web.json_response({"error": "Choose the file type."}, status=400)
    try:
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(None, check_url, url)
    except ModelError as e:
        return web.json_response({"error": str(e)}, status=400)
    safe_source = urllib.parse.urlsplit(url).hostname or ""
    job = {"id": uuid.uuid4().hex, "kind": kind, "name": os.path.basename(urllib.parse.urlsplit(url).path) or safe_source,
           "done": 0, "total": 0, "status": "queued", "error": None, "cancel": False, "source": safe_source}
    with JOB_LOCK:
        JOBS[job["id"]] = job
        for old in [j["id"] for j in JOBS.values() if j["status"] in ("done", "error", "cancelled")][:-20]:
            JOBS.pop(old, None)
    JOB_QUEUE.put((job, url, token))
    return web.json_response(public_job(job))


@routes.get("/pocket/api/models/jobs")
async def pocket_model_jobs(request):
    return web.json_response([public_job(j) for j in JOBS.values()])


@routes.post("/pocket/api/models/cancel")
async def pocket_model_cancel(request):
    data = await request.json()
    job = JOBS.get(str(data.get("id")))
    if job:
        job["cancel"] = True
    return web.json_response({"ok": bool(job)})


@routes.post("/pocket/api/models/upload")
async def pocket_model_upload(request):
    # Файл читается потоком, поэтому большие модели не занимают оперативную память.
    part = None
    loop = asyncio.get_running_loop()
    try:
        name = clean_name(request.query.get("filename", ""))
        path = target_path(request.query.get("kind", ""), name)
        check_space(path, request.content_length or 0)
        part = f"{path}.{uuid.uuid4().hex}.part"
        f = open(part, "wb")
        try:
            async for chunk in request.content.iter_chunked(CHUNK):
                await loop.run_in_executor(None, f.write, chunk)
        finally:
            f.close()
        if request.content_length and os.path.getsize(part) != request.content_length:
            raise ModelError("The connection dropped and the file was not fully transferred.")
        await loop.run_in_executor(None, verify_model, part)
        os.replace(part, path)
        part = None
        return web.json_response({"name": name})
    except ModelError as e:
        return web.json_response({"error": str(e)}, status=400)
    except OSError:
        return web.json_response({"error": "Could not write the file to the computer."}, status=500)
    finally:
        if part and os.path.exists(part):
            try:
                os.remove(part)
            except OSError:
                pass


# Этот маршрут должен идти последним: он перехватывает все остальные адреса /pocket/.
# Настройка компьютера из фиксированного списка: сюда нельзя передать свою ссылку.
SETUP_FILES = {
    "face_detector": ("https://huggingface.co/Bingsu/adetailer/resolve/main/face_yolov8m.pt", ("ultralytics", "bbox"), "face_yolov8m.pt"),
    "hand_detector": ("https://huggingface.co/Bingsu/adetailer/resolve/main/hand_yolov8s.pt", ("ultralytics", "bbox"), "hand_yolov8s.pt"),
    "gguf_nodes": ("https://github.com/city96/ComfyUI-GGUF/archive/refs/heads/main.zip", None, "ComfyUI-GGUF"),
}
SETUP_JOBS = {}


def _setup_extract(archive, name):
    import subprocess
    import zipfile
    target = os.path.join(os.path.dirname(HERE), name)
    if os.path.exists(target):
        raise ModelError("This node pack is already installed.")
    temp = target + ".tmp"
    shutil.rmtree(temp, ignore_errors=True)
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            parts = info.filename.split("/")[1:]
            if not parts or not parts[-1] or ".." in parts:
                continue
            path = os.path.join(temp, *parts)
            if not inside(temp, path) and not os.path.normpath(path).startswith(os.path.normpath(temp)):
                raise ModelError("The archive is damaged.")
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with z.open(info) as src, open(path, "wb") as dst:
                shutil.copyfileobj(src, dst)
    done = subprocess.run([sys.executable, "-m", "pip", "install", "gguf"], capture_output=True, text=True, timeout=600)
    if done.returncode != 0:
        shutil.rmtree(temp, ignore_errors=True)
        raise ModelError("Could not install the gguf package: " + done.stderr[-300:])
    os.replace(temp, target)


def setup_job(job, url, folder, name):
    part = None
    try:
        if folder:
            base = os.path.join(os.path.dirname(folder_paths.get_folder_paths("loras")[0]), *folder)
            os.makedirs(base, exist_ok=True)
            final = os.path.join(base, name)
            if os.path.exists(final):
                job["status"] = "done"
                return
        else:
            base = THUMB_DIR
            os.makedirs(base, exist_ok=True)
            final = None
        part = os.path.join(base, f"{name}.{job['id']}.part")
        with open_url(url) as resp, open(part, "wb") as f:
            job["total"] = int(resp.headers.get("Content-Length") or 0)
            while True:
                chunk = resp.read(CHUNK)
                if not chunk:
                    break
                f.write(chunk)
                job["done"] += len(chunk)
        if job["total"] and job["done"] != job["total"]:
            raise ModelError("The connection dropped and the file was not fully downloaded.")
        if final:
            os.replace(part, final)
            part = None
        else:
            _setup_extract(part, name)
        job["status"] = "done"
    except (ModelError, OSError, ValueError, urllib.error.URLError) as e:
        job["status"] = "error"
        job["error"] = str(e)[:400]
    finally:
        if part and os.path.exists(part):
            try:
                os.remove(part)
            except OSError:
                pass


@routes.post("/pocket/api/setup/fetch")
async def pocket_setup_fetch(request):
    data = await request.json()
    item = SETUP_FILES.get(data.get("id"))
    if not item:
        return web.json_response({"error": "unknown"}, status=404)
    job = {"id": uuid.uuid4().hex[:12], "name": data["id"], "status": "running", "done": 0, "total": 0, "error": None}
    SETUP_JOBS[job["id"]] = job
    threading.Thread(target=setup_job, args=(job, *item), daemon=True).start()
    return web.json_response(job)


@routes.get("/pocket/api/setup/jobs")
async def pocket_setup_jobs(request):
    return web.json_response({"items": list(SETUP_JOBS.values())})


@routes.get("/pocket/{path:.+}")
async def pocket_static(request):
    path = os.path.join(WEB_DIR, request.match_info["path"])
    if not inside(WEB_DIR, path) or not os.path.isfile(path):
        return web.Response(status=404)
    ext = os.path.splitext(path)[1].lower()
    return web.FileResponse(path, headers={
        "Content-Type": TYPES.get(ext, "application/octet-stream"), "Cache-Control": "no-cache"})


print("[PocketComfy] extension loaded. Connect the PocketComfy app to this computer on port 8188.")
