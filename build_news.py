#!/usr/bin/env python3
"""
Football news page builder (Python standard library only).

What it does
  1. Reads config.json (sources, leagues, clubs, settings).
  2. Fetches every RSS/Atom feed (several at once; a broken feed never stops the run).
  3. Sorts stories into leagues and clubs by keyword, drops anything older than the
     time window, merges the same story reported by several sources and ranks them.
  4. Writes a small static website: index.html plus one page per league.

Run:     python build_news.py
Options: --open            open the page in your browser when done
         --config FILE     use another config file
         --samples DIR     test mode: read feeds from local files instead of the internet
         --now ISO_TIME    test mode: pretend it is this time (e.g. 2026-11-19T08:00:00+00:00)
"""
from __future__ import annotations

import argparse
import colorsys
import concurrent.futures
import datetime as dt
import email.utils
import gzip
import hashlib
import html
import json
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import zoneinfo
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from pathlib import Path

UTC = dt.timezone.utc
CLUB_STYLES = {}  # club name -> (short code, colour), from config 'club_styles'
DISPLAY_TZ = None  # set from config 'timezone'; None = this computer's own time zone


def to_local(d: dt.datetime) -> dt.datetime:
    return d.astimezone(DISPLAY_TZ) if DISPLAY_TZ else d.astimezone()


# --------------------------------------------------------------------------- text helpers

def norm(text: str) -> str:
    """Lower-case and strip accents so 'Atlético' matches 'Atletico', 'Köln' matches 'Koln'."""
    text = unicodedata.normalize("NFKD", text or "")
    text = "".join(c for c in text if not unicodedata.combining(c))
    for a, b in (("ß", "ss"), ("ø", "o"), ("Ø", "o"), ("æ", "ae"), ("đ", "d"), ("ł", "l"), ("ı", "i")):
        text = text.replace(a, b)
    return text.lower()


def slugify(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", norm(text)).strip("-")


def phrase_re(phrase: str) -> re.Pattern:
    """Whole-word, accent-insensitive match for a phrase (the phrase is normalised like the text)."""
    p = norm(phrase).strip()
    return re.compile(r"(?<![a-z0-9])" + re.escape(p) + r"(?![a-z0-9])")


def esc(text: str) -> str:
    return html.escape(text or "", quote=True)


def strip_html(text: str, limit: int = 0) -> str:
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    if limit and len(text) > limit:
        text = text[:limit].rsplit(" ", 1)[0].rstrip(",.;:- ") + "…"
    return text


STOPWORDS = set(
    "the and for with from after before over into his her its their this that will new vs "
    "beat beats wins win won lose loses lost defeat draw draws says said live report reports "
    "news update latest match game goal goals preview "
    "del los las una por con que des les pour sur aux und der die das den dem mit von vor nach "
    "per gli alla dello della sono più dei".split()
)


def title_tokens(title: str) -> set:
    return {w for w in re.findall(r"[a-z0-9]+", norm(title)) if len(w) > 2 and w not in STOPWORDS}


def similar(a: set, b: set) -> bool:
    if not a or not b:
        return False
    inter = len(a & b)
    union = len(a | b)
    jac = inter / union
    return (inter >= 3 and jac >= 0.5) or (inter >= 2 and jac >= 0.75)


def source_key(name: str) -> str:
    """'BBC Sport' and 'BBC News' count as one outlet; 'The Guardian' == 'Guardian'."""
    k = norm(name)
    k = re.sub(r"\b(the|sport|sports|news|fc|football)\b", " ", k)
    return re.sub(r"[^a-z0-9]+", "", k) or norm(name)


# --------------------------------------------------------------------------- config models

class Team:
    def __init__(self, spec):
        if isinstance(spec, str):
            spec = {"name": spec}
        self.name = spec["name"]
        self.slug = slugify(self.name)
        strong = list(spec.get("aliases", []))
        weak = list(spec.get("weak_aliases", []))
        (weak if spec.get("name_weak") else strong).insert(0, self.name)
        self.strong = [phrase_re(a) for a in strong]
        self.weak = [phrase_re(a) for a in weak]
        self.exclude = [phrase_re(a) for a in spec.get("exclude", [])]

    def _clean(self, text: str) -> str:
        for rx in self.exclude:
            text = rx.sub(" ", text)
        return text

    def strong_match(self, text: str) -> bool:
        t = self._clean(text)
        return any(rx.search(t) for rx in self.strong)

    def weak_match(self, text: str) -> bool:
        t = self._clean(text)
        return any(rx.search(t) for rx in self.weak)


class League:
    def __init__(self, spec: dict, team_specs: dict):
        self.key = spec["key"]
        self.name = spec["name"]
        self.slug = spec.get("slug", self.key.replace("_", "-"))
        self.file = self.slug + ".html"
        self.color = spec.get("color", "")
        self.keywords = [phrase_re(k) for k in spec.get("keywords", [])]
        self.keyword_exclude = [phrase_re(k) for k in spec.get("keyword_exclude", [])]
        self.assign_by_team = spec.get("assign_by_team", True)
        self.teams = []
        for t in spec.get("teams", []):
            if isinstance(t, str) and t in team_specs:
                t = team_specs[t]  # reuse the full definition (aliases etc.) from another league
            self.teams.append(Team(t))

    def keyword_match(self, text: str) -> bool:
        for rx in self.keyword_exclude:
            text = rx.sub(" ", text)
        return any(rx.search(text) for rx in self.keywords)


def build_leagues(cfg: dict) -> list:
    known = {}
    for lg in cfg["leagues"]:
        for t in lg.get("teams", []):
            if isinstance(t, dict):
                known[t["name"]] = t
    return [League(spec, known) for spec in cfg["leagues"]]


# --------------------------------------------------------------------------- sources

def google_news_url(query: str, days: int, st: dict) -> str:
    hl = st.get("google_news_hl", "en-GB")
    gl = st.get("google_news_gl", "GB")
    params = {"q": f"{query} when:{days}d", "hl": hl, "gl": gl, "ceid": f"{gl}:{hl.split('-')[0]}"}
    return "https://news.google.com/rss/search?" + urllib.parse.urlencode(params)


def expand_sources(cfg: dict) -> list:
    st = cfg["settings"]
    days = st["max_age_days"]
    out = []
    for s in cfg["sources"]:
        s = dict(s)
        s.setdefault("lang", "en")
        if s.get("type") == "google_news":
            s["urls"] = [{"url": google_news_url(s["query"], days, st), "default_leagues": s.get("default_leagues", [])}]
            s.setdefault("aggregator", True)
        else:
            urls = []
            for u in s["urls"]:
                if isinstance(u, str):
                    u = {"url": u}
                u = dict(u)
                u.setdefault("default_leagues", s.get("default_leagues", []))
                urls.append(u)
            s["urls"] = urls
        s.setdefault("aggregator", False)
        s.setdefault("use_summary", not s["aggregator"])
        out.append(s)

    if st.get("google_news_club_feeds"):
        seen = set()
        for lg in cfg["leagues"]:
            for t in lg.get("teams", []):
                name = t if isinstance(t, str) else t["name"]
                if name in seen:
                    continue
                seen.add(name)
                out.append({
                    "id": "google-club-" + slugify(name), "name": "Google News", "lang": "en",
                    "aggregator": True, "use_summary": False,
                    "urls": [{"url": google_news_url(f"{name} football", days, st), "default_leagues": [lg["key"]]}],
                })
    for i, s in enumerate(out):
        s["prio"] = i
    return out


@dataclass
class Item:
    title: str
    link: str
    summary: str
    published: dt.datetime
    source_name: str
    source_key: str
    via: str
    lang: str
    aggregator: bool
    prio: int
    default_leagues: set
    leagues: set = field(default_factory=set)
    teams: dict = field(default_factory=dict)
    image: str = ""


# --------------------------------------------------------------------------- fetching and parsing

def local(tag) -> str:
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) and "}" in tag else tag


def read_limited(resp, max_bytes: int, deadline: float, partial_ok: bool = False) -> bytes:
    """Read a response in pieces so a slowly dripping server cannot keep us waiting for ever."""
    chunks, total = [], 0
    while total < max_bytes:
        if time.monotonic() > deadline:
            if partial_ok:
                break
            raise TimeoutError("download too slow")
        n = min(16384, max_bytes - total)
        chunk = resp.read1(n) if hasattr(resp, "read1") else resp.read(n)
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
    return b"".join(chunks)


def fetch(url: str, timeout: int, ua: str) -> bytes:
    req = urllib.request.Request(url, headers={
        "User-Agent": ua,
        "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml;q=0.9, */*;q=0.5",
        "Accept-Encoding": "identity",
    })
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return read_limited(resp, 5_000_000, time.monotonic() + timeout * 2)


def fetch_retry(url: str, timeout: int, ua: str, tries: int = 3) -> bytes:
    """Like fetch(), but a temporary problem (503, 429, timeout...) gets another try after a short wait."""
    delay = 2.0
    for attempt in range(tries):
        try:
            return fetch(url, timeout, ua)
        except urllib.error.HTTPError as exc:
            if exc.code not in (429, 500, 502, 503, 504) or attempt == tries - 1:
                raise
        except OSError:  # timeouts, dropped connections, DNS hiccups
            if attempt == tries - 1:
                raise
        time.sleep(delay)
        delay *= 2.5
    raise RuntimeError("unreachable")


def clean_bytes(data: bytes) -> bytes:
    if data[:2] == b"\x1f\x8b":
        data = gzip.decompress(data)
    return re.sub(rb"[\x00-\x08\x0b\x0c\x0e-\x1f]", b"", data)


def parse_xml(data: bytes):
    try:
        return ET.fromstring(data)
    except ET.ParseError:
        text = data.decode("utf-8", "replace")
        text = re.sub(r"^\s*<\?xml[^>]*\?>", "", text)
        # named HTML entities such as &nbsp; are not valid XML: turn them into characters
        text = re.sub(
            r"&([A-Za-z][A-Za-z0-9]*);",
            lambda m: m.group(0) if m.group(1) in ("amp", "lt", "gt", "quot", "apos") else html.unescape(m.group(0)),
            text,
        )
        # a bare & that is not part of an entity
        text = re.sub(r"&(?!(?:[A-Za-z][A-Za-z0-9]*|#\d+|#x[0-9A-Fa-f]+);)", "&amp;", text)
        return ET.fromstring(text)


def child_text(el, *names) -> str:
    for c in el:
        if local(c.tag) in names:
            txt = "".join(c.itertext()).strip()
            if txt:
                return txt
    return ""


def entry_link(el) -> str:
    link = ""
    for c in el:
        if local(c.tag) == "link":
            href = c.get("href")
            if href:
                if c.get("rel", "alternate") == "alternate" or not link:
                    link = href
            elif (c.text or "").strip():
                return c.text.strip()
    if link:
        return link
    guid = child_text(el, "guid", "id")
    return guid if guid.startswith("http") else ""


def parse_date(text: str):
    if not text:
        return None
    text = text.strip()
    d = None
    try:
        d = email.utils.parsedate_to_datetime(text)
    except Exception:
        d = None
    if d is None:
        try:
            d = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
        except ValueError:
            return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=UTC)
    return d.astimezone(UTC)


IMG_TAG_RE = re.compile(r"<img[^>]+src=[\"']([^\"']+)[\"']", re.I)
IMG_EXT_RE = re.compile(r"\.(jpe?g|png|webp|gif)(\?|$)", re.I)


def entry_image(el, base: str) -> str:
    """Best thumbnail for a feed entry: media:thumbnail / media:content / enclosure / first <img> in the text."""
    cands = []  # (width, url)
    for c in el.iter():
        t = local(c.tag)
        url = (c.get("url") or "").strip()
        if t == "thumbnail" and url:
            cands.append((int(c.get("width") or 0) if str(c.get("width") or "").isdigit() else 0, url))
        elif t == "content" and url:
            kind = ((c.get("medium") or "") + " " + (c.get("type") or "")).lower()
            if "image" in kind or IMG_EXT_RE.search(url):
                cands.append((int(c.get("width") or 0) if str(c.get("width") or "").isdigit() else 0, url))
        elif t == "enclosure" and url and (c.get("type") or "").lower().startswith("image"):
            cands.append((0, url))
        elif t == "image" and not url and (c.text or "").strip().startswith("http"):
            cands.append((0, c.text.strip()))  # e.g. Bing News <News:Image>
    if not cands:
        for name in ("encoded", "description", "content", "summary"):
            m = IMG_TAG_RE.search(html.unescape(child_text(el, name)))
            if m:
                cands.append((0, m.group(1).strip()))
                break
    if not cands:
        return ""
    sized = sorted(c for c in cands if c[0])
    if sized:
        big = [c for c in sized if c[0] >= 300]
        url = (big[0] if big else sized[-1])[1]  # smallest picture that is still sharp enough
    else:
        url = cands[0][1]
    url = urllib.parse.urljoin(base, url) if base else url
    if url.startswith("http://"):
        url = "https://" + url[len("http://"):]
    return url if url.startswith("https://") else ""


def parse_feed(data: bytes, base: str = "") -> list:
    root = parse_xml(data)
    entries = []
    first = None
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        if first is None:
            first = el
        title = strip_html(child_text(el, "title"))
        link = entry_link(el)
        link = link.strip()
        if link.startswith("//"):
            link = "https:" + link
        elif link.lower().startswith("www."):
            link = "https://" + link
        elif base and link.startswith("/"):
            link = urllib.parse.urljoin(base, link)  # some feeds give relative links
        if not title or not link.lower().startswith(("http://", "https://")):
            continue
        entries.append({
            "title": title,
            "link": link.strip(),
            "summary_raw": child_text(el, "description", "summary", "encoded", "content"),
            "published": parse_date(child_text(el, "pubDate", "published", "updated", "date")),
            "publisher": child_text(el, "source"),
            "image": entry_image(el, base),
        })
    if not entries and first is not None:
        raw = re.sub(r"\s+", " ", ET.tostring(first, encoding="unicode"))[:500]
        raise ValueError("items found but none usable. First item was: " + raw)
    return entries


def load_source(src: dict, args, st: dict, now: dt.datetime) -> dict:
    res = {"id": src["id"], "name": src["name"], "ok": False, "url": "", "raw": 0, "kept": 0, "images": 0, "error": "", "items": []}
    errors = []
    for idx, u in enumerate(src["urls"]):
        data = b""
        try:
            if args.samples:
                suffix = "" if idx == 0 else f".{idx}"
                path = Path(args.samples) / f"{src['id']}{suffix}.xml"
                if not path.exists():
                    raise FileNotFoundError(f"no sample file {path.name}")
                data = path.read_bytes()
            else:
                data = fetch_retry(u["url"], st["timeout_seconds"], src.get("user_agent") or st["user_agent"])
            entries = parse_feed(clean_bytes(data), u["url"])
            if not entries:
                raise ValueError("feed contained no usable items")
        except Exception as exc:  # one bad feed must never stop the build
            host = urllib.parse.urlparse(u["url"]).netloc
            snip = re.sub(r"\s+", " ", data[:160].decode("utf-8", "replace")).strip()
            errors.append(f"{host}: {type(exc).__name__}: {exc}" + (f' [site sent: "{snip}"]' if snip else " [site sent nothing]"))
            continue

        res.update(ok=True, url=u["url"], raw=len(entries))
        for e in entries:
            title, publisher = e["title"], e["publisher"]
            if src["aggregator"] and publisher and title.endswith(" - " + publisher):
                title = title[: -len(publisher) - 3].rstrip()
            name = publisher if (src["aggregator"] and publisher) else src["name"]
            published = e["published"] or now
            res["items"].append(Item(
                title=title,
                link=e["link"],
                summary=strip_html(e["summary_raw"], 240) if src["use_summary"] else "",
                published=min(published, now),
                source_name=name,
                source_key=source_key(name),
                via=src["name"] if (src["aggregator"] and publisher) else "",
                lang=src["lang"],
                aggregator=src["aggregator"],
                prio=src["prio"],
                default_leagues=set(u["default_leagues"]),
                image=e["image"],
            ))
        res["images"] = sum(1 for it in res["items"] if it.image)
        return res
    res["error"] = " | ".join(errors)
    return res


# --------------------------------------------------------------------------- classification

def classify(item: Item, leagues: list) -> None:
    text = norm(item.title + " " + item.summary)
    # a search feed (Google News) returns loosely related articles, so its league is not trusted:
    # the headline itself must mention the league or one of its clubs
    found = set() if item.aggregator else set(item.default_leagues)
    for lg in leagues:
        if lg.keyword_match(text):
            found.add(lg.key)
    for lg in leagues:
        if lg.assign_by_team and lg.key not in found and any(t.strong_match(text) for t in lg.teams):
            found.add(lg.key)
    teams = {}
    for lg in leagues:
        if lg.key in found:
            hits = [t for t in lg.teams if t.strong_match(text) or t.weak_match(text)]
            if hits:
                teams[lg.key] = hits
    # an exclusion phrase (e.g. "Women's Champions League") drops the whole story
    if any(rx.search(text) for lg in leagues for rx in lg.keyword_exclude):
        found, teams = set(), {}
    item.leagues = found
    item.teams = teams


# --------------------------------------------------------------------------- clustering and ranking

def build_clusters(items: list, now: dt.datetime) -> list:
    items = sorted(items, key=lambda i: i.published, reverse=True)
    clusters = []
    for it in items:
        toks = title_tokens(it.title)
        key = norm(it.title).strip()
        target = None
        for c in clusters:
            if key in c["keys"] or any(similar(toks, t2) for t2 in c["toks"]):
                target = c
                break
        if target is None:
            target = {"items": [], "toks": [], "keys": set()}
            clusters.append(target)
        target["items"].append(it)
        target["toks"].append(toks)
        target["keys"].add(key)

    result = []
    for c in clusters:
        members = c["items"]
        rep = min(members, key=lambda i: (i.aggregator, i.prio, not i.summary, -i.published.timestamp()))
        sources = {}
        for m in members:
            sources.setdefault(m.source_key, m.source_name)
        leagues = set()
        teams = {}
        for m in members:
            leagues |= m.leagues
            for lk, ts in m.teams.items():
                teams.setdefault(lk, {})
                for t in ts:
                    teams[lk][t.slug] = t.name
        image = ""
        for m in [rep] + sorted(members, key=lambda i: i.published, reverse=True):
            if m.image:
                image = m.image
                break
        links = []
        for m in [rep] + sorted(members, key=lambda i: i.published, reverse=True):
            if not urllib.parse.urlparse(m.link).netloc.endswith("news.google.com") and m.link not in links:
                links.append(m.link)
        latest = max(m.published for m in members)
        age_h = max(0.0, (now - latest).total_seconds() / 3600)
        score = 2.0 * min(len(sources) - 1, 5) + 4.0 * 0.5 ** (age_h / 12)
        result.append({"rep": rep, "sources": sources, "leagues": leagues, "teams": teams,
                       "latest": latest, "score": score, "image": image, "links": links})
    return result


# --------------------------------------------------------------------------- picture lookup on article pages

OG_RES = [
    re.compile(r'<meta[^>]+?(?:property|name)=["\'](?:og:image(?::secure_url)?|twitter:image)["\'][^>]*?content=["\']([^"\']+)["\']', re.I),
    re.compile(r'<meta[^>]+?content=["\']([^"\']+)["\'][^>]*?(?:property|name)=["\'](?:og:image(?::secure_url)?|twitter:image)["\']', re.I),
]


LOOKUP_STATS: dict = {}
LOOKUP_SAMPLES: list = []


def _note(reason: str, url: str = "") -> str:
    LOOKUP_STATS[reason] = LOOKUP_STATS.get(reason, 0) + 1
    if url and reason != "picture found" and len(LOOKUP_SAMPLES) < 6:
        LOOKUP_SAMPLES.append(f"{reason}: {urllib.parse.urlparse(url).netloc}")
    return ""


def find_page_image(url: str, timeout: int, ua: str) -> str:
    """Read the start of an article page and return its social-sharing picture (og:image), or ''."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": ua, "Accept": "text/html,*/*;q=0.5",
                                                   "Accept-Encoding": "identity"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            page = read_limited(resp, 200000, time.monotonic() + timeout, partial_ok=True).decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return _note(f"HTTP {e.code}", url)
    except Exception as e:
        return _note(type(e).__name__, url)
    head = page.split("</head>", 1)[0]
    for rx in OG_RES:
        m = rx.search(head)
        if m:
            img = urllib.parse.urljoin(url, html.unescape(m.group(1).strip()))
            if img.startswith("http://"):
                img = "https://" + img[len("http://"):]
            if img.startswith("https://"):
                LOOKUP_STATS["picture found"] = LOOKUP_STATS.get("picture found", 0) + 1
                return img
            return _note("picture link not https", url)
    return _note("page has no picture tag", url)


def add_page_images(clusters: list, leagues: list, st: dict) -> tuple:
    """For top stories still without a picture, look one up on the publisher's article page."""
    limit = st.get("max_image_lookups", 60)
    if not limit:
        return 0, 0
    ranked = sorted(clusters, key=lambda c: (-c["score"], -c["latest"].timestamp()))
    first, seen = [], set()
    for lg in leagues:  # stories shown on the front page come first
        for c in [c for c in ranked if lg.key in c["leagues"]][: st["front_page_items"]]:
            if id(c) not in seen:
                seen.add(id(c))
                first.append(c)
    order = first + [c for c in ranked if id(c) not in seen]
    todo = [c for c in order if not c["image"] and c["links"]][:limit]

    t0 = time.monotonic()
    budget = st.get("image_lookup_total_seconds", 45)

    def work(c):
        if time.monotonic() - t0 > budget:  # out of time: skip the rest, the page is more important
            _note("skipped (time budget used up)")
            return 0
        for link in c["links"][:2]:
            img = find_page_image(link, st.get("image_lookup_timeout", 8), st["user_agent"])
            if img:
                c["image"] = img
                return 1
        return 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=st["max_workers"]) as pool:
        found = sum(pool.map(work, todo))
    return found, len(todo)


# --------------------------------------------------------------------------- HTML output

CSS = """
:root{--bg:#f4f5f7;--card:#fff;--text:#14181f;--muted:#5d6675;--line:#e2e5ea;--accent:#0a7d4f;--accent-soft:#e2f3ea;--chip:#eceff3}
@media (prefers-color-scheme:dark){:root{--bg:#0e1217;--card:#161b22;--text:#e8ecf1;--muted:#98a2b0;--line:#252c36;--accent:#3ecf8e;--accent-soft:#143226;--chip:#212934}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:16px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
a{color:inherit}
.wrap{max-width:960px;margin:0 auto;padding:0 16px}
header.top{background:var(--card);border-bottom:1px solid var(--line);padding:20px 0 14px}
header.top h1{margin:0;font-size:1.6rem;letter-spacing:-.01em}
header.top h1 a{text-decoration:none}
.meta-line{margin:.25rem 0 0;color:var(--muted);font-size:.9rem}
.chips{display:flex;flex-wrap:wrap;gap:8px;margin:14px 0 0;padding:0;list-style:none}
.chips a{display:inline-block;padding:5px 12px;border-radius:999px;background:var(--chip);text-decoration:none;font-size:.9rem}
.chips a:hover{background:var(--accent-soft)}
.chips a[aria-current]{background:var(--accent);color:#fff}
main{padding:20px 0 40px}
.league{background:var(--card);border:1px solid var(--line);border-left:6px solid var(--lc,var(--line));border-radius:12px;padding:6px 18px 12px;margin:0 0 18px}
.league-head{display:flex;justify-content:space-between;align-items:baseline;gap:12px;padding:10px 0 6px}
.league-head h2{margin:0;font-size:1.2rem}
.league-head h2 a{text-decoration:none}
.league-head h2 a:hover,.all:hover{color:var(--accent)}
.all{font-size:.9rem;color:var(--muted);text-decoration:none;white-space:nowrap}
.stories{list-style:none;margin:0;padding:0}
.story{display:flex;gap:12px;align-items:flex-start;padding:10px 0;border-top:1px solid var(--line)}
.story .body{flex:1;min-width:0}
.thumbwrap{flex:none;display:block}
.thumb{display:block;width:96px;height:64px;object-fit:cover;border-radius:6px;background:var(--chip)}
.club{display:inline-block;padding:0 6px;border-radius:4px;font-size:.7rem;font-weight:700;letter-spacing:.02em;line-height:1.55;box-shadow:inset 0 0 0 1px rgba(128,128,128,.35)}
.story:first-child{border-top:0}
.story .title{font-weight:600;text-decoration:none}
.story .title:hover{color:var(--accent);text-decoration:underline}
.story .sum{margin:.2rem 0 0;color:var(--muted);font-size:.9rem}
.meta{display:flex;flex-wrap:wrap;gap:4px 10px;align-items:center;margin-top:3px;font-size:.8rem;color:var(--muted)}
.src{font-weight:600}
.badge{background:var(--accent-soft);color:var(--accent);padding:1px 8px;border-radius:999px;font-weight:600}
.lang{border:1px solid var(--line);border-radius:4px;padding:0 5px;font-size:.72rem;letter-spacing:.03em}
.tr{color:var(--accent);text-decoration:none;font-weight:600}
.tr:hover{text-decoration:underline}
.empty{color:var(--muted);padding:12px 0}
h3.sec{margin:22px 0 4px;font-size:1rem;color:var(--muted);text-transform:uppercase;letter-spacing:.06em}
.filters{display:flex;flex-wrap:wrap;gap:6px;margin:6px 0 0}
.filters button{font:inherit;font-size:.85rem;border:1px solid var(--line);background:var(--card);color:var(--text);border-radius:999px;padding:3px 11px;cursor:pointer}
.filters button:hover:not(:disabled){border-color:var(--accent)}
.filters button[aria-pressed="true"]{background:var(--accent);border-color:var(--accent);color:#fff}
.filters button:disabled{opacity:.4;cursor:default}
.filters .n{opacity:.7;margin-left:3px;font-size:.78rem}
details.status{margin-top:26px;color:var(--muted);font-size:.85rem}
details.status summary{cursor:pointer}
details.status table{border-collapse:collapse;margin-top:8px;width:100%}
details.status th,details.status td{text-align:left;padding:4px 8px;border-bottom:1px solid var(--line);vertical-align:top}
.bad{color:#c0392b}
footer{color:var(--muted);font-size:.8rem;padding:0 0 30px}
[hidden]{display:none!important}
"""

TIME_JS = """
(function(){
  var els=document.querySelectorAll('time[datetime]');
  for(var i=0;i<els.length;i++){
    var t=els[i], m=Math.round((Date.now()-new Date(t.getAttribute('datetime')))/60000), s;
    if(isNaN(m)) continue;
    if(m<2) s='just now'; else if(m<60) s=m+' min ago'; else if(m<1440) s=Math.round(m/60)+' h ago'; else s=Math.round(m/1440)+' d ago';
    t.title=t.textContent; t.textContent=s;
  }
})();
"""

FILTER_JS = """
(function(){
  var bar=document.getElementById('teams'); if(!bar) return;
  var rows=[].slice.call(document.querySelectorAll('#latest li'));
  var top=document.getElementById('top'), none=document.getElementById('none');
  var buttons=[].slice.call(bar.querySelectorAll('button'));
  function apply(team){
    var shown=0;
    rows.forEach(function(li){
      var ok=!team||(' '+(li.getAttribute('data-teams')||'')+' ').indexOf(' '+team+' ')>-1;
      li.hidden=!ok; if(ok) shown++;
    });
    if(top) top.hidden=!!team;
    none.hidden=shown>0;
    buttons.forEach(function(b){b.setAttribute('aria-pressed',String((b.getAttribute('data-team')||'')===(team||'')));});
    try{history.replaceState(null,'',team?'#team='+team:location.pathname);}catch(e){}
  }
  bar.addEventListener('click',function(e){
    var b=e.target.closest('button'); if(!b||b.disabled) return;
    var t=b.getAttribute('data-team')||'';
    apply(b.getAttribute('aria-pressed')==='true'?'':t);
  });
  var m=/#team=([a-z0-9-]+)/.exec(location.hash);
  if(m&&buttons.some(function(b){return b.getAttribute('data-team')===m[1]&&!b.disabled;})) apply(m[1]);
})();
"""


def club_style(name: str):
    spec = CLUB_STYLES.get(name)
    if spec:
        return spec[0], spec[1]
    words = re.findall(r"[a-z]+", norm(name))
    short = (words[0] if words else name)[:3].upper()
    hue = int(hashlib.md5(name.encode("utf-8")).hexdigest()[:4], 16) / 65535
    r, g, b = colorsys.hls_to_rgb(hue, 0.35, 0.55)
    return short, "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))


def text_on(color: str) -> str:
    r, g, b = (int(color[i:i + 2], 16) for i in (1, 3, 5))
    return "#111" if (0.299 * r + 0.587 * g + 0.114 * b) > 160 else "#fff"


def club_chips(teams: dict) -> list:
    out = []
    for name in list(teams.values())[:3]:
        short, color = club_style(name)
        out.append(f'<span class="club" style="background:{color};color:{text_on(color)}" title="{esc(name)}">{esc(short)}</span>')
    return out


def fmt_time(d: dt.datetime) -> str:
    return to_local(d).strftime("%d %b %H:%M")


def translate_url(link: str, lang: str = "auto") -> str:
    return f"https://translate.google.com/translate?sl={lang}&tl=en&u=" + urllib.parse.quote(link, safe="")


def story_li(c: dict, league: League, with_teams_attr: bool, with_summary: bool = False) -> str:
    rep = c["rep"]
    lang_attr = f' lang="{esc(rep.lang)}"' if rep.lang != "en" else ""
    teams = c["teams"].get(league.key, {})
    data = f' data-teams="{esc(" ".join(sorted(teams)))}"' if with_teams_attr else ""
    meta = club_chips(teams) + [f'<span class="src">{esc(rep.source_name)}</span>']
    if rep.via:
        meta.append(f"via {esc(rep.via)}")
    meta.append(f'<time datetime="{c["latest"].isoformat()}">{fmt_time(c["latest"])}</time>')
    n = len(c["sources"])
    if n > 1:
        names = ", ".join(sorted(c["sources"].values()))
        meta.append(f'<span class="badge" title="{esc(names)}">{n} sources</span>')
    if rep.lang != "en":
        meta.append(f'<span class="lang">{esc(rep.lang.upper())}</span>')
        meta.append(f'<a class="tr" href="{esc(translate_url(rep.link, rep.lang))}" target="_blank" rel="noopener">Translate</a>')
    summary = f'<p class="sum"{lang_attr}>{esc(rep.summary)}</p>' if (with_summary and rep.summary) else ""
    thumb = ""
    if c.get("image"):
        thumb = (f'<a class="thumbwrap" href="{esc(rep.link)}" target="_blank" rel="noopener" tabindex="-1" aria-hidden="true">'
                 f'<img class="thumb" src="{esc(c["image"])}" alt="" loading="lazy" referrerpolicy="no-referrer" '
                 f'onerror="this.remove()"></a>')
    return (
        f'<li class="story"{data}><div class="body"><a class="title"{lang_attr} href="{esc(rep.link)}" target="_blank" rel="noopener">'
        f'{esc(rep.title)}</a>{summary}<div class="meta">{" ".join(meta)}</div></div>{thumb}</li>'
    )


def page_shell(title: str, header_html: str, body_html: str, extra_js: str, footer: str) -> str:
    return (
        '<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1">'
        f"<title>{esc(title)}</title>"
        '<link rel="stylesheet" href="style.css"></head><body>'
        f"{header_html}<main class=\"wrap\">{body_html}</main>"
        f'<footer class="wrap">{footer}</footer>'
        f"<script>{TIME_JS}{extra_js}</script></body></html>\n"
    )


def nav_chips(leagues: list, current: str | None) -> str:
    links = []
    for lg in leagues:
        cur = ' aria-current="page"' if lg.key == current else ""
        links.append(f'<li><a href="{lg.file}"{cur}>{esc(lg.name)}</a></li>')
    return f'<ul class="chips">{"".join(links)}</ul>'


def build_site(out: Path, cfg: dict, leagues: list, clusters: list, results: list, now: dt.datetime) -> None:
    st = cfg["settings"]
    title = st["title"]
    n_front = st["front_page_items"]
    cap = st["max_stories_per_league"]
    days = st["max_age_days"]
    stamp = to_local(now).strftime("%d %b %Y, %H:%M")
    out.mkdir(parents=True, exist_ok=True)
    (out / "style.css").write_text(CSS.strip() + "\n", encoding="utf-8")

    by_league = {lg.key: [c for c in clusters if lg.key in c["leagues"]] for lg in leagues}
    for lg in leagues:
        by_league[lg.key].sort(key=lambda c: (-c["score"], -c["latest"].timestamp()))

    # ---- front page
    sections = []
    for lg in leagues:
        cl = by_league[lg.key]
        if cl:
            lis = "".join(story_li(c, lg, False) for c in cl[:n_front])
            body = f'<ol class="stories">{lis}</ol>'
        else:
            body = f'<p class="empty">No stories in the last {days} days.</p>'
        sections.append(
            f'<section class="league" id="{lg.slug}"{(" style=" + chr(34) + "--lc:" + lg.color + chr(34)) if lg.color else ""}><div class="league-head">'
            f'<h2><a href="{lg.file}">{esc(lg.name)}</a></h2>'
            f'<a class="all" href="{lg.file}">All {len(cl)} stories →</a></div>{body}</section>'
        )

    ok = sum(1 for r in results if r["ok"])
    rows = []
    for r in results:
        if r["ok"]:
            host = urllib.parse.urlparse(r["url"]).netloc
            rows.append(f'<tr><td>{esc(r["name"])} <span>({esc(r["id"])})</span></td><td>OK</td>'
                        f'<td>{esc(host)}</td><td>{r["raw"]} read, {r["kept"]} used, {r["images"]} with image</td></tr>')
        else:
            rows.append(f'<tr><td>{esc(r["name"])} <span>({esc(r["id"])})</span></td><td class="bad">Failed</td>'
                        f'<td colspan="2" class="bad">{esc(r["error"])}</td></tr>')
    status = (
        f'<details class="status"><summary>Feed status: {ok} of {len(results)} feeds worked</summary>'
        '<table><tr><th>Source</th><th>Result</th><th>Host</th><th>Items</th></tr>'
        f'{"".join(rows)}</table></details>'
    )
    header = (
        f'<header class="top"><div class="wrap"><h1><a href="index.html">{esc(title)}</a></h1>'
        f'<p class="meta-line">Updated {stamp} · last {days} days · top {n_front} per section</p>'
        f'{nav_chips(leagues, None)}</div></header>'
    )
    (out / "index.html").write_text(
        page_shell(title, header, "".join(sections) + status, "",
                   "Stories link to the original publishers. Non-English items have a Translate link."),
        encoding="utf-8",
    )

    # ---- league pages
    for lg in leagues:
        cl = by_league[lg.key][:cap]
        latest = sorted(cl, key=lambda c: -c["latest"].timestamp())
        counts = {}
        for c in cl:
            for slug in c["teams"].get(lg.key, {}):
                counts[slug] = counts.get(slug, 0) + 1
        buttons = ['<button type="button" data-team="" aria-pressed="true">All</button>']
        for t in sorted(lg.teams, key=lambda t: norm(t.name)):
            n = counts.get(t.slug, 0)
            dis = "" if n else " disabled"
            buttons.append(f'<button type="button" data-team="{t.slug}" aria-pressed="false"{dis}>'
                           f'{esc(t.name)}<span class="n">{n}</span></button>')
        if cl:
            top_html = (f'<div id="top"><h3 class="sec">Top stories</h3><ol class="stories">'
                        f'{"".join(story_li(c, lg, False, True) for c in cl[:n_front])}</ol></div>')
            latest_html = (f'<h3 class="sec">Latest</h3><ol class="stories" id="latest">'
                           f'{"".join(story_li(c, lg, True) for c in latest)}</ol>'
                           f'<p class="empty" id="none" hidden>No stories for this club in the last {days} days.</p>')
        else:
            top_html = f'<p class="empty">No stories in the last {days} days.</p>'
            latest_html = ""
        header = (
            f'<header class="top"><div class="wrap"><h1><a href="index.html">{esc(title)}</a></h1>'
            f'<p class="meta-line">{esc(lg.name)} · {len(cl)} stories · updated {stamp} · '
            f'<a href="index.html">← all sections</a></p>{nav_chips(leagues, lg.key)}</div></header>'
        )
        if lg.color:
            header = header.replace('<header class="top">', f'<header class="top" style="border-top:5px solid {lg.color}">', 1)
        body = f'<div class="filters" id="teams">{"".join(buttons)}</div>{top_html}{latest_html}'
        (out / lg.file).write_text(
            page_shell(f"{lg.name} – {title}", header, body, FILTER_JS,
                       "Stories link to the original publishers. Non-English items have a Translate link."),
            encoding="utf-8",
        )


# --------------------------------------------------------------------------- main

def classify_source(r: dict, leagues: list, exclude_titles: list, cutoff, now) -> None:
    """Decide which items of one feed are used, and record why the others were dropped."""
    r["kept_items"] = []
    r["drop_old"] = r["drop_excluded"] = r["drop_noleague"] = 0
    r["newest_h"] = None
    if r["items"]:
        r["newest_h"] = (now - max(it.published for it in r["items"])).total_seconds() / 3600
    for it in r["items"]:
        if it.published < cutoff:
            r["drop_old"] += 1
            continue
        if any(rx.search(it.title) for rx in exclude_titles):
            r["drop_excluded"] += 1
            continue
        classify(it, leagues)
        if it.leagues:
            r["kept_items"].append(it)
            r["kept"] += 1
        else:
            r["drop_noleague"] += 1


def fmt_age(h) -> str:
    if h is None:
        return "-"
    return f"{h:.0f} h" if h < 48 else f"{h / 24:.1f} d"


def run_trial(results: list, leagues: list, exclude_titles: list, cutoff, now, args) -> int:
    """Trial mode: judge many candidate feeds without building a page."""
    rows = []
    for r in results:
        if not r["ok"]:
            rows.append({"r": r, "score": -1})
            continue
        classify_source(r, leagues, exclude_titles, cutoff, now)
        used_img = sum(1 for it in r["kept_items"] if it.image)
        per = {lg.key: sum(1 for it in r["kept_items"] if lg.key in it.leagues) for lg in leagues}
        rows.append({"r": r, "used_img": used_img, "per": per, "score": used_img})
    rows.sort(key=lambda x: (-x["score"], x["r"]["id"]))
    short = {lg.key: "".join(w[0] for w in lg.name.split()).upper()[:3] for lg in leagues}
    lines = [f"TRIAL REPORT  {now:%Y-%m-%d %H:%M} UTC   ({len(results)} candidate feeds, items newer than {(now - cutoff).days} days)",
             "",
             "Ranked by: used items that have a picture. 'used' = fresh and about one of the six competitions.",
             "Leagues: " + ", ".join(f"{short[k]}={lg.name}" for k, lg in zip(short, leagues)),
             "",
             f"{'feed':<26}{'read':>5}{'img':>5}{'used':>5}{'used+img':>9}{'newest':>8}  per league",
             "-" * 100]
    for x in rows:
        r = x["r"]
        if not r["ok"]:
            continue
        pl = " ".join(f"{short[k]}:{v}" for k, v in x["per"].items() if v)
        lines.append(f"{r['id']:<26}{r['raw']:>5}{r['images']:>5}{r['kept']:>5}{x['used_img']:>9}{fmt_age(r['newest_h']):>8}  {pl}")
    failed = [x["r"] for x in rows if not x["r"]["ok"]]
    lines += ["", f"FAILED ({len(failed)}):"]
    for r in failed:
        lines.append(f"  {r['id']:<26}{r['error'][:110]}")
    total_ok = sum(1 for x in rows if x["r"]["ok"])
    lines += ["", f"{total_ok} of {len(results)} feeds worked; "
                  f"{sum(1 for x in rows if x['score'] > 0)} had at least one used story with a picture."]
    text = "\n".join(lines)
    print(text)
    out = Path(args.out or "trial_output")
    out.mkdir(parents=True, exist_ok=True)
    (out / "trial_report.txt").write_text(text, encoding="utf-8")
    print(f"\nReport also saved to {out / 'trial_report.txt'}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Build a static football news page from RSS feeds.")
    ap.add_argument("--config", default=str(Path(__file__).with_name("config.json")))
    ap.add_argument("--out", help="output folder (default: 'output_dir' in config.json)")
    ap.add_argument("--open", action="store_true", help="open the page in the browser when done")
    ap.add_argument("--samples", help="test mode: read feeds from this folder instead of the internet")
    ap.add_argument("--now", help="test mode: pretend it is this ISO time")
    ap.add_argument("--trial", metavar="FILE", help="trial mode: test the candidate feeds listed in FILE and print a report")
    args = ap.parse_args()

    cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    st = cfg["settings"]
    global DISPLAY_TZ, CLUB_STYLES
    CLUB_STYLES = {k: tuple(v) for k, v in cfg.get("club_styles", {}).items()}
    try:
        DISPLAY_TZ = zoneinfo.ZoneInfo(st["timezone"]) if st.get("timezone") else None
    except Exception:  # e.g. Windows without the time zone database: use the computer's own time
        DISPLAY_TZ = None
    now = parse_date(args.now) if args.now else dt.datetime.now(UTC)
    if now is None:
        sys.exit("Could not read --now value")
    leagues = build_leagues(cfg)
    if args.trial:
        cand = json.loads(Path(args.trial).read_text(encoding="utf-8"))
        cfg = dict(cfg, sources=cand["sources"])
        cfg["settings"] = dict(st, google_news_club_feeds=False, max_workers=max(st["max_workers"], 12))
        st = cfg["settings"]
    sources = expand_sources(cfg)
    exclude_titles = [re.compile(p) for p in cfg.get("exclude_title_patterns", [])]

    print(f"Fetching {len(sources)} feeds ...")
    with concurrent.futures.ThreadPoolExecutor(max_workers=st["max_workers"]) as pool:
        results = list(pool.map(lambda s: load_source(s, args, st, now), sources))

    cutoff = now - dt.timedelta(days=st["max_age_days"])
    if args.trial:
        return run_trial(results, leagues, exclude_titles, cutoff, now, args)
    kept = []
    for r in results:
        classify_source(r, leagues, exclude_titles, cutoff, now)
        kept.extend(r["kept_items"])

    clusters = build_clusters(kept, now)
    lookups = None
    if not args.samples:  # test mode has no internet
        lookups = add_page_images(clusters, leagues, st)
    out = Path(args.out or st["output_dir"])
    if not out.is_absolute():
        out = Path(args.config).resolve().parent / out
    build_site(out, cfg, leagues, clusters, results, now)

    ok = sum(1 for r in results if r["ok"])
    print(f"\nFeeds that worked: {ok} of {len(results)}")
    for r in results:
        if r["ok"]:
            drops = ", ".join(f"{n} {why}" for n, why in ((r["drop_old"], "too old"), (r["drop_excluded"], "excluded"), (r["drop_noleague"], "no league")) if n)
            print(f"  OK      {r['id']:<22} {r['raw']:>4} read, {r['kept']:>4} used, {r['images']:>4} with image"
                  f"   newest {fmt_age(r['newest_h'])}" + (f"   dropped: {drops}" if drops else ""))
        else:
            print(f"  FAILED  {r['id']:<22} {r['error']}")
    print(f"\n{len(kept)} items -> {len(clusters)} stories after merging duplicates")
    if lookups:
        print(f"Pictures found on article pages: {lookups[0]} of {lookups[1]} looked up")
        for reason, n in sorted(LOOKUP_STATS.items(), key=lambda kv: -kv[1]):
            print(f"    {n:>3} x {reason}")
        for line in LOOKUP_SAMPLES:
            print(f"    e.g. {line}")
    print(f"Stories with a picture: {sum(1 for c in clusters if c['image'])} of {len(clusters)}")
    for lg in leagues:
        print(f"  {lg.name:<18} {sum(1 for c in clusters if lg.key in c['leagues']):>4} stories")
    index = out / "index.html"
    print(f"\nDone. Open this file in your browser:\n  {index}")
    if args.open:
        webbrowser.open(index.as_uri())
    return 0


if __name__ == "__main__":
    sys.exit(main())
