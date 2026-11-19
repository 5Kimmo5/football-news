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
import concurrent.futures
import datetime as dt
import email.utils
import gzip
import html
import json
import re
import sys
import unicodedata
import urllib.parse
import urllib.request
import webbrowser
import zoneinfo
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from pathlib import Path

UTC = dt.timezone.utc
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


# --------------------------------------------------------------------------- fetching and parsing

def local(tag) -> str:
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) and "}" in tag else tag


def fetch(url: str, timeout: int, ua: str) -> bytes:
    req = urllib.request.Request(url, headers={
        "User-Agent": ua,
        "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml;q=0.9, */*;q=0.5",
        "Accept-Encoding": "identity",
    })
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


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
        })
    if not entries and first is not None:
        raw = re.sub(r"\s+", " ", ET.tostring(first, encoding="unicode"))[:500]
        raise ValueError("items found but none usable. First item was: " + raw)
    return entries


def load_source(src: dict, args, st: dict, now: dt.datetime) -> dict:
    res = {"id": src["id"], "name": src["name"], "ok": False, "url": "", "raw": 0, "kept": 0, "error": "", "items": []}
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
                data = fetch(u["url"], st["timeout_seconds"], src.get("user_agent") or st["user_agent"])
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
            ))
        return res
    res["error"] = " | ".join(errors)
    return res


# --------------------------------------------------------------------------- classification

def classify(item: Item, leagues: list) -> None:
    text = norm(item.title + " " + item.summary)
    found = set(item.default_leagues)
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
        latest = max(m.published for m in members)
        age_h = max(0.0, (now - latest).total_seconds() / 3600)
        score = 2.0 * min(len(sources) - 1, 5) + 4.0 * 0.5 ** (age_h / 12)
        result.append({"rep": rep, "sources": sources, "leagues": leagues, "teams": teams,
                       "latest": latest, "score": score})
    return result


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
.league{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:6px 18px 12px;margin:0 0 18px}
.league-head{display:flex;justify-content:space-between;align-items:baseline;gap:12px;padding:10px 0 6px}
.league-head h2{margin:0;font-size:1.2rem}
.league-head h2 a{text-decoration:none}
.league-head h2 a:hover,.all:hover{color:var(--accent)}
.all{font-size:.9rem;color:var(--muted);text-decoration:none;white-space:nowrap}
.stories{list-style:none;margin:0;padding:0}
.story{padding:10px 0;border-top:1px solid var(--line)}
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


def fmt_time(d: dt.datetime) -> str:
    return to_local(d).strftime("%d %b %H:%M")


def translate_url(link: str) -> str:
    return "https://translate.google.com/translate?sl=auto&tl=en&u=" + urllib.parse.quote(link, safe="")


def story_li(c: dict, league: League, with_teams_attr: bool, with_summary: bool = False) -> str:
    rep = c["rep"]
    lang_attr = f' lang="{esc(rep.lang)}"' if rep.lang != "en" else ""
    teams = c["teams"].get(league.key, {})
    data = f' data-teams="{esc(" ".join(sorted(teams)))}"' if with_teams_attr else ""
    meta = [f'<span class="src">{esc(rep.source_name)}</span>']
    if rep.via:
        meta.append(f"via {esc(rep.via)}")
    meta.append(f'<time datetime="{c["latest"].isoformat()}">{fmt_time(c["latest"])}</time>')
    n = len(c["sources"])
    if n > 1:
        names = ", ".join(sorted(c["sources"].values()))
        meta.append(f'<span class="badge" title="{esc(names)}">{n} sources</span>')
    if rep.lang != "en":
        meta.append(f'<span class="lang">{esc(rep.lang.upper())}</span>')
        meta.append(f'<a class="tr" href="{esc(translate_url(rep.link))}" target="_blank" rel="noopener">Translate</a>')
    summary = f'<p class="sum"{lang_attr}>{esc(rep.summary)}</p>' if (with_summary and rep.summary) else ""
    return (
        f'<li class="story"{data}><a class="title"{lang_attr} href="{esc(rep.link)}" target="_blank" rel="noopener">'
        f'{esc(rep.title)}</a>{summary}<div class="meta">{" ".join(meta)}</div></li>'
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
            f'<section class="league" id="{lg.slug}"><div class="league-head">'
            f'<h2><a href="{lg.file}">{esc(lg.name)}</a></h2>'
            f'<a class="all" href="{lg.file}">All {len(cl)} stories →</a></div>{body}</section>'
        )

    ok = sum(1 for r in results if r["ok"])
    rows = []
    for r in results:
        if r["ok"]:
            host = urllib.parse.urlparse(r["url"]).netloc
            rows.append(f'<tr><td>{esc(r["name"])} <span>({esc(r["id"])})</span></td><td>OK</td>'
                        f'<td>{esc(host)}</td><td>{r["raw"]} read, {r["kept"]} used</td></tr>')
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
        body = f'<div class="filters" id="teams">{"".join(buttons)}</div>{top_html}{latest_html}'
        (out / lg.file).write_text(
            page_shell(f"{lg.name} – {title}", header, body, FILTER_JS,
                       "Stories link to the original publishers. Non-English items have a Translate link."),
            encoding="utf-8",
        )


# --------------------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser(description="Build a static football news page from RSS feeds.")
    ap.add_argument("--config", default=str(Path(__file__).with_name("config.json")))
    ap.add_argument("--out", help="output folder (default: 'output_dir' in config.json)")
    ap.add_argument("--open", action="store_true", help="open the page in the browser when done")
    ap.add_argument("--samples", help="test mode: read feeds from this folder instead of the internet")
    ap.add_argument("--now", help="test mode: pretend it is this ISO time")
    args = ap.parse_args()

    cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    st = cfg["settings"]
    global DISPLAY_TZ
    try:
        DISPLAY_TZ = zoneinfo.ZoneInfo(st["timezone"]) if st.get("timezone") else None
    except Exception:  # e.g. Windows without the time zone database: use the computer's own time
        DISPLAY_TZ = None
    now = parse_date(args.now) if args.now else dt.datetime.now(UTC)
    if now is None:
        sys.exit("Could not read --now value")
    leagues = build_leagues(cfg)
    sources = expand_sources(cfg)
    exclude_titles = [re.compile(p) for p in cfg.get("exclude_title_patterns", [])]

    print(f"Fetching {len(sources)} feeds ...")
    with concurrent.futures.ThreadPoolExecutor(max_workers=st["max_workers"]) as pool:
        results = list(pool.map(lambda s: load_source(s, args, st, now), sources))

    cutoff = now - dt.timedelta(days=st["max_age_days"])
    kept = []
    for r in results:
        for it in r["items"]:
            if it.published < cutoff or any(rx.search(it.title) for rx in exclude_titles):
                continue
            classify(it, leagues)
            if it.leagues:
                kept.append(it)
                r["kept"] += 1

    clusters = build_clusters(kept, now)
    out = Path(args.out or st["output_dir"])
    if not out.is_absolute():
        out = Path(args.config).resolve().parent / out
    build_site(out, cfg, leagues, clusters, results, now)

    ok = sum(1 for r in results if r["ok"])
    print(f"\nFeeds that worked: {ok} of {len(results)}")
    for r in results:
        if r["ok"]:
            print(f"  OK      {r['id']:<22} {r['raw']:>4} read, {r['kept']:>4} used")
        else:
            print(f"  FAILED  {r['id']:<22} {r['error']}")
    print(f"\n{len(kept)} items -> {len(clusters)} stories after merging duplicates")
    for lg in leagues:
        print(f"  {lg.name:<18} {sum(1 for c in clusters if lg.key in c['leagues']):>4} stories")
    index = out / "index.html"
    print(f"\nDone. Open this file in your browser:\n  {index}")
    if args.open:
        webbrowser.open(index.as_uri())
    return 0


if __name__ == "__main__":
    sys.exit(main())
