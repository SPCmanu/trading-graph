"""
Graphique boursier interactif (Lightweight Charts) : marchés US, français et européens.

- Recherche par ticker OU par nom, avec suggestions (Yahoo Finance)
- 20 indicateurs ajoutables / supprimables (dont vos 17 favoris TradingView), paramètres et couleurs
  modifiables ; CLIC DROIT sur le graphique : ajouter un indicateur sur le graphique ou en dessous,
  masquer / déplacer / régler / supprimer les indicateurs actifs
- Listes déroulantes : actions par pays, indices mondiaux, matières premières
- Onglet « Performances » (États-Unis = S&P 500 complet, France = 250 plus grosses
  capitalisations, Europe, Asie-Pacifique) : un clic sur une ligne ouvre l'action
  dans le graphique ; le séparateur central se glisse à la souris ; filtre par nom
- Onglet « Screener » : « Europe » (500), « France » et « Euronext » (250) et les places européennes = tableaux propres aux sociétés dont le siège est en Europe
  (sans Nvidia & co cotées en Europe, doubles cotations fusionnées), mêmes vues de colonnes et tris que le widget ; sinon widget TradingView avec choix de la région (États-Unis, France,
  Allemagne, Royaume-Uni, Europe, Asie…) et de la vue de colonnes (Général, Valorisation
  avec P/E et P/B, Dividendes, Rentabilité, Croissance, Santé financière)
- Clic sur une société (onglet Performances) : cadre « fiche » aux 6 onglets inspirés de TradingView :
  Finances, Dossiers, Actualités, Données techniques, Prévisions, Saisonniers
  (widget TradingView pour Finances ; Dossiers (résultats + dépôts SEC) et Actualités
  (Google Actualités + Yahoo) sont construits ici ; le reste est calculé ici)
- Les listes S&P 500 et France sont récupérées en ligne puis mises en cache 7 jours
  (fichier univers_cache.json à côté du script) ; si la récupération échoue, la
  petite liste intégrée est utilisée à la place
- Périodes (1 mois, 3, 6 mois, 1, 2, 3, 4, 5, 10 ans, Max) et intervalles (5 min à 1 mois) en listes déroulantes du bandeau
- Disposition 1 graphique, 3 graphiques côte à côte (colonnes) ou 3 graphiques empilés (liste déroulante du bandeau) : même action, durée de bougies propre à chaque graphique ;
  clic droit = indicateur sur CE graphique seulement, panneau de droite = indicateur sur tous les graphiques
- Ichimoku : nuage Kumo rempli entre Senkou Span A et B, vert en tendance haussière / rouge en tendance baissière, couleurs paramétrables

Installation :  pip install yfinance pandas
Utilisation  :  python totalenergies_chart.py
                -> ouvre http://127.0.0.1:8765 dans le navigateur (internet requis)
                Ctrl+C dans le terminal pour arrêter.

Pourquoi un petit serveur local ? Un fichier HTML ouvert seul ne peut pas
interroger Yahoo Finance (blocage CORS). Le script sert donc la page ET relaie
les requêtes de données et de recherche. Les indicateurs sont calculés dans le
navigateur : changer un paramètre met le graphique à jour instantanément.
"""
import base64
import html as html_mod
import ipaddress
import socket
import json
import math
import os
import re
import sys
import threading
import time
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from email.utils import parsedate_to_datetime
from datetime import datetime, timedelta
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import pandas as pd
import yfinance as yf

PORT = 8765
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124 Safari/537.36"
TYPES_OK = {"EQUITY", "ETF", "INDEX"}
LIMITES_JOURS = {"5m": 59, "15m": 59, "30m": 59, "1h": 729, "4h": 729}   # limites imposées par Yahoo en intraday
INTERVALLES = {"5m", "15m", "30m", "1h", "4h", "1d", "1wk", "1mo"}      # le 4 h est reconstruit à partir du 1 h (Yahoo ne le propose pas)
VERROU = threading.Lock()                        # yfinance n'aime pas les appels simultanés


# ---------- Données ----------
def recherche(q):
    url = "https://query2.finance.yahoo.com/v1/finance/search?" + urllib.parse.urlencode(
        {"q": q, "quotesCount": 12, "newsCount": 0, "listsCount": 0, "lang": "fr-FR", "region": "FR"})
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=8) as r:
            quotes = json.load(r).get("quotes", [])
    except Exception:
        try:                                       # repli via yfinance si disponible
            quotes = yf.Search(q, max_results=12).quotes
        except Exception:
            quotes = []
    out = []
    for x in quotes:
        if x.get("symbol") and x.get("quoteType") in TYPES_OK:
            out.append({"symbol": x["symbol"],
                        "name": x.get("longname") or x.get("shortname") or "",
                        "exch": x.get("exchDisp") or x.get("exchange") or "",
                        "type": x.get("quoteType")})
    return out


def historique(symbole, jours, interv):
    if interv not in INTERVALLES:
        raise ValueError("intervalle invalide")
    n = None if jours == "max" else int(jours)
    limite, note = LIMITES_JOURS.get(interv), ""
    if limite and (n is None or n > limite):
        n, note = limite, f"En {interv}, Yahoo limite l'historique à {limite} jours."
    kw = dict(interval="1h" if interv == "4h" else interv, auto_adjust=True, progress=False)
    if n is None:
        kw["period"] = "max"
    else:
        kw["start"] = (datetime.now() - timedelta(days=n)).strftime("%Y-%m-%d")
    with VERROU:
        df = yf.download(symbole, **kw)
        devise = ""
        try:
            devise = yf.Ticker(symbole).fast_info["currency"] or ""
        except Exception:
            pass
    if df is None or df.empty:
        raise ValueError("symbole introuvable ou sans données")
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)
    df = df[["Open", "High", "Low", "Close", "Volume"]].dropna()
    df = df[~df.index.duplicated(keep="last")].sort_index()
    if interv == "4h":                             # bougies de 4 h = regroupement des bougies d'1 h (bornes à 8 h, 12 h, 16 h… heure locale)
        df = df.resample(pd.Timedelta(hours=4), origin="start_day").agg(
            {"Open": "first", "High": "max", "Low": "min", "Close": "last", "Volume": "sum"}).dropna()
    idx = pd.DatetimeIndex(df.index)
    if idx.tz is not None:
        idx = idx.tz_localize(None)                # heure locale de la place de cotation
    t = ((idx - pd.Timestamp("1970-01-01")) // pd.Timedelta(seconds=1)).to_numpy()
    bars = [[int(a), round(float(o), 4), round(float(h), 4), round(float(l), 4), round(float(c), 4), int(v)]
            for a, o, h, l, c, v in zip(t, df.Open, df.High, df.Low, df.Close, df.Volume)]
    return {"symbol": symbole, "currency": devise, "note": note, "bars": bars}


CACHE_EPS = {}


def eps_historique(sym):
    """BPA publiés par trimestre [[horodatage, bpa], ...] (pour le ratio cours/bénéfices glissant 4 trimestres)."""
    c = CACHE_EPS.get(sym)
    if c and time.time() - c[0] < 3600:
        return c[1]
    with VERROU:
        try:
            df = yf.Ticker(sym).get_earnings_dates(limit=60)
        except Exception:
            df = None
    out = []
    if df is not None and len(df):
        col = next((k for k in df.columns if str(k).lower().startswith("reported")), None)
        if col is not None:
            for d, v in df[col].dropna().items():
                try:
                    ts = pd.Timestamp(d)
                    if ts.tzinfo is not None:
                        ts = ts.tz_localize(None)
                    out.append([int((ts - pd.Timestamp("1970-01-01")).total_seconds()), round(float(v), 4)])
                except Exception:
                    pass
    out.sort()
    CACHE_EPS[sym] = (time.time(), out)
    return out


CACHE_PERF = {}                                  # {(symboles...): (horodatage, résultat)}


def _cloture(df, s):
    try:
        c = df[s]["Close"]
    except KeyError:
        c = df["Close"]                          # cas d'un seul symbole
    if isinstance(c, pd.DataFrame):
        c = c.iloc[:, 0]
    return c.dropna()


def _perf(c):
    if len(c) < 2:
        return None
    idx = pd.DatetimeIndex(c.index)
    if idx.tz is not None:
        idx = idx.tz_localize(None)
    c = pd.Series(c.values, index=idx)
    d, dernier = c.index[-1], float(c.iloc[-1])

    def base(ts):                                # dernier cours connu à la date ts
        x = c[c.index <= ts]
        return float(x.iloc[-1]) if len(x) else None

    def pct(b):
        return round((dernier / b - 1) * 100, 2) if b else None

    res = {"price": round(dernier, 4), "d1": pct(float(c.iloc[-2]))}
    for cle, ts in (("w1", d - pd.Timedelta(days=7)), ("m1", d - pd.DateOffset(months=1)),
                    ("m3", d - pd.DateOffset(months=3)), ("m6", d - pd.DateOffset(months=6)),
                    ("y1", d - pd.DateOffset(years=1))):
        res[cle] = pct(base(ts))
    res["ytd"] = pct(base(pd.Timestamp(d.year, 1, 1) - pd.Timedelta(days=1)))
    return res


def performances(symboles):
    cle, maintenant = tuple(symboles), time.time()
    if cle in CACHE_PERF and maintenant - CACHE_PERF[cle][0] < 300:
        return CACHE_PERF[cle][1]
    debut = (datetime.now() - timedelta(days=400)).strftime("%Y-%m-%d")
    with VERROU:
        df = yf.download(list(symboles), start=debut, interval="1d", auto_adjust=True,
                         progress=False, group_by="ticker", threads=True)
    out = {}
    for s in symboles:
        try:
            p = _perf(_cloture(df, s))
            if p:
                out[s] = p
        except Exception:
            pass
    CACHE_PERF[cle] = (maintenant, out)
    return out


# ---------- Listes complètes (S&P 500, France 250) ----------
UNIVERS_FICHIER = Path(__file__).with_name("univers_cache.json")
UNIVERS_DUREE = 7 * 86400                        # rafraîchi une fois par semaine
VERROU_U = threading.Lock()


def _texte(cellule):
    return html_mod.unescape(re.sub(r"<[^>]+>", "", cellule)).strip()


def _sp500_depuis_html(page):
    """Extrait [symbole, nom] du tableau « constituents » de la page Wikipedia."""
    m = re.search(r'<table[^>]*id="constituents".*?</table>', page, re.S)
    if not m:
        raise ValueError("tableau S&P 500 introuvable")
    out = []
    for tr in m.group(0).split("<tr")[1:]:
        cel = [_texte(c) for c in re.findall(r"<td[^>]*>(.*?)</td>", tr, re.S)]
        if len(cel) >= 2 and cel[0]:
            out.append([cel[0].replace(".", "-"), cel[1]])   # BRK.B -> BRK-B (format Yahoo)
    if len(out) < 400:
        raise ValueError(f"liste S&P 500 incomplète ({len(out)})")
    return out


def _sp500():
    req = urllib.request.Request("https://en.wikipedia.org/wiki/List_of_S%26P_500_companies",
                                 headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=20) as r:
        page = r.read().decode("utf-8", "replace")
    return _sp500_depuis_html(page), "Wikipedia (composition du S&P 500)"


def _france():
    """250 plus grosses capitalisations d'Euronext Paris, triées par capitalisation (screener Yahoo)."""
    q = yf.EquityQuery("and", [yf.EquityQuery("eq", ["exchange", "PAR"]),
                               yf.EquityQuery("gt", ["intradaymarketcap", 0])])
    with VERROU:
        res = yf.screen(q, sortField="intradaymarketcap", sortAsc=False, size=250)
    out, vus = [], set()
    for x in (res or {}).get("quotes", []):
        sym = x.get("symbol", "")
        if sym.endswith(".PA") and sym not in vus:
            vus.add(sym)
            out.append([sym, x.get("longName") or x.get("shortName") or sym])
    if len(out) < 100:
        raise ValueError(f"screener Yahoo : seulement {len(out)} résultats")
    return out, "Yahoo Finance (capitalisation décroissante)"


def univers(cle):
    sources = {"us": _sp500, "fr": _france}
    if cle not in sources:
        raise ValueError("liste inconnue")
    with VERROU_U:
        try:
            cache = json.loads(UNIVERS_FICHIER.read_text(encoding="utf-8"))
        except Exception:
            cache = {}
        e = cache.get(cle)
        if e and time.time() - e["t"] < UNIVERS_DUREE:
            return e
        try:
            liste, source = sources[cle]()
        except Exception as ex:
            if e:                                # liste périmée valable plutôt que rien
                return {**e, "note": "liste en cache (actualisation impossible)"}
            raise ValueError(f"récupération impossible : {ex}")
        e = {"t": time.time(), "list": liste, "note": source}
        cache[cle] = e
        try:
            UNIVERS_FICHIER.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")
        except Exception:
            pass
        return e


# ---------- Fiche société (infos, résultats, actualités, synthèse IA) ----------
GOOGLE_BOURSES = {"PA": "EPA", "DE": "ETR", "L": "LON", "AS": "AMS", "MC": "BME", "MI": "BIT", "SW": "SWX",
                  "BR": "EBR", "ST": "STO", "CO": "CPH", "OL": "OSL", "HE": "HEL", "LS": "ELI", "VI": "VIE",
                  "IR": "ISE", "T": "TYO", "HK": "HKG", "KS": "KRX", "TW": "TPE", "NS": "NSE", "AX": "ASX"}
YAHOO_US = {"NMS": "NASDAQ", "NGM": "NASDAQ", "NCM": "NASDAQ", "NYQ": "NYSE", "ASE": "NYSEAMERICAN",
            "PCX": "NYSEARCA", "BTS": "BATS"}
MODELE_IA = os.environ.get("ANTHROPIC_MODEL", "claude-sonnet-5-5")
CACHE_INFO, CACHE_IA = {}, {}


def _n(x):
    """Nombre JSON-compatible (NaN / inf / non numérique -> None)."""
    try:
        x = float(x)
        return None if math.isnan(x) or math.isinf(x) else x
    except Exception:
        return None


def lien_google(sym, exch=""):
    """URL Google Finance (ex. TTE.PA -> TTE:EPA). Renvoie None si la place est inconnue."""
    base, bourse = sym, None
    if "." in sym and not sym.startswith("^"):
        base, suf = sym.rsplit(".", 1)
        bourse = GOOGLE_BOURSES.get(suf)
    else:
        bourse = YAHOO_US.get(exch)
        base = sym.replace("-", ".")             # BRK-B -> BRK.B
    if not bourse:
        return None
    return f"https://www.google.com/finance/quote/{urllib.parse.quote(base)}:{bourse}?hl=fr"


def _ajoute_tv(lignes, tv):
    """Complète les résultats avec le scanner public de TradingView (dernière et prochaine publication, BPA publié / attendu).
    Aucun identifiant n'est nécessaire ; en cas d'échec ou de champ absent, on garde simplement les données Yahoo."""
    champs = ["earnings_release_date", "earnings_release_next_date", "earnings_per_share_fq",
              "earnings_per_share_forecast_fq", "earnings_per_share_forecast_next_fq"]
    url = ("https://scanner.tradingview.com/symbol?symbol=" + urllib.parse.quote(tv, safe="")
           + "&fields=" + ",".join(champs) + "&no_404=true")
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Origin": "https://fr.tradingview.com", "Referer": "https://fr.tradingview.com/"})
    with urllib.request.urlopen(req, timeout=8) as r:
        d = json.load(r)
    jour = lambda ts: datetime.fromtimestamp(ts).strftime("%Y-%m-%d")
    for ts, est, rep in ((d.get("earnings_release_date"), d.get("earnings_per_share_forecast_fq"), d.get("earnings_per_share_fq")),
                         (d.get("earnings_release_next_date"), d.get("earnings_per_share_forecast_next_fq"), None)):
        if not isinstance(ts, (int, float)) or ts <= 0:
            continue
        j = jour(ts)
        proche = next((e for e in lignes if abs((datetime.strptime(e["date"], "%Y-%m-%d") - datetime.strptime(j, "%Y-%m-%d")).days) <= 3), None)
        if proche:
            if proche["est"] is None: proche["est"] = _n(est)
            if proche["rep"] is None: proche["rep"] = _n(rep)
        else:
            lignes.append({"date": j, "est": _n(est), "rep": _n(rep), "sur": None})
    lignes.sort(key=lambda e: e["date"], reverse=True)


def infos(sym):
    cle, maintenant = sym, time.time()
    if cle in CACHE_INFO and maintenant - CACHE_INFO[cle][0] < 600:
        return CACHE_INFO[cle][1]
    with VERROU:
        t = yf.Ticker(sym)
        try:
            info = t.info or {}
        except Exception:
            info = {}
        try:
            dates = t.get_earnings_dates(limit=16)
        except Exception:
            dates = None
        try:
            trim = t.quarterly_income_stmt
        except Exception:
            trim = None
        try:
            actus = t.news or []
        except Exception:
            actus = []
        try:
            cal = t.calendar or {}
        except Exception:
            cal = {}
        try:
            ann = t.income_stmt
        except Exception:
            ann = None
    if not info and not actus and dates is None:
        raise ValueError("aucune information trouvée pour ce symbole")
    ceo = ""
    for o in info.get("companyOfficers") or []:
        t = (o.get("title") or "").lower()
        if "ceo" in t or "chief executive" in t:
            ceo = o.get("name") or ""
            break
    prix = _n(info.get("currentPrice") or info.get("regularMarketPrice"))
    div = _n(info.get("dividendRate"))
    res = {
        "symbol": sym,
        "name": info.get("longName") or info.get("shortName") or sym,
        "currency": info.get("currency") or "",
        "sector": info.get("sector") or "", "industry": info.get("industry") or "",
        "country": info.get("country") or "", "website": info.get("website") or "",
        "employees": _n(info.get("fullTimeEmployees")), "ceo": ceo, "city": info.get("city") or "",
        "about": (info.get("longBusinessSummary") or "")[:1800],
        "cap": _n(info.get("marketCap")), "pe": _n(info.get("trailingPE")), "fpe": _n(info.get("forwardPE")),
        "div_rate": div, "div_yield": round(div / prix * 100, 2) if div and prix else None,
        "lo52": _n(info.get("fiftyTwoWeekLow")), "hi52": _n(info.get("fiftyTwoWeekHigh")),
        "beta": _n(info.get("beta")),
        "reco": info.get("recommendationKey") or "", "n_analystes": _n(info.get("numberOfAnalystOpinions")),
        "cible": _n(info.get("targetMeanPrice")), "cible_haut": _n(info.get("targetHighPrice")),
        "cible_bas": _n(info.get("targetLowPrice")),
        "google": lien_google(sym, info.get("exchange", "")),
        "tv": symbole_tv(sym, info.get("exchange", "")),
        "tv_dossiers": None, "tv_actus": None,
        "earnings": [], "quarters": [], "years": [], "news": [],
    }
    if res["tv"]:
        base_tv = "https://fr.tradingview.com/symbols/" + res["tv"].replace(":", "-") + "/"
        res["tv_dossiers"], res["tv_actus"] = base_tv + "documents/", base_tv + "news/"
    if res["google"]:
        res["google_earnings"] = res["google"] + "&tab=earnings"
    try:
        for idx, r in dates.iterrows():
            res["earnings"].append({"date": idx.strftime("%Y-%m-%d"), "est": _n(r.get("EPS Estimate")),
                                    "rep": _n(r.get("Reported EPS")), "sur": _n(r.get("Surprise(%)"))})
        lim = (datetime.now() - timedelta(days=3 * 366)).strftime("%Y-%m-%d")    # Yahoo mêle parfois des dates de 2015-2019 aux récentes
        res["earnings"] = [e for e in res["earnings"] if e["date"] >= lim]
        res["earnings"].sort(key=lambda e: e["date"], reverse=True)
        res["earnings"] = res["earnings"][:8]
    except Exception:
        res["earnings"] = []
    try:                                         # prochaine publication annoncée (si Yahoo ne la donne pas dans la liste)
        auj = datetime.now().strftime("%Y-%m-%d")
        if not any(e["date"] >= auj and e["rep"] is None for e in res["earnings"]):
            for d in (cal.get("Earnings Date") or [])[:1]:
                res["earnings"].insert(0, {"date": d.strftime("%Y-%m-%d"), "est": _n(cal.get("Earnings Average")), "rep": None, "sur": None})
    except Exception:
        pass
    if res["tv"]:
        try:
            _ajoute_tv(res["earnings"], res["tv"])
        except Exception:
            pass
    try:
        for col in list(ann.columns)[:4]:
            g = lambda k: _n(ann.at[k, col]) if k in ann.index else None
            res["years"].append({"date": col.strftime("%Y-%m-%d"), "rev": g("Total Revenue"), "net": g("Net Income")})
    except Exception:
        res["years"] = []
    try:
        for col in list(trim.columns)[:4]:
            g = lambda k: _n(trim.at[k, col]) if k in trim.index else None
            res["quarters"].append({"date": col.strftime("%Y-%m-%d"), "rev": g("Total Revenue"), "net": g("Net Income")})
    except Exception:
        res["quarters"] = []
    for x in actus[:8]:
        c = x.get("content") or x
        lien = ((c.get("canonicalUrl") or c.get("clickThroughUrl") or {}).get("url")) or c.get("link") or ""
        if c.get("title") and lien.startswith("http"):
            res["news"].append({"title": c["title"], "url": lien, "summary": (c.get("summary") or "")[:400],
                                "src": (c.get("provider") or {}).get("displayName") or c.get("publisher") or "",
                                "date": (c.get("pubDate") or "")[:10]})
    CACHE_INFO[cle] = (maintenant, res)
    return res


def synthese_ia(sym):
    """Récapitulatif façon « Fais-moi un récapitulatif sur X » via l'API Claude, à partir des données de la fiche."""
    cle_api = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if not cle_api:
        raise ValueError("synthèse IA désactivée : définissez la variable d'environnement ANTHROPIC_API_KEY")
    if sym in CACHE_IA and time.time() - CACHE_IA[sym][0] < 1800:
        return CACHE_IA[sym][1]
    d = infos(sym)
    contexte = json.dumps({k: d[k] for k in ("name", "symbol", "currency", "sector", "industry", "country", "cap", "pe",
                                             "fpe", "div_yield", "lo52", "hi52", "reco", "n_analystes", "cible",
                                             "cible_haut", "cible_bas", "earnings", "quarters", "news")},
                          ensure_ascii=False)
    prompt = (f"Fais-moi un récapitulatif sur {d['name']} ({sym}) à la date du {datetime.now():%d/%m/%Y}.\n"
              "Appuie-toi UNIQUEMENT sur les données ci-dessous (Yahoo Finance : chiffres clés, résultats, "
              "consensus d'analystes, titres d'actualité). N'invente aucun chiffre ni événement ; si les données "
              "sont insuffisantes sur un point, dis-le.\n"
              "Format de réponse, en français, sans markdown :\n"
              "- un paragraphe de 3 à 4 phrases (situation actuelle) ;\n"
              "- une ligne contenant seulement HAUSSIER, puis 2 à 3 puces commençant par « - » (Titre : explication) ;\n"
              "- une ligne contenant seulement BAISSIER, puis 2 à 3 puces au même format.\n\n"
              f"Données :\n{contexte}")
    corps = json.dumps({"model": MODELE_IA, "max_tokens": 1200,
                        "messages": [{"role": "user", "content": prompt}]}).encode()
    req = urllib.request.Request("https://api.anthropic.com/v1/messages", data=corps, method="POST",
                                 headers={"x-api-key": cle_api, "anthropic-version": "2023-06-01",
                                          "content-type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            out = json.load(r)
    except urllib.error.HTTPError as e:
        raise ValueError(f"API Claude : erreur {e.code}")
    texte = "".join(b.get("text", "") for b in out.get("content", []) if b.get("type") == "text").strip()
    if not texte:
        raise ValueError("réponse vide de l'API")
    CACHE_IA[sym] = (time.time(), texte)
    return texte


# ---------- Profil (Wikipédia) et points forts / faibles (ABC Bourse) ----------
CACHE_WIKI, CACHE_SWOT = {}, {}
_SUFFIXES = re.compile(r"\b(SE|SA|S\.A\.?|Inc\.?|Corp\.?|Corporation|plc|N\.V\.|NV|AG|Ltd\.?|Limited|Company|Co\.?|"
                       r"Holdings?|Cie|SpA|S\.p\.A\.?|AB|ASA|A/S|Oyj)(?=\s|$|,)", re.I)


def _nom_court(nom):
    n = re.sub(r"^The\s+", "", nom.replace(",", " "), flags=re.I)
    return re.sub(r"\s+", " ", _SUFFIXES.sub(" ", n)).strip()


def _json_url(url):
    req = urllib.request.Request(url, headers={"User-Agent": "graphique-boursier/1.0 (usage personnel)"})
    with urllib.request.urlopen(req, timeout=10) as r:
        return json.load(r)


def profil_wikipedia(nom, lang="fr"):
    """Chapeau de l'article Wikipédia de la société (même source que le « Profil » de Google Finance)."""
    court = _nom_court(nom) or nom
    cle = court if lang == "fr" else lang + ":" + court
    if cle in CACHE_WIKI:
        return CACHE_WIKI[cle]
    try:
        j = _json_url(f"https://{lang}.wikipedia.org/w/api.php?" + urllib.parse.urlencode(
            {"action": "query", "list": "search", "srsearch": court + (" entreprise" if lang == "fr" else " company"),
             "srlimit": 4, "format": "json"}))
        mot = court.split()[0].lower()
        for h in j["query"]["search"]:
            if mot not in h["title"].lower():     # évite les articles sans rapport
                continue
            r = _json_url(f"https://{lang}.wikipedia.org/api/rest_v1/page/summary/"
                          + urllib.parse.quote(h["title"].replace(" ", "_"), safe=""))
            if r.get("type") == "standard" and r.get("extract"):
                txt = r["extract"]
                if len(txt) > 900:
                    txt = txt[:900].rsplit(". ", 1)[0] + "."
                res = {"title": r["title"], "extract": txt,
                       "url": ((r.get("content_urls") or {}).get("desktop") or {}).get("page", "")}
                CACHE_WIKI[cle] = res
                return res
    except Exception:
        pass
    return None                                  # échec non mis en cache : nouvelle tentative possible


def profil(sym):
    d = infos(sym)
    return {"wiki": profil_wikipedia(d["name"]), "about": d["about"], "ceo": d["ceo"], "employees": d["employees"],
            "city": d["city"], "country": d["country"], "sector": d["sector"], "industry": d["industry"],
            "website": d["website"], "google": d["google"]}


def _swot_depuis_html(page, url):
    marques = [("forces", "swot_str.svg"), ("faiblesses", "swot_weak.svg"),
               ("opportunites", "swot_opp.svg"), ("menaces", "swot_thr.svg")]
    pos = sorted((page.find(m), k) for k, m in marques if page.find(m) >= 0)
    if not pos:
        raise ValueError("analyse SWOT introuvable sur la page ABC Bourse")
    out = {k: [] for k, _ in marques}
    for i, (p, k) in enumerate(pos):
        seg = page[p:pos[i + 1][0] if i + 1 < len(pos) else len(page)]
        h2 = seg.find("<h2")                     # la dernière rubrique s'arrête au titre suivant
        if h2 > 0:
            seg = seg[:h2]
        out[k] = [t for t in (_texte(x) for x in re.findall(r"<li[^>]*>(.*?)</li>", seg, re.S)) if t]
    if not any(out.values()):
        raise ValueError("analyse SWOT vide sur la page ABC Bourse")
    m = re.search(r"Note ABC Bourse\s*:\s*(\d+)\s*/\s*20", _texte(page))
    out["note"] = int(m.group(1)) if m else None
    out["url"] = url
    return out


def swot(sym):
    if not sym.endswith(".PA"):
        raise ValueError("analyse ABC Bourse disponible uniquement pour les valeurs cotées à Paris")
    if sym in CACHE_SWOT and time.time() - CACHE_SWOT[sym][0] < 6 * 3600:
        return CACHE_SWOT[sym][1]
    url = "https://www.abcbourse.com/analyses/conseil/" + urllib.parse.quote(sym[:-3] + "p")   # ERF.PA -> ERFp
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept-Language": "fr-FR,fr;q=0.9"})
    try:
        with urllib.request.urlopen(req, timeout=15) as r:
            page = r.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        raise ValueError(f"page ABC Bourse introuvable (erreur {e.code})")
    res = _swot_depuis_html(page, url)
    CACHE_SWOT[sym] = (time.time(), res)
    return res


# ---------- Serveur ----------
# ---------- Onglets « façon TradingView » : symbole TV, dossiers, prévisions, actualités ----------
TV_BOURSES = {"PA": "EURONEXT", "AS": "EURONEXT", "BR": "EURONEXT", "LS": "EURONEXT", "IR": "EURONEXT", "DE": "XETR",
              "F": "FWB", "L": "LSE", "MC": "BME", "MI": "MIL", "SW": "SIX", "ST": "OMXSTO", "CO": "OMXCOP",
              "HE": "OMXHEX", "OL": "OSL", "VI": "VIE", "WA": "GPW", "T": "TSE", "HK": "HKEX", "KS": "KRX",
              "KQ": "KRX", "TW": "TWSE", "NS": "NSE", "BO": "BSE", "AX": "ASX", "SS": "SSE", "SZ": "SZSE",
              "TO": "TSX", "SA": "BMFBOVESPA", "SI": "SGX", "TA": "TASE"}
TV_US = {"NMS": "NASDAQ", "NGM": "NASDAQ", "NCM": "NASDAQ", "NYQ": "NYSE", "ASE": "AMEX", "PCX": "NYSE ARCA"}


def symbole_tv(sym, exch=""):
    """Symbole Yahoo -> symbole TradingView (EURONEXT:TTE, NASDAQ:AAPL...). None pour indices et futures."""
    if sym.startswith("^") or "=" in sym:
        return None
    if "." in sym and sym.rsplit(".", 1)[1].upper() in TV_BOURSES:
        base, suf = sym.rsplit(".", 1)
        suf = suf.upper()
        base = base.replace("-", "_") if suf in ("ST", "CO", "HE", "OL") else base.replace("-", ".")
        if suf == "HK":
            base = base.lstrip("0") or "0"
        return f"{TV_BOURSES[suf]}:{base}"
    place = TV_US.get(exch, "")
    base = sym.replace("-", ".")
    return f"{place}:{base}" if place else base


def _lignes(df, limite=None):
    """DataFrame pandas -> liste de dictionnaires JSON (l'index devient la première colonne)."""
    if df is None or not hasattr(df, "reset_index") or len(df) == 0:
        return []
    d = df.reset_index()
    out = []
    for _, r in (d.head(limite) if limite else d).iterrows():
        o = {}
        for k, v in r.items():
            if hasattr(v, "strftime"):
                o[str(k)] = v.strftime("%Y-%m-%d")
            elif isinstance(v, str):
                o[str(k)] = v
            else:
                o[str(k)] = _n(v)
        out.append(o)
    return out


CACHE_PREV = {}


def prevision(sym):
    """Objectifs de cours, recommandations, estimations BPA / CA, historique des surprises, révisions (Yahoo Finance)."""
    c = CACHE_PREV.get(sym)
    if c and time.time() - c[0] < 900:
        return c[1]
    def essai(f):
        try:
            return f()
        except Exception:
            return None
    with VERROU:
        t = yf.Ticker(sym)
        info = essai(lambda: t.info) or {}
        pt = essai(lambda: t.analyst_price_targets)
        res = {
            "symbol": sym, "currency": info.get("currency") or "",
            "cible": {k: _n(v) for k, v in pt.items()} if isinstance(pt, dict) else {},
            "reco": info.get("recommendationKey") or "", "reco_moy": _n(info.get("recommendationMean")),
            "n_analystes": _n(info.get("numberOfAnalystOpinions")),
            "recos": _lignes(essai(lambda: t.recommendations_summary), 6),
            "eps": _lignes(essai(lambda: t.earnings_estimate)),
            "ca": _lignes(essai(lambda: t.revenue_estimate)),
            "hist": _lignes(essai(lambda: t.earnings_history), 8),
            "croissance": _lignes(essai(lambda: t.growth_estimates)),
            "revisions": _lignes(essai(lambda: t.upgrades_downgrades), 15),
        }
    if not res["cible"] and not res["eps"] and not res["recos"] and not res["ca"]:
        raise ValueError("aucune prévision d'analystes disponible pour ce symbole")
    CACHE_PREV[sym] = (time.time(), res)
    return res


# ---------- Résumé « Dossiers » : profil + résumé des résultats (inspirés de Google Finance) ----------
CACHE_RESUME = {}


def _gf_page(url):
    """Page Google Finance en français (cookie de consentement pour éviter la page d'avertissement européenne)."""
    _, raw, ct = _http(url, headers={"Cookie": "CONSENT=YES+cb.20240101-00-p0.fr+FX+000; SOCS=CAI"}, timeout=10)
    return _decoder_page(raw, ct)


def _txt_html(fragment):
    return re.sub(r"\s+", " ", html_mod.unescape(re.sub(r"<[^>]+>", " ", fragment))).strip()


def _gf_profil(page):
    """Texte « Profil » de la page Overview de Google Finance (None si la structure de la page a changé)."""
    for m in re.finditer(r'class="bLLb2d"[^>]*>(.*?)</div>', page, re.S):
        t = _txt_html(m.group(1))
        if len(t) > 60:
            return t
    return None


def _gf_insights(page):
    """Insights « En bref » de l'onglet Earnings de Google Finance : liste de {titre, texte}."""
    t = _txt_html(page.replace("\\u003c", "<").replace("\\u003e", ">"))
    i = t.find("En bref")
    if i < 0:
        return []
    bloc = t[i:i + 5000]
    out = []
    for m in re.finditer(r"(?:insights_auto)\s*([^:]{5,90}?)\s*:\s*(.+?)(?=insights_auto|$)", bloc):
        txt = m.group(2).strip()
        if len(txt) > 40:
            out.append({"titre": m.group(1).strip(), "texte": txt[:700]})
    return out[:8]


def _f(x, d=2):
    return f"{x:.{d}f}".replace(".", ",")


def _m(x):
    return _f(x / 1e6, 1) + " M"


def _insights_calcules(sym, d):
    """Résumé des résultats construit à partir des données Yahoo / TradingView quand Google Finance n'est pas lisible."""
    dev = d.get("currency") or ""
    auj = datetime.now().strftime("%Y-%m-%d")
    ea = d.get("earnings") or []
    out = []
    try:
        pr = prevision(sym)
    except Exception:
        pr = {}
    nxt = next((e for e in reversed(ea) if e["date"] >= auj and e["rep"] is None), None)
    ca_t = next((r for r in pr.get("ca", []) if str(r.get("period", "")) == "0q"), None)
    if nxt:
        t = f"Prochaine publication prévue le {nxt['date']}."
        if nxt.get("est") is not None:
            t += f" Les analystes attendent un BPA d'environ {_f(nxt['est'])} {dev}"
            t += (f" pour un chiffre d'affaires consensuel de {_m(ca_t['avg'])} {dev}." if ca_t and ca_t.get("avg") else ".")
        out.append({"titre": "Prévisions du chiffre d'affaires et du BPA", "texte": t})
    pub = [e for e in ea if e["rep"] is not None]
    if pub:
        e = pub[0]
        t = f"Dernière publication le {e['date']} : BPA de {_f(e['rep'])} {dev}"
        if e.get("est") is not None:
            ecart = "au-dessus" if e["rep"] > e["est"] else "en dessous" if e["rep"] < e["est"] else "en ligne avec"
            t += f", {ecart} de l'estimation ({_f(e['est'])})"
        if e.get("sur") is not None:
            t += f", soit une surprise de {_f(e['sur'], 1)} %"
        out.append({"titre": "Dernier rapport", "texte": t + "."})
    h = [e for e in pub if e.get("est") is not None][:8]
    if len(h) >= 3:
        bat = sum(1 for e in h if e["rep"] > e["est"])
        out.append({"titre": "Historique des surprises",
                    "texte": f"Sur les {len(h)} dernières publications, le BPA a dépassé l'estimation {bat} fois et est resté inférieur ou égal {len(h) - bat} fois."})
    q = d.get("quarters") or []
    if len(q) >= 2 and q[0].get("rev") and q[1].get("rev"):
        v = (q[0]["rev"] / q[1]["rev"] - 1) * 100
        t = f"Chiffre d'affaires du dernier trimestre clos ({q[0]['date']}) : {_m(q[0]['rev'])} {dev}, soit {_f(v, 1)} % par rapport au trimestre précédent."
        if q[0].get("net") is not None:
            t += f" Résultat net : {_m(q[0]['net'])} {dev}."
        out.append({"titre": "Activité récente", "texte": t})
    ca_a = next((r for r in pr.get("ca", []) if str(r.get("period", "")) == "0y"), None)
    if ca_a and ca_a.get("avg"):
        t = f"Chiffre d'affaires annuel attendu : {_m(ca_a['avg'])} {dev}"
        if ca_a.get("growth") is not None:
            t += f" (croissance prévue de {_f(ca_a['growth'] * 100, 1)} %)"
        out.append({"titre": "Perspectives de l'exercice", "texte": t + "."})
    if d.get("cible") and d.get("n_analystes"):
        t = f"Objectif de cours moyen de {_f(d['cible'])} {dev} selon {int(d['n_analystes'])} analystes"
        if d.get("reco"):
            t += f" ; recommandation générale : {d['reco']}"
        out.append({"titre": "Avis des analystes", "texte": t + "."})
    return out


def resume_societe(sym):
    """Profil de la société (Google Finance → Wikipédia → description Yahoo) et résumé des derniers résultats."""
    c = CACHE_RESUME.get(sym)
    if c and time.time() - c[0] < 1800:
        return c[1]
    d = infos(sym)
    g = d.get("google")
    res = {"nom": d["name"], "google": g, "google_earnings": d.get("google_earnings"),
           "profil": None, "profil_source": "", "insights": [], "insights_source": ""}
    if g:
        try:
            p = _gf_profil(_gf_page(g + "&tab=overview"))
            if p:
                res["profil"], res["profil_source"] = p, "Google Finance"
        except Exception:
            pass
        try:
            ins = _gf_insights(_gf_page(g + "&tab=earnings"))
            if ins:
                res["insights"], res["insights_source"] = ins, "Google Finance"
        except Exception:
            pass
    if not res["profil"]:
        for lang in ("fr", "en"):
            w = profil_wikipedia(d["name"], lang)
            if w:
                res["profil"], res["profil_source"] = w["extract"], "Wikipédia (" + lang + ")"
                break
    if not res["profil"] and d.get("about"):
        res["profil"], res["profil_source"] = d["about"][:900], "Yahoo Finance"
    if not res["insights"]:
        try:
            res["insights"] = _insights_calcules(sym, d)
            res["insights_source"] = "calculé à partir de Yahoo Finance et TradingView"
        except Exception:
            pass
    CACHE_RESUME[sym] = (time.time(), res)
    return res


SEC_UA = os.environ.get("SEC_USER_AGENT", "GraphiqueBoursierPerso votre-email@exemple.com")   # la SEC demande un contact : définissez SEC_USER_AGENT
SEC = {"t": 0, "par_ticker": {}, "par_nom": {}}
CACHE_DOCS = {}
FORMES = {"10-K": "Rapport annuel", "10-Q": "Rapport trimestriel", "8-K": "Événement important", "20-F": "Rapport annuel (émetteur étranger)",
          "40-F": "Rapport annuel (émetteur canadien)", "6-K": "Information périodique (émetteur étranger)", "DEF 14A": "Assemblée générale (procuration)",
          "S-1": "Introduction en bourse", "S-3": "Enregistrement de titres", "4": "Transaction d'initié", "SC 13G": "Participation > 5 %", "SC 13D": "Participation > 5 % (active)"}


def _sec_get(url):
    req = urllib.request.Request(url, headers={"User-Agent": SEC_UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=12) as r:
        return json.load(r)


def _norm(nom):
    return re.sub(r"[^a-z0-9]", "", _nom_court(nom or "").lower())


def _sec_index():
    if time.time() - SEC["t"] < 7 * 86400 and SEC["par_ticker"]:
        return
    d = _sec_get("https://www.sec.gov/files/company_tickers.json")
    pt, pn = {}, {}
    for v in d.values():
        pt[v["ticker"].upper()] = (int(v["cik_str"]), v["title"])
        pn.setdefault(_norm(v["title"]), (int(v["cik_str"]), v["title"]))
    SEC.update(t=time.time(), par_ticker=pt, par_nom=pn)


def documents(sym, nom):
    """Dépôts officiels (SEC EDGAR) : actions américaines, et sociétés étrangères cotées aux États-Unis (rapports 20-F / 6-K)."""
    cle = (sym, nom)
    c = CACHE_DOCS.get(cle)
    if c and time.time() - c[0] < 1800:
        return c[1]
    _sec_index()
    trouve = None
    if "." not in sym or sym.upper().endswith(".US"):
        trouve = SEC["par_ticker"].get(sym.upper().replace(".US", ""))
    if not trouve and nom:
        trouve = SEC["par_nom"].get(_norm(nom))
    if not trouve:
        return {"docs": [], "note": "Société non déclarée à la SEC : pas de dépôts réglementaires américains pour ce titre."}
    cik, titre = trouve
    sub = _sec_get(f"https://data.sec.gov/submissions/CIK{cik:010d}.json")
    r = (sub.get("filings") or {}).get("recent") or {}
    docs = []
    for i, f in enumerate(r.get("form", [])[:150]):
        acc = r["accessionNumber"][i].replace("-", "")
        doc = r["primaryDocument"][i]
        docs.append({"date": r["filingDate"][i], "form": f, "type": FORMES.get(f, ""),
                     "desc": (r.get("primaryDocDescription") or [""] * 999)[i] or "",
                     "url": f"https://www.sec.gov/Archives/edgar/data/{cik}/{acc}/{doc}" if doc else ""})
    res = {"docs": docs, "societe": titre,
           "liste": f"https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK={cik:010d}&type=&dateb=&owner=include&count=40"}
    CACHE_DOCS[cle] = (time.time(), res)
    return res


CACHE_ACTUS = {}


def _rss_google(requete, hl, gl):
    """Flux RSS de Google Actualités pour une requête (aucune clé nécessaire)."""
    url = ("https://news.google.com/rss/search?q=" + urllib.parse.quote(requete)
           + f"&hl={hl}&gl={gl}&ceid={gl}:{hl.split('-')[0]}")
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=10) as r:
        racine = ET.fromstring(r.read())
    out = []
    for it in racine.iter("item"):
        titre, lien = (it.findtext("title") or "").strip(), (it.findtext("link") or "").strip()
        el = it.find("source")
        src = (el.text or "").strip() if el is not None and el.text else ""
        if src and titre.endswith(" - " + src):
            titre = titre[:-len(src) - 3].strip()
        try:
            ts = int(parsedate_to_datetime(it.findtext("pubDate") or "").timestamp())
        except Exception:
            ts = 0
        if titre and lien.startswith("http"):
            out.append({"title": titre, "url": lien, "src": src, "ts": ts})
    return out


def actualites(sym, nom):
    """Actualités de la société : Google Actualités (français, puis anglais) + titres Yahoo Finance, dédoublonnés."""
    cle = (sym, nom)
    c = CACHE_ACTUS.get(cle)
    if c and time.time() - c[0] < 600:
        return c[1]
    court = _nom_court(nom) if nom else sym.split(".")[0]
    items, erreurs = [], []
    for hl, gl in (("fr", "FR"), ("en-US", "US")):
        try:
            items += _rss_google(f'"{court}"', hl, gl)
        except Exception as e:
            erreurs.append(str(e))
        if len(items) >= 12:
            break
    try:
        for n in infos(sym).get("news", []):
            try:
                ts = int(datetime.fromisoformat(n["date"]).timestamp())
            except Exception:
                ts = 0
            items.append({"title": n["title"], "url": n["url"], "src": n.get("src") or "Yahoo Finance", "ts": ts})
    except Exception:
        pass
    vus, out = set(), []
    for x in sorted(items, key=lambda x: -x["ts"]):
        k = re.sub(r"\W+", "", x["title"].lower())[:60]
        if k not in vus:
            vus.add(k)
            out.append(x)
    if not out and erreurs:
        raise ValueError("sources d'actualités injoignables (" + erreurs[0] + ")")
    res = {"items": out[:30]}
    CACHE_ACTUS[cle] = (time.time(), res)
    return res


# ---------- Calendrier des résultats par région (scanner public de TradingView) ----------
EARN_MARCHES = {"us": ["america"], "fr": ["france"],
                "eu": ["germany", "uk", "netherlands", "spain", "italy", "switzerland", "belgium", "sweden", "denmark", "norway"],
                "as": ["japan", "hongkong", "china", "korea", "taiwan", "india", "australia"]}
FX_EUR = {"EUR": 1, "USD": 0.86, "GBP": 1.15, "GBX": 0.0115, "CHF": 1.07, "SEK": 0.09, "DKK": 0.134, "NOK": 0.085, "JPY": 0.0057,
          "HKD": 0.11, "CNY": 0.12, "KRW": 0.00062, "TWD": 0.028, "INR": 0.0098, "AUD": 0.56}   # taux approximatifs : sert seulement à classer les capitalisations
TV_VERS_YAHOO = {"XETR": ".DE", "FWB": ".F", "LSE": ".L", "BME": ".MC", "MIL": ".MI", "SIX": ".SW", "OMXSTO": ".ST", "OMXCOP": ".CO",
                 "OMXHEX": ".HE", "OSL": ".OL", "VIE": ".VI", "GPW": ".WA", "TSE": ".T", "HKEX": ".HK", "KRX": ".KS", "TWSE": ".TW",
                 "NSE": ".NS", "BSE": ".BO", "ASX": ".AX", "SSE": ".SS", "SZSE": ".SZ", "TSX": ".TO", "SGX": ".SI", "TASE": ".TA"}
EURONEXT_MARCHE = {"france": ".PA", "netherlands": ".AS", "belgium": ".BR", "portugal": ".LS", "ireland": ".IR"}
CACHE_EARN = {}
PAYS_EUROPE = ["Germany", "United Kingdom", "Netherlands", "Spain", "Italy", "Switzerland", "Belgium", "Sweden", "Denmark", "Norway",
               "Finland", "France", "Ireland", "Austria", "Portugal", "Luxembourg", "Poland", "Greece"]   # pays du siège (champ « country » de TradingView)
COLONNES_EARN = ["name", "description", "country", "market_cap_basic", "currency", "earnings_release_date", "earnings_release_next_date",
                 "earnings_per_share_fq", "earnings_per_share_forecast_fq", "earnings_per_share_forecast_next_fq"]


def tv_vers_yahoo(s, marche):
    """Symbole TradingView (EURONEXT:EDEN, NASDAQ:AAPL, HKEX:700…) -> symbole Yahoo (EDEN.PA, AAPL, 0700.HK). None si inconnu."""
    bourse, _, tick = s.partition(":")
    if not tick:
        return None
    if bourse in ("NASDAQ", "NYSE", "AMEX", "NYSE ARCA", "CBOE"):
        return tick.replace(".", "-")
    suf = EURONEXT_MARCHE.get(marche, ".PA") if bourse == "EURONEXT" else TV_VERS_YAHOO.get(bourse)
    if not suf:
        return None
    tick = tick.replace("_", "-").replace(".", "-")
    if suf == ".HK":
        tick = tick.zfill(4)
    return tick + suf


def _scan(marche, colonne, t0, t1, pays=None):
    filtre = [{"left": colonne, "operation": "in_range", "right": [t0, t1]}, {"left": "type", "operation": "equal", "right": "stock"}]
    if pays:                                       # filtre côté TradingView, AVANT le « top 40 » : sinon les ADR américains cotés en Allemagne occupent les places
        filtre.append({"left": "country", "operation": "in_range", "right": pays})
    corps = {"filter": filtre,
             "options": {"lang": "fr"}, "columns": COLONNES_EARN,
             "sort": {"sortBy": "market_cap_basic", "sortOrder": "desc"}, "range": [0, 40]}
    req = urllib.request.Request(f"https://scanner.tradingview.com/{marche}/scan", data=json.dumps(corps).encode(), method="POST",
                                 headers={"User-Agent": UA, "Content-Type": "application/json",
                                          "Origin": "https://fr.tradingview.com", "Referer": "https://fr.tradingview.com/"})
    with urllib.request.urlopen(req, timeout=12) as r:
        data = json.load(r).get("data") or []
    return [(marche, x["s"], dict(zip(COLONNES_EARN, x["d"]))) for x in data]


def calendrier_earnings(region, semaine):
    """Résultats de la semaine en cours (semaine=0, du lundi au dimanche) ou de la suivante (1) : 40 plus grosses capitalisations de la région."""
    if region not in EARN_MARCHES or semaine not in (0, 1):
        raise ValueError("paramètres invalides")
    cle = (region, semaine, datetime.now().strftime("%Y-%m-%d"))
    c = CACHE_EARN.get(cle)
    if c and time.time() - c[0] < 1800:
        return c[1]
    auj = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
    debut = auj - timedelta(days=auj.weekday()) + timedelta(days=7 * semaine)
    fin = debut + timedelta(days=7) - timedelta(seconds=1)
    t0, t1 = int(debut.timestamp()), int(fin.timestamp())
    taches = [(m, col) for m in EARN_MARCHES[region] for col in ("earnings_release_next_date", "earnings_release_date")]
    brut, erreurs = [], []
    with ThreadPoolExecutor(max_workers=6) as ex:
        pays = PAYS_EUROPE if region == "eu" else None
        futs = [ex.submit(_scan, m, col, t0, t1, pays) for m, col in taches]
        for f in futs:
            try:
                brut += f.result()
            except Exception as e:
                erreurs.append(str(e))
    par_nom = {}
    for marche, sym, d in brut:
        rd, nd = d.get("earnings_release_date"), d.get("earnings_release_next_date")
        if isinstance(rd, (int, float)) and t0 <= rd <= t1:
            ts, est, rep = rd, d.get("earnings_per_share_forecast_fq"), d.get("earnings_per_share_fq")
        elif isinstance(nd, (int, float)) and t0 <= nd <= t1:
            ts, est, rep = nd, d.get("earnings_per_share_forecast_next_fq"), None
        else:
            continue
        if region == "eu" and d.get("country") and d["country"] not in PAYS_EUROPE:
            continue                               # société dont le siège n'est pas en Europe (ex. américaine cotée à Francfort)
        cap, dev = _n(d.get("market_cap_basic")), d.get("currency") or ""
        nom = d.get("description") or d.get("name") or sym
        ligne = {"date": datetime.fromtimestamp(ts).strftime("%Y-%m-%d"), "tv": sym, "yahoo": tv_vers_yahoo(sym, marche), "nom": nom,
                 "cap": cap, "cur": dev, "est": _n(est), "rep": _n(rep), "_eur": (cap or 0) * FX_EUR.get(dev, 1)}
        k = re.sub(r"[^a-z0-9]", "", nom.lower())            # une même société cotée sur plusieurs places : on garde la plus grosse ligne
        if k not in par_nom or ligne["_eur"] > par_nom[k]["_eur"]:
            par_nom[k] = ligne
    lignes = sorted(par_nom.values(), key=lambda x: -x["_eur"])[:40]
    if not lignes and erreurs:
        raise ValueError("calendrier TradingView injoignable (" + erreurs[0] + ")")
    lignes.sort(key=lambda x: (x["date"], -x["_eur"]))
    for x in lignes:
        del x["_eur"]
    res = {"items": lignes, "debut": debut.strftime("%Y-%m-%d"), "fin": fin.strftime("%Y-%m-%d"), "erreurs": len(erreurs)}
    if lignes:
        CACHE_EARN[cle] = (time.time(), res)
    return res


# ---------- Screener européen : plus grosses capitalisations dont le SIÈGE est en Europe (scanner public de TradingView) ----------
MARCHE_PAYS = {"france": "France", "germany": "Germany", "uk": "United Kingdom", "netherlands": "Netherlands", "spain": "Spain",
               "italy": "Italy", "switzerland": "Switzerland", "belgium": "Belgium", "sweden": "Sweden", "denmark": "Denmark",
               "norway": "Norway", "finland": "Finland", "ireland": "Ireland", "austria": "Austria", "portugal": "Portugal",
               "poland": "Poland", "greece": "Greece"}
FX_EUR.setdefault("PLN", 0.23)
# zone -> (marchés TradingView, pays du siège acceptés, bourse imposée ou None, nombre de sociétés)
ZONES_SCR = {
    "eu":          (list(MARCHE_PAYS), PAYS_EUROPE, None, 500),
    "fr":          (["france"], ["France"], None, 250),
    "euronext":    (["france", "netherlands", "belgium", "portugal", "ireland"], PAYS_EUROPE, "EURONEXT", 250),
    "germany":     (["germany"], ["Germany"], None, 250),
    "uk":          (["uk"], ["United Kingdom"], None, 250),
    "italy":       (["italy"], ["Italy"], None, 250),
    "spain":       (["spain"], ["Spain"], None, 250),
    "switzerland": (["switzerland"], ["Switzerland"], None, 250),
    "sweden":      (["sweden"], ["Sweden"], None, 250),
    "poland":      (["poland"], ["Poland"], None, 250),
}
# vues de colonnes (mêmes thèmes que le widget TradingView) : [champ du scanner, libellé, format]
VUES_SCR = {
    "overview": [["close", "Cours", "n"], ["change", "% jour", "p"], ["market_cap_basic", "Capitalisation", "cap"], ["price_earnings_ttm", "P/E", "n1"],
                 ["earnings_per_share_diluted_ttm", "BPA dilué", "n"], ["dividends_yield", "Rdt dividende", "pl"], ["sector", "Secteur", "txt"]],
    "valuation": [["market_cap_basic", "Capitalisation", "cap"], ["price_earnings_ttm", "P/E", "n1"], ["price_book_fq", "P/B", "n1"],
                  ["price_sales_current", "P/S", "n1"], ["enterprise_value_ebitda_ttm", "VE/EBITDA", "n1"], ["price_free_cash_flow_ttm", "P/FCF", "n1"],
                  ["enterprise_value_fq", "Valeur d'entreprise", "cap"]],
    "dividends": [["dividends_yield", "Rdt dividende", "pl"], ["dividend_payout_ratio_ttm", "Taux de distribution", "pl"],
                  ["dividends_per_share_fq", "Dividende / action", "n"], ["market_cap_basic", "Capitalisation", "cap"], ["sector", "Secteur", "txt"]],
    "profitability": [["gross_margin_ttm", "Marge brute", "pl"], ["operating_margin_ttm", "Marge opérationnelle", "pl"], ["net_margin_ttm", "Marge nette", "pl"],
                      ["return_on_equity", "ROE", "pl"], ["return_on_assets", "ROA", "pl"], ["return_on_invested_capital", "ROIC", "pl"]],
    "growth": [["total_revenue_yoy_growth_ttm", "Croissance du CA (an)", "p"], ["earnings_per_share_diluted_yoy_growth_ttm", "Croissance du BPA (an)", "p"],
               ["net_income_yoy_growth_ttm", "Croissance du résultat net", "p"], ["free_cash_flow_yoy_growth_ttm", "Croissance du FCF", "p"]],
    "health": [["debt_to_equity", "Dette / fonds propres", "n"], ["current_ratio", "Ratio de liquidité", "n"], ["quick_ratio", "Liquidité immédiate", "n"],
               ["net_debt", "Dette nette", "cap"], ["total_debt", "Dette totale", "cap"]],
    "performance": [["change", "1 jour", "p"], ["Perf.W", "1 semaine", "p"], ["Perf.1M", "1 mois", "p"], ["Perf.3M", "3 mois", "p"],
                    ["Perf.6M", "6 mois", "p"], ["Perf.YTD", "Depuis janvier", "p"], ["Perf.Y", "1 an", "p"], ["Perf.5Y", "5 ans", "p"]],
}
COLS_BASE_SCR = ["name", "description", "country", "market_cap_basic", "currency", "close", "change", "sector"]
CACHE_SCR, CACHE_COLS_SCR = {}, {}


def _requete_scan(marche, colonnes, pays, n, bourse=None):
    """Filtre côté TradingView AVANT le tri : le pays du siège exclut les sociétés américaines (Nvidia…) cotées en Europe."""
    filtre = [{"left": "type", "operation": "equal", "right": "stock"},
              {"left": "country", "operation": "in_range", "right": pays},
              {"left": "market_cap_basic", "operation": "greater", "right": 0}]
    if bourse:
        filtre.append({"left": "exchange", "operation": "in_range", "right": [bourse]})
    corps = {"filter": filtre, "options": {"lang": "fr"}, "columns": colonnes,
             "sort": {"sortBy": "market_cap_basic", "sortOrder": "desc"}, "range": [0, n]}
    req = urllib.request.Request(f"https://scanner.tradingview.com/{marche}/scan", data=json.dumps(corps).encode(), method="POST",
                                 headers={"User-Agent": UA, "Content-Type": "application/json",
                                          "Origin": "https://fr.tradingview.com", "Referer": "https://fr.tradingview.com/"})
    with urllib.request.urlopen(req, timeout=20) as r:
        data = json.load(r).get("data") or []
    return [(marche, x["s"], dict(zip(colonnes, x["d"]))) for x in data]


def _colonnes_valides():
    """Teste une fois chaque champ du scanner (un champ inconnu ferait échouer toute la requête) : on ne garde que ceux acceptés."""
    if "ok" in CACHE_COLS_SCR:
        return CACHE_COLS_SCR["ok"]
    tous = list(dict.fromkeys(c[0] for v in VUES_SCR.values() for c in v if c[0] not in COLS_BASE_SCR))
    def test(col):
        try:
            _requete_scan("france", COLS_BASE_SCR + [col], ["France"], 1)
            return col
        except urllib.error.HTTPError:
            return None                                # champ refusé par TradingView
    with ThreadPoolExecutor(max_workers=8) as ex:
        res = list(ex.map(test, tous))
    try:
        _requete_scan("france", COLS_BASE_SCR, ["France"], 1)
    except Exception as e:
        raise ValueError("TradingView injoignable (" + str(e) + ")")
    ok = COLS_BASE_SCR + [c for c in res if c]
    CACHE_COLS_SCR["ok"] = ok
    return ok


def screener_top(zone):
    if zone not in ZONES_SCR:
        raise ValueError("zone inconnue")
    c = CACHE_SCR.get(zone)
    if c and time.time() - c[0] < 1800:
        return c[1]
    marches, pays, bourse, cible = ZONES_SCR[zone]
    colonnes = _colonnes_valides()
    brut, erreurs = [], []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futs = [ex.submit(_requete_scan, m, colonnes, pays, 300 if cible >= 500 else 400, bourse) for m in marches]
        for f in futs:
            try:
                brut += f.result()
            except Exception as e:
                erreurs.append(str(e))
    meilleur = {}
    for marche, sym, d in brut:
        if d.get("country") not in pays:
            continue                               # sécurité : siège hors zone
        dev, cap = d.get("currency") or "", _n(d.get("market_cap_basic")) or 0
        nom = d.get("description") or d.get("name") or sym
        k = re.sub(r"[^a-z0-9]", "", nom.lower())  # même société cotée sur plusieurs places : une seule ligne (place d'origine de préférence)
        cle = (MARCHE_PAYS.get(marche) == d.get("country"), sym.startswith(("XETR:", "EURONEXT:", "LSE:")), cap * FX_EUR.get(dev, 1))
        v = {col: (d.get(col) if col in ("sector",) else _n(d.get(col))) for col in colonnes if col not in ("name", "description", "country", "currency")}
        ligne = {"n": nom, "tv": sym, "y": tv_vers_yahoo(sym, marche), "c": d.get("country"), "cap": cap, "cur": dev,
                 "ceur": cap * FX_EUR.get(dev, 1), "v": v, "_k": cle}
        if k not in meilleur or cle > meilleur[k]["_k"]:
            meilleur[k] = ligne
    lignes = sorted(meilleur.values(), key=lambda x: -x["ceur"])[:cible]
    for x in lignes:
        del x["_k"]
    if not lignes:
        raise ValueError("TradingView injoignable" + (" (" + erreurs[0] + ")" if erreurs else ""))
    vues = {k: [c for c in v if c[0] in colonnes] for k, v in VUES_SCR.items()}
    res = {"rows": lignes, "cible": cible, "erreurs": len(erreurs), "vues": vues}
    CACHE_SCR[zone] = (time.time(), res)
    return res


def verifier_listes():
    """python analyse_graphique_et_fondamentale.py --verifier-listes : signale les symboles des listes déroulantes sans données Yahoo."""
    bloc = PAGE[PAGE.index("const LISTES = {"):PAGE.index("function remplirListe")]
    paires = re.findall(r'\["([^"\]]+)","([^"]*)"\]', bloc)
    syms = list(dict.fromkeys(p[0] for p in paires))
    noms = dict(paires)
    print(f"Vérification de {len(syms)} symboles auprès de Yahoo Finance…")
    df = yf.download(syms, period="10d", interval="1d", group_by="ticker", progress=False, threads=True, auto_adjust=True)
    ko = []
    for sym in syms:
        try:
            col = df[sym]["Close"].dropna() if len(syms) > 1 else df["Close"].dropna()
            if col.empty:
                ko.append(sym)
        except Exception:
            ko.append(sym)
    if ko:
        print("Sans données (à corriger ou retirer) :")
        for sym in ko:
            print(f"  {sym:14s} {noms.get(sym, '')}")
    else:
        print("Tous les symboles répondent.")

# ---------- Mode lecture : texte d'un article d'actualité ----------
CACHE_ART = {}
_SKIP = {"script", "style", "noscript", "nav", "header", "footer", "aside", "form", "svg", "iframe", "button", "select", "template", "figure"}
_BLOCS = ("p", "h2", "h3", "li", "blockquote")
_BRUIT = re.compile(r"(cookie|abonn|subscribe|newsletter|©|tous droits|all rights|lire aussi|read more|sign in|connectez|s'inscrire|publicité|advertisement|partager|share on)", re.I)


class _Lecteur(HTMLParser):
    """Extrait titre, métadonnées et paragraphes d'une page HTML (bibliothèque standard uniquement)."""
    def __init__(self, strict=True):
        super().__init__(convert_charrefs=True)
        self.skipset = _SKIP if strict else {"script", "style", "noscript"}
        self.skip = self.art = 0
        self.buf, self.kind, self.inart = None, "p", False
        self.blocs, self.meta, self.titre, self._t = [], {}, "", False
        self.ld, self.ldtxt = None, []

    def _flush(self):
        if self.buf is not None:
            t = re.sub(r"\s+", " ", "".join(self.buf)).strip()
            if t:
                self.blocs.append((self.kind, t, self.inart))
        self.buf = None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "meta":
            k = (a.get("property") or a.get("name") or "").lower()
            if k and a.get("content") and k not in self.meta:
                self.meta[k] = a["content"].strip()
            return
        if tag == "title":
            self._t = True
            return
        if tag == "script":
            if "ld+json" in (a.get("type") or ""):
                self.ld = []
            self.skip += 1
            return
        if tag in self.skipset:
            self.skip += 1
            return
        if tag in ("article", "main"):
            self.art += 1
        if self.skip:
            return
        if tag in _BLOCS:
            self._flush()
            self.buf, self.kind, self.inart = [], ("h" if tag in ("h2", "h3") else "p"), self.art > 0
        elif tag == "br" and self.buf is not None:
            self.buf.append(" ")

    def handle_endtag(self, tag):
        if tag == "title":
            self._t = False
            return
        if tag == "script":
            if self.ld is not None:
                self.ldtxt.append("".join(self.ld))
                self.ld = None
            self.skip = max(0, self.skip - 1)
            return
        if tag in self.skipset:
            self.skip = max(0, self.skip - 1)
            return
        if tag in ("article", "main"):
            self.art = max(0, self.art - 1)
        if tag in _BLOCS and not self.skip:
            self._flush()

    def handle_data(self, d):
        if self.ld is not None:
            self.ld.append(d)
        elif self._t:
            self.titre += d
        elif not self.skip and self.buf is not None:
            self.buf.append(d)


def _corps_ld(o):
    """Cherche le champ « articleBody » dans les données structurées (JSON-LD) d'une page."""
    if isinstance(o, dict):
        v = o.get("articleBody")
        best = v if isinstance(v, str) else ""
        for x in o.values():
            if isinstance(x, (dict, list)):
                c = _corps_ld(x)
                if len(c) > len(best):
                    best = c
        return best
    if isinstance(o, list):
        return max((_corps_ld(x) for x in o), key=len, default="")
    return ""


def _texte_article(page, strict=True):
    p = _Lecteur(strict)
    try:
        p.feed(page)
        p.close()
    except Exception:
        pass
    pool = [b for b in p.blocs if b[2]] or p.blocs          # de préférence ce qui est dans <article> / <main>
    paras, vus, total = [], set(), 0
    for k, t, _ in pool:
        if k == "p" and len(t) < 45 or k == "h" and len(t) > 140:
            continue
        if _BRUIT.search(t) and len(t) < 220 or t in vus:
            continue
        vus.add(t)
        total += len(t)
        paras.append({"k": k, "t": t})
        if total > 25000:
            break
    corps = ""
    for raw in p.ldtxt:
        try:
            corps = max(corps, _corps_ld(json.loads(raw)), key=len)
        except Exception:
            continue
    if corps and len(corps) > max(total, 500):              # page à texte masqué : on prend le texte des données structurées
        paras = [{"k": "p", "t": re.sub(r"\s+", " ", t).strip()} for t in re.split(r"\n+", html_mod.unescape(corps)) if len(t.strip()) >= 20][:200]
    return paras, p.meta, re.sub(r"\s+", " ", p.titre).strip()


def _lien_public(url):
    u = urllib.parse.urlparse(url)
    if u.scheme not in ("http", "https") or not u.hostname:
        raise ValueError("lien invalide")
    for info in socket.getaddrinfo(u.hostname, u.port or 80):
        ip = ipaddress.ip_address(info[4][0].split("%")[0])
        if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved:
            raise ValueError("adresse non autorisée")


def _http(url, data=None, headers=None, timeout=12, limite=3_000_000):
    h = {"User-Agent": UA, "Accept-Language": "fr-FR,fr;q=0.9,en;q=0.8", "Accept": "text/html,application/xhtml+xml,*/*;q=0.8"}
    h.update(headers or {})
    with urllib.request.urlopen(urllib.request.Request(url, data=data, headers=h), timeout=timeout) as r:
        return r.geturl(), r.read(limite), r.headers.get("Content-Type", "")


def _decoder_page(raw, ctype):
    cs = None
    m = re.search(r"charset=([\w-]+)", ctype or "", re.I)
    if m:
        cs = m.group(1)
    else:
        m = re.search(rb"charset=[\"']?([\w-]+)", raw[:4096], re.I)
        if m:
            cs = m.group(1).decode("ascii", "ignore")
    for c in (cs, "utf-8", "latin-1"):
        if c:
            try:
                return raw.decode(c)
            except (LookupError, UnicodeDecodeError):
                continue
    return raw.decode("utf-8", "replace")


def _google_vers_source(url):
    """Les liens de Google Actualités sont des redirections codées : on retrouve l'adresse de l'article d'origine."""
    u = urllib.parse.urlparse(url)
    if u.hostname != "news.google.com":
        return url
    m = re.search(r"/articles/([^/?]+)", u.path)
    if not m:
        return url
    gid = m.group(1)
    try:                                                    # anciens liens : l'adresse est en clair dans l'identifiant
        b = base64.urlsafe_b64decode(gid + "=" * (-len(gid) % 4))
        m2 = re.search(rb"https?://[^\x00-\x20\"<>]+", b)
        if m2 and "news.google.com" not in m2.group(0).decode("ascii", "ignore"):
            return m2.group(0).decode("ascii", "ignore")
    except Exception:
        pass
    sg = ts = None
    for base in ("https://news.google.com/articles/", "https://news.google.com/rss/articles/"):
        try:
            _, raw, ct = _http(base + gid + "?hl=en-US&gl=US&ceid=US:en")
        except Exception:
            continue
        page = _decoder_page(raw, ct)
        sg, ts = re.search(r'data-n-a-sg="([^"]+)"', page), re.search(r'data-n-a-ts="([^"]+)"', page)
        if sg and ts:
            break
    if not (sg and ts):
        raise ValueError("lien Google Actualités non résolu")
    arg = ["garturlreq", [["X", "X", ["X", "X"], None, None, 1, 1, "US:en", None, 1, None, None, None, None, None, 0, 1], "X", "X", 1, [1, 1, 1], 1, 1, None, 0, 0, None, 0],
           gid, int(ts.group(1)), sg.group(1)]
    corps = urllib.parse.urlencode({"f.req": json.dumps([[["Fbv4je", json.dumps(arg), None, "generic"]]])}).encode()
    try:
        _, raw, ct = _http("https://news.google.com/_/DotsSplashUi/data/batchexecute", data=corps,
                           headers={"Content-Type": "application/x-www-form-urlencoded;charset=UTF-8"})
        rep_ = json.loads(_decoder_page(raw, ct).split("\n\n")[1])[:-2]
        return json.loads(rep_[0][2])[1]
    except Exception:
        raise ValueError("lien Google Actualités non résolu")


def article(url):
    """Texte épuré d'un article (mode lecture) : page d'origine téléchargée côté serveur, puis nettoyée."""
    url = url.strip()
    c = CACHE_ART.get(url)
    if c and time.time() - c[0] < 3600:
        return c[1]
    reel = _google_vers_source(url)
    _lien_public(reel)
    final, raw, ct = _http(reel)
    page = _decoder_page(raw, ct)
    paras, meta, titre = _texte_article(page)
    if sum(len(x["t"]) for x in paras) < 300:
        p2, m2, t2 = _texte_article(page, strict=False)
        if sum(len(x["t"]) for x in p2) > sum(len(x["t"]) for x in paras):
            paras, meta, titre = p2, m2, t2
    desc = meta.get("og:description") or meta.get("description") or ""
    if not paras and desc:
        paras = [{"k": "p", "t": desc}]
    if not paras:
        raise ValueError("aucun texte d'article exploitable (page protégée ou affichée par script)")
    img = meta.get("og:image", "")
    res = {"url": final, "title": meta.get("og:title") or titre, "site": meta.get("og:site_name") or (urllib.parse.urlparse(final).hostname or ""),
           "image": img if img.startswith("http") else "", "paras": paras, "chars": sum(len(x["t"]) for x in paras)}
    CACHE_ART[url] = (time.time(), res)
    return res


# ---------- Onglet « Analyse » : Moning (statistiques, valorisation, dividendes), Bourseur (atouts, risques, consensus) + états financiers Yahoo ----------
CACHE_ANA = {}


def _lignes_page(html):
    """Texte d'une page, une ligne par bloc (balises de bloc = retour à la ligne), pour retrouver « libellé -> valeur »."""
    h = re.sub(r"(?is)<(script|style|noscript|svg|template)\b.*?</\1>", " ", html)
    h = re.sub(r"(?i)<br\s*/?>|</?(p|div|li|ul|ol|h[1-6]|tr|td|th|table|section|article|dd|dt|label|button|header|footer|nav)\b[^>]*>", "\n", h)
    h = re.sub(r"<[^>]+>", " ", h)
    h = html_mod.unescape(h).replace("\xa0", " ")
    return [re.sub(r"\s+", " ", x).strip() for x in h.split("\n") if x.strip()]


def _apres(L, lib, debut=0, chiffre=True):
    """Valeur qui suit le libellé `lib` (ligne suivante, ou fin de la même ligne). Renvoie (valeur, index)."""
    bas = lib.lower()
    for i in range(max(0, debut), len(L)):
        t = L[i].lower()
        if t == bas:
            v = L[i + 1] if i + 1 < len(L) else ""
        elif t.startswith(bas) and len(t) > len(bas):
            v = L[i][len(lib):].strip()
        else:
            continue
        if not chiffre or re.search(r"\d", v):
            return v, i
    return "", -1


def _tableau(L, entetes, debut=0):
    """Tableau « en-têtes puis valeurs » aplati en lignes : renvoie la liste des valeurs sous les en-têtes."""
    n = len(entetes)
    for i in range(max(0, debut), len(L) - 2 * n + 1):
        if L[i:i + n] == entetes:
            return L[i + n:i + 2 * n]
    return [""] * n


def _fr(txt):
    """'182,56 Md €' -> 182.56 (nombre à la française) ; None si rien."""
    m = re.search(r"-?\d[\d\s]*(?:[.,]\d+)?", (txt or "").replace("\u2212", "-"))
    if not m:
        return None
    try:
        return float(m.group(0).replace(" ", "").replace(",", "."))
    except ValueError:
        return None


def _moning(sym):
    code = sym if "." in sym else sym.upper() + ".US"
    url = "https://moning.co/fr/actions/" + urllib.parse.quote(code)
    final, raw, ct = _http(url, timeout=20)
    page = _decoder_page(raw, ct)
    L = _lignes_page(page)
    deb = -1
    for i, x in enumerate(L):
        if x == "Rendement" and i + 1 < len(L) and re.search(r"\d", L[i + 1]) and any(y == "Capitalisation" for y in L[i:i + 16]):
            deb = i
            break
    if deb < 0:
        raise ValueError("société absente de Moning (" + code + ")")
    txt = " ".join(L[deb:])
    pb, tx, peg = _tableau(L, ["Prix / Valeur comptable", "Taux de distribution", "Ratio PEG"], deb)
    ps, pfcf, evr = _tableau(L, ["Prix / Chiffre d'affaires", "Prix / FCF", "E.V.R."], deb)
    isin = re.search(r"ISIN\s*:?\s*([A-Z]{2}[A-Z0-9]{9}\d)", " ".join(L))
    apropos = ""
    for i, x in enumerate(L):
        if x.startswith("ISIN") and i + 1 < len(L):
            apropos = next((y for y in L[i:i + 4] if len(y) > 70), "")
            break
    annees = {}
    for i, x in enumerate(L[deb:], deb):
        mm = re.match(r"Dividendes en (\d{4})$", x)
        if mm and i + 1 < len(L):
            annees[mm.group(1)] = L[i + 1]
    return {
        "url": url, "isin": isin.group(1) if isin else "", "apropos": apropos,
        "stats": {"rendement": _apres(L, "Rendement", deb)[0], "croiss_div": _apres(L, "Croissance div. / 5 ans", deb)[0],
                  "capi": _apres(L, "Capitalisation", deb)[0], "per": _apres(L, "Ratio cours/bénéfices", deb)[0],
                  "beta": _apres(L, "Beta (volatilité)", deb)[0], "bpa": _apres(L, "Bénéfice par action", deb)[0]},
        "valo": {"pb": pb, "payout": tx, "peg": peg, "ps": ps, "pfcf": pfcf, "evr": evr},
        "div": {"sans_interruption": _apres(L, "Dividende sans interruption", deb)[0], "frequence": _apres(L, "Fréquence", deb)[0],
                "montant": _apres(L, "Montant Annuel à terme", deb)[0], "ex_div": _apres(L, "Ex-dividende", deb)[0], "mois": annees},
        "perf": {"1 an": _apres(L, "Retour sur 1 an", deb)[0], "5 ans": _apres(L, "Retour sur 5 ans", deb)[0]},
    }


def _entre(L, debut, fin):
    """Lignes situées entre deux intitulés (exclus)."""
    try:
        i = L.index(debut)
    except ValueError:
        return []
    j = next((k for k in range(i + 1, len(L)) if L[k] in fin), len(L))
    return L[i + 1:j]


def _bourseur(sym):
    url = "https://bourseur.fr/cotation/" + urllib.parse.quote(sym)
    final, raw, ct = _http(url, timeout=20)
    L = _lignes_page(_decoder_page(raw, ct))
    i0 = next((i for i, x in enumerate(L) if x.startswith("Analyse Bourseur")), -1)
    if i0 < 0:
        raise ValueError("société absente de Bourseur (" + sym + ")")
    txt = " ".join(L)
    scores = {k: _apres(L, k, i0, False)[0] for k in ("Momentum", "Valorisation", "Qualité", "Sentiment")}
    achat = re.search(r"(\d+)\s*Acheter\s*(\d+)\s*Conserver\s*(\d+)\s*Vendre", txt)
    bh = re.search(r"Bas\s*([\d.,]+)\s*Haut\s*([\d.,]+)", txt)
    perfs = dict(re.findall(r"(1 mois|3 mois|6 mois|1 an)\s*([+\-\u2212]\s?\d+[.,]\d+\s?%)", txt))
    obj, io = _apres(L, "Objectif de cours moyen", i0)
    vs = re.search(r"([+\-\u2212]\d+[.,]?\d*\s?%)\s*vs cours actuel", txt)
    div_ann = re.search(r"Dividende annuel\s*([\d.,]+\s?€)", txt)
    rend = re.search(r"Rendement\s*([\d.,]+\s?%)", txt)
    payout = re.search(r"Taux de distribution\s*([\d.,]+\s?%)", txt)
    hist = []
    k = next((i for i, x in enumerate(L) if x == "Montant par action"), -1)
    if k >= 0:
        j = k + 1
        while j + 1 < len(L) and re.match(r"^\d{1,2}\S* \S+\.? \d{4}$", L[j]) and "€" in L[j + 1]:
            hist.append({"date": L[j], "montant": L[j + 1], "v": _fr(L[j + 1])})
            j += 2
    comptes = []
    k = next((i for i, x in enumerate(L) if x == "Marge nette"), -1)
    if k >= 0:
        j = k + 1
        while j + 3 < len(L) and re.match(r"^\d{4}$", L[j]):
            comptes.append({"annee": L[j], "ca": L[j + 1], "net": L[j + 2], "marge": L[j + 3]})
            j += 4
    echeances = []
    for i, x in enumerate(_entre(L, "Prochaines échéances", {"Résultats", "Ex-dividende", "Paiement dividende"})):
        pass
    ech = _entre(L, "Prochaines échéances", {"Résultats"})
    j = 0
    while j + 2 < len(ech):
        if re.match(r"^\d{1,2} \S+\.?$", ech[j]):
            echeances.append({"quand": ech[j], "quoi": ech[j + 1], "detail": ech[j + 2] if j + 2 < len(ech) else ""})
            j += 3
        else:
            j += 1
    para = lambda a, b: "\n".join(_entre(L, a, b))
    return {
        "url": url,
        "verdict": L[i0 - 1] if i0 > 0 else "", "synthese": L[i0 + 1] if i0 + 1 < len(L) else "", "scores": scores,
        "chiffres": {"capi": _apres(L, "Capitalisation", i0)[0], "per": _apres(L, "PER (12 m)", i0)[0], "ev_ebitda": _apres(L, "EV / EBITDA", i0)[0],
                     "roe": _apres(L, "ROE", i0)[0], "dette_equity": _apres(L, "Dette / Equity", i0)[0],
                     "haut52": _apres(L, "52 sem. haut", i0)[0], "bas52": _apres(L, "52 sem. bas", i0)[0]},
        "perfs": {k: v.replace(" ", "") for k, v in perfs.items()},
        "reco": _apres(L, "Recommandation moyenne", i0, False)[0], "score_consensus": _apres(L, "Score consensus", i0)[0],
        "n_analystes": (re.search(r"(\d+)\s*analystes", txt) or [None, ""])[1],
        "achat": [int(x) for x in achat.groups()] if achat else None,
        "objectif": {"moyen": obj, "v": _fr(obj), "ecart": vs.group(1).replace(" ", "") if vs else "",
                     "bas": _fr(bh.group(1)) if bh else None, "haut": _fr(bh.group(2)) if bh else None},
        "profil": para("Profil de l'entreprise", {"Fondamentaux clés", "Atouts stratégiques"}),
        "fondamentaux": para("Fondamentaux clés", {"Atouts stratégiques", "Risques à surveiller"}),
        "atouts": _entre(L, "Atouts stratégiques", {"Risques à surveiller", "Calendrier & dividende"}),
        "risques": _entre(L, "Risques à surveiller", {"Calendrier & dividende", "Historique des dividendes"}),
        "calendrier": {"rendement": rend.group(1) if rend else "", "dividende": div_ann.group(1) if div_ann else "",
                       "payout": payout.group(1) if payout else "", "echeances": echeances},
        "hist_div": hist, "comptes": comptes,
    }


def _series_yahoo(sym):
    """Séries annuelles (≈ 4-5 exercices) calculées à partir des états financiers Yahoo : CA, FCF, BPA, croissances, marges, ROE, santé financière."""
    t = yf.Ticker(sym)

    def tab(nom):
        try:
            d = getattr(t, nom)
            return d if d is not None and not d.empty else None
        except Exception:
            return None
    inc, cf, bs = tab("income_stmt"), tab("cashflow"), tab("balance_sheet")
    cols = sorted({c for d in (inc, cf, bs) if d is not None for c in d.columns})[-5:]
    if not cols:
        raise ValueError("états financiers indisponibles chez Yahoo")

    def g(d, *noms):
        out = []
        for c in cols:
            v = None
            if d is not None and c in d.columns:
                for k in noms:
                    if k in d.index:
                        v = _n(d.at[k, c])
                        if v is not None:
                            break
            out.append(v)
        return out

    def rapport(a, b, k=1.0, abs_b=False):
        r = []
        for x, y in zip(a, b):
            if x is not None and y not in (None, 0):
                y = abs(y) if abs_b else y
                r.append(round(abs(x) / y * k, 2) if abs_b == "num" else round(x / y * k, 2))
            else:
                r.append(None)
        return r

    def croiss(a):
        return [None] + [round((a[i] / a[i - 1] - 1) * 100, 1) if a[i] is not None and a[i - 1] not in (None, 0) and a[i - 1] > 0 else None
                         for i in range(1, len(a))]
    rev, net, eps = g(inc, "Total Revenue", "Operating Revenue"), g(inc, "Net Income Common Stockholders", "Net Income"), g(inc, "Diluted EPS", "Basic EPS")
    ebit, ebitda = g(inc, "Operating Income", "EBIT"), g(inc, "EBITDA", "Normalized EBITDA")
    intr, fcf = g(inc, "Interest Expense", "Interest Expense Non Operating"), g(cf, "Free Cash Flow")
    divp = [abs(x) if x is not None else None for x in g(cf, "Cash Dividends Paid", "Common Stock Dividend Paid")]
    debt, eq = g(bs, "Total Debt"), g(bs, "Stockholders Equity", "Common Stock Equity", "Total Equity Gross Minority Interest")
    sh = g(bs, "Ordinary Shares Number", "Share Issued")
    cover = [round(e / abs(i), 1) if e is not None and i not in (None, 0) else None for e, i in zip(ebit, intr)]
    res = {"years": [c.year for c in cols], "rev": rev, "net": net, "eps": eps, "fcf": fcf,
           "g_rev": croiss(rev), "g_fcf": croiss(fcf), "g_net": croiss(net), "g_eps": croiss(eps),
           "m_op": rapport(ebit, rev, 100), "m_net": rapport(net, rev, 100), "roe": rapport(net, eq, 100), "cover": cover,
           "payout": rapport(divp, net, 100), "payout_fcf": rapport(divp, fcf, 100), "de": rapport(debt, eq, 100), "debt_ebitda": rapport(debt, ebitda),
           "per": [None] * len(cols), "shares": [], "div_an": []}
    try:                                                                # PER de fin d'exercice = cours / BPA (estimation)
        h = t.history(start=(cols[0] - pd.Timedelta(days=40)).strftime("%Y-%m-%d"), interval="1mo", auto_adjust=False)["Close"].dropna()
        if getattr(h.index, "tz", None) is not None:
            h.index = h.index.tz_localize(None)
        for i, c in enumerate(cols):
            p = h[h.index <= c + pd.Timedelta(days=10)]
            if len(p) and eps[i] and eps[i] > 0:
                res["per"][i] = round(float(p.iloc[-1]) / eps[i], 1)
    except Exception:
        pass
    try:                                                                # actions en circulation : fin d'année sur 6 ans
        s = t.get_shares_full(start=(datetime.now() - timedelta(days=6 * 366)).strftime("%Y-%m-%d"))
        if s is not None and len(s) > 3:
            s = s.dropna()
            res["shares"] = [{"y": int(a), "v": float(v)} for a, v in s.groupby(s.index.year).last().items()]
    except Exception:
        pass
    if not res["shares"]:
        res["shares"] = [{"y": c.year, "v": v} for c, v in zip(cols, sh) if v]
    try:                                                                # dividende versé par exercice civil
        dv = t.dividends
        if dv is not None and len(dv):
            an = dv.groupby(dv.index.year).sum()
            res["div_an"] = [{"y": int(a), "v": round(float(v), 3), "p": int(a) == datetime.now().year} for a, v in an.items()][-11:]
    except Exception:
        pass
    return res


def analyse_approfondie(sym):
    sym = sym.strip()
    c = CACHE_ANA.get(sym)
    if c and time.time() - c[0] < 3600:
        return c[1]
    res = {"symbol": sym, "sources": {}}
    taches = {"moning": _moning, "bourseur": _bourseur, "yahoo": _series_yahoo, "info": infos}
    with ThreadPoolExecutor(4) as ex:
        futs = {k: ex.submit(f, sym) for k, f in taches.items()}
        for k, f in futs.items():
            try:
                res[k] = f.result(timeout=75)
                res["sources"][k] = "ok"
            except Exception as e:
                res[k] = None
                res["sources"][k] = str(e)[:160] or "erreur"
    info = res.pop("info") or {}
    res["name"], res["currency"], res["about_yahoo"] = info.get("name") or sym, info.get("currency") or "", info.get("about") or ""
    res["liens"] = {"moning": "https://moning.co/fr/actions/" + urllib.parse.quote(sym if "." in sym else sym.upper() + ".US"),
                    "bourseur": "https://bourseur.fr/cotation/" + urllib.parse.quote(sym)}
    ok = any(res.get(k) for k in ("moning", "bourseur", "yahoo"))
    CACHE_ANA[sym] = (time.time() - (0 if ok else 3300), res)
    return res


class Handler(BaseHTTPRequestHandler):
    def _envoyer(self, code, corps, type_="application/json; charset=utf-8"):
        self.send_response(code)
        self.send_header("Content-Type", type_)
        self.send_header("Content-Length", str(len(corps)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(corps)

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        q = {k: v[0] for k, v in urllib.parse.parse_qs(u.query).items()}
        try:
            if u.path == "/":
                self._envoyer(200, PAGE.encode("utf-8"), "text/html; charset=utf-8")
            elif u.path == "/api/search":
                self._envoyer(200, json.dumps({"results": recherche(q.get("q", "").strip()[:60])}).encode())
            elif u.path == "/api/history":
                data = historique(q.get("symbol", "").strip()[:30], q.get("days", "1095"), q.get("interval", "1d"))
                self._envoyer(200, json.dumps(data).encode())
            elif u.path == "/api/forecast":
                self._envoyer(200, json.dumps(prevision(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/docs":
                self._envoyer(200, json.dumps(documents(q.get("symbol", "").strip()[:30], q.get("name", "").strip()[:80])).encode())
            elif u.path == "/api/earnings":
                self._envoyer(200, json.dumps(calendrier_earnings(q.get("region", ""), int(q.get("week", "0")))).encode())
            elif u.path == "/api/news":
                self._envoyer(200, json.dumps(actualites(q.get("symbol", "").strip()[:30], q.get("name", "").strip()[:80])).encode())
            elif u.path == "/api/article":
                self._envoyer(200, json.dumps(article(q.get("url", "")[:2000])).encode())
            elif u.path == "/api/eps":
                self._envoyer(200, json.dumps({"eps": eps_historique(q.get("symbol", "").strip()[:30])}).encode())
            elif u.path == "/api/perf":
                syms = [s.strip() for s in q.get("symbols", "").split(",") if s.strip()][:60]
                if not syms:
                    raise ValueError("aucun symbole")
                self._envoyer(200, json.dumps({"data": performances(syms)}).encode())
            elif u.path == "/api/info":
                self._envoyer(200, json.dumps(infos(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/profil":
                self._envoyer(200, json.dumps(profil(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/resume":
                self._envoyer(200, json.dumps(resume_societe(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/screener":
                self._envoyer(200, json.dumps(screener_top(q.get("r", ""))).encode())
            elif u.path == "/api/analyse":
                self._envoyer(200, json.dumps(analyse_approfondie(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/swot":
                self._envoyer(200, json.dumps(swot(q.get("symbol", "").strip()[:30])).encode())
            elif u.path == "/api/ai":
                self._envoyer(200, json.dumps({"text": synthese_ia(q.get("symbol", "").strip()[:30])}).encode())
            elif u.path == "/api/universe":
                e = univers(q.get("c", ""))
                self._envoyer(200, json.dumps({"list": e["list"], "note": e.get("note", "")}).encode())
            else:
                self._envoyer(404, b'{"error":"not found"}')
        except Exception as e:
            self._envoyer(200, json.dumps({"error": str(e)}).encode())

    def log_message(self, *args):
        pass


PAGE = r"""<!DOCTYPE html>
<html lang="fr">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Graphique boursier · v12 screener TradingView, outils de dessin, indicateurs</title>
<style>
  :root { --ink:#1c2230; --mut:#6b7280; --line:#e5e7eb; --acc:#1d4ed8; --up:#26a69a; --dn:#ef5350; }
  * { box-sizing:border-box; }
  [hidden] { display:none !important; }
  body { margin:0; height:100vh; display:flex; flex-direction:column; font:13px/1.4 system-ui,-apple-system,"Segoe UI",sans-serif; color:var(--ink); background:#fff; }
  header { display:flex; align-items:center; gap:10px; padding:8px 14px; border-bottom:1px solid var(--line); flex-wrap:wrap; }
  .search { position:relative; width:170px; max-width:100%; }
  #q { width:100%; padding:7px 10px; border:1px solid #cbd5e1; border-radius:6px; font:inherit; text-overflow:ellipsis; background:#fff; color:inherit; }
  #q:focus { position:relative; z-index:21; width:min(340px, calc(100vw - 28px)); text-overflow:clip; }   /* le champ s'élargit en saisie, sans décaler le bandeau */
  #q:focus, select:focus, button:focus-visible, input:focus-visible { outline:2px solid var(--acc); outline-offset:1px; }
  #sug { position:absolute; top:100%; left:0; width:max-content; min-width:min(340px, calc(100vw - 28px)); max-width:min(560px, calc(100vw - 28px)); z-index:20; margin-top:4px; max-height:340px; overflow:auto; background:#fff; border:1px solid var(--line); border-radius:6px; box-shadow:0 8px 24px rgba(0,0,0,.12); }
  .it { display:grid; grid-template-columns:96px 1fr auto; gap:8px; padding:7px 10px; cursor:pointer; align-items:baseline; }
  .it.hi, .it:hover { background:#eef2ff; }
  .it span { color:var(--mut); min-width:0; white-space:normal; overflow-wrap:anywhere; }
  .it em { font-style:normal; font-size:11px; color:var(--mut); }
  .none { padding:10px; color:var(--mut); }
  .seg { display:flex; border:1px solid #cbd5e1; border-radius:6px; overflow:hidden; }
  .seg button { border:0; background:#fff; padding:6px 9px; font:inherit; cursor:pointer; border-right:1px solid var(--line); }
  .seg button:last-child { border-right:0; }
  .seg button.on { background:var(--acc); color:#fff; }
  select, .btn { padding:6px 8px; border:1px solid #cbd5e1; border-radius:6px; background:#fff; font:inherit; }
  .btn { cursor:pointer; }
  header select { max-width:140px; }
  #status { margin-left:auto; color:var(--mut); }
  #status.err { color:#b91c1c; }
  main { flex:1; display:flex; min-height:0; }
  #wrap { flex:1; position:relative; min-width:0; }
  #charts { position:absolute; inset:0; display:flex; flex-direction:column; }
  .pn { flex:1; min-height:0; position:relative; }
  .pn + .pn { border-top:2px solid #cbd5e1; }
  #charts.l1 .pn:nth-child(n+2) { display:none; }
  .pchart { position:absolute; inset:0; }
  .piv { pointer-events:auto; margin-left:8px; padding:1px 4px; font-size:12px; }
  .leg { display:flex; flex-wrap:wrap; gap:3px; margin-top:3px; max-width:560px; }
  .plg { position:absolute; left:8px; top:4px; z-index:6; pointer-events:none; }   /* nom d'un indicateur, dans son propre cadre */
  .legt { pointer-events:auto; margin-left:4px; width:20px; height:20px; padding:0; border:1px solid var(--line); border-radius:4px; background:#fff; cursor:pointer; font:inherit; line-height:1; color:var(--mut); }
  .legt:hover { color:var(--acc); }
  #charts.dk .legt { background:#1e222d; color:#d1d4dc; border-color:#363a45; }
  .chip { pointer-events:auto; display:inline-flex; align-items:center; gap:4px; padding:1px 2px 1px 6px; border:1px solid var(--line); border-radius:10px; background:#fff; font-size:11px; }
  .chip.off { opacity:.5; } .chip i { width:8px; height:8px; border-radius:50%; display:inline-block; }
  .chip button { border:0; background:none; cursor:pointer; color:var(--mut); padding:0 4px; font-size:11px; line-height:1; } .chip button:hover { color:#b91c1c; }
  #charts.v { flex-direction:row; }
  #charts.v .pn { min-width:0; }
  #charts.v .pn + .pn { border-top:0; border-left:2px solid #cbd5e1; }
  .rd { border:1px solid #cbd5e1; background:#fff; border-radius:5px; padding:2px 8px; margin-top:4px; cursor:pointer; font:inherit; color:var(--acc); }
  .rd:hover { background:#eef2ff; }
  #rdpop { position:fixed; z-index:2000; margin:0; padding:0 16px 8px; border:1px solid #cbd5e1; border-left:3px solid var(--acc); border-radius:8px; box-shadow:0 14px 40px rgba(0,0,0,.3); background:#fbfaf6; }
  #rdpop .rdbar { position:sticky; top:0; display:flex; justify-content:flex-end; gap:6px; padding:4px 0 2px; background:#fbfaf6; }
  #rdpop .rdx { border:0; background:none; cursor:pointer; font-size:15px; color:var(--mut); } #rdpop .rdx:hover { color:#b91c1c; }
  .news:hover { background:#f8fafc; }
  .rdr { margin:6px 0 4px; padding:8px 14px; background:#fbfaf6; border-left:3px solid var(--acc); border-radius:4px; max-height:65vh; overflow:auto; font:15px/1.65 Georgia,"Times New Roman",serif; color:#222; }
  .rdr h5 { margin:12px 0 4px; font:700 15px/1.4 system-ui,sans-serif; } .rdr p { margin:0 0 10px; } .rdr img { max-width:100%; border-radius:4px; margin:4px 0 8px; }
  .rdr .rdh { font:12px system-ui,sans-serif; color:var(--mut); margin-bottom:6px; } .rdr .rdh b { display:block; font:700 17px/1.3 Georgia,serif; color:#111; }
  .rdr .rdn { font:12px system-ui,sans-serif; color:#92400e; background:#fffbeb; padding:4px 8px; border-radius:4px; }

  #fbtns button { padding:6px 8px; color:var(--acc); font-weight:600; font-size:12px; }
  #fbtns button.on { color:#fff; }



  .pinfo { position:absolute; left:10px; top:6px; z-index:5; pointer-events:none; background:rgba(255,255,255,.85); padding:2px 4px; border-radius:4px; }
  .ttl { font-size:14px; } .ttl span { color:var(--mut); font-size:12px; }
  .ohlc { font-size:12px; font-variant-numeric:tabular-nums; }
  .up { color:var(--up); } .dn { color:var(--dn); }
  aside { width:300px; min-width:240px; max-width:80vw; overflow:hidden; padding:10px; display:flex; flex-direction:column; gap:8px; }
  #split { flex:0 0 7px; cursor:col-resize; border-left:1px solid var(--line); touch-action:none; }
  #split:hover, #split.drag { box-shadow:inset 2px 0 0 var(--acc); }
  body.dragging { user-select:none; cursor:col-resize; }
  aside select { width:100%; }
  .card { border:1px solid var(--line); border-radius:6px; padding:8px; }
  .card.off { opacity:.5; }
  .ch { display:flex; align-items:center; gap:4px; }
  .ch b { flex:1; }
  .ch button { border:0; background:none; cursor:pointer; font-size:14px; color:var(--mut); padding:2px 5px; }
  .ch button:hover { color:var(--ink); }
  .cp { display:flex; flex-wrap:wrap; gap:6px 10px; margin-top:6px; }
  .cp label { display:flex; flex-direction:column; font-size:11px; color:var(--mut); }
  .cp input[type=number] { width:70px; padding:3px 5px; border:1px solid #cbd5e1; border-radius:4px; font:inherit; color:var(--ink); }
  .cp input[type=color] { width:34px; height:24px; padding:0; border:1px solid #cbd5e1; border-radius:4px; background:#fff; }
  .empty { color:var(--mut); }
  #pane-earn, #pane-ana { flex:1; min-height:0; display:flex; flex-direction:column; gap:8px; overflow:auto; }
  #pane-earn .eh { display:flex; gap:10px; align-items:center; flex-wrap:wrap; } #pane-earn .eh a { color:var(--acc); text-decoration:none; margin-left:auto; }
  #ebody { padding:6px 12px 12px; } #ebody table { width:100%; border-collapse:collapse; } #ebody th, #ebody td { padding:4px 6px; border-bottom:1px solid #f1f5f9; text-align:left; }
  #ebody tr.cl { cursor:pointer; } #ebody tr.cl td:nth-child(2) b { color:var(--acc); } #ebody tr.cl:hover { background:#f8fafc; } #ebody small { color:var(--mut); }
  aside .seg button { flex:1; }
  #pane-ind { flex:1; min-height:0; overflow:auto; display:flex; flex-direction:column; gap:8px; }
  #pane-perf { flex:1; min-height:0; display:flex; flex-direction:column; gap:8px; }
  #pane-screener { flex:1; min-height:0; display:flex; flex-direction:column; gap:8px; }
  #tv-screener-container { flex:1; min-height:0; border:1px solid var(--line); border-radius:6px; overflow:hidden; }
  .pbar { display:flex; gap:6px; }
  #pstat { color:var(--mut); font-size:12px; min-height:16px; }
  #pfilter { flex:1; min-width:0; padding:6px 8px; border:1px solid #cbd5e1; border-radius:6px; font:inherit; }


  #fiche { position:absolute; right:10px; top:36px; z-index:49; width:min(430px, calc(100% - 20px)); max-height:calc(100% - 50px); overflow:auto; background:#fff; border:1px solid var(--line); border-radius:8px; box-shadow:0 10px 30px rgba(0,0,0,.18); padding:8px 10px; font-size:12px; }
  #fiche .fh { display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
  #fiche .fh b { flex:1; font-size:13px; }
  #sc-tbl tr.cl { cursor:pointer; } #sc-tbl tr.cl:hover { background:#f8fafc; } #sc-tbl a.sclk { color:var(--acc); text-decoration:none; } #sc-tbl a.sclk:hover { text-decoration:underline; } #sc-tbl small { color:var(--mut); }
  #fiche .fh a, #fiche .lk { color:var(--acc); text-decoration:none; } #fiche a:hover { text-decoration:underline; }
  #fiche .fh button { border:0; background:none; cursor:pointer; color:var(--mut); font-size:14px; }
  #fiche h4 { margin:10px 0 4px; font-size:11px; text-transform:uppercase; letter-spacing:.04em; color:var(--mut); }
  .sw { margin:8px 0; padding:6px 10px; border-left:3px solid var(--line); border-radius:3px; background:#fafafa; }
  .sw h4 { margin:0 0 4px; } .sw ul { margin:0; padding-left:18px; } .sw li { margin:2px 0; }
  .sw.f { border-color:var(--up); } .sw.w { border-color:var(--dn); } .sw.o { border-color:#2563eb; } .sw.t { border-color:#d97706; }
  .kv { display:grid; grid-template-columns:repeat(auto-fill,minmax(130px,1fr)); gap:4px 10px; }
  .kv div { display:flex; flex-direction:column; } .kv small { color:var(--mut); }
  #fiche table { border-collapse:collapse; width:100%; font-variant-numeric:tabular-nums; }
  #fiche td, #fiche th { text-align:right; padding:3px 6px; border-bottom:1px solid #f1f5f9; font-weight:normal; }
  #fiche th { color:var(--mut); } #fiche td:first-child, #fiche th:first-child { text-align:left; }
  .news { padding:4px 0; border-bottom:1px solid #f1f5f9; } .news small { color:var(--mut); display:block; }
  .ia { white-space:pre-wrap; line-height:1.5; } .ia .bu { color:#0f766e; font-weight:600; } .ia .be { color:#b91c1c; font-weight:600; }
  .ptw { flex:1; min-height:0; overflow:auto; border:1px solid var(--line); border-radius:6px; }
  #ptab { border-collapse:collapse; width:100%; font-size:12px; font-variant-numeric:tabular-nums; }
  #ptab th { position:sticky; top:0; z-index:2; background:#f8fafc; text-align:right; padding:6px 7px; border-bottom:1px solid var(--line); white-space:nowrap; font-weight:600; }
  #ptab th[data-k] { cursor:pointer; }
  #ptab td { text-align:right; padding:5px 7px; border-bottom:1px solid #f1f5f9; white-space:nowrap; }
  #ptab th:first-child, #ptab td:first-child { text-align:left; position:sticky; left:0; background:#fff; }
  #ptab th:first-child { z-index:3; background:#f8fafc; }
  #ptab td:first-child { z-index:1; }
  #ptab tbody tr { cursor:pointer; }
  #ptab tbody tr:hover td:first-child { background:#eef2ff; }
  #ptab tr.on td:first-child { box-shadow:inset 3px 0 0 var(--acc); }
  #ptab td.nm b { display:block; font-weight:600; max-width:150px; overflow:hidden; text-overflow:ellipsis; }
  #ptab td.nm small { color:var(--mut); }
  #tip { font-size:11px; color:var(--mut); }
  #fiche { width:min(860px, calc(100% - 20px)) !important; height:calc(100% - 50px); max-height:none !important; display:flex; flex-direction:column; overflow:hidden !important; }
  #fbody { flex:1; min-height:0; overflow:auto; }
  .tvbox { height:100%; min-height:460px; }
  .tvbox .tradingview-widget-container, .tvbox .tradingview-widget-container__widget { height:100%; }
  .sub { display:flex; flex-wrap:wrap; gap:4px; margin:6px 0; }
  .sub button { border:1px solid #cbd5e1; background:#fff; border-radius:5px; padding:3px 8px; cursor:pointer; font:inherit; }
  .sub button.on { background:var(--acc); color:#fff; border-color:var(--acc); }
  .gg { display:flex; gap:6px; justify-content:space-around; flex-wrap:wrap; }
  .gg figure { margin:0; text-align:center; width:30%; min-width:170px; }
  .gg figcaption { font-weight:600; }
  .gg .lab { font-weight:700; font-size:14px; }
  .gg .cnt { display:flex; justify-content:space-around; color:var(--mut); font-size:11px; }
  .gg .cnt b { display:block; font-size:14px; color:var(--ink); }
  .bar2 { position:relative; height:8px; background:#e5e7eb; border-radius:4px; margin:18px 8px 26px; }
  .bar2 i { position:absolute; top:-5px; width:2px; height:18px; background:var(--ink); }
  .bar2 em { position:absolute; top:15px; transform:translateX(-50%); font-style:normal; font-size:11px; color:var(--mut); white-space:nowrap; }
  .stk { display:flex; height:14px; border-radius:3px; overflow:hidden; min-width:160px; }
  .stk span { display:block; }
  #fiche td.hm { text-align:center; min-width:46px; }
  #fiche .scr { overflow-x:auto; }
  .hint { font-size:11px; color:var(--mut); margin-top:4px; }
  .card.flash { box-shadow:0 0 0 2px var(--acc); }
  .cp select { padding:3px 5px; font-size:12px; }
  #cm { position:fixed; z-index:1000; }
  .cmenu { background:#fff; border:1px solid var(--line); border-radius:8px; box-shadow:0 10px 30px rgba(0,0,0,.2); padding:4px; min-width:210px; font-size:13px; }
  .cmi { position:relative; display:flex; align-items:center; gap:8px; padding:6px 10px; border-radius:5px; cursor:pointer; white-space:nowrap; user-select:none; }
  .cmi:hover { background:#eef2ff; }
  .cmi.dis { color:#9ca3af; cursor:default; }
  .cmi .ar { margin-left:auto; padding-left:14px; color:var(--mut); }
  .cmi .bd { margin-left:auto; padding-left:12px; font-style:normal; font-size:11px; color:var(--acc); }
  .cmi .bd + .ar { margin-left:0; padding-left:8px; }
  .cmsep { height:1px; background:var(--line); margin:4px 2px; }
  .cmlab { padding:4px 10px 2px; font-size:11px; color:var(--mut); }
  .cmi > .cmenu { display:none; position:absolute; left:100%; top:-5px; margin-left:-2px; max-height:min(72vh,560px); overflow:auto; }
  .cmi > .cmenu.nov { overflow:visible; max-height:none; }
  .cmi:hover > .cmenu { display:block; }
  #cm.left .cmi > .cmenu { left:auto; right:100%; margin:0 -2px 0 0; }
  @media (max-width:800px) { main { flex-direction:column; } #split { display:none; } aside { width:auto !important; max-width:none; min-height:48vh; border-top:1px solid var(--line); } }
  /* ===== v11 : barre d'outils de dessin, rail de droite, thème ===== */
  #ltb { flex:0 0 auto; width:46px; display:flex; flex-direction:column; align-items:center; border-right:1px solid var(--line); background:#fff; position:relative; z-index:30; transition:width .2s ease; min-height:0; }
  #ltb.col { width:16px; } #ltb.col #dtools { display:none; }
  #ltbx { border:0; background:none; cursor:pointer; color:var(--mut); width:100%; height:24px; font-size:15px; line-height:1; flex:0 0 auto; }
  #ltbx:hover { color:var(--acc); background:#f1f5f9; }
  #dtools { display:flex; flex-direction:column; align-items:center; gap:2px; padding:4px 0 8px; flex:1; min-height:0; width:100%; overflow-y:auto; overflow-x:hidden; scrollbar-width:none; }
  .tb { position:relative; width:36px; height:34px; flex:0 0 auto; border:0; border-radius:6px; background:none; color:#4b5563; cursor:pointer; display:flex; align-items:center; justify-content:center; padding:0; }
  .tb:hover { background:#f1f5f9; } .tb.on { background:var(--acc); color:#fff; }
  .tb .arw { position:absolute; right:0; top:0; bottom:0; width:10px; display:flex; align-items:center; justify-content:center; font-size:8px; opacity:.55; border-radius:0 6px 6px 0; }
  .tb .arw:hover { opacity:1; background:rgba(0,0,0,.14); }
  .tbsep { height:1px; width:28px; background:var(--line); margin:4px 0; flex:0 0 auto; }
  #dfly { position:fixed; z-index:60; min-width:260px; padding:4px; background:#fff; border:1px solid var(--line); border-radius:8px; box-shadow:0 10px 30px rgba(0,0,0,.22); max-height:calc(100vh - 12px); overflow:auto; }
  #dfly .fl { padding:6px 10px 2px; font-size:10px; letter-spacing:.06em; color:var(--mut); font-weight:600; }
  #dfly .fi { display:flex; align-items:center; gap:10px; padding:6px 10px; border-radius:5px; cursor:pointer; white-space:nowrap; }
  #dfly .fi:hover { background:#eef2ff; } #dfly .fi.on { background:#111827; color:#fff; } #dfly .fi svg { flex:0 0 auto; }
  #dfly .ck { width:22px; text-align:center; color:var(--acc); font-weight:700; }
  #dbar { position:absolute; top:8px; left:50%; transform:translateX(-50%); z-index:40; display:flex; align-items:center; gap:6px; padding:4px 8px; background:#fff; border:1px solid var(--line); border-radius:8px; box-shadow:0 6px 20px rgba(0,0,0,.2); }
  #dbar input[type=color] { width:30px; height:24px; padding:0; border:1px solid #cbd5e1; border-radius:4px; background:#fff; }
  #dbar select { padding:2px 4px; } #dbar button { border:0; background:none; cursor:pointer; font-size:15px; padding:2px 6px; border-radius:4px; } #dbar button:hover, #dbar button.on { background:#eef2ff; }
  .dcv { position:absolute; left:0; top:0; z-index:4; pointer-events:none; }
  .pn.dm .pchart canvas, .pn.dm .pchart td { cursor:crosshair !important; }
  .pn.mv .pchart canvas { cursor:move !important; } .pn.pt .pchart canvas { cursor:pointer !important; }
  .clr input[type=color] { width:26px; height:26px; padding:0; border:1px solid #cbd5e1; border-radius:5px; background:#fff; cursor:pointer; vertical-align:middle; }
  #rtb { flex:0 0 auto; width:32px; display:flex; flex-direction:column; align-items:center; gap:8px; padding:10px 0; border-left:1px solid var(--line); background:#fff; z-index:30; }
  #rtb button { writing-mode:vertical-rl; transform:rotate(180deg); border:1px solid #cbd5e1; background:#fff; border-radius:6px; padding:12px 4px; font:inherit; font-weight:600; color:var(--acc); cursor:pointer; letter-spacing:.03em; }
  #rtb button:hover { background:#eef2ff; } #rtb button.on { background:var(--acc); color:#fff; border-color:var(--acc); }
  aside { transition:width .25s ease, padding .25s ease, min-width .25s ease; }
  aside > * { min-width:224px; }
  aside.closed { width:0 !important; min-width:0; padding:0; border:0; }
  body.dragging aside { transition:none; }
  #charts.dk .pn { background:#131722; } #charts.dk .pn + .pn { border-color:#2a2e39; }
  #charts.dk .pinfo { background:rgba(19,23,34,.82); color:#d1d4dc; } #charts.dk .ttl span, #charts.dk #tip { color:#868993; }
  #charts.dk .chip { background:#1e222d; border-color:#363a45; color:#d1d4dc; } #charts.dk .piv { background:#1e222d; color:#d1d4dc; border-color:#363a45; }

  /* ===== Onglet « Analyse » ===== */
  .ana { padding:2px 2px 24px; font-size:13px; }
  .ana h3 { margin:0; font-size:20px; } .ana .atk { color:var(--mut); font-size:12px; }
  .ana .ah { display:flex; justify-content:space-between; gap:10px; flex-wrap:wrap; align-items:flex-start; margin-bottom:8px; }
  .ana .acs { display:flex; gap:6px; flex-wrap:wrap; }
  .ana .pill { padding:3px 9px; border-radius:99px; font-size:11px; font-weight:600; background:#e2e8f0; color:#334155; }
  .ana .pill.g { background:#dcfce7; color:#166534; } .ana .pill.r { background:#fee2e2; color:#991b1b; } .ana .pill.o { background:#fef3c7; color:#92400e; }
  .ana .ac { background:#fff; border:1px solid var(--line); border-left:4px solid var(--acc); border-radius:8px; padding:10px 12px; margin:10px 0; box-shadow:0 1px 3px rgba(15,23,42,.06); }
  .ana .ac > h4 { margin:0 0 8px; font-size:12px; text-transform:uppercase; letter-spacing:.05em; color:#334155; }
  .ana .ag { display:grid; grid-template-columns:repeat(auto-fit,minmax(112px,1fr)); gap:8px; }
  .ana .at { background:#f8fafc; border-radius:6px; padding:7px 9px; display:flex; flex-direction:column; gap:2px; }
  .ana .at span { font-size:11px; color:var(--mut); } .ana .at b { font-size:16px; } .ana .at small { font-size:11px; color:var(--mut); }
  .ana .cg { display:grid; grid-template-columns:repeat(auto-fit,minmax(250px,1fr)); gap:10px; margin-top:8px; }
  .ana .ach { border:1px solid #eef2f7; border-radius:6px; padding:6px 6px 2px; } .ana .ach > b { display:block; font-size:12px; margin:0 0 2px 4px; }
  .ana .chs { width:100%; height:auto; display:block; } .ana .cv { font-size:9.5px; fill:#334155; } .ana .cl2 { font-size:9.5px; fill:#94a3b8; }
  .ana table { width:100%; border-collapse:collapse; margin-top:6px; } .ana th, .ana td { padding:4px 6px; border-bottom:1px solid #f1f5f9; text-align:left; } .ana th { color:var(--mut); font-weight:600; font-size:11px; }
  .ana .two { display:grid; grid-template-columns:repeat(auto-fit,minmax(240px,1fr)); gap:10px; }
  .ana .pro, .ana .con { border-radius:8px; padding:8px 10px 8px 12px; } .ana .pro { background:#f0fdf4; border-left:4px solid #22c55e; } .ana .con { background:#fef2f2; border-left:4px solid #ef4444; }
  .ana .pro h5, .ana .con h5 { margin:0 0 4px; font-size:12px; } .ana ul { margin:0; padding-left:18px; } .ana li { margin:3px 0; }
  .ana .bar { display:flex; height:16px; border-radius:99px; overflow:hidden; margin:6px 0; } .ana .bar i { display:block; color:#fff; font:600 10px/16px system-ui; text-align:center; font-style:normal; }
  .ana .rng { position:relative; height:8px; background:linear-gradient(90deg,#fca5a5,#fde68a,#86efac); border-radius:99px; margin:20px 6px 22px; }
  .ana .rng i { position:absolute; top:-5px; width:3px; height:18px; background:#0f172a; border-radius:2px; } .ana .rng em { position:absolute; top:14px; font:11px system-ui; font-style:normal; color:#334155; transform:translateX(-50%); white-space:nowrap; }
  .ana .aw { background:#fffbeb; color:#92400e; border-radius:6px; padding:5px 8px; font-size:12px; margin:6px 0; } .ana .lks a { color:var(--acc); margin-right:12px; }
  .ana p { margin:4px 0; line-height:1.45; } .ana .mut { color:var(--mut); font-size:12px; }
  /* ===== v12 : contrôles du screener ===== */
  .scbar { display:flex; gap:6px; }
  .scbar select { flex:1; min-width:0; }
  @media (max-width:800px) { #rtb { flex-direction:row; width:auto; border-left:0; border-top:1px solid var(--line); padding:6px; } #rtb button { writing-mode:horizontal-tb; transform:none; padding:6px 12px; } aside.closed { display:none; } }
</style>
</head>
<body>
<header>
  <div class="search">
    <input id="q" placeholder="Ticker ou nom…" autocomplete="off" spellcheck="false">
    <div id="sug" hidden></div>
  </div>
  <select id="lst-actions" aria-label="Actions par pays"></select>
  <select id="lst-indices" aria-label="Indices mondiaux"></select>
  <select id="lst-matieres" aria-label="Matières premières"></select>
  <select id="rng" aria-label="Période affichée" title="Période affichée">
    <option value="30">1 mois</option><option value="91">3 mois</option><option value="182">6 mois</option><option value="365">1 an</option><option value="730">2 ans</option>
    <option value="1095">3 ans</option><option value="1460">4 ans</option><option value="1825">5 ans</option><option value="3650">10 ans</option><option value="max">Max</option>
  </select>
  <select id="lay" aria-label="Disposition des graphiques" title="Disposition : un graphique, trois côte à côte ou trois empilés">
    <option value="1">▭ 1 graphique</option><option value="3v">▥ 3 côte à côte</option><option value="3h">☰ 3 empilés</option>
  </select>
  <div class="seg" id="fbtns" title="Informations sur la société affichée"><button data-s="finances">Finances</button><button data-s="dossiers">Dossiers</button><button data-s="actus">Actualités</button><button data-s="tech">Données techniques</button><button data-s="prev">Prévisions</button><button data-s="saison">Saisonniers</button></div>
  <button class="btn" id="reset">Réinitialiser</button>
  <span class="clr" title="Couleur des bougies : hausse (gauche) / baisse (droite)"><input type="color" id="cup"> <input type="color" id="cdn"></span>
  <button class="btn" id="theme" title="Thème clair / sombre du graphique">☾</button>
  <span id="status"></span>
</header>
<main>
  <nav id="ltb"><button id="ltbx" title="Replier la barre d’outils">‹</button><div id="dtools"></div></nav>
  <div id="dfly" hidden></div>
  <div id="wrap">
    <div id="charts" class="l1"></div>
    <div id="dbar" hidden><input type="color" id="dbc" title="Couleur"><select id="dbw" title="Épaisseur"><option>1</option><option>2</option><option>3</option><option>4</option></select><select id="dbl" title="Style"><option value="0">——</option><option value="1">– – –</option><option value="2">· · ·</option></select><button id="dbk" title="Verrouiller ce dessin">🔒</button><button id="dbd" title="Dupliquer">⧉</button><button id="dbx" title="Supprimer">🗑</button></div>
    <div id="fiche" hidden>
      <div class="fh"><b id="fnm"></b><a id="fgf" target="_blank" rel="noopener" hidden>Google Finance ↗</a><a id="fge" target="_blank" rel="noopener" hidden>Résultats ↗</a><button id="fx" title="Fermer">✕</button></div>
      <div id="fbody"></div>
    </div>
  </div>
  <div id="split" role="separator" aria-orientation="vertical" title="Glisser pour redimensionner (double-clic : taille d'origine)"></div>
  <aside>
    <section id="pane-ind">
      <select id="add" aria-label="Ajouter un indicateur"></select>
      <div id="list"></div>
    </section>
    <section id="pane-perf" hidden>
      <div class="seg" id="reg"><button data-r="us">États-Unis</button><button data-r="fr">France</button><button data-r="eu">Europe</button><button data-r="as">Asie-Pacifique</button></div>
      <div class="pbar"><select id="pcountry" aria-label="Pays"></select><input id="pfilter" placeholder="Filtrer par nom ou ticker…" autocomplete="off" spellcheck="false"><button class="btn" id="prefresh" title="Actualiser">↻</button></div>
      <div id="pstat"></div>
      <div class="ptw"><table id="ptab"></table></div>
    </section>
    <section id="pane-earn" hidden>
      <div class="eh"><b>Calendrier des résultats</b><a class="lk" href="https://fr.tradingview.com/earnings-calendar/" target="_blank" rel="noopener">TradingView ↗</a></div>
      <div class="seg" id="ewk"><button data-w="0" class="on">Semaine en cours</button><button data-w="1">Semaine prochaine</button></div>
      <div class="seg" id="ereg"><button data-r="us" class="on">États-Unis</button><button data-r="fr">France</button><button data-r="eu">Europe</button><button data-r="as">Asie-Pacifique</button></div>
      <div id="ebody"></div>
    </section>
    <section id="pane-ana" hidden><div id="ana" class="ana"></div></section>
    <section id="pane-screener" hidden>
      <div class="scbar">
        <select id="sc-country" title="Zone géographique">
          <option value="eu_top">🇪🇺 Europe : 500 premières capitalisations (siège européen)</option>
          <option value="fr_top">🇫🇷 France : 250 premières capitalisations</option>
          <option value="america" selected>🇺🇸 États-Unis</option>
          <option value="euronext">🇪🇺 Euronext : 250 premières capitalisations (sièges européens)</option>
          <option value="germany">🇩🇪 Allemagne</option>
          <option value="uk">🇬🇧 Royaume-Uni</option>
          <option value="italy">🇮🇹 Italie</option>
          <option value="spain">🇪🇸 Espagne</option>
          <option value="switzerland">🇨🇭 Suisse</option>
          <option value="sweden">🇸🇪 Suède</option>
          <option value="poland">🇵🇱 Pologne</option>
          <option value="japan">🇯🇵 Japon</option>
          <option value="hongkong">🇭🇰 Hong Kong</option>
          <option value="korea">🇰🇷 Corée du Sud</option>
          <option value="india">🇮🇳 Inde</option>
          <option value="canada">🇨🇦 Canada</option>
          <option value="australia">🇦🇺 Australie</option>
          <option value="turkey">🇹🇷 Turquie</option>
          <option value="israel">🇮🇱 Israël</option>
          <option value="luxembourg">🇱🇺 Luxembourg</option>
          <option value="egypt">🇪🇬 Égypte</option>
          <option value="vietnam">🇻🇳 Vietnam</option>
        </select>
        <select id="sc-columns" title="Colonnes affichées (données fondamentales)">
          <option value="overview">Vue générale (P/E, capitalisation…)</option>
          <option value="valuation" selected>Valorisation (P/E, P/B, P/S, EV/EBITDA…)</option>
          <option value="dividends">Dividendes (rendement, distribution…)</option>
          <option value="profitability">Rentabilité (marge, ROE, ROA…)</option>
          <option value="growth">Croissance (CA, bénéfices…)</option>
          <option value="health">Santé financière (dette, liquidité…)</option>
          <option value="performance">Performance (perf. 1J, 1M, YTD…)</option>
        </select>
      </div>
      <select id="sc-screen" title="Univers et filtre initial">
        <option value="most_capitalized">Plus grosses capitalisations</option>
        <option value="volume_leaders">Volumes les plus élevés</option>
        <option value="gainers">Plus fortes hausses du jour</option>
        <option value="losers">Plus fortes baisses du jour</option>
      </select>
      <div id="tv-screener-container"></div>
    </section>
  </aside>
  <nav id="rtb">
    <button data-t="ind" title="Afficher / masquer le panneau des indicateurs">Indicateurs</button>
    <button data-t="perf" title="Afficher / masquer le panneau des performances">Performance</button>
    <button data-t="screener" title="Afficher / masquer le screener TradingView">Screener</button>
    <button data-t="earn" title="Calendrier des résultats : semaine en cours et semaine prochaine">Earnings</button>
    <button data-t="ana" id="anab" title="Analyse approfondie de la société affichée">Analyse</button>
  </nav>
</main>

<div id="cm" hidden></div>

<script src="https://unpkg.com/lightweight-charts@5.0.0/dist/lightweight-charts.standalone.production.js"></script>
<script type="module">
  // Le web component du screener TradingView est chargé à la demande (voir loadScreener côté UI).
</script>
<script>
const $ = s => document.querySelector(s);
const { createChart, CandlestickSeries, LineSeries, HistogramSeries, CrosshairMode, LineStyle } = LightweightCharts;
const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({ '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;' }[c]));
const rgba = (h, a) => `rgba(${parseInt(h.slice(1,3),16)},${parseInt(h.slice(3,5),16)},${parseInt(h.slice(5,7),16)},${a})`;

/* ================= Calculs ================= */
const first = a => a.findIndex(v => v != null);
function sma(a, n) {
  n = Math.max(1, Math.round(n)); const o = Array(a.length).fill(null), f = first(a); if (f < 0) return o;
  let s = 0;
  for (let i = f; i < a.length; i++) { s += a[i]; if (i - f >= n) s -= a[i - n]; if (i - f >= n - 1) o[i] = s / n; }
  return o;
}
function ema(a, n, al) {
  n = Math.max(1, Math.round(n)); al = al || 2 / (n + 1);
  const o = Array(a.length).fill(null), f = first(a); if (f < 0 || a.length - f < n) return o;
  let s = 0; for (let i = f; i < f + n; i++) s += a[i];
  let p = s / n; o[f + n - 1] = p;
  for (let i = f + n; i < a.length; i++) { p = al * a[i] + (1 - al) * p; o[i] = p; }
  return o;
}
const rma = (a, n) => ema(a, n, 1 / Math.max(1, Math.round(n)));
function std(a, n) {
  n = Math.max(1, Math.round(n)); const m = sma(a, n), o = Array(a.length).fill(null);
  for (let i = n - 1; i < a.length; i++) { if (m[i] == null) continue; let s = 0; for (let j = i - n + 1; j <= i; j++) s += (a[j] - m[i]) ** 2; o[i] = Math.sqrt(s / n); }
  return o;
}
function roll(a, n, f) {
  n = Math.max(1, Math.round(n));
  return a.map((_, i) => { if (i < n - 1) return null; let r = a[i]; for (let j = i - n + 1; j < i; j++) r = f(r, a[j]); return r; });
}
const hh = (a, n) => roll(a, n, Math.max), ll = (a, n) => roll(a, n, Math.min);
const trf = X => X.H.map((h, i) => i ? Math.max(h - X.L[i], Math.abs(h - X.C[i-1]), Math.abs(X.L[i] - X.C[i-1])) : h - X.L[i]);
const pts = (X, a, col) => a.map((v, i) => v == null || !isFinite(v) ? null : { time: X.T[i], value: v, ...(col ? { color: col(i) } : {}) }).filter(Boolean);
function wma(a, n) {
  n = Math.max(1, Math.round(n)); const o = Array(a.length).fill(null), f = first(a); if (f < 0) return o; const den = n * (n + 1) / 2;
  for (let i = f + n - 1; i < a.length; i++) { let s = 0, ok = true; for (let j = 0; j < n; j++) { const v = a[i - n + 1 + j]; if (v == null) { ok = false; break; } s += v * (j + 1); } if (ok) o[i] = s / den; }
  return o;
}
const ptsG = (X, a, m) => X.T.map((t, i) => a[i] != null && m(i) ? { time:t, value:a[i] } : { time:t });   // trous = ligne interrompue
const S = (t, c, d, o = {}) => ({ t, c, d, ...o });          // description d'une série

function sarCalc(X, s0, st, mx) {
  const H = X.H, L = X.L, n = H.length, sar = Array(n).fill(null), up = Array(n).fill(true);
  if (n < 2) return { sar, up };
  up[0] = H[1] > H[0]; let ep = up[0] ? H[0] : L[0]; sar[0] = up[0] ? L[0] : H[0]; let af = s0;
  for (let i = 1; i < n; i++) {
    sar[i] = sar[i-1] + af * (ep - sar[i-1]);
    const l2 = i > 1 ? L[i-2] : L[i-1], h2 = i > 1 ? H[i-2] : H[i-1];
    if (up[i-1]) {
      sar[i] = Math.min(sar[i], L[i-1], l2);
      if (L[i] < sar[i]) { up[i] = false; sar[i] = ep; ep = L[i]; af = s0; }
      else { up[i] = true; if (H[i] > ep) { ep = H[i]; af = Math.min(af + st, mx); } }
    } else {
      sar[i] = Math.max(sar[i], H[i-1], h2);
      if (H[i] > sar[i]) { up[i] = true; sar[i] = ep; ep = H[i]; af = s0; }
      else { up[i] = false; if (L[i] < ep) { ep = L[i]; af = Math.min(af + st, mx); } }
    }
  }
  return { sar, up };
}

/* ---- Outils pour les indicateurs supplémentaires ---- */
const zip2 = (a, b, f) => a.map((v, i) => v == null || b[i] == null ? null : f(v, b[i], i));
const hl2 = X => X.H.map((h, i) => (h + X.L[i]) / 2);
const rollS = (a, n, f) => { n = Math.max(1, Math.round(n)); return a.map((_, i) => { if (i < n - 1 || a[i] == null) return null; let r = a[i]; for (let j = i - n + 1; j < i; j++) { if (a[j] == null) return null; r = f(r, a[j]); } return r; }); };
const hhS = (a, n) => rollS(a, n, Math.max), llS = (a, n) => rollS(a, n, Math.min);
const sumN = (a, n) => { n = Math.max(1, Math.round(n)); return a.map((_, i) => { if (i < n - 1) return null; let s = 0; for (let j = i - n + 1; j <= i; j++) { if (a[j] == null) return null; s += a[j]; } return s; }); };
const dema = (a, n) => { const e = ema(a, n), e2 = ema(e, n); return zip2(e, e2, (x, y) => 2 * x - y); };
const tema = (a, n) => { const e = ema(a, n), e2 = ema(e, n), e3 = ema(e2, n); return e.map((v, i) => v == null || e2[i] == null || e3[i] == null ? null : 3 * v - 3 * e2[i] + e3[i]); };
const vwma = (X, n) => { const pv = sumN(X.C.map((c, i) => c * X.V[i]), n), v = sumN(X.V, n); return pv.map((s, i) => s == null || !v[i] ? null : s / v[i]); };
const rocA = (a, n) => a.map((v, i) => i >= n && a[i - n] ? 100 * (v - a[i - n]) / a[i - n] : null);
const clvA = X => X.C.map((c, i) => X.H[i] === X.L[i] ? 0 : ((c - X.L[i]) - (X.H[i] - c)) / (X.H[i] - X.L[i]));
const adlA = X => { let s = 0; const c = clvA(X); return X.V.map((v, i) => (s += c[i] * v)); };
const rsiA = (C, n) => { const g = C.map((v, i) => i ? Math.max(v - C[i-1], 0) : null), l = C.map((v, i) => i ? Math.max(C[i-1] - v, 0) : null), ag = rma(g, n), al = rma(l, n);
  return ag.map((v, i) => v == null || al[i] == null ? null : al[i] === 0 ? 100 : 100 - 100 / (1 + v / al[i])); };
const cciA = (X, n) => { n = Math.round(n); const tp = X.C.map((v, i) => (X.H[i] + X.L[i] + v) / 3), m = sma(tp, n);
  return m.map((mm, i) => { if (mm == null) return null; let s = 0; for (let j = i - n + 1; j <= i; j++) s += Math.abs(tp[j] - mm); const md = s / n; return md ? (tp[i] - mm) / (0.015 * md) : null; }); };
const macdA = (C, a, b, s) => { const m = zip2(ema(C, a), ema(C, b), (x, y) => x - y), sg = ema(m, s); return { m, sg, h: zip2(m, sg, (x, y) => x - y) }; };
const stochRaw = (X, n) => { const h = hh(X.H, n), l = ll(X.L, n); return X.C.map((v, i) => h[i] == null || h[i] === l[i] ? null : 100 * (v - l[i]) / (h[i] - l[i])); };
function kama(a, n, f, s) {
  const o = Array(a.length).fill(null), fa = 2 / (f + 1), sa = 2 / (s + 1); n = Math.round(n); if (a.length < n) return o;
  o[n - 1] = a[n - 1];
  for (let i = n; i < a.length; i++) { let vol = 0; for (let j = i - n + 1; j <= i; j++) vol += Math.abs(a[j] - a[j-1]); const er = vol ? Math.abs(a[i] - a[i-n]) / vol : 0, sc = (er * (fa - sa) + sa) ** 2; o[i] = o[i-1] + sc * (a[i] - o[i-1]); }
  return o;
}
function linreg(a, n) {
  n = Math.max(2, Math.round(n)); const L = a.length, v = Array(L).fill(null), sd = Array(L).fill(null), sl = Array(L).fill(null);
  const sx = n * (n - 1) / 2, sxx = (n - 1) * n * (2 * n - 1) / 6, den = n * sxx - sx * sx;
  for (let i = n - 1; i < L; i++) {
    let sy = 0, sxy = 0; for (let j = 0; j < n; j++) { const y = a[i - n + 1 + j]; sy += y; sxy += j * y; }
    const b = (n * sxy - sx * sy) / den, c = (sy - b * sx) / n; v[i] = c + b * (n - 1); sl[i] = b;
    let ss = 0; for (let j = 0; j < n; j++) { const e = a[i - n + 1 + j] - (c + b * j); ss += e * e; } sd[i] = Math.sqrt(ss / n);
  }
  return { v, sl, sd };
}
const dynZone = (a, lb, q) => a.map((_, i) => { if (i < lb - 1) return null; const w = []; for (let j = i - lb + 1; j <= i; j++) { if (a[j] == null) return null; w.push(a[j]); }
  w.sort((x, y) => x - y); const k = q / 100 * (w.length - 1), f = Math.floor(k); return w[f] + (w[Math.min(f + 1, w.length - 1)] - w[f]) * (k - f); });
function pivA(a, r, hi) {                                          // pivots confirmés par r barres de chaque côté
  const o = [];
  for (let i = r; i < a.length - r; i++) { if (a[i] == null) continue; let ok = true;
    for (let j = 1; j <= r && ok; j++) { const u = a[i-j], w = a[i+j]; if (u == null || w == null || (hi ? (a[i] <= u || a[i] < w) : (a[i] >= u || a[i] > w))) ok = false; }
    if (ok) o.push(i); }
  return o;
}
function divSeries(X, osc, r) {                                    // divergences classiques entre l'oscillateur et le cours
  const out = [], lo = pivA(osc, r, false), hi = pivA(osc, r, true);
  for (let k = 1; k < lo.length; k++) { const a = lo[k-1], b = lo[k]; if (b - a <= 60 && osc[b] > osc[a] && X.L[b] < X.L[a]) out.push([a, b, 1]); }
  for (let k = 1; k < hi.length; k++) { const a = hi[k-1], b = hi[k]; if (b - a <= 60 && osc[b] < osc[a] && X.H[b] > X.H[a]) out.push([a, b, 2]); }
  out.sort((u, v) => u[1] - v[1]);
  return out.slice(-30).map(([a, b, c]) => S('line', c, [{ time:X.T[a], value:osc[a] }, { time:X.T[b], value:osc[b] }]));
}
function pivLv(h, l, c, o, kind) {
  const r = h - l, p = (h + l + c) / 3;
  if (kind === 'fib') return [[0,p],[1,p+.382*r],[1,p+.618*r],[1,p+r],[2,p-.382*r],[2,p-.618*r],[2,p-r]];
  if (kind === 'cam') { const k = [1.1/12, 1.1/6, 1.1/4, 1.1/2]; return [[0,p], ...k.map(x => [1, c + x * r]), ...k.map(x => [2, c - x * r])]; }
  if (kind === 'woo') { const w = (h + l + 2 * c) / 4; return [[0,w],[1,2*w-l],[1,w+r],[1,h+2*(w-l)],[2,2*w-h],[2,w-r],[2,l-2*(h-w)]]; }
  if (kind === 'dem') { const x = c < o ? h + 2 * l + c : c > o ? 2 * h + l + c : h + l + 2 * c; return [[0,x/4],[1,x/2-l],[2,x/2-h]]; }
  return [[0,p],[1,2*p-l],[1,p+r],[1,h+2*(p-l)],[2,2*p-h],[2,p-r],[2,l-2*(h-p)]];
}
function pivSeries(X, n, kind) {                                   // niveaux calculés sur le bloc précédent de n barres
  n = Math.max(2, Math.round(n)); const N = X.C.length, arrs = [];
  for (let b = 1; b * n < N; b++) {
    let h = -Infinity, l = Infinity; const s = (b - 1) * n, e = b * n - 1;
    for (let i = s; i <= e; i++) { h = Math.max(h, X.H[i]); l = Math.min(l, X.L[i]); }
    pivLv(h, l, X.C[e], X.O[s], kind).forEach(([c, v], k) => {
      const a = arrs[k] || (arrs[k] = { c, d:[] }); a.d.push({ time:X.T[b * n] });
      for (let i = b * n + 1; i < Math.min(N, (b + 1) * n); i++) a.d.push({ time:X.T[i], value:v });
    });
  }
  return arrs.map(a => S('line', a.c, a.d));
}
function zigzag(X, dv) {
  const H = X.H, L = X.L, n = H.length, piv = []; let dir = 0, hi = 0, lo = 0; dv /= 100;
  for (let i = 1; i < n; i++) {
    if (dir >= 0 && H[i] > H[hi]) hi = i; if (dir <= 0 && L[i] < L[lo]) lo = i;
    if (dir === 0) { if (H[i] >= L[lo] * (1 + dv)) { piv.push([lo, L[lo]]); dir = 1; hi = i; } else if (L[i] <= H[hi] * (1 - dv)) { piv.push([hi, H[hi]]); dir = -1; lo = i; } }
    else if (dir === 1) { if (L[i] <= H[hi] * (1 - dv)) { piv.push([hi, H[hi]]); dir = -1; lo = i; } }
    else if (H[i] >= L[lo] * (1 + dv)) { piv.push([lo, L[lo]]); dir = 1; hi = i; }
  }
  if (dir === 1) piv.push([hi, H[hi]]); else if (dir === -1) piv.push([lo, L[lo]]);
  return piv.filter((q, k) => !k || q[0] > piv[k-1][0]);
}
const CMPD = {}, CMPW = {};
async function loadCmp(sym, iv, key) {
  if (CMPW[key]) return; CMPW[key] = 1;
  try { const j = await (await fetch(`/api/history?symbol=${encodeURIComponent(sym)}&days=${ST.days}&interval=${iv}`)).json(); if (j.error) throw new Error(j.error);
    const m = new Map(); j.bars.forEach(r => m.set(r[0], r[4])); CMPD[key] = m; }
  catch (e) { CMPD[key] = new Map(); status(`Valeur comparée « ${sym} » : ${e.message}`, true); }
  build(true);
}

/* ================= Catalogue d'indicateurs =================
   ov:1 = sur le graphique ; sinon panneau séparé.
   p = [clé, libellé, défaut, pas]   c = [libellé, couleur par défaut] */
const IND = {
  sma: { n:'Moyenne mobile simple (SMA)', ov:1, p:[['n','Période',20]], c:[['Ligne','#2962ff']],
    f:(p,X) => [S('line',0,pts(X,sma(X.C,p.n)))] },
  ema: { n:'Moyenne mobile exponentielle (EMA)', ov:1, p:[['n','Période',20]], c:[['Ligne','#00897b']],
    f:(p,X) => [S('line',0,pts(X,ema(X.C,p.n)))] },
  bb: { n:'Bandes de Bollinger', ov:1, p:[['n','Période',20],['k','Écarts-types',2,0.1]], c:[['Bandes','#78909c'],['Médiane','#b0bec5']],
    f:(p,X) => { const m = sma(X.C,p.n), s = std(X.C,p.n);
      return [S('line',0,pts(X,m.map((v,i)=>v==null?null:v+p.k*s[i])),{st:'dash'}), S('line',1,pts(X,m),{st:'dot'}), S('line',0,pts(X,m.map((v,i)=>v==null?null:v-p.k*s[i])),{st:'dash'})]; } },
  sar: { n:'SAR parabolique', ov:1, p:[['s0','Pas initial',0.02,0.01],['st','Incrément',0.02,0.01],['mx','Maximum',0.2,0.05]], c:[['Haussier','#26a69a'],['Baissier','#ef5350']],
    f:(p,X,K) => { const r = sarCalc(X,p.s0,p.st,p.mx); return [S('dots',0,pts(X,r.sar,i=>r.up[i]?K[0]:K[1]))]; } },
  ichi: {
    n:'Ichimoku',
    ov:1,
    p:[['a','Tenkan',9],['b','Kijun',26],['c','Senkou B',52],['d','Décalage',26]],
    c:[['Tenkou','#2962ff'],['Kijun','#e53935'],['Senkou A','#43a047'],['Senkou B','#ff9800'],['Chikou','#8e24aa']],
    f:(p,X,K) => {
      const mid = n => { const h = hh(X.H,n), l = ll(X.L,n); return h.map((v,i)=>v==null?null:(v+l[i])/2); };
      const t = mid(p.a), k = mid(p.b), sb = mid(p.c), d = Math.round(p.d), E = X.T.concat(X.fut(d));
      const sa = t.map((v,i)=>v==null||k[i]==null?null:(v+k[i])/2);
      const sh = a => a.map((v,i)=>v==null?null:{time:E[i+d],value:v}).filter(Boolean);
      return [
        S('line',0,pts(X,t)),
        S('line',1,pts(X,k)),
        S('line',2,sh(sa)),
        S('line',3,sh(sb)),
        S('line',4,X.C.map((v,i)=>i<d?null:{time:X.T[i-d],value:v}).filter(Boolean))
      ];
    }
  },
  vol: { n:'Volume', p:[['n','Moyenne du volume',20]], c:[['Hausse','#26a69a'],['Baisse','#ef5350'],['Moyenne','#ff9800']],
    f:(p,X,K) => [S('hist',0,pts(X,X.V,i=>rgba(X.C[i]>=X.O[i]?K[0]:K[1],.6)),{pf:'volume'}), S('line',2,pts(X,sma(X.V,p.n)))] },
  rsi: { n:'RSI', p:[['n','Période',14],['hi','Surachat',70],['lo','Survente',30]], c:[['RSI','#7e57c2']],
    f:(p,X) => { const g = X.C.map((v,i)=>i?Math.max(v-X.C[i-1],0):null), l = X.C.map((v,i)=>i?Math.max(X.C[i-1]-v,0):null);
      const ag = rma(g,p.n), al = rma(l,p.n);
      return [S('line',0,pts(X,ag.map((v,i)=>v==null?null:al[i]===0?100:100-100/(1+v/al[i]))),{lv:[p.hi,p.lo]})]; } },
  macd: { n:'MACD', p:[['a','Rapide',12],['b','Lente',26],['s','Signal',9]], c:[['MACD','#2962ff'],['Signal','#ff6d00'],['Hausse','#26a69a'],['Baisse','#ef5350']],
    f:(p,X,K) => { const fa = ema(X.C,p.a), sl = ema(X.C,p.b), m = fa.map((v,i)=>v==null||sl[i]==null?null:v-sl[i]), sg = ema(m,p.s);
      const h = m.map((v,i)=>v==null||sg[i]==null?null:v-sg[i]);
      return [S('hist',2,pts(X,h,i=>rgba(h[i]>=0?K[2]:K[3],.7))), S('line',0,pts(X,m)), S('line',1,pts(X,sg))]; } },
  sto: { n:'Stochastique', p:[['n','Période %K',14],['k','Lissage %K',3],['d','Lissage %D',3],['hi','Haut',80],['lo','Bas',20]], c:[['%K','#2962ff'],['%D','#ff6d00']],
    f:(p,X) => { const h = hh(X.H,p.n), l = ll(X.L,p.n);
      const raw = X.C.map((v,i)=>h[i]==null||h[i]===l[i]?null:100*(v-l[i])/(h[i]-l[i])), k = sma(raw,p.k), d = sma(k,p.d);
      return [S('line',0,pts(X,k),{lv:[p.hi,p.lo]}), S('line',1,pts(X,d))]; } },
  atr: { n:'Average True Range (ATR, Wilder)', p:[['n','Période',14]], c:[['ATR','#795548']],
    f:(p,X) => [S('line',0,pts(X,rma(trf(X),p.n)))] },
  adx: { n:'ADX / DMI', p:[['n','Période',14],['lv','Seuil',25]], c:[['ADX','#e53935'],['+DI','#26a69a'],['−DI','#2962ff']],
    f:(p,X) => { const up = [null], dn = [null];
      for (let i = 1; i < X.H.length; i++) { const u = X.H[i]-X.H[i-1], d = X.L[i-1]-X.L[i]; up.push(u>d&&u>0?u:0); dn.push(d>u&&d>0?d:0); }
      const tr = rma(trf(X).map((v,i)=>i?v:null),p.n);
      const P = rma(up,p.n).map((v,i)=>v==null||!tr[i]?null:100*v/tr[i]), M = rma(dn,p.n).map((v,i)=>v==null||!tr[i]?null:100*v/tr[i]);
      const dx = P.map((v,i)=>v==null||M[i]==null||v+M[i]===0?null:100*Math.abs(v-M[i])/(v+M[i]));
      return [S('line',0,pts(X,rma(dx,p.n)),{lv:[p.lv]}), S('line',1,pts(X,P)), S('line',2,pts(X,M))]; } },
  cci: { n:'CCI', p:[['n','Période',20]], c:[['CCI','#009688']],
    f:(p,X) => { const n = Math.round(p.n), tp = X.C.map((v,i)=>(X.H[i]+X.L[i]+v)/3), m = sma(tp,n);
      const o = m.map((mm,i)=>{ if (mm==null) return null; let s = 0; for (let j=i-n+1;j<=i;j++) s += Math.abs(tp[j]-mm); const md = s/n; return md ? (tp[i]-mm)/(0.015*md) : null; });
      return [S('line',0,pts(X,o),{lv:[100,-100]})]; } },
  obv: { n:'OBV (volume cumulé)', p:[], c:[['OBV','#5c6bc0']],
    f:(p,X) => { let s = 0; return [S('line',0,pts(X,X.C.map((v,i)=>{ if (i) s += v>X.C[i-1]?X.V[i]:v<X.C[i-1]?-X.V[i]:0; return s; })))]; } },
  wr: { n:'Williams %R', p:[['n','Période',14]], c:[['%R','#ab47bc']],
    f:(p,X) => { const h = hh(X.H,p.n), l = ll(X.L,p.n);
      return [S('line',0,pts(X,X.C.map((v,i)=>h[i]==null||h[i]===l[i]?null:-100*(h[i]-v)/(h[i]-l[i]))),{lv:[-20,-80]})]; } },
  atr2: { n:'Average true range (lissage au choix)', p:[['n','Période',14],['m','Lissage 1-4',2,1,1,4],['pct','En % (0/1)',0,1,0,1]], c:[['ATR','#e65100']],
    h:'Lissage : 1 = Wilder (RMA), 2 = moyenne simple, 3 = exponentielle, 4 = pondérée. En % : ATR rapporté au cours.',
    f:(p,X) => { const t = trf(X), a = p.m === 1 ? rma(t,p.n) : p.m === 3 ? ema(t,p.n) : p.m === 4 ? wma(t,p.n) : sma(t,p.n);
      return [S('line',0,pts(X,p.pct ? a.map((v,i)=>v==null?null:100*v/X.C[i]) : a))]; } },
  cvi: { n:'Cumulative volume index', p:[['n','Signal (EMA)',21]], c:[['CVI','#00838f'],['Signal','#ff6d00']],
    h:'Volume cumulé signé par la bougie (hausse = +, baisse = −), avec ligne de signal. Version pour un titre isolé.',
    f:(p,X) => { let s = 0; const v = X.C.map((c,i)=>{ s += c > X.O[i] ? X.V[i] : c < X.O[i] ? -X.V[i] : 0; return s; });
      return [S('line',0,pts(X,v)), S('line',1,pts(X,ema(v,p.n)))]; } },
  stpmt: { n:'Medium Term Weighted Stochastic (STPMT)', p:[['a','Période courte',13],['b','Période moyenne',21],['c','Période longue',34],['w','Lissage (WMA)',3],['hi','Haut',80],['lo','Bas',20]], c:[['STPMT','#1565c0'],['Signal','#ef6c00']],
    h:'Reconstitution : moyenne pondérée (1-2-3) de trois stochastiques, lissée, avec signal. Le script d’origine n’étant pas connu, vérifiez la ressemblance.',
    f:(p,X) => { const k = n => { const h = hh(X.H,n), l = ll(X.L,n); return X.C.map((v,i)=>h[i]==null||h[i]===l[i]?null:100*(v-l[i])/(h[i]-l[i])); };
      const A = k(p.a), B = k(p.b), C = k(p.c), m = A.map((v,i)=>v==null||B[i]==null||C[i]==null?null:(v+2*B[i]+3*C[i])/6), line = wma(m,p.w);
      return [S('line',0,pts(X,line),{lv:[p.hi,p.lo]}), S('line',1,pts(X,sma(line,3)))]; } },
  rsio: { n:'RSI optimisé (lissé)', p:[['s','Lissage du cours (EMA)',3],['n','Période',14],['sg','Signal (EMA)',5],['hi','Surachat',70],['lo','Survente',30]], c:[['RSI','#6a1b9a'],['Signal','#fb8c00']],
    h:'Reconstitution : RSI calculé sur un cours lissé, avec ligne de signal (moins de faux signaux que le RSI classique).',
    f:(p,X) => { const c = ema(X.C,p.s);
      const g = c.map((v,i)=>(i && v != null && c[i-1] != null) ? Math.max(v-c[i-1],0) : null), l = c.map((v,i)=>(i && v != null && c[i-1] != null) ? Math.max(c[i-1]-v,0) : null);
      const ag = rma(g,p.n), al = rma(l,p.n), r = ag.map((v,i)=>v==null||al[i]==null?null:al[i]===0?100:100-100/(1+v/al[i]));
      return [S('line',0,pts(X,r),{lv:[p.hi,p.lo]}), S('line',1,pts(X,ema(r,p.sg)))]; } },
  st: { n:'Supertrend', ov:1, p:[['n','Période ATR',10],['m','Multiplicateur',3,0.5]], c:[['Haussier','#26a69a'],['Baissier','#ef5350']],
    f:(p,X) => { const n = X.C.length, a = rma(trf(X),p.n), fu = Array(n).fill(null), fl = Array(n).fill(null), up = Array(n).fill(true), v = Array(n).fill(null);
      for (let i = 0; i < n; i++) { if (a[i] == null) continue;
        const m = (X.H[i]+X.L[i])/2, u = m + p.m*a[i], l = m - p.m*a[i];
        if (i === 0 || fu[i-1] == null) { fu[i] = u; fl[i] = l; up[i] = X.C[i] >= m; }
        else { fu[i] = (u < fu[i-1] || X.C[i-1] > fu[i-1]) ? u : fu[i-1]; fl[i] = (l > fl[i-1] || X.C[i-1] < fl[i-1]) ? l : fl[i-1];
          up[i] = up[i-1] ? X.C[i] >= fl[i] : X.C[i] > fu[i]; }
        v[i] = up[i] ? fl[i] : fu[i]; }
      return [S('line',0,ptsG(X,v,i=>up[i])), S('line',1,ptsG(X,v,i=>!up[i]))]; } },
  pe: { n:'Ratio cours/bénéfices (P/E)', p:[['cap','Plafond affiché',200,10,10]], c:[['P/E','#8d6e63']],
    h:'Cours ÷ bénéfice par action des 4 derniers trimestres publiés (actions uniquement ; masqué si le bénéfice est négatif).',
    f:(p,X) => { const E = X.eps || []; if (E.length < 4) return []; let j = -1;
      return [S('line',0,pts(X,X.T.map((t,i)=>{ while (j + 1 < E.length && E[j+1][0] <= t) j++;
        if (j < 3) return null; const ttm = E[j][1]+E[j-1][1]+E[j-2][1]+E[j-3][1]; const r = ttm > 0 ? X.C[i]/ttm : null; return r != null && r <= p.cap ? r : null; })))]; } },
  /* ---------- Indicateurs ajoutés (liste TradingView) ---------- */
  hl: { n:'+ Hauts et + Bas', ov:1, p:[['n','Période',20]], c:[['Plus haut','#26a69a'],['Plus bas','#ef5350']],
    f:(p,X) => [S('line',0,pts(X,hh(X.H,p.n))), S('line',1,pts(X,ll(X.L,p.n)))] },
  accd: { n:'Accumulation / Distribution', p:[], c:[['A/D','#3949ab']], f:(p,X) => [S('line',0,pts(X,adlA(X)))] },
  aroon: { n:'Aroon', p:[['n','Période',14]], c:[['Aroon haut','#26a69a'],['Aroon bas','#ef5350']],
    f:(p,X) => { const n = Math.round(p.n), f = (A, hi) => A.map((_, i) => { if (i < n) return null; let m = hi ? -Infinity : Infinity, k = i;
        for (let j = i - n; j <= i; j++) if (hi ? A[j] >= m : A[j] <= m) { m = A[j]; k = j; } return 100 * (n - (i - k)) / n; });
      return [S('line',0,pts(X,f(X.H,true)),{lv:[70,30]}), S('line',1,pts(X,f(X.L,false)))]; } },
  ao: { n:'Awesome Oscillator (AO)', p:[['a','Courte',5],['b','Longue',34]], c:[['Hausse','#26a69a'],['Baisse','#ef5350']],
    f:(p,X,K) => { const m = hl2(X), o = zip2(sma(m,p.a), sma(m,p.b), (x,y)=>x-y); return [S('hist',0,pts(X,o,i=>o[i] >= (o[i-1] ?? o[i]) ? K[0] : K[1]))]; } },
  kelt: { n:'Bandes de Keltner', ov:1, p:[['n','Période EMA',20],['m','Multiplicateur',2,0.1],['a','Période ATR',10]], c:[['Bandes','#2962ff'],['Médiane','#90a4ae']],
    f:(p,X) => { const e = ema(X.C,p.n), a = rma(trf(X),p.a);
      return [S('line',0,pts(X,zip2(e,a,(x,y)=>x+p.m*y))), S('line',1,pts(X,e),{st:'dot'}), S('line',0,pts(X,zip2(e,a,(x,y)=>x-p.m*y)))]; } },
  bbb: { n:'Bollinger %b', p:[['n','Période',20],['k','Écarts-types',2,0.1]], c:[['%b','#7e57c2']],
    f:(p,X) => { const m = sma(X.C,p.n), s = std(X.C,p.n); return [S('line',0,pts(X,X.C.map((v,i)=>m[i]==null||!s[i]?null:(v-(m[i]-p.k*s[i]))/(2*p.k*s[i]))),{lv:[1,0]})]; } },
  donch: { n:'Canal de Donchian', ov:1, p:[['n','Période',20]], c:[['Canal','#2962ff'],['Médiane','#ff6d00']],
    f:(p,X) => { const h = hh(X.H,p.n), l = ll(X.L,p.n); return [S('line',0,pts(X,h)), S('line',1,pts(X,zip2(h,l,(x,y)=>(x+y)/2)),{st:'dot'}), S('line',0,pts(X,l))]; } },
  cmf: { n:'Chaikin Money Flow (CMF)', p:[['n','Période',20]], c:[['CMF','#00897b']],
    f:(p,X) => { const a = sumN(clvA(X).map((c,i)=>c*X.V[i]),p.n), v = sumN(X.V,p.n); return [S('line',0,pts(X,a.map((s,i)=>s==null||!v[i]?null:s/v[i])),{lv:[0]})]; } },
  cho: { n:'Chaikin Oscillateur', p:[['a','Courte',3],['b','Longue',10]], c:[['Chaikin','#5e35b1']],
    f:(p,X) => { const d = adlA(X); return [S('line',0,pts(X,zip2(ema(d,p.a),ema(d,p.b),(x,y)=>x-y)),{lv:[0]})]; } },
  chv: { n:'Chaikin volatilité', p:[['n','Lissage',10],['r','Variation sur',10]], c:[['Volatilité','#c62828']],
    f:(p,X) => { const e = ema(X.H.map((h,i)=>h-X.L[i]),p.n), r = Math.round(p.r); return [S('line',0,pts(X,e.map((v,i)=>i<r||v==null||!e[i-r]?null:100*(v-e[i-r])/e[i-r])),{lv:[0]})]; } },
  cks: { n:'Chande Kroll Stop', ov:1, p:[['p','Période ATR',10],['x','Multiplicateur',1,0.5],['q','Période du stop',9]], c:[['Stop vendeur','#ef5350'],['Stop acheteur','#26a69a']],
    f:(p,X) => { const a = rma(trf(X),p.p), h = hh(X.H,p.p), l = ll(X.L,p.p), fh = zip2(h,a,(x,y)=>x-p.x*y), fl = zip2(l,a,(x,y)=>x+p.x*y);
      return [S('line',0,pts(X,hhS(fh,p.q))), S('line',1,pts(X,llS(fl,p.q)))]; } },
  cop: { n:'Courbe de Coppock', p:[['a','ROC long',14],['b','ROC court',11],['w','WMA',10]], c:[['Coppock','#6d4c41']],
    f:(p,X) => [S('line',0,pts(X,wma(zip2(rocA(X.C,p.a),rocA(X.C,p.b),(x,y)=>x+y),p.w)),{lv:[0]})] },
  dpo: { n:'Detrended Price Oscillator (DPO)', p:[['n','Période',21]], c:[['DPO','#00838f']],
    f:(p,X) => { const n = Math.round(p.n), k = Math.floor(n/2) + 1, m = sma(X.C,n); return [S('line',0,pts(X,m.map((v,i)=>v==null||i<k?null:X.C[i-k]-v)),{lv:[0]})]; } },
  divrsi: { n:'Divergences RSI', p:[['n','Période RSI',14],['r','Pivot (barres)',5]], c:[['RSI','#7e57c2'],['Haussière','#26a69a'],['Baissière','#ef5350']],
    h:'Traits verts : divergence haussière (cours plus bas, RSI plus haut). Traits rouges : divergence baissière.',
    f:(p,X) => { const r = rsiA(X.C,p.n); return [S('line',0,pts(X,r),{lv:[70,30]}), ...divSeries(X,r,Math.round(p.r))]; } },
  divmacd: { n:'Divergences MACD', p:[['a','Rapide',12],['b','Lente',26],['s','Signal',9],['r','Pivot (barres)',5]], c:[['MACD','#2962ff'],['Haussière','#26a69a'],['Baissière','#ef5350']],
    h:'Divergences entre la ligne MACD et le cours (traits verts : haussières, rouges : baissières).',
    f:(p,X) => { const m = macdA(X.C,p.a,p.b,p.s).m; return [S('line',0,pts(X,m),{lv:[0]}), ...divSeries(X,m,Math.round(p.r))]; } },
  divcci: { n:'Divergences CCI', p:[['n','Période CCI',20],['r','Pivot (barres)',5]], c:[['CCI','#009688'],['Haussière','#26a69a'],['Baissière','#ef5350']],
    h:'Divergences entre le CCI et le cours (traits verts : haussières, rouges : baissières).',
    f:(p,X) => { const c = cciA(X,p.n); return [S('line',0,pts(X,c),{lv:[100,-100]}), ...divSeries(X,c,Math.round(p.r))]; } },
  vwma: { n:'Moyenne mobile pondérée par le volume (VWMA)', ov:1, p:[['n','Période',20]], c:[['Ligne','#d81b60']], f:(p,X) => [S('line',0,pts(X,vwma(X,p.n)))] },
  ppo: { n:'Oscillateur prix', p:[['a','Courte',9],['b','Longue',26],['pct','En % (0/1)',0,1,0,1]], c:[['Oscillateur','#2962ff']],
    f:(p,X) => { const a = ema(X.C,p.a), b = ema(X.C,p.b); return [S('line',0,pts(X,zip2(a,b,(x,y)=>p.pct?100*(x-y)/y:x-y)),{lv:[0]})]; } },
  vosc: { n:'Oscillateur volume', p:[['a','Courte',5],['b','Longue',10]], c:[['Oscillateur','#6a1b9a']],
    f:(p,X) => [S('line',0,pts(X,zip2(ema(X.V,p.a),ema(X.V,p.b),(x,y)=>y?100*(x-y)/y:null)),{lv:[0]})] },
  piv: { n:'Points pivots (classiques)', ov:1, p:[['n','Barres par période',20]], c:[['Pivot','#ff9800'],['Résistances','#ef5350'],['Supports','#26a69a']],
    h:'Niveaux calculés sur le bloc précédent de N barres (ex. 20 barres journalières ≈ 1 mois).', f:(p,X) => pivSeries(X,p.n,'cls') },
  pivcam: { n:'Points pivots Camarilla', ov:1, p:[['n','Barres par période',20]], c:[['Pivot','#ff9800'],['Résistances','#ef5350'],['Supports','#26a69a']], f:(p,X) => pivSeries(X,p.n,'cam') },
  pivdem: { n:'Points pivots DeMark', ov:1, p:[['n','Barres par période',20]], c:[['Pivot','#ff9800'],['Résistance','#ef5350'],['Support','#26a69a']], f:(p,X) => pivSeries(X,p.n,'dem') },
  pivfib: { n:'Points pivots Fibonacci', ov:1, p:[['n','Barres par période',20]], c:[['Pivot','#ff9800'],['Résistances','#ef5350'],['Supports','#26a69a']], f:(p,X) => pivSeries(X,p.n,'fib') },
  pivwoo: { n:'Points pivots Woodie', ov:1, p:[['n','Barres par période',20]], c:[['Pivot','#ff9800'],['Résistances','#ef5350'],['Supports','#26a69a']], f:(p,X) => pivSeries(X,p.n,'woo') },
  roc: { n:'Price Rate of Change (ROC)', p:[['n','Période',9]], c:[['ROC','#1e88e5']], f:(p,X) => [S('line',0,pts(X,rocA(X.C,Math.round(p.n))),{lv:[0]})] },
  px: { n:'Prix', ov:1, p:[], c:[['Cours','#455a64']], f:(p,X) => [S('line',0,pts(X,X.C))] },
  prt: { n:'PRT Bands', ov:1, p:[['n','Période',50],['k','Écarts-types',2,0.5]], c:[['Bandes','#1e88e5'],['Médiane','#90a4ae']],
    h:'Reconstitution : régression linéaire ± k écarts-types des résidus (formule exacte ProRealTime non disponible ici).',
    f:(p,X) => { const r = linreg(X.C,p.n); return [S('line',0,pts(X,zip2(r.v,r.sd,(x,y)=>x+p.k*y))), S('line',1,pts(X,r.v),{st:'dot'}), S('line',0,pts(X,zip2(r.v,r.sd,(x,y)=>x-p.k*y)))]; } },
  linreg: { n:'Régression linéaire', ov:1, p:[['n','Période',100],['k','Écarts-types (0 = aucun)',2,0.5,0]], c:[['Droite','#ff6d00'],['Canal','#ffb74d']],
    f:(p,X) => { const r = linreg(X.C,p.n), o = [S('line',0,pts(X,r.v))];
      if (p.k > 0) o.push(S('line',1,pts(X,zip2(r.v,r.sd,(x,y)=>x+p.k*y)),{st:'dash'}), S('line',1,pts(X,zip2(r.v,r.sd,(x,y)=>x-p.k*y)),{st:'dash'})); return o; } },
  rep: { n:'Repulse', p:[['p','Période',5]], c:[['Repulse','#2e7d32']],
    h:'Reconstitution (Éric Lefort) : pression acheteuse − pression vendeuse en % du cours, lissée par une EMA de 5×période.',
    f:(p,X) => { const n = Math.round(p.p), h = hh(X.H,n), l = ll(X.L,n), b = X.C.map((c,i)=>l[i]==null||i<n-1?null:100*(3*c-2*l[i]-X.O[i-n+1])/c), s = X.C.map((c,i)=>h[i]==null||i<n-1?null:100*(X.O[i-n+1]+2*h[i]-3*c)/c);
      return [S('line',0,pts(X,ema(zip2(b,s,(x,y)=>x-y),5*n)),{lv:[0]})]; } },
  stc: { n:'Schaff Trend Cycle', p:[['a','Rapide',23],['b','Lente',50],['c','Cycle',10]], c:[['STC','#8e24aa']],
    f:(p,X) => { const m = zip2(ema(X.C,p.a),ema(X.C,p.b),(x,y)=>x-y);
      const st = A => { const h = hhS(A,p.c), l = llS(A,p.c); return A.map((v,i)=>h[i]==null||v==null||h[i]===l[i]?null:100*(v-l[i])/(h[i]-l[i])); };
      const sm = A => { let q = null; return A.map(v => { if (v == null) return null; q = q == null ? v : q + .5 * (v - q); return q; }); };
      return [S('line',0,pts(X,sm(st(sm(st(m))))),{lv:[75,25]})]; } },
  smi: { n:'Stochastic Momentum Index (SMI)', p:[['n','Période',10],['a','Lissage 1',3],['s','Signal',3]], c:[['SMI','#2962ff'],['Signal','#ff6d00']],
    f:(p,X) => { const h = hh(X.H,p.n), l = ll(X.L,p.n), rel = X.C.map((c,i)=>h[i]==null?null:c-(h[i]+l[i])/2), rg = h.map((v,i)=>v==null?null:v-l[i]);
      const a = ema(ema(rel,p.a),p.a), b = ema(ema(rg,p.a),p.a), s = zip2(a,b,(x,y)=>y?200*x/y:null); return [S('line',0,pts(X,s),{lv:[40,-40]}), S('line',1,pts(X,ema(s,p.s)))]; } },
  srsi: { n:'Stochastique RSI', p:[['n','Période RSI',14],['s','Période stochastique',14],['k','Lissage %K',3],['d','Lissage %D',3]], c:[['%K','#2962ff'],['%D','#ff6d00']],
    f:(p,X) => { const r = rsiA(X.C,p.n), h = hhS(r,p.s), l = llS(r,p.s), raw = r.map((v,i)=>h[i]==null||v==null||h[i]===l[i]?null:100*(v-l[i])/(h[i]-l[i])), k = sma(raw,p.k);
      return [S('line',0,pts(X,k),{lv:[80,20]}), S('line',1,pts(X,sma(k,p.d)))]; } },
  dzrsi: { n:'Dynamic Zone RSI', p:[['n','Période RSI',14],['lb','Historique des zones',100,10,20],['hi','Percentile haut',80],['lo','Percentile bas',20]], c:[['RSI','#7e57c2'],['Zone haute','#ef5350'],['Zone basse','#26a69a']],
    h:'Zones de surachat / survente dynamiques : percentiles du RSI sur l’historique choisi.',
    f:(p,X) => { const r = rsiA(X.C,p.n); return [S('line',0,pts(X,r)), S('line',1,pts(X,dynZone(r,p.lb,p.hi)),{st:'dash'}), S('line',2,pts(X,dynZone(r,p.lb,p.lo)),{st:'dash'})]; } },
  dzsto: { n:'Dynamic Zone Stochastique', p:[['n','Période %K',14],['k','Lissage %K',3],['lb','Historique des zones',100,10,20],['hi','Percentile haut',80],['lo','Percentile bas',20]], c:[['%K','#2962ff'],['Zone haute','#ef5350'],['Zone basse','#26a69a']],
    f:(p,X) => { const k = sma(stochRaw(X,p.n),p.k); return [S('line',0,pts(X,k)), S('line',1,pts(X,dynZone(k,p.lb,p.hi)),{st:'dash'}), S('line',2,pts(X,dynZone(k,p.lb,p.lo)),{st:'dash'})]; } },
  sd: { n:'Écart-type', p:[['n','Période',20]], c:[['Écart-type','#6d4c41']], f:(p,X) => [S('line',0,pts(X,std(X.C,p.n)))] },
  env: { n:'Enveloppes', ov:1, p:[['n','Période',20],['pct','Écart (%)',2.5,0.5,0.1],['m','Moyenne : 1 simple, 2 expo',1,1,1,2]], c:[['Enveloppes','#00897b'],['Médiane','#80cbc4']],
    f:(p,X) => { const m = p.m === 2 ? ema(X.C,p.n) : sma(X.C,p.n); return [S('line',0,pts(X,m.map(v=>v==null?null:v*(1+p.pct/100)))), S('line',1,pts(X,m),{st:'dot'}), S('line',0,pts(X,m.map(v=>v==null?null:v*(1-p.pct/100))))]; } },
  hline: { n:'Ligne de prix horizontale', ov:1, p:[['v','Prix (0 = dernier cours)',0,0.01,0]], c:[['Ligne','#f57c00']],
    f:(p,X) => { const v = p.v > 0 ? p.v : X.C[X.C.length-1]; return [S('line',0,pts(X,X.C.map(()=>v)),{st:'dash'})]; } },
  macdzl: { n:'MACD Zéro Lag', p:[['a','Rapide',12],['b','Lente',26],['s','Signal',9]], c:[['MACD','#2962ff'],['Signal','#ff6d00'],['Hausse','#26a69a'],['Baisse','#ef5350']],
    f:(p,X,K) => { const m = zip2(dema(X.C,p.a),dema(X.C,p.b),(x,y)=>x-y), sg = dema(m,p.s), h = zip2(m,sg,(x,y)=>x-y);
      return [S('hist',2,pts(X,h,i=>rgba(h[i]>=0?K[2]:K[3],.7))), S('line',0,pts(X,m)), S('line',1,pts(X,sg))]; } },
  mom: { n:'Momentum', p:[['n','Période',10]], c:[['Momentum','#3949ab']], f:(p,X) => [S('line',0,pts(X,X.C.map((v,i)=>i<p.n?null:v-X.C[i-Math.round(p.n)])),{lv:[0]})] },
  mfi: { n:'Money Flow Index (MFI)', p:[['n','Période',14]], c:[['MFI','#7b1fa2']],
    f:(p,X) => { const tp = X.C.map((v,i)=>(X.H[i]+X.L[i]+v)/3), pos = tp.map((v,i)=>i&&v>tp[i-1]?v*X.V[i]:i?0:null), neg = tp.map((v,i)=>i&&v<tp[i-1]?v*X.V[i]:i?0:null);
      const a = sumN(pos,p.n), b = sumN(neg,p.n); return [S('line',0,pts(X,a.map((s,i)=>s==null||b[i]==null?null:b[i]===0?100:100-100/(1+s/b[i]))),{lv:[80,20]})]; } },
  kama: { n:'Moyenne mobile adaptative (KAMA)', ov:1, p:[['n','Période',10],['f','Rapide',2],['s','Lente',30]], c:[['KAMA','#e65100']], f:(p,X) => [S('line',0,pts(X,kama(X.C,p.n,p.f,p.s)))] },
  dema: { n:'Moyenne mobile exponentielle double (DEMA)', ov:1, p:[['n','Période',20]], c:[['DEMA','#c2185b']], f:(p,X) => [S('line',0,pts(X,dema(X.C,p.n)))] },
  tema: { n:'TEMA', ov:1, p:[['n','Période',20]], c:[['TEMA','#6a1b9a']], f:(p,X) => [S('line',0,pts(X,tema(X.C,p.n)))] },
  wma: { n:'Moyenne mobile pondérée (WMA)', ov:1, p:[['n','Période',20]], c:[['WMA','#0277bd']], f:(p,X) => [S('line',0,pts(X,wma(X.C,p.n)))] },
  trix: { n:'TRIX', p:[['n','Période',15]], c:[['TRIX','#d84315']],
    f:(p,X) => { const t = ema(ema(ema(X.C.map(Math.log),p.n),p.n),p.n); return [S('line',0,pts(X,t.map((v,i)=>i&&v!=null&&t[i-1]!=null?10000*(v-t[i-1]):null)),{lv:[0]})]; } },
  cmp: { n:'Valeur comparée', ov:1, p:[], c:[['Titre comparé','#e91e63']],
    h:'Courbe d’un autre titre ramenée à l’échelle du cours (symbole demandé à l\'ajout ; « Paramètres… » du menu pour le changer).',
    f:(p,X,K,it) => { if (!p.s) return []; const key = `${p.s}|${ST.days}|${X.iv}`, m = CMPD[key]; if (!m) { loadCmp(p.s,X.iv,key); return []; }
      let q = null, base = null; const v = X.T.map((t,i)=>{ if (m.has(t)) q = m.get(t); if (q == null) return null; if (base == null) base = X.C[i] / q; return q * base; }); return [S('line',0,pts(X,v))]; } },
  vp: { n:'Volume profile (zone visible)', ov:1, p:[['rows','Lignes',24,2,4,120],['w','Largeur max (%)',30,5,10,80]], c:[['Volume hausse','#26a69a'],['Volume baisse','#ef5350']],
    h:'Histogramme horizontal du volume par niveau de prix, sur la période visible (dessiné à gauche du graphique).', f:() => [] },
  vroc: { n:'Volume Rate of Change (V-ROC)', p:[['n','Période',14]], c:[['V-ROC','#00695c']], f:(p,X) => [S('line',0,pts(X,rocA(X.V,Math.round(p.n))),{lv:[0]})] },
  vwap: { n:'Volume Weighted Average Price (VWAP)', ov:1, p:[['r','Réinit. : 0 auto, 1 jour, 2 sem., 3 mois, 4 an, 5 jamais',0,1,0,5]], c:[['VWAP','#2962ff']],
    f:(p,X) => { const T = X.T, intr = (T[T.length-1] - T[0]) / Math.max(1, T.length - 1) < 80000, mode = p.r || (intr ? 1 : 3);
      const key = t => { const d = new Date(t * 1000); return mode === 1 ? d.getUTCFullYear() * 10000 + d.getUTCMonth() * 100 + d.getUTCDate() : mode === 2 ? Math.floor((t / 86400 + 3) / 7) : mode === 3 ? d.getUTCFullYear() * 100 + d.getUTCMonth() : mode === 4 ? d.getUTCFullYear() : 0; };
      let k0 = null, sv = 0, spv = 0; return [S('line',0,pts(X,T.map((t,i)=>{ const k = key(t); if (k !== k0) { k0 = k; sv = 0; spv = 0; } const tp = (X.H[i]+X.L[i]+X.C[i])/3; sv += X.V[i]; spv += tp * X.V[i]; return sv ? spv / sv : null; })))]; } },
  vxp: { n:'Volume × Prix (capital échangé)', p:[], c:[['Capital','#5c6bc0']], f:(p,X,K) => [S('hist',0,pts(X,X.C.map((c,i)=>c*X.V[i]),i=>rgba(X.C[i]>=X.O[i]?'#26a69a':'#ef5350',.6)),{pf:'volume'})] },
  vtx: { n:'Vortex', p:[['n','Période',14]], c:[['VI+','#26a69a'],['VI−','#ef5350']],
    f:(p,X) => { const tr = sumN(trf(X),p.n), vp = sumN(X.H.map((h,i)=>i?Math.abs(h-X.L[i-1]):null),p.n), vm = sumN(X.L.map((l,i)=>i?Math.abs(l-X.H[i-1]):null),p.n);
      return [S('line',0,pts(X,vp.map((v,i)=>v==null||!tr[i]?null:v/tr[i]))), S('line',1,pts(X,vm.map((v,i)=>v==null||!tr[i]?null:v/tr[i])))]; } },
  alli: { n:'Williams Alligator', ov:1, p:[], c:[['Mâchoire','#1e88e5'],['Dents','#e53935'],['Lèvres','#43a047']],
    f:(p,X) => { const m = hl2(X), E = X.T.concat(X.fut(8)), sh = (a,d) => a.map((v,i)=>v==null?null:{ time:E[i+d], value:v }).filter(Boolean);
      return [S('line',0,sh(rma(m,13),8)), S('line',1,sh(rma(m,8),5)), S('line',2,sh(rma(m,5),3))]; } },
  zz: { n:'ZigZag', ov:1, p:[['d','Retournement (%)',5,0.5,0.1]], c:[['ZigZag','#ff6d00']],
    f:(p,X) => [S('line',0,zigzag(X,p.d).map(([i,v])=>({ time:X.T[i], value:v })))] },
  zab: { n:'Zone d’achat / vente', p:[['n','Période',20],['hi','Seuil de vente',80],['lo','Seuil d’achat',20]], c:[['Zone d’achat','#26a69a'],['Zone de vente','#ef5350'],['Neutre','#b0bec5']],
    h:'Reconstitution : position du cours dans le canal haut/bas des N dernières barres (verte sous le seuil d’achat, rouge au-dessus du seuil de vente).',
    f:(p,X,K) => { const h = hh(X.H,p.n), l = ll(X.L,p.n), o = X.C.map((c,i)=>h[i]==null||h[i]===l[i]?null:100*(c-l[i])/(h[i]-l[i]));
      return [S('hist',2,pts(X,o,i=>o[i]<=p.lo?K[0]:o[i]>=p.hi?K[1]:K[2]),{lv:[p.lo,p.hi]})]; } },
};

const FAV = ['atr','atr2','bb','cvi','ema','ichi','stpmt','macd','obv','sar','pe','rsi','rsio','sma','sto','st','vol'];
const EPSC = {};
async function ensureEps() {
  if (!ST.inds.some(i => i.type === 'pe' && i.on)) return;
  const sy = ST.sym;
  if (!(sy in EPSC)) { try { EPSC[sy] = (await (await fetch('/api/eps?symbol=' + encodeURIComponent(sy))).json()).eps || []; } catch (e) { EPSC[sy] = []; } }
  if (sy === ST.sym && PN.some(P => P.X)) { PN.forEach(P => { if (P.X) P.X.eps = EPSC[sy]; }); build(true); if (!EPSC[sy].length) status('P/E indisponible : aucun bénéfice publié trouvé pour ce titre', true); }
}

/* ================= État ================= */
const KEY = 'graphique-boursier-v1', PALETTE = ['#2962ff','#ff9800','#9c27b0','#e91e63','#00897b'];
const ST = { sym:'TTE.PA', name:'TotalEnergies SE', exch:'Paris', cur:'', days:'1095', iv:'1d', ivs:['1d','1h','1wk'], layout:1, split:'v', hideLeg:false, inds:[] };
let nid = 0;

function addInd(type, p, c, pos, pn) {
  const d = IND[type], it = { id:++nid, type, on:true, pn:pn == null ? 'all' : pn, pos:pos || (d.ov ? 'over' : 'pane'), p:Object.fromEntries(d.p.map(q => [q[0], q[2]])), c:d.c.map(q => q[1]) };
  if (!c && d.ov && d.c.length === 1 && (type === 'sma' || type === 'ema')) it.c[0] = PALETTE[ST.inds.filter(x => x.type === type).length % PALETTE.length];
  Object.assign(it.p, p || {}); (c || []).forEach((v, i) => { if (v) it.c[i] = v; });
  ST.inds.push(it); return it;
}
function defaults() {
  ST.inds = []; nid = 0;
  addInd('sma',{n:20},['#2962ff']); addInd('sma',{n:50},['#ff9800']); addInd('sma',{n:200},['#9c27b0']);
  addInd('bb'); addInd('sar'); addInd('rsi'); addInd('sto');
}
function save() {
  try { localStorage.setItem(KEY, JSON.stringify({ sym:ST.sym, name:ST.name, exch:ST.exch, days:ST.days, iv:ST.ivs[0], ivs:ST.ivs, layout:ST.layout, split:ST.split, hideLeg:ST.hideLeg, inds:ST.inds })); } catch (e) {}
}
function restore() {
  try {
    const j = JSON.parse(localStorage.getItem(KEY)); if (!j || !Array.isArray(j.inds)) return false;
    Object.assign(ST, { sym:j.sym || ST.sym, name:j.name || '', exch:j.exch || '', days:String(j.days || ST.days), iv:j.iv || ST.iv });
    if (Array.isArray(j.ivs) && j.ivs.length === 3 && j.ivs.every(v => IVL[v])) ST.ivs = j.ivs; else ST.ivs[0] = ST.iv;
    ST.iv = ST.ivs[0]; ST.layout = j.layout === 3 ? 3 : 1; ST.split = j.split === 'v' ? 'v' : (j.layout === 3 && !j.split ? 'h' : 'v');
    ST.hideLeg = !!j.hideLeg; ST.inds = []; nid = 0;
    j.inds.forEach(o => { if (IND[o.type]) addInd(o.type, o.p, o.c || [], o.pos, (o.pn === 'all' || [0,1,2].includes(o.pn) || (Array.isArray(o.pn) && o.pn.length && o.pn.every(v => [0,1,2].includes(v)))) ? o.pn : 'all').on = o.on !== false; });
    return true;
  } catch (e) { return false; }
}

/* ================= Graphique ================= */
function mkFut(T, iv) {
  return n => {
    const o = []; let t = T[T.length-1];
    const step = iv === '1wk' ? 604800 : iv === '1mo' ? 2629800 : iv === '1d' ? 86400 : (T[T.length-1] - T[T.length-2]) || 3600;
    for (let i = 0; i < n; i++) { t += step; if (iv === '1d') { const w = new Date(t*1000).getUTCDay(); if (w === 6) t += 172800; else if (w === 0) t += 86400; } o.push(t); }
    return o;
  };
}
/* ---- Les 3 cadrans de graphique (le 1er seul en mode « 1 graphique ») ---- */
const IVL = { '5m':'5 min', '15m':'15 min', '30m':'30 min', '1h':'1 heure', '4h':'4 heures', '1d':'1 jour', '1wk':'1 semaine', '1mo':'1 mois' };
const PN = [], nAct = () => ST.layout === 3 ? 3 : 1;
const pnList = it => it.pn === 'all' || it.pn == null ? [0, 1, 2] : Array.isArray(it.pn) ? it.pn : [it.pn];
const forPanel = (it, k) => pnList(it).includes(k);                                // l'indicateur s'affiche-t-il sur le graphique k ?
const normPn = l => { l = [...new Set(l)].sort(); return l.length === 3 ? 'all' : l.length === 1 ? l[0] : l; };
function closeInd(it, k) {                                                          // petite croix de la légende
  if (ST.layout !== 3) ST.inds = ST.inds.filter(x => x !== it);
  else { const l = pnList(it).filter(x => x !== k); if (l.length) it.pn = normPn(l); else ST.inds = ST.inds.filter(x => x !== it); }
  apply();
}
const shortName = it => { const n = IND[it.type].n, m = n.match(/\(([^)]+)\)/); const s = m ? m[1].split(',')[0] : ''; return /^[A-Z0-9%\/&\- ]+$/.test(s) ? s : n; };
const isOver = it => (it.pos || (IND[it.type].ov ? 'over' : 'pane')) === 'over';
function chipHtml(it) {
  const pr = IND[it.type].p.slice(0, 3).map(q => it.p[q[0]]).join(', ');
  return `<span class="chip${it.on ? '' : ' off'}"><i style="background:${esc(it.c[0])}"></i>${esc(shortName(it))}${it.p.s ? ' ' + esc(it.p.s) : ''}${pr ? ' ' + esc(pr) : ''}<button data-id="${it.id}" title="${ST.layout === 3 && pnList(it).length > 1 ? 'Retirer de ce graphique' : 'Supprimer cet indicateur'}">✕</button></span>`;
}
const legClick = (e, k) => { const b = e.target.closest('button'); const it = b && ST.inds.find(x => x.id === +b.dataset.id); if (it) closeInd(it, k); };
/* Légende du haut : indicateurs superposés au prix (+ ceux masqués ou sans données). Ceux d'un cadre séparé portent leur nom DANS ce cadre (paneLabels). */
function drawLegend(k) {
  const P = PN[k];
  P.tog.textContent = ST.hideLeg ? '+' : '−';
  P.tog.title = ST.hideLeg ? 'Afficher les noms des indicateurs' : 'Masquer les noms des indicateurs';
  P.leg.innerHTML = k >= nAct() || ST.hideLeg ? '' : ST.inds.filter(it => forPanel(it, k) && (isOver(it) || !it.on || (P.orph || []).includes(it))).map(chipHtml).join('');
}
function paneLabels(P, k) {
  if (!P.chart || ST.hideLeg) return;
  let panes; try { panes = P.chart.panes(); } catch (e) { return; }
  (P.pl || []).forEach(({ pi, it }) => {
    const row = panes[pi] && panes[pi].getHTMLElement(); const el = row && (row.children[1] || row); if (!el) return;
    const d = document.createElement('div'); d.className = 'plg'; d.innerHTML = chipHtml(it);
    d.addEventListener('click', e => legClick(e, k));
    el.appendChild(d);
  });
}
function mkPanels() {
  const box = $('#charts');
  for (let i = 0; i < 3; i++) {
    const el = document.createElement('div'); el.className = 'pn';
    el.innerHTML = `<div class="pinfo"><div class="prow"><span class="ttl"></span><select class="piv" title="Durée des bougies de ce graphique" aria-label="Durée des bougies"></select><button class="legt" type="button"></button></div><div class="ohlc"></div><div class="leg"></div>${i ? '' : '<div id="tip">Clic droit sur un graphique : ajouter un indicateur</div>'}</div><div class="pchart"></div>`;
    box.appendChild(el);
    const P = { i, el, cel:el.querySelector('.pchart'), ttl:el.querySelector('.ttl'), ohlc:el.querySelector('.ohlc'), sel:el.querySelector('.piv'), leg:el.querySelector('.leg'), tog:el.querySelector('.legt'),
      chart:null, candle:null, X:null, req:0, key:'', iv:ST.ivs[i], note:'', err:'' };
    P.sel.innerHTML = Object.entries(IVL).map(([k, l]) => `<option value="${k}">${l}</option>`).join('');
    P.sel.value = ST.ivs[i];
    P.sel.addEventListener('change', () => { ST.ivs[i] = P.sel.value; ST.iv = ST.ivs[0]; load(i); });
    P.leg.addEventListener('click', e => legClick(e, i));
    P.tog.addEventListener('click', () => { ST.hideLeg = !ST.hideLeg; build(true); save(); });      // petit « − » : masque / affiche les noms des indicateurs
    P.cel.addEventListener('contextmenu', e => { e.preventDefault(); cmOpen(e.clientX, e.clientY, i); });
    PN.push(P); drawInit(P);
  }
}
function showBar(P, i) {
  const X = P.X; if (!X) return;
  const f = v => v.toLocaleString('fr-FR', { maximumFractionDigits:4 });
  const c = X.C[i], p = i ? X.C[i-1] : c, ch = c - p, pc = p ? ch / p * 100 : 0;
  P.ohlc.innerHTML = `O ${f(X.O[i])} &nbsp;H ${f(X.H[i])} &nbsp;B ${f(X.L[i])} &nbsp;C ${f(c)} &nbsp;<span class="${ch>=0?'up':'dn'}">${ch>=0?'+':''}${f(ch)} (${pc.toFixed(2)} %)</span>`;
}
/* Proportions par défaut : chaque indicateur = 10 % de la hauteur, 20 % au maximum pour l'ensemble (quel que soit leur nombre) ; le prix prend le reste (80 % ou plus).
   (setStretchFactor n'existe pas dans Lightweight Charts 5.0.0 : on règle la hauteur du cadre du prix avec setHeight, les autres cadres se partagent le reste à égalité.) */
function applyHeights(P) {
  const run = () => {
    let panes; try { panes = P.chart.panes(); } catch (e) { return; }
    const n = panes.length - 1; if (n < 1) return;
    const total = panes.reduce((a, p) => a + p.getHeight(), 0); if (total < 100) return;     // mise en page pas encore calculée
    try { panes[0].setHeight(Math.round(total * (1 - Math.min(n * 0.1, 0.2)))); } catch (e) {}
  };
  run(); requestAnimationFrame(run); setTimeout(run, 120);
}
function buildPanel(k, keep) {
  const P = PN[k], X = P.X; P.pl = []; P.orph = []; drawLegend(k);
  const lr = keep && P.chart ? P.chart.timeScale().getVisibleLogicalRange() : null;
  if (P.chart) { P.chart.remove(); P.chart = null; }
  if (!X || k >= nAct()) return;
  const DK = !!UI.dark, bd = DK ? '#2a2e39' : '#ccc', cu = UI.cup || '#089981', cd = UI.cdn || '#f23645';
  const chart = P.chart = createChart(P.cel, {
    autoSize:true, layout:{ background:{ color:DK ? '#131722' : '#ffffff' }, textColor:DK ? '#d1d4dc' : '#333', panes:{ separatorColor:DK ? '#2a2e39' : '#e0e3eb' } },
    grid:{ vertLines:{ color:DK ? '#1e222d' : '#f0f0f0' }, horzLines:{ color:DK ? '#1e222d' : '#f0f0f0' } },
    crosshair:{ mode:CrosshairMode.Normal },
    timeScale:{ borderColor:bd, timeVisible:!['1d','1wk','1mo'].includes(P.iv), secondsVisible:false, rightOffset:10 },
    rightPriceScale:{ borderColor:bd },
  });
  const candle = P.candle = chart.addSeries(CandlestickSeries, {
    upColor:cu, downColor:cd, borderUpColor:cu, borderDownColor:cd, wickUpColor:cu, wickDownColor:cd,
  }, 0);
  P.cvk = (P.cvk || 0) + 1;
  candle.setData(X.T.map((t,i) => ({ time:t, open:X.O[i], high:X.H[i], low:X.L[i], close:X.C[i] })));

  let pane = 0;
  for (const it of ST.inds) {
    if (!it.on || !forPanel(it, k)) continue;
    const d = IND[it.type], over = (it.pos || (d.ov ? 'over' : 'pane')) === 'over';
    const ss = d.f(it.p, X, it.c, it); if (!ss.length) { P.orph.push(it); continue; }
    const pi = over ? 0 : ++pane, sid = over && !d.ov ? 'o' + it.id : null;
    if (!over) P.pl.push({ pi, it });
    ss.forEach((s, j) => {
      let ser;
      if (s.t === 'hist') ser = chart.addSeries(HistogramSeries, { ...baseOpt(j, sid), color:it.c[s.c], ...(s.pf ? { priceFormat:{ type:s.pf } } : {}) }, pi);
      else if (s.t === 'dots') ser = chart.addSeries(LineSeries, { ...baseOpt(j, sid), color:it.c[s.c], lineVisible:false, pointMarkersVisible:true, pointMarkersRadius:2 }, pi);
      else ser = chart.addSeries(LineSeries, { ...baseOpt(j, sid), color:it.c[s.c], lineWidth:1.5,
        lineStyle:s.st === 'dash' ? LineStyle.Dashed : s.st === 'dot' ? LineStyle.Dotted : LineStyle.Solid }, pi);
      ser.setData(s.d);
      (s.lv || []).forEach(v => ser.createPriceLine({ price:v, color:'#999', lineStyle:LineStyle.Dashed, lineWidth:1, axisLabelVisible:true }));
    });
    if (sid) try { chart.priceScale(sid, 0).applyOptions({ scaleMargins:{ top:it.type === 'vol' ? .8 : .72, bottom:.03 }, visible:false }); } catch (e) {}
  }
  function baseOpt(j, sid) { return { priceLineVisible:false, lastValueVisible:j === 0 && !sid, crosshairMarkerVisible:false, ...(sid ? { priceScaleId:sid } : {}) }; }
  applyHeights(P);
  if (P.ro) P.ro.disconnect();
  let hPrev = P.cel.clientHeight;
  P.ro = new ResizeObserver(() => { const h = P.cel.clientHeight; if (Math.abs(h - hPrev) > 4) { hPrev = h; applyHeights(P); } });   // fenêtre redimensionnée : on recalcule
  P.ro.observe(P.cel);
  chart.subscribeCrosshairMove(p => { const i = p.time != null ? X.idx.get(p.time) : null; showBar(P, i ?? X.T.length - 1); });
  if (lr) chart.timeScale().setVisibleLogicalRange(lr); else chart.timeScale().fitContent();
  showBar(P, X.T.length - 1);
  drawLegend(k); paneLabels(P, k);
}
function build(keep) { PN.forEach((P, k) => buildPanel(k, keep)); }

/* ================= Chargement des données ================= */
function status(msg, err) { const s = $('#status'); s.textContent = msg || ''; s.className = err ? 'err' : ''; }
async function loadPanel(i) {
  const P = PN[i], my = ++P.req, sym = ST.sym, iv = P.iv = ST.ivs[i];
  P.sel.value = iv; P.err = ''; P.note = '';
  try {
    const r = await fetch(`/api/history?symbol=${encodeURIComponent(sym)}&days=${ST.days}&interval=${iv}`);
    const j = await r.json(); if (my !== P.req) return;
    if (j.error) throw new Error(j.error);
    const b = j.bars;
    const X = P.X = { T:b.map(r=>r[0]), O:b.map(r=>r[1]), H:b.map(r=>r[2]), L:b.map(r=>r[3]), C:b.map(r=>r[4]), V:b.map(r=>r[5]) };
    X.fut = mkFut(X.T, iv); X.iv = iv; X.idx = new Map(X.T.map((t, i) => [t, i]));
    P.key = sym + '|' + ST.days + '|' + iv;
    ST.cur = j.currency || '';
    P.ttl.innerHTML = i ? `<b>${esc(sym)}</b>` : `<b>${esc(sym)}</b> ${esc(ST.name)} <span>${esc([ST.exch, ST.cur].filter(Boolean).join(', '))}</span>`;
    X.eps = EPSC[sym] || [];
    buildPanel(i, false); P.note = j.note || '';
    return true;
  } catch (e) { if (my === P.req) { P.err = `« ${sym} » : ${e.message}`; return false; } }
}
function report() {
  const act = PN.slice(0, nAct()), errs = act.map(P => P.err).filter(Boolean);
  if (errs.length) status(errs[0], true); else status([...new Set(act.map(P => P.note).filter(Boolean))].join(' · '));
}
async function load(only) {
  status('Chargement…');
  const idx = only != null ? [only] : [...Array(nAct()).keys()];
  const res = await Promise.all(idx.map(loadPanel));
  if (res.every(r => r === undefined)) return;                    // requête dépassée par une plus récente
  report(); save(); ensureEps();
  return res[0];
}
const layKey = () => ST.layout === 3 ? '3' + ST.split : '1';
function layUI() {
  $('#charts').className = (ST.layout === 3 ? 'l3 ' + ST.split : 'l1') + (UI.dark ? ' dk' : '');
  $('#lay').value = layKey();
}
function setLayout(n, split) {
  ST.layout = n; if (split) ST.split = split; layUI();
  side(); build(true); save();
  const need = [...Array(nAct()).keys()].filter(i => !PN[i].X || PN[i].key !== ST.sym + '|' + ST.days + '|' + ST.ivs[i]);
  if (need.length) { status('Chargement…'); Promise.all(need.map(loadPanel)).then(() => { report(); ensureEps(); }); }
}

/* ================= Recherche avec suggestions ================= */
const q = $('#q'), box = $('#sug'); let sug = [], hi = -1, tmr = 0, sreq = 0;
async function search(v) {
  const my = ++sreq;
  try { const j = await (await fetch('/api/search?q=' + encodeURIComponent(v))).json(); if (my !== sreq) return; sug = j.results || []; }
  catch (e) { sug = []; }
  hi = -1; drawSug();
}
function drawSug() {
  box.innerHTML = sug.map((s, i) => `<div class="it${i===hi?' hi':''}" data-i="${i}"><b>${esc(s.symbol)}</b><span>${esc(s.name)}</span><em>${esc(s.exch)}</em></div>`).join('') || '<div class="none">Aucun résultat</div>';
  box.hidden = false;
}
function qShow() {                                                  // le champ affiche le NOM de la société, lu depuis le début
  q.value = ST.name || ST.sym; q.title = ST.name ? `${ST.name} (${ST.sym})` : ST.sym;
  try { q.setSelectionRange(0, 0); } catch (e) {}
  q.scrollLeft = 0; setTimeout(() => { q.scrollLeft = 0; }, 0);
  anaSync();
}
function choose(s) {
  box.hidden = true; q.blur();
  ST.sym = s.symbol; ST.name = s.name || ''; ST.exch = s.exch || ''; qShow(); const p = load(); refreshFiche(); return p;
}
q.addEventListener('focus', () => q.select());
q.addEventListener('input', () => { clearTimeout(tmr); const v = q.value.trim(); if (!v) { box.hidden = true; return; } tmr = setTimeout(() => search(v), 220); });
q.addEventListener('keydown', async e => {
  if (e.key === 'ArrowDown') { hi = Math.min(hi + 1, sug.length - 1); drawSug(); e.preventDefault(); }
  else if (e.key === 'ArrowUp') { hi = Math.max(hi - 1, -1); drawSug(); e.preventDefault(); }
  else if (e.key === 'Escape') { box.hidden = true; }
  else if (e.key === 'Enter') {
    e.preventDefault(); const v = q.value.trim(); if (!v) return;
    if (hi >= 0) return choose(sug[hi]);
    clearTimeout(tmr); await search(v);
    choose(sug.find(s => s.symbol.toUpperCase() === v.toUpperCase()) || sug[0] || { symbol:v.toUpperCase(), name:'', exch:'' });
  }
});
box.addEventListener('mousedown', e => { e.preventDefault(); const it = e.target.closest('.it'); if (it) choose(sug[+it.dataset.i]); });
q.addEventListener('blur', () => { box.hidden = true; qShow(); });

/* ================= Listes : actions par pays, indices, matières premières =================
   Sélection de grandes valeurs (non exhaustive) : la recherche couvre tout le reste. */
const LISTES = {
  actions: {
    "États-Unis": [["AAPL","Apple"],["MSFT","Microsoft"],["NVDA","Nvidia"],["AMZN","Amazon"],["GOOGL","Alphabet"],["META","Meta"],["TSLA","Tesla"],["BRK-B","Berkshire Hathaway"],["AVGO","Broadcom"],["JPM","JPMorgan Chase"],["LLY","Eli Lilly"],["V","Visa"],["XOM","Exxon Mobil"],["WMT","Walmart"],["JNJ","Johnson & Johnson"],["UNH","UnitedHealth"],["ORCL","Oracle"],["COST","Costco"],["HD","Home Depot"],["PG","Procter & Gamble"],["MA","Mastercard"],["NFLX","Netflix"],["BAC","Bank of America"],["KO","Coca-Cola"],["PEP","PepsiCo"],["AMD","AMD"],["CRM","Salesforce"],["CVX","Chevron"],["ABBV","AbbVie"],["MRK","Merck"],["ADBE","Adobe"],["DIS","Disney"]],
    "France": [["TTE.PA","TotalEnergies"],["MC.PA","LVMH"],["RMS.PA","Hermès"],["OR.PA","L'Oréal"],["SAN.PA","Sanofi"],["AIR.PA","Airbus"],["SU.PA","Schneider Electric"],["AI.PA","Air Liquide"],["BNP.PA","BNP Paribas"],["CS.PA","AXA"],["SAF.PA","Safran"],["DG.PA","Vinci"],["EL.PA","EssilorLuxottica"],["KER.PA","Kering"],["GLE.PA","Société Générale"],["ORA.PA","Orange"],["STLAP.PA","Stellantis"],["RI.PA","Pernod Ricard"]],
    "Allemagne": [["SAP.DE","SAP"],["SIE.DE","Siemens"],["ALV.DE","Allianz"],["DTE.DE","Deutsche Telekom"],["MBG.DE","Mercedes-Benz"],["BMW.DE","BMW"],["VOW3.DE","Volkswagen"],["BAS.DE","BASF"],["ADS.DE","Adidas"],["IFX.DE","Infineon"],["MUV2.DE","Munich Re"],["DBK.DE","Deutsche Bank"],["RHM.DE","Rheinmetall"],["ENR.DE","Siemens Energy"]],
    "Royaume-Uni": [["SHEL.L","Shell"],["AZN.L","AstraZeneca"],["HSBA.L","HSBC"],["ULVR.L","Unilever"],["BP.L","BP"],["GSK.L","GSK"],["RIO.L","Rio Tinto"],["BATS.L","British American Tobacco"],["DGE.L","Diageo"],["LSEG.L","London Stock Exchange Group"],["BARC.L","Barclays"],["LLOY.L","Lloyds"],["RR.L","Rolls-Royce"],["VOD.L","Vodafone"]],
    "Pays-Bas": [["ASML.AS","ASML"],["INGA.AS","ING"],["PHIA.AS","Philips"],["AD.AS","Ahold Delhaize"],["PRX.AS","Prosus"],["HEIA.AS","Heineken"],["ADYEN.AS","Adyen"],["WKL.AS","Wolters Kluwer"],["UNA.AS","Unilever (Amsterdam)"],["SHELL.AS","Shell (Amsterdam)"]],
    "Espagne": [["SAN.MC","Banco Santander"],["BBVA.MC","BBVA"],["ITX.MC","Inditex"],["IBE.MC","Iberdrola"],["TEF.MC","Telefónica"],["REP.MC","Repsol"],["AMS.MC","Amadeus"],["CABK.MC","CaixaBank"]],
    "Italie": [["ENEL.MI","Enel"],["ISP.MI","Intesa Sanpaolo"],["UCG.MI","UniCredit"],["ENI.MI","Eni"],["RACE.MI","Ferrari"],["G.MI","Generali"],["PRY.MI","Prysmian"],["MONC.MI","Moncler"],["LDO.MI","Leonardo"]],
    "Suisse": [["NESN.SW","Nestlé"],["ROG.SW","Roche"],["NOVN.SW","Novartis"],["UBSG.SW","UBS"],["ZURN.SW","Zurich Insurance"],["ABBN.SW","ABB"],["CFR.SW","Richemont"],["SREN.SW","Swiss Re"],["LONN.SW","Lonza"],["SIKA.SW","Sika"]],
    "Belgique": [["ABI.BR","AB InBev"],["UCB.BR","UCB"],["KBC.BR","KBC"],["SOLB.BR","Solvay"],["ARGX.BR","argenx"],["AGS.BR","Ageas"]],
    "Suède": [["VOLV-B.ST","Volvo"],["ERIC-B.ST","Ericsson"],["ATCO-A.ST","Atlas Copco"],["INVE-B.ST","Investor"],["HM-B.ST","H&M"],["SEB-A.ST","SEB"],["ASSA-B.ST","Assa Abloy"],["SAND.ST","Sandvik"]],
    "Danemark": [["NOVO-B.CO","Novo Nordisk"],["MAERSK-B.CO","Maersk"],["DSV.CO","DSV"],["VWS.CO","Vestas"],["CARL-B.CO","Carlsberg"],["ORSTED.CO","Ørsted"]],
    "Norvège": [["EQNR.OL","Equinor"],["DNB.OL","DNB"],["TEL.OL","Telenor"],["MOWI.OL","Mowi"],["NHY.OL","Norsk Hydro"],["YAR.OL","Yara"]],
    "Japon": [["7203.T","Toyota"],["6758.T","Sony"],["8306.T","Mitsubishi UFJ"],["6861.T","Keyence"],["9984.T","SoftBank Group"],["8035.T","Tokyo Electron"],["9983.T","Fast Retailing"],["6501.T","Hitachi"],["7974.T","Nintendo"],["9432.T","NTT"]],
    "Chine / Hong Kong": [["0700.HK","Tencent"],["9988.HK","Alibaba"],["1299.HK","AIA"],["0939.HK","China Construction Bank"],["1398.HK","ICBC"],["3690.HK","Meituan"],["1810.HK","Xiaomi"],["0941.HK","China Mobile"],["1211.HK","BYD"],["9618.HK","JD.com"]],
    "Corée du Sud": [["005930.KS","Samsung Electronics"],["000660.KS","SK Hynix"],["373220.KS","LG Energy Solution"],["207940.KS","Samsung Biologics"],["005380.KS","Hyundai Motor"],["035420.KS","Naver"]],
    "Taïwan": [["2330.TW","TSMC"],["2317.TW","Hon Hai (Foxconn)"],["2454.TW","MediaTek"],["2308.TW","Delta Electronics"],["2881.TW","Fubon Financial"]],
    "Inde": [["RELIANCE.NS","Reliance Industries"],["TCS.NS","Tata Consultancy"],["HDFCBANK.NS","HDFC Bank"],["INFY.NS","Infosys"],["ICICIBANK.NS","ICICI Bank"],["BHARTIARTL.NS","Bharti Airtel"]],
    "Australie": [["BHP.AX","BHP"],["CBA.AX","Commonwealth Bank"],["CSL.AX","CSL"],["NAB.AX","NAB"],["WBC.AX","Westpac"],["WES.AX","Wesfarmers"]],
  },
  indices: {
    "Amérique": [["^GSPC","S&P 500"],["^DJI","Dow Jones"],["^IXIC","Nasdaq Composite"],["^NDX","Nasdaq 100"],["^RUT","Russell 2000"],["^VIX","VIX (volatilité)"],["^GSPTSE","S&P/TSX (Canada)"],["^BVSP","Bovespa (Brésil)"]],
    "Europe": [["^FCHI","CAC 40"],["^GDAXI","DAX"],["^FTSE","FTSE 100"],["^STOXX50E","Euro Stoxx 50"],["^STOXX","STOXX Europe 600"],["^AEX","AEX"],["^IBEX","IBEX 35"],["FTSEMIB.MI","FTSE MIB"],["^SSMI","SMI"],["^BFX","BEL 20"]],
    "Asie-Pacifique": [["^N225","Nikkei 225"],["^HSI","Hang Seng"],["000001.SS","Shanghai Composite"],["^KS11","KOSPI"],["^BSESN","Sensex"],["^AXJO","ASX 200"]],
  },
  matieres: {
    "Métaux": [["GC=F","Or"],["SI=F","Argent"],["PL=F","Platine"],["HG=F","Cuivre"]],
    "Énergie": [["CL=F","Pétrole WTI"],["BZ=F","Pétrole Brent"],["NG=F","Gaz naturel"]],
    "Agricoles": [["ZW=F","Blé"],["ZC=F","Maïs"],["ZS=F","Soja"],["KC=F","Café"],["SB=F","Sucre"],["CC=F","Cacao"],["CT=F","Coton"]],
  },
};
function remplirListe(id, titre, groupes, prefixe) {
  const s = $(id);
  s.innerHTML = `<option value="">${titre}</option>` + Object.entries(groupes).map(([g, a]) =>
    `<optgroup label="${esc(g)}">${a.map(([k, n]) => `<option value="${esc(k)}" data-n="${esc(n)}">${esc(n)} (${esc(k)})</option>`).join('')}</optgroup>`).join('');
  s.addEventListener('change', () => {
    if (!s.value) return;
    const o = s.selectedOptions[0];
    choose({ symbol:s.value, name:o.dataset.n, exch:(prefixe ? prefixe + ' ' : '') + o.parentElement.label });
    s.value = '';
  });
}
remplirListe('#lst-actions', 'Actions par pays', LISTES.actions, '');
remplirListe('#lst-indices', 'Indices mondiaux', LISTES.indices, 'Indice');
remplirListe('#lst-matieres', 'Matières premières', LISTES.matieres, 'Future');

/* ================= Périodes, intervalle, réinitialisation ================= */
function syncUI() {
  $('#rng').value = ST.days;
  PN.forEach((P, i) => { P.sel.value = ST.ivs[i]; }); qShow();
}
$('#rng').addEventListener('change', e => { ST.days = e.target.value; syncUI(); load(); });
$('#lay').addEventListener('change', e => { const l = e.target.value; setLayout(l === '1' ? 1 : 3, l === '1' ? null : l[1]); });
$('#reset').addEventListener('click', () => {
  Object.assign(ST, { sym:'TTE.PA', name:'TotalEnergies SE', exch:'Paris', days:'1095', iv:'1d', ivs:['1d','1h','1wk'] });
  defaults(); syncUI(); side(); load(); refreshFiche();
});

/* ================= Calendrier des résultats (semaine en cours / semaine prochaine, par région) ================= */
const EARN = { w:0, r:'us' }, ECACHE = {};
async function loadEarn() {
  const k = EARN.r + EARN.w, b = $('#ebody');
  document.querySelectorAll('#ewk button').forEach(x => x.classList.toggle('on', +x.dataset.w === EARN.w));
  document.querySelectorAll('#ereg button').forEach(x => x.classList.toggle('on', x.dataset.r === EARN.r));
  b.innerHTML = '<p class="empty">Chargement…</p>';
  try { ECACHE[k] = ECACHE[k] || await get(`/api/earnings?region=${EARN.r}&week=${EARN.w}`); }
  catch (e) { if (k === EARN.r + EARN.w) b.innerHTML = `<p class="empty">Calendrier indisponible : ${esc(e.message)}</p>`; return; }
  if (k !== EARN.r + EARN.w) return;
  const j = ECACHE[k], jour = d => new Date(d + 'T12:00:00').toLocaleDateString('fr-FR', { weekday:'short', day:'numeric', month:'short' });
  const rows = j.items.map((x, i) => `<tr class="cl" data-i="${i}"><td>${esc(jour(x.date))}</td><td><b>${esc(x.nom)}</b><br><small>${esc(x.tv)}</small></td>
    <td>${x.cap == null ? '–' : fnum(x.cap / 1e9, 1) + ' Md ' + esc(x.cur)}</td><td>${fnum(x.est)}</td><td>${fnum(x.rep)}</td></tr>`).join('');
  b.innerHTML = `<p class="empty">Du ${esc(jour(j.debut))} au ${esc(jour(j.fin))} · ${j.items.length} sociétés (40 plus grosses capitalisations maximum) · clic sur une ligne : ouvrir le graphique</p>`
    + (j.items.length ? `<table><tr><th>Date</th><th>Société</th><th>Capitalisation</th><th>BPA estimé</th><th>BPA publié</th></tr>${rows}</table>` : '<p class="empty">Aucune publication trouvée sur cette période.</p>')
    + (j.erreurs ? `<p class="empty">${j.erreurs} requête(s) vers TradingView ont échoué : la liste peut être incomplète.</p>` : '');
  b.onclick = async e => {
    const tr = e.target.closest('tr.cl'); if (!tr) return; const x = j.items[+tr.dataset.i];
    const parNom = async () => { try { const r = (await get('/api/search?q=' + encodeURIComponent(x.nom))).results || []; return r[0]; } catch (err) { return null; } };
    let ok = x.yahoo ? await choose({ symbol:x.yahoo, name:x.nom, exch:'' }) : false;
    if (ok === false) {                                              // symbole Yahoo inconnu ou sans données : on cherche la société par son nom
      const r = await parNom();
      if (r && r.symbol !== x.yahoo) choose(r); else if (!x.yahoo) status(`Aucun symbole trouvé pour « ${x.nom} »`, true);
    }
  };
}
$('#ewk').addEventListener('click', e => { const b = e.target.closest('button'); if (b) { EARN.w = +b.dataset.w; loadEarn(); } });
$('#ereg').addEventListener('click', e => { const b = e.target.closest('button'); if (b) { EARN.r = b.dataset.r; loadEarn(); } });

/* ================= Panneau des indicateurs ================= */
const sel = $('#add'), optF = ks => ks.map(k => `<option value="${k}">${IND[k].n}</option>`).join('');
sel.innerHTML = `<option value="">+ Ajouter un indicateur</option><optgroup label="★ Favoris">${optF(FAV)}</optgroup><optgroup label="Autres">${optF(Object.keys(IND).filter(k => !FAV.includes(k)).sort((a, b) => IND[a].n.localeCompare(IND[b].n, 'fr')))}</optgroup>`;
function addAt(type, where, pn) {
  let sy = null;
  if (type === 'cmp') { sy = (prompt('Symbole du titre à comparer (ex. ^FCHI, AAPL, MC.PA) :') || '').trim().toUpperCase(); if (!sy) return null; }
  const it = addInd(type, sy ? { s:sy } : null, null, where, pn); side(); build(true); save(); if (type === 'pe') ensureEps(); return it; }
sel.addEventListener('change', () => { if (!sel.value) return; addAt(sel.value); sel.value = ''; });

function side() {
  $('#list').innerHTML = ST.inds.map(it => {
    const d = IND[it.type];
    const ps = d.p.map(p => `<label>${p[1]}<input type="number" data-k="${p[0]}" value="${it.p[p[0]]}" step="${p[3] || 1}" min="${p[4] ?? (p[3] || 1)}"${p[5] != null ? ` max="${p[5]}"` : ''}></label>`).join('');
    const pos = `<label>Position<select data-pos><option value="over"${it.pos === 'over' ? ' selected' : ''}>Sur le graphique</option><option value="pane"${it.pos !== 'over' ? ' selected' : ''}>Sous le graphique</option></select></label>`;
    const pl = pnList(it), pnSel = ST.layout === 3 ? `<label>Graphique<select data-pn><option value="all"${pl.length === 3 ? ' selected' : ''}>Les 3</option>${[0,1,2].map(k => `<option value="${k}"${pl.length === 1 && pl[0] === k ? ' selected' : ''}>Graphique ${k + 1}</option>`).join('')}${pl.length === 2 ? `<option value="x" selected>Graphiques ${pl.map(k => k + 1).join(' et ')}</option>` : ''}</select></label>` : '';
    const cs = d.c.map((c, i) => `<label title="${esc(c[0])}">${esc(c[0])}<input type="color" data-c="${i}" value="${it.c[i]}"></label>`).join('');
    return `<div class="card${it.on ? '' : ' off'}" data-id="${it.id}"><div class="ch"><b>${d.n}${it.p.s ? ' · ' + esc(it.p.s) : ''}</b>
      <button data-a="eye" title="Afficher / masquer">${it.on ? '◉' : '○'}</button><button data-a="del" title="Supprimer">✕</button></div>
      ${d.h ? `<div class="hint">${esc(d.h)}</div>` : ''}<div class="cp">${pos}${pnSel}${ps}${cs}</div></div>`;
  }).join('') || '<p class="empty">Aucun indicateur. Ajoutez-en un avec la liste ci-dessus.</p>';
}
const getIt = e => { const c = e.target.closest('.card'); return c && ST.inds.find(x => x.id === +c.dataset.id); };
let ctm = 0;
$('#list').addEventListener('click', e => {
  const b = e.target.closest('button'); const it = b && getIt(e); if (!it) return;
  if (b.dataset.a === 'eye') { it.on = !it.on; ensureEps(); } else ST.inds = ST.inds.filter(x => x !== it);
  side(); build(true); save();
});
$('#list').addEventListener('change', e => {
  const it = getIt(e), t = e.target; if (it && t.dataset.pos != null) { it.pos = t.value; build(true); save(); return; }
  if (it && t.dataset.pn != null) { if (t.value === 'x') return; it.pn = t.value === 'all' ? 'all' : +t.value; build(true); save(); return; }
  if (!it || t.dataset.k == null) return;
  const def = IND[it.type].p.find(p => p[0] === t.dataset.k), step = def[3] || 1;
  let v = parseFloat(t.value); if (isNaN(v)) v = def[2];
  v = Math.min(def[5] ?? Infinity, Math.max(def[4] ?? step, step >= 1 ? Math.round(v) : v)); t.value = v; it.p[t.dataset.k] = v;
  build(true); save();
});
$('#list').addEventListener('input', e => {
  const it = getIt(e), t = e.target; if (!it || t.dataset.c == null) return;
  it.c[+t.dataset.c] = t.value; clearTimeout(ctm); ctm = setTimeout(() => { build(true); save(); }, 80);
});

/* ================= Onglet Performances et séparateur ================= */
const REGIONS = {
  us: ["États-Unis"],
  fr: ["France"],
  eu: ["Allemagne","Royaume-Uni","Pays-Bas","Espagne","Italie","Suisse","Belgique","Suède","Danemark","Norvège"],
  as: ["Japon","Chine / Hong Kong","Corée du Sud","Taïwan","Inde","Australie"],
};
const COLS = [["n","Nom"],["price","Cours"],["d1","1J"],["w1","1S"],["m1","1M"],["m3","3M"],["m6","6M"],["ytd","YTD"],["y1","1A"]];
const UI = { tab:'ind', open:'', w:{ ind:300, perf:580, screener:720, earn:640, ana:780 }, reg:'us', country:'', k:null, dir:-1,
  dark:0, cup:'#089981', cdn:'#f23645', ltb:1, mag:0, keep:0, lock:0, hide:0, auto:{ sr:0, ch:0, tl:0 }, sens:1, lastT:{}, dcol:'#2962ff', dw:2, dls:0 };
const PERF = {}, PTIME = {}, UNIV = {}, UFAIL = {}; let preq = 0, PF = '';
const UKEY = { "États-Unis":'us', "France":'fr' };      // pays dont la liste complète vient du serveur
const CHUNK = 50;                                          // symboles par requête de performances
const perfSymbols = c => UNIV[c] || LISTES.actions[c] || [];
function uiSave() { try { localStorage.setItem('graphique-boursier-ui', JSON.stringify(UI)); } catch (e) {} }
function uiRestore() {
  try {
    const j = JSON.parse(localStorage.getItem('graphique-boursier-ui')); if (!j) return;
    Object.assign(UI, j, { w:{ ...UI.w, ...(j.w || {}) } });
    if (!REGIONS[UI.reg]) UI.reg = 'us';
    if (!['ind', 'perf', 'screener', 'earn', 'ana'].includes(UI.tab)) UI.tab = 'ind';
    if (!['ind', 'perf', 'screener', 'earn', 'ana'].includes(UI.open)) UI.open = '';
    if (!UI.auto) UI.auto = { sr:0, ch:0, tl:0 }; if (!UI.lastT) UI.lastT = {};
  } catch (e) {}
}
function setW(w) {
  const a = $('aside');
  if (innerWidth <= 800) { a.style.width = ''; return; }
  a.style.width = Math.round(Math.max(240, Math.min(w, innerWidth * .8))) + 'px';
}
function applyPane() {                                            // panneau de droite : ouvert (coulisse) ou refermé (le graphique reprend toute la largeur)
  const op = !!UI.open, a = $('aside'); a.classList.toggle('closed', !op); $('#split').hidden = !op;
  $('#pane-ind').hidden = UI.tab !== 'ind'; $('#pane-perf').hidden = UI.tab !== 'perf'; $('#pane-screener').hidden = UI.tab !== 'screener';
  $('#pane-earn').hidden = UI.tab !== 'earn'; $('#pane-ana').hidden = UI.tab !== 'ana';
  document.querySelectorAll('#rtb button').forEach(b => b.classList.toggle('on', op && b.dataset.t === UI.open));
  if (op) { setW(UI.w[UI.tab]); if (UI.tab === 'perf') { renderPerf(); loadPerf(); } if (UI.tab === 'screener') loadScreener(); if (UI.tab === 'earn') loadEarn(); if (UI.tab === 'ana') loadAna(); }
}
function setTab(t, toggle) {
  if (toggle && UI.open === t) UI.open = ''; else { UI.open = t; UI.tab = t; }
  applyPane(); uiSave();
}
function syncReg() {
  document.querySelectorAll('#reg button').forEach(b => b.classList.toggle('on', b.dataset.r === UI.reg));
  const cs = REGIONS[UI.reg];
  if (!cs.includes(UI.country)) UI.country = '';
  const s = $('#pcountry');
  s.innerHTML = `<option value="">Tous les pays (${cs.length})</option>` + cs.map(c => `<option>${esc(c)}</option>`).join('');
  s.value = UI.country; s.hidden = cs.length < 2;
}
const fmtPct = v => (v > 0 ? '+' : '') + v.toFixed(2).replace('.', ',') + ' %';
function perfCell(v) {
  if (v == null) return '<td>–</td>';
  const a = Math.min(Math.abs(v) / 15, 1) * .3;
  return `<td style="background:${v >= 0 ? `rgba(38,166,154,${a})` : `rgba(239,83,80,${a})`};color:${v >= 0 ? '#0f766e' : '#b91c1c'}">${fmtPct(v)}</td>`;
}
function perfRows() {
  const cs = UI.country ? [UI.country] : REGIONS[UI.reg], r = [];
  cs.forEach(c => perfSymbols(c).forEach(([s, n]) => r.push({ s, n, c, p:PERF[s] })));
  const f = PF.trim().toLowerCase();
  if (f) r.splice(0, r.length, ...r.filter(x => x.n.toLowerCase().includes(f) || x.s.toLowerCase().includes(f)));
  if (UI.k) {
    const v = x => UI.k === 'n' ? x.n : (x.p ? x.p[UI.k] : null);
    r.sort((a, b) => { const x = v(a), y = v(b); if (x == null && y == null) return 0; if (x == null) return 1; if (y == null) return -1;
      return (UI.k === 'n' ? x.localeCompare(y) : x - y) * UI.dir; });
  }
  return r;
}
function renderPerf() {
  const th = COLS.map(([k, l]) => `<th${k !== 'price' ? ` data-k="${k}"` : ''}>${l}${UI.k === k ? (UI.dir === 1 ? ' ▲' : ' ▼') : ''}</th>`).join('');
  const tb = perfRows().map(r => `<tr data-s="${esc(r.s)}" data-n="${esc(r.n)}" data-c="${esc(r.c)}"${r.s === ST.sym ? ' class="on"' : ''}>`
    + `<td class="nm"><b>${esc(r.n)}</b><small>${esc(r.s)}</small></td>`
    + `<td>${r.p ? r.p.price.toLocaleString('fr-FR', { maximumFractionDigits:2 }) : '…'}</td>`
    + ['d1','w1','m1','m3','m6','ytd','y1'].map(k => perfCell(r.p ? r.p[k] : null)).join('') + '</tr>').join('');
  $('#ptab').innerHTML = `<thead><tr>${th}</tr></thead><tbody>${tb}</tbody>`;
}
async function loadUniv(c) {
  const k = UKEY[c]; if (!k || UNIV[c] || UFAIL[c]) return;
  $('#pstat').textContent = `Récupération de la liste : ${c}…`;
  try {
    const j = await (await fetch('/api/universe?c=' + k)).json();
    if (j.error) throw new Error(j.error);
    UNIV[c] = j.list; renderPerf();
  } catch (e) { UFAIL[c] = e.message; }
}
async function loadPerf(force) {
  const my = ++preq, cs = UI.country ? [UI.country] : REGIONS[UI.reg], errs = [];
  if (force) cs.forEach(c => { delete UFAIL[c]; if (UKEY[c]) delete UNIV[c]; });
  for (const c of cs) {
    if (my !== preq) return;
    await loadUniv(c); if (my !== preq) return;
    const syms = perfSymbols(c).map(a => a[0]);
    const todo = syms.filter(s => force || !PTIME[s] || Date.now() - PTIME[s] > 300000);
    for (let i = 0; i < todo.length; i += CHUNK) {
      if (my !== preq) return;
      $('#pstat').textContent = `Chargement : ${c} ${Math.min(i + CHUNK, todo.length)}/${todo.length}…`;
      const lot = todo.slice(i, i + CHUNK);
      try {
        const j = await (await fetch('/api/perf?symbols=' + encodeURIComponent(lot.join(',')))).json();
        if (my !== preq) return;
        if (j.error) throw new Error(j.error);
        Object.assign(PERF, j.data); lot.forEach(s => PTIME[s] = Date.now()); renderPerf();
      } catch (e) { errs.push(c); break; }
    }
  }
  if (my !== preq) return;
  const msg = [];
  cs.forEach(c => { if (UFAIL[c]) msg.push(`liste complète indisponible pour ${c} (${UFAIL[c]}), liste réduite affichée`); });
  if (errs.length) msg.push(`données indisponibles : ${[...new Set(errs)].join(', ')}`);
  $('#pstat').textContent = msg.length ? msg.join(' · ')
    : `${perfRows().length} sociétés` + (PF.trim() ? ' (filtre actif)' : '');
}
$('#rtb').addEventListener('click', e => { const b = e.target.closest('button'); if (b) setTab(b.dataset.t, true); });
$('#reg').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  UI.reg = b.dataset.r; UI.country = ''; syncReg(); renderPerf(); loadPerf(); uiSave();
});
$('#pcountry').addEventListener('change', e => { UI.country = e.target.value; renderPerf(); loadPerf(); uiSave(); });
$('#pfilter').addEventListener('input', e => { PF = e.target.value; renderPerf(); });
$('#prefresh').addEventListener('click', () => loadPerf(true));
$('#ptab').addEventListener('click', e => {
  const th = e.target.closest('th');
  if (th) {
    const k = th.dataset.k; if (!k) return;
    const d0 = k === 'n' ? 1 : -1;
    if (UI.k === k) { if (UI.dir === d0) UI.dir = -d0; else UI.k = null; } else { UI.k = k; UI.dir = d0; }
    renderPerf(); uiSave(); return;
  }
  const tr = e.target.closest('tbody tr');
  if (tr) { choose({ symbol:tr.dataset.s, name:tr.dataset.n, exch:tr.dataset.c });
    document.querySelectorAll('#ptab tbody tr').forEach(r => r.classList.toggle('on', r === tr)); }
});

/* ================= Onglet « Analyse » : fiche approfondie de la société affichée (Moning + Bourseur + états financiers Yahoo) ================= */
const AF = { sym:'', d:null };
const nf = (v, d = 2) => v == null || isNaN(v) ? '–' : (+v).toLocaleString('fr-FR', { maximumFractionDigits:d });
const nbig = v => { if (v == null) return '–'; const a = Math.abs(v); return a >= 1e12 ? nf(v / 1e12, 2) + ' Bn' : a >= 1e9 ? nf(v / 1e9, 1) + ' Md' : a >= 1e6 ? nf(v / 1e6, 0) + ' M' : nf(v, 0); };
function anaSync() {                                              // l'onglet porte le ticker de la société affichée (TTE, AAPL…)
  try {
    const b = $('#anab'); if (!b) return;
    b.textContent = (ST.sym || '').split('.')[0].toUpperCase() || 'Analyse';
    b.title = 'Analyse approfondie : ' + (ST.name || ST.sym || '');
    if (UI.open === 'ana') loadAna();
  } catch (e) {}
}
function chBar(vals, labs, o = {}) {
  const nums = vals.filter(v => v != null);
  if (!nums.length) return '<p class="mut" style="margin:10px 6px">Données indisponibles</p>';
  const W = 320, H = 150, pl = 8, pr = 8, pt = 18, pb = 22, n = vals.length, mx = Math.max(0, ...nums), mn = Math.min(0, ...nums), rg = (mx - mn) || 1;
  const y = v => pt + (mx - v) / rg * (H - pt - pb), bw = (W - pl - pr) / n, f = o.fmt || (v => nf(v, 1));
  let s = `<svg viewBox="0 0 ${W} ${H}" class="chs"><line x1="${pl}" x2="${W - pr}" y1="${y(0)}" y2="${y(0)}" stroke="#cbd5e1"/>`;
  vals.forEach((v, i) => {
    const x = pl + i * bw + bw * .18, w = bw * .64, cx = x + w / 2;
    s += `<text x="${cx}" y="${H - 6}" text-anchor="middle" class="cl2">${esc(labs[i])}</text>`;
    if (v == null) return;
    const y0 = y(0), y1 = y(v), top = Math.min(y0, y1), h = Math.max(1.5, Math.abs(y1 - y0)), col = v < 0 ? '#ef5350' : (o.col || '#2962ff');
    s += `<rect x="${x}" y="${top}" width="${w}" height="${h}" rx="3" fill="${col}" opacity="${o.p && o.p[i] ? .4 : (i === n - 1 ? 1 : .8)}"/><text x="${cx}" y="${v < 0 ? y1 + 11 : top - 4}" text-anchor="middle" class="cv">${esc(f(v))}</text>`;
  });
  return s + '</svg>';
}
function chLine(vals, labs, o = {}) {
  const pts = vals.map((v, i) => ({ v, i })).filter(p => p.v != null);
  if (pts.length < 2) return '<p class="mut" style="margin:10px 6px">Données indisponibles</p>';
  const W = 320, H = 150, pl = 14, pr = 14, pt = 18, pb = 22, n = vals.length, mx = Math.max(...pts.map(p => p.v)), mn = Math.min(...pts.map(p => p.v)), rg = (mx - mn) || 1;
  const X = i => pl + (n === 1 ? 0 : i / (n - 1)) * (W - pl - pr), Y = v => pt + (mx - v) / rg * (H - pt - pb), f = o.fmt || (v => nf(v, 1)), col = o.col || '#2962ff';
  const path = pts.map((p, k) => (k ? 'L' : 'M') + X(p.i) + ' ' + Y(p.v)).join(' ');
  let s = `<svg viewBox="0 0 ${W} ${H}" class="chs"><path d="${path} L${X(pts[pts.length - 1].i)} ${H - pb} L${X(pts[0].i)} ${H - pb} Z" fill="${col}" opacity=".1"/><path d="${path}" fill="none" stroke="${col}" stroke-width="2.2"/>`;
  pts.forEach(p => { s += `<circle cx="${X(p.i)}" cy="${Y(p.v)}" r="3.2" fill="${col}"/><text x="${X(p.i)}" y="${Y(p.v) - 7}" text-anchor="middle" class="cv">${esc(f(p.v))}</text>`; });
  labs.forEach((l, i) => { if (n <= 8 || i % 2 === 0) s += `<text x="${X(i)}" y="${H - 6}" text-anchor="middle" class="cl2">${esc(l)}</text>`; });
  return s + '</svg>';
}
const aCard = (t, body) => `<section class="ac"><h4>${t}</h4>${body}</section>`;
const aTile = (l, v, sub) => `<div class="at"><span>${esc(l)}</span><b>${esc(v || '–')}</b>${sub ? `<small>${esc(sub)}</small>` : ''}</div>`;
const aCh = (t, svg) => `<div class="ach"><b>${esc(t)}</b>${svg}</div>`;
const pillCls = t => { t = (t || '').toLowerCase(); return /défavorable|negatif|négatif|vendre/.test(t) ? 'r' : /favorable|achat|positif/.test(t) ? 'g' : /neutre|conserver|mitig/.test(t) ? 'o' : ''; };
function renderAna(d) {
  const m = d.moning || {}, b = d.bourseur || {}, y = d.yahoo || {}, S = d.sources || {}, cur = d.currency || '', L = d.liens || {};
  const ms = m.stats || {}, mv = m.valo || {}, md = m.div || {}, bc = b.chiffres || {}, yrs = (y.years || []).map(String);
  const avert = ['moning', 'bourseur', 'yahoo'].filter(k => S[k] && S[k] !== 'ok').map(k => `<div class="aw">${{ moning:'Moning', bourseur:'Bourseur', yahoo:'États financiers Yahoo' }[k]} : ${esc(S[k])}</div>`).join('');
  const pc = v => v == null ? '–' : nf(v, 1) + ' %';
  const eur = v => nf(v, 2) + (cur ? ' ' + cur : '');
  let h = `<div class="ah"><div><h3>${esc(d.name)}</h3><span class="atk">${esc(d.symbol)}${m.isin ? ' · ' + esc(m.isin) : ''}${cur ? ' · ' + esc(cur) : ''}</span></div>`
    + `<div class="acs">${b.verdict ? `<span class="pill ${pillCls(b.verdict)}">${esc(b.verdict)}</span>` : ''}${Object.entries(b.scores || {}).filter(([k, v]) => v).map(([k, v]) => `<span class="pill ${pillCls(v)}" title="${esc(k)}">${esc(k)} : ${esc(v)}</span>`).join('')}</div></div>`
    + avert + (b.synthese ? `<p><b>${esc(b.synthese)}</b></p>` : '');
  // Statistiques
  h += aCard('Statistiques', `<div class="ag">${aTile('Rendement', ms.rendement || (b.calendrier || {}).rendement)}${aTile('Croissance div. / 5 ans', ms.croiss_div)}${aTile('Capitalisation', ms.capi || bc.capi)}${aTile('PER', ms.per || bc.per)}${aTile('Bêta', ms.beta)}${aTile('Bénéfice / action', ms.bpa)}${bc.roe ? aTile('ROE', bc.roe) : ''}${bc.ev_ebitda ? aTile('EV / EBITDA', bc.ev_ebitda) : ''}${bc.dette_equity ? aTile('Dette / fonds propres', bc.dette_equity) : ''}</div>`);
  // À propos
  const ap = m.apropos || (b.profil || '') || d.about_yahoo || '';
  if (ap) h += aCard('À propos', ap.split('\n').map(p => `<p>${esc(p)}</p>`).join('') + (b.fondamentaux ? `<p class="mut">${esc(b.fondamentaux)}</p>` : ''));
  // Performance
  const pf = [...Object.entries(b.perfs || {}), ...Object.entries(m.perf || {}).map(([k, v]) => ['Moning · ' + k, v])];
  if (pf.length) h += aCard('Performance', `<div class="ag">${pf.map(([k, v]) => aTile(k, v)).join('')}</div>`);
  // Valorisation
  h += aCard('Valorisation', `<div class="ag">${aTile('Prix / valeur comptable', mv.pb)}${aTile('Taux de distribution', mv.payout)}${aTile('Ratio PEG', mv.peg)}${aTile('Prix / chiffre d’affaires', mv.ps)}${aTile('Prix / FCF', mv.pfcf)}${aTile('Valeur d’entreprise / CA', mv.evr)}</div>`
    + `<div class="cg">${aCh('Historique du PER (cours de fin d’exercice / BPA, estimé)', chLine(y.per || [], yrs, { col:'#7c3aed', fmt:v => nf(v, 1) + ' x' }))}</div>`);
  // Dividendes
  const cal = b.calendrier || {};
  const mois = Object.entries(md.mois || {}).sort((a, c) => c[0] - a[0]).map(([a, v]) => `<p class="mut">Dividendes en ${esc(a)} : ${esc(v)}</p>`).join('');
  const dv = y.div_an || [];
  h += aCard('Dividendes', `<div class="ag">${aTile('Sans interruption', md.sans_interruption)}${aTile('Fréquence', md.frequence)}${aTile('Montant annuel à terme', md.montant || cal.dividende)}${aTile('Ex-dividende', md.ex_div)}${aTile('Rendement', cal.rendement || ms.rendement)}${aTile('Taux de distribution', cal.payout || mv.payout)}</div>`
    + `<div class="cg">${aCh('Historique du dividende par an' + (cur ? ' (' + cur + ')' : ''), chBar(dv.map(x => x.v), dv.map(x => String(x.y).slice(2)), { col:'#0d9488', fmt:v => nf(v, 2), p:dv.map(x => x.p) }))}</div>` + mois
    + ((b.hist_div || []).length ? `<table><tr><th>Date de détachement</th><th>Montant</th></tr>${b.hist_div.map(x => `<tr><td>${esc(x.date)}</td><td>${esc(x.montant)}</td></tr>`).join('')}</table>` : '')
    + ((cal.echeances || []).length ? `<table><tr><th>Prochaines échéances</th><th></th></tr>${cal.echeances.map(x => `<tr><td>${esc(x.quand)}</td><td>${esc(x.quoi)}<br><span class="mut">${esc(x.detail)}</span></td></tr>`).join('')}</table>` : ''));
  // Actions en circulation
  const sh = y.shares || [];
  if (sh.length > 1) h += aCard('Nombre d’actions en circulation', `<div class="cg">${aCh('Actions (millions)', chLine(sh.map(x => x.v / 1e6), sh.map(x => String(x.y).slice(2)), { col:'#2962ff', fmt:v => nf(v, 0) }))}</div>`);
  // Objectif de cours & consensus
  const ob = b.objectif || {};
  if (ob.moyen || b.reco) {
    let c = `<div class="ag">${aTile('Objectif moyen', ob.moyen, ob.ecart ? ob.ecart + ' vs cours' : '')}${aTile('Recommandation', b.reco, b.score_consensus)}${aTile('Analystes', b.n_analystes)}</div>`;
    if (ob.bas != null && ob.haut != null && ob.v != null && ob.haut > ob.bas) c += `<div class="rng"><i style="left:${Math.min(100, Math.max(0, (ob.v - ob.bas) / (ob.haut - ob.bas) * 100))}%"></i><em style="left:0">${nf(ob.bas, 2)}</em><em style="left:50%">objectif moyen ${nf(ob.v, 2)}</em><em style="left:100%">${nf(ob.haut, 2)}</em></div>`;
    if (b.achat) { const t = b.achat.reduce((a, c2) => a + c2, 0) || 1; c += `<div class="bar"><i style="width:${b.achat[0] / t * 100}%;background:#22c55e">${b.achat[0]} Achat</i><i style="width:${b.achat[1] / t * 100}%;background:#f59e0b">${b.achat[1]} Conserver</i><i style="width:${b.achat[2] / t * 100}%;background:#ef4444">${b.achat[2]}</i></div>`; }
    h += aCard('Objectif de cours et consensus des analystes', c);
  }
  // Segmentation des ventes
  h += aCard('Segmentation des ventes', `<p class="mut">La répartition du chiffre d’affaires par activité est dessinée en JavaScript sur Moning : elle n’est pas lisible automatiquement. <a class="lk" href="${esc(L.moning)}#performanceComparsion" target="_blank" rel="noopener">Voir la segmentation sur Moning ↗</a></p>`);
  // Finances / croissance / rentabilité / santé
  const cb = (t, a, o) => aCh(t, chBar(a || [], yrs, o)), big = v => nbig(v);
  h += aCard('Finances', `<div class="cg">${cb('Chiffre d’affaires' + (cur ? ' (' + cur + ')' : ''), y.rev, { fmt:big, col:'#2962ff' })}${cb('Free cash flow', y.fcf, { fmt:big, col:'#0d9488' })}${cb('Bénéfice par action', y.eps, { fmt:v => nf(v, 2), col:'#7c3aed' })}${cb('Bénéfice net', y.net, { fmt:big, col:'#f59e0b' })}</div>`
    + ((b.comptes || []).length ? `<table><tr><th>Exercice</th><th>Chiffre d’affaires</th><th>Résultat net</th><th>Marge nette</th></tr>${b.comptes.map(x => `<tr><td>${esc(x.annee)}</td><td>${esc(x.ca)}</td><td>${esc(x.net)}</td><td>${esc(x.marge)}</td></tr>`).join('')}</table>` : ''));
  h += aCard('Croissance annuelle', `<div class="cg">${cb('Croissance du chiffre d’affaires', y.g_rev, { fmt:pc })}${cb('Croissance du free cash flow', y.g_fcf, { fmt:pc, col:'#0d9488' })}${cb('Croissance du bénéfice net', y.g_net, { fmt:pc, col:'#f59e0b' })}${cb('Croissance du BPA', y.g_eps, { fmt:pc, col:'#7c3aed' })}</div>`);
  h += aCard('Rentabilité', `<div class="cg">${cb('Marge opérationnelle', y.m_op, { fmt:pc })}${cb('Marge nette', y.m_net, { fmt:pc, col:'#0d9488' })}${cb('Retour sur capitaux propres (ROE)', y.roe, { fmt:pc, col:'#7c3aed' })}</div>`);
  h += aCard('Santé financière', `<div class="cg">${cb('Couverture des intérêts', y.cover, { fmt:v => nf(v, 1) + ' x' })}${cb('Ratio de distribution (bénéfice)', y.payout, { fmt:pc, col:'#f59e0b' })}${cb('Ratio de distribution (FCF)', y.payout_fcf, { fmt:pc, col:'#0d9488' })}${cb('Dette / capitaux propres', y.de, { fmt:pc, col:'#ef4444' })}${cb('Dette / EBITDA', y.debt_ebitda, { fmt:v => nf(v, 1) + ' x', col:'#7c3aed' })}</div>`);
  // Atouts / risques
  if ((b.atouts || []).length || (b.risques || []).length)
    h += aCard('Atouts stratégiques et risques à surveiller', `<div class="two"><div class="pro"><h5>✅ Atouts stratégiques</h5><ul>${(b.atouts || []).map(x => `<li>${esc(x)}</li>`).join('')}</ul></div><div class="con"><h5>⚠️ Risques à surveiller</h5><ul>${(b.risques || []).map(x => `<li>${esc(x)}</li>`).join('')}</ul></div></div>`);
  h += `<p class="mut lks">Sources : <a href="${esc(L.moning)}" target="_blank" rel="noopener">Moning ↗</a><a href="${esc(L.bourseur)}" target="_blank" rel="noopener">Bourseur ↗</a> · graphiques financiers recalculés à partir des états financiers Yahoo Finance. Information uniquement, pas un conseil en investissement.</p>`;
  return h;
}
async function loadAna() {
  const box = $('#ana'); if (!box || UI.tab !== 'ana' || !ST.sym) return;
  const sym = ST.sym;
  if (AF.sym === sym && AF.d) { if (!box.firstChild || box.dataset.sym !== sym) { box.innerHTML = renderAna(AF.d); box.dataset.sym = sym; } return; }
  AF.sym = sym; AF.d = null; box.dataset.sym = ''; box.innerHTML = '<p class="mut" style="padding:12px">Chargement de l’analyse (Moning, Bourseur, états financiers)… quelques secondes.</p>';
  try {
    const d = await get('/api/analyse?symbol=' + encodeURIComponent(sym));
    if (ST.sym !== sym) return;
    AF.d = d; box.innerHTML = renderAna(d); box.dataset.sym = sym;
  } catch (e) { if (AF.sym === sym) { AF.sym = ''; box.innerHTML = `<p class="aw">Analyse indisponible : ${esc(e.message)}</p>`; } }
}

/* ================= Onglet Screener (widget TradingView) ================= */
/* === Interception globale du screener TradingView -> graphique local === */
(function() {
  // 1. Patch window.open : bloque les ouvertures vers tradingview.com/symbols/
  const _origOpen = window.open;
  window.open = function(url, ...rest) {
    try {
      const u = String(url || '');
      if (u.includes('tradingview.com') && u.includes('/symbols/')) {
        const m = u.match(/\/symbols\/([A-Z0-9]+)-([A-Z0-9\.\-_]+)/i);
        if (m) {
          const tvSym = (m[1].toUpperCase() + ':' + m[2].toUpperCase()).replace(/-PA$/,'.PA');
          // déclenche notre recherche locale
          if (window._scOpenFromTv) window._scOpenFromTv(tvSym);
          return null; // bloque l'onglet
        }
      }
    } catch {}
    return _origOpen.apply(this, [url, ...rest]);
  };

  // 2. Extraction robuste du symbole depuis un event (composedPath pour Shadow DOM)
  window._scExtractTv = function(e) {
    const path = (e.composedPath && e.composedPath()) || [e.target];
    for (const el of path) {
      if (!el || !el.getAttribute) continue;
      // href direct
      const href = el.getAttribute('href') || '';
      let m = href.match(/\/symbols\/([A-Z0-9]+)-([A-Z0-9\.\-_]+)/i);
      if (m) return m[1].toUpperCase() + ':' + m[2].toUpperCase();
      m = href.match(/symbol=([A-Z]+%3A[A-Z0-9\.\-_]+)/i);
      if (m) try { return decodeURIComponent(m[1]); } catch {}
      const ds = el.getAttribute('data-symbol') || el.getAttribute('data-ticker') || el.getAttribute('aria-label') || '';
      if (ds && /[A-Z]+:[A-Z0-9\.\-]+/.test(ds)) {
        const mm = ds.match(/[A-Z]+:[A-Z0-9\.\-]+/);
        if (mm) return mm[0];
      }
      // texte court type EXCHANGE:SYMBOL
      const txt = (el.textContent || '').trim().slice(0,40);
      if (/^[A-Z]{1,8}:[A-Z0-9\.\-_]{1,15}$/.test(txt)) return txt;
    }
    return null;
  };

  window._scOpenFromTv = async function(tvSym) {
    const base = tvSym.split(':').pop().replace(/\.PA$/i,'').replace(/\.AS$/i,'').replace(/\.BR$/i,'').replace(/\.LS$/i,'');
    const q = base;
    try {
      status('Chargement de ' + q + '…');
      const r = await fetch('/api/search?q=' + encodeURIComponent(q));
      const j = await r.json();
      const hits = j.results || j || [];
      if (hits.length) {
        // si le symbole exact existe, on le prend
        let pick = hits[0];
        const upQ = q.toUpperCase();
        const exact = hits.find(h => h.symbol && h.symbol.toUpperCase().startsWith(upQ));
        if (exact) pick = exact;
        choose(pick);
      } else {
        status('Symbole ' + q + ' introuvable', true);
      }
    } catch (err) {
      status('Erreur: ' + err.message, true);
    }
  };

  // 3. Listener global en capture : intercepte tout clic dans le screener
  document.addEventListener('click', (e) => {
    const container = document.getElementById('tv-screener-container');
    if (!container) return;
    // le clic est-il dans le screener ?
    const path = (e.composedPath && e.composedPath()) || [];
    const inside = path.some(n => n === container) || container.contains(e.target) || (e.target && e.target.closest && e.target.closest('tv-screener'));
    if (!inside) return;
    const tvSym = window._scExtractTv(e);
    if (!tvSym) return;
    e.preventDefault();
    e.stopPropagation();
    e.stopImmediatePropagation();
    window._scOpenFromTv(tvSym);
  }, true);
})();

let screenerLoaded = false;
const SC = { rows:{}, k:'market_cap_basic', dir:-1, q:'' };
const SC_OWN = { eu_top:'eu', fr_top:'fr', euronext:'euronext', germany:'germany', uk:'uk', italy:'italy', spain:'spain', switzerland:'switzerland', sweden:'sweden', poland:'poland' };
const scTop = () => SC_OWN[$('#sc-country').value] || '';
function scWidget() {
  const c = $('#tv-screener-container'); c.innerHTML = '';
  const el = document.createElement('tv-screener');
  el.setAttribute('screener-type', 'stock');
  el.setAttribute('screen', $('#sc-screen').value);
  el.setAttribute('columns', $('#sc-columns').value);
  const mkt = $('#sc-country').value; if (mkt) el.setAttribute('market', mkt);
  el.setAttribute('hide-toolbar', '');
  el.style.width = '100%'; el.style.height = '100%';
  c.appendChild(el);
}
const scVal = (x, k) => k === 'n' || k === 'c' ? x[k] : k === 'market_cap_basic' ? x.ceur : x.v[k];
function scFmt(x, col) {
  const [k, , f] = col, v = x.v[k];
  if (v == null || v === '') return '–';
  return f === 'txt' ? esc(v) : f === 'p' ? pc(v) : f === 'pl' ? fnum(v, 1) + ' %' : f === 'n1' ? fnum(v, 1)
    : f === 'cap' ? fbig(v) + (k === 'market_cap_basic' || k === 'enterprise_value_fq' || k === 'net_debt' || k === 'total_debt' ? ' ' + esc(x.cur) : '') : fnum(v);
}
function scDrawRows(r) {
  const j = SC.rows[r], q = SC.q.trim().toLowerCase(), vue = j.vues[$('#sc-columns').value] || j.vues.valuation || [];
  if (SC.k !== 'n' && SC.k !== 'c' && !vue.some(c => c[0] === SC.k)) { SC.k = vue.length ? vue[0][0] : 'n'; SC.dir = -1; }
  let rows = j.rows.map((x, i) => ({ ...x, i: i + 1 })).filter(x => !q || (x.n + ' ' + x.tv + ' ' + (x.v.sector || '')).toLowerCase().includes(q));
  const k = SC.k, d = SC.dir, txt = k === 'n' || k === 'c' || k === 'sector';
  rows.sort((a, b) => txt ? d * -String(scVal(a, k) ?? '').localeCompare(String(scVal(b, k) ?? ''), 'fr')
    : (scVal(a, k) == null) - (scVal(b, k) == null) || d * ((scVal(a, k) ?? 0) - (scVal(b, k) ?? 0)));      // valeurs absentes toujours en bas
  const fl = h => SC.k === h ? (SC.dir > 0 ? ' ▲' : ' ▼') : '';
  $('#sc-count').textContent = `${rows.length} / ${j.rows.length} sociétés (siège européen, doubles cotations fusionnées)` + (j.erreurs ? ` · ${j.erreurs} marché(s) injoignable(s) : liste possiblement incomplète` : '');
  $('#sc-tbl').innerHTML = `<tr><th data-k="n" class="sk">Société${fl('n')}</th><th data-k="c" class="sk">Pays${fl('c')}</th>`
    + vue.map(c => `<th data-k="${c[0]}" class="sk">${esc(c[1])}${fl(c[0])}</th>`).join('') + '</tr>'
    + rows.map(x => `<tr class="cl" data-y="${esc(x.y || '')}" data-n="${esc(x.n)}"><td><a href="#" class="sclk" title="Afficher le graphique de ${esc(x.n)}"><b>${esc(x.n)}</b></a><br><small>${esc(x.tv)}</small></td><td>${esc(x.c)}</td>`
      + vue.map(c => `<td>${scFmt(x, c)}</td>`).join('') + '</tr>').join('');
}
async function scTable(r) {
  const c = $('#tv-screener-container');
  c.innerHTML = '<div style="display:flex;flex-direction:column;height:100%"><div class="scbar"><input id="sc-q" placeholder="Filtrer par nom, symbole ou secteur…" style="flex:1"><span id="sc-count" class="empty"></span></div><div class="ptw" style="flex:1;overflow:auto"><table id="sc-tbl"></table></div></div>';
  $('#sc-tbl').innerHTML = '<tr><td>Chargement…</td></tr>';
  try { SC.rows[r] = SC.rows[r] || await get('/api/screener?r=' + r); }
  catch (e) { if (scTop() === r) $('#sc-tbl').innerHTML = `<tr><td>Liste indisponible : ${esc(e.message)}</td></tr>`; return; }
  if (scTop() !== r) return;
  $('#sc-q').value = SC.q;
  $('#sc-q').oninput = e => { SC.q = e.target.value; scDrawRows(r); };
  $('#sc-tbl').onclick = async e => {
    const th = e.target.closest('th.sk');
    if (th) { const k = th.dataset.k; if (SC.k === k) SC.dir = -SC.dir; else { SC.k = k; SC.dir = ['n', 'c', 'sector'].includes(k) ? 1 : -1; } scDrawRows(r); return; }
    const tr = e.target.closest('tr.cl'); if (!tr) return; e.preventDefault();
    const nom = tr.dataset.n; let ok = tr.dataset.y ? await choose({ symbol: tr.dataset.y, name: nom, exch: '' }) : false;
    if (ok === false) { try { const rs = (await get('/api/search?q=' + encodeURIComponent(nom))).results || []; if (rs[0]) choose(rs[0]); else status(`Aucun symbole trouvé pour « ${nom} »`, true); } catch (err) { status(`Aucun symbole trouvé pour « ${nom} »`, true); } }
  };
  scDrawRows(r);
}
function scRefresh() {
  const t = scTop();
  $('#sc-screen').style.display = t ? 'none' : '';
  if (t) scTable(t); else scWidget();
}
function loadScreener() {
  if (UI.tab !== 'screener') return;
  if (!document.querySelector('script[src*="tv-screener.js"]')) {
    const sc = document.createElement('script');
    sc.type = 'module'; sc.src = 'https://widgets.tradingview-widget.com/w/fr/tv-screener.js';
    document.head.appendChild(sc);
  }
  [['#sc-country', scRefresh], ['#sc-screen', scRefresh], ['#sc-columns', () => { const t = scTop(); if (t && SC.rows[t] && $('#sc-q')) scDrawRows(t); else scRefresh(); }]].forEach(([sid, fn]) => {
    const el = $(sid); if (!el || el.dataset.scbound) return; el.dataset.scbound = '1';
    el.addEventListener('change', fn);
  });
  if (!$('#tv-screener-container').hasChildNodes()) scRefresh();
}


/* ================= Fiche société ================= */
const FICHE = {}; let freq = 0;
const fnum = (v, d = 2) => v == null ? '–' : v.toLocaleString('fr-FR', { maximumFractionDigits:d });
function fbig(v) {
  if (v == null) return '–'; const a = Math.abs(v);
  if (a >= 1e12) return fnum(v / 1e12) + ' Bn'; if (a >= 1e9) return fnum(v / 1e9) + ' Md';
  if (a >= 1e6) return fnum(v / 1e6) + ' M'; return fnum(v, 0);
}
const pc = v => v == null ? '–' : `<span class="${v > 0 ? 'up' : v < 0 ? 'dn' : ''}">${fmtPct(v)}</span>`;
const vide = m => `<p class="empty">${m}</p>`;
const table = (heads, rows) => `<div class="scr"><table><tr>${heads.map(h => `<th>${h}</th>`).join('')}</tr>${rows.map(r => `<tr>${r.map(c => `<td>${c}</td>`).join('')}</tr>`).join('')}</table></div>`;
let CURS = '', CURJ = null, FS = 'finances';
const CACHE = {};                                               // résultats par onglet et par symbole
async function get(url) { const j = await (await fetch(url)).json(); if (j.error) throw new Error(j.error); return j; }
const still = (s, tab) => s === CURS && tab === FS && !$('#fiche').hidden;

/* ---- widgets officiels TradingView (Finances, Actualités) ---- */
function tvWidget(file, cfg) {
  const box = $('#fbody'); box.innerHTML = '<div class="tvbox"></div>';
  const w = document.createElement('div'); w.className = 'tradingview-widget-container';
  const inner = document.createElement('div'); inner.className = 'tradingview-widget-container__widget'; w.appendChild(inner);
  const sc = document.createElement('script'); sc.src = 'https://s3.tradingview.com/external-embedding/' + file; sc.async = true;
  sc.text = JSON.stringify({ width:'100%', height:'100%', colorTheme:'light', isTransparent:false, locale:'fr', ...cfg });
  w.appendChild(sc); box.firstChild.appendChild(w);
}
async function infoSym() {
  const s = CURS; if (CURJ && CURJ.symbol === s) return CURJ;
  const p = FICHE[s] || (FICHE[s] = get('/api/info?symbol=' + encodeURIComponent(s)).catch(e => { delete FICHE[s]; throw e; }));
  const j = await p; if (s === CURS) CURJ = j; return j;
}
async function tabTv(kind) {
  const s = CURS, tab = FS; $('#fbody').innerHTML = vide('Chargement…');
  let j; try { j = await infoSym(); } catch (e) { if (still(s, tab)) $('#fbody').innerHTML = vide('Symbole TradingView introuvable : ' + esc(e.message)); return; }
  if (!still(s, tab)) return;
  if (!j.tv) { $('#fbody').innerHTML = vide('Cet onglet n’existe pas pour un indice ou une matière première (actions uniquement).'); return; }
  tvWidget('embed-widget-financials.js', { symbol:j.tv, displayMode:'regular', largeChartUrl:'' });
}

/* ---- Actualités (Google Actualités + Yahoo, construites côté serveur : le widget TradingView restait vide) ---- */
async function tabActus() {
  const s = CURS, tab = FS, k = s + '|news';
  $('#fbody').innerHTML = vide('Chargement…');
  let j0 = null; try { j0 = await infoSym(); } catch (e) { /* on tente quand même avec le symbole */ }
  if (!still(s, tab)) return;
  const nom = (j0 && j0.name) || (ST.sym === s ? ST.name : '') || s;
  try { CACHE[k] = CACHE[k] || await get(`/api/news?symbol=${encodeURIComponent(s)}&name=${encodeURIComponent(nom)}`); }
  catch (e) { if (still(s, tab)) $('#fbody').innerHTML = vide('Actualités indisponibles : ' + esc(e.message)); return; }
  if (!still(s, tab)) return;
  const j = CACHE[k];
  const tv = j0 && j0.tv_actus ? `<p class="empty"><a class="lk" href="${esc(j0.tv_actus)}" target="_blank" rel="noopener">Voir aussi les actualités sur TradingView ↗</a></p>` : '';
  $('#fbody').innerHTML = tv + (j.items.length ? j.items.map((x, n) => `<div class="news" data-n="${n}"><a class="lk" href="${esc(x.url)}" target="_blank" rel="noopener">${esc(x.title)}</a><small>${esc(x.src)}${x.ts ? ' · ' + new Date(x.ts * 1000).toLocaleDateString('fr-FR') : ''}</small><button class="rd" data-n="${n}" title="Survolez pour lire ici ; cliquez pour garder le cadre ouvert">📖 Lire ici</button></div>`).join('') : vide('Aucune actualité trouvée pour ce titre.'));
  const bx = $('#fbody'); POP.row = null;
  bx.onmouseover = ev => { const row = ev.target.closest('.news'); if (!row || row === POP.row) return; POP.row = row; popSoon(row, j.items[+row.dataset.n]); };
  bx.onmouseout = ev => { const row = ev.target.closest('.news'); if (row && !row.contains(ev.relatedTarget)) { POP.row = null; popLater(); } };
  bx.onclick = ev => { const b = ev.target.closest('button.rd'); if (b) popOpen(b.closest('.news'), j.items[+b.dataset.n], true); };

}

/* ---- Mode lecture : texte épuré de l'article, affiché sous le titre ---- */
const ART = {};
function rendreArticle(a, x) {
  const corps = a.paras.map(p => p.k === 'h' ? `<h5>${esc(p.t)}</h5>` : `<p>${esc(p.t)}</p>`).join('');
  return `<div class="rdh"><b>${esc(a.title || x.title)}</b>${esc(a.site || x.src)}</div>${a.image ? `<img src="${esc(a.image)}" alt="" referrerpolicy="no-referrer" loading="lazy" onerror="this.remove()">` : ''}${corps}`
    + (a.chars < 500 ? '<p class="rdn">Texte court : l’article est peut-être réservé aux abonnés ou affiché par script. </p>' : '')
    + `<p><a class="lk" href="${esc(a.url || x.url)}" target="_blank" rel="noopener">Ouvrir l’article original ↗</a></p>`;
}
/* Cadre de lecture flottant : s'affiche au survol d'une actualité (clic sur « Lire ici » = le garder ouvert) */
const POP = { el:null, cur:null, row:null, tShow:0, tHide:0, pin:false };
function popEl() {
  if (POP.el) return POP.el;
  const e = POP.el = document.createElement('div'); e.id = 'rdpop'; e.className = 'rdr'; e.hidden = true; document.body.appendChild(e);
  e.addEventListener('mouseenter', () => clearTimeout(POP.tHide));
  e.addEventListener('mouseleave', () => popLater());
  e.addEventListener('click', ev => { if (ev.target.closest('.rdx')) popClose(); });
  return e;
}
function popClose() { clearTimeout(POP.tShow); clearTimeout(POP.tHide); POP.pin = false; POP.cur = null; POP.row = null; if (POP.el) POP.el.hidden = true; }
function popLater() { clearTimeout(POP.tShow); clearTimeout(POP.tHide); if (!POP.pin) POP.tHide = setTimeout(popClose, 300); }
function popSoon(row, x) { clearTimeout(POP.tShow); clearTimeout(POP.tHide); POP.tShow = setTimeout(() => popOpen(row, x, false), 350); }
function popPlace(row) {
  const e = POP.el, f = $('#fiche').getBoundingClientRect(), r = row.getBoundingClientRect(), side = f.left >= 420;
  const w = side ? Math.min(660, f.left - 16) : Math.max(300, f.width - 16);
  const top = side ? Math.max(8, Math.min(r.top - 10, innerHeight * .25)) : Math.min(r.bottom + 6, innerHeight * .4);
  Object.assign(e.style, { width:w + 'px', left:(side ? f.left - w - 8 : f.left + 8) + 'px', top:top + 'px', maxHeight:Math.max(200, innerHeight - top - 12) + 'px', overflow:'auto' });
}
async function popOpen(row, x, pin) {
  const e = popEl(); clearTimeout(POP.tShow); clearTimeout(POP.tHide);
  if (pin) POP.pin = true; else if (POP.cur !== x) POP.pin = false;
  POP.cur = x; e.hidden = false; popPlace(row);
  const head = '<div class="rdbar"><button class="rdx" title="Fermer">✕</button></div>';
  const draw = h => { if (POP.cur === x) e.innerHTML = head + h; };
  const lien = `<p><a class="lk" href="${esc(x.url)}" target="_blank" rel="noopener">Ouvrir l’article original ↗</a></p>`;
  if (ART[x.url]) return draw(rendreArticle(ART[x.url], x));
  draw('<p class="empty">Chargement de l’article…</p>');
  try { ART[x.url] = await get('/api/article?url=' + encodeURIComponent(x.url)); draw(rendreArticle(ART[x.url], x)); }
  catch (err) { delete ART[x.url]; draw(vide('Lecture impossible : ' + esc(err.message)) + lien); }
}
addEventListener('keydown', e => { if (e.key === 'Escape') popClose(); });

/* ---- Dossiers : résultats (Yahoo Finance) + dépôts réglementaires SEC EDGAR ---- */
const mio = v => v == null ? '–' : fnum(v / 1e6, 0) + ' M';
async function tabDossiers() {
  const s = CURS, tab = FS, nom = ST.sym === s ? (ST.name || '') : '', k = s + '|docs';
  $('#fbody').innerHTML = vide('Chargement…');
  let info = null; try { info = await infoSym(); } catch (e) { /* la partie SEC peut fonctionner seule */ }
  if (!still(s, tab)) return;
  let docs = CACHE[k];
  if (!docs) {
    try { docs = CACHE[k] = await get(`/api/docs?symbol=${encodeURIComponent(s)}&name=${encodeURIComponent((info && info.name) || nom)}`); }
    catch (e) { docs = { docs: [], note: 'Dépôts SEC indisponibles : ' + e.message }; }
  }
  if (!still(s, tab)) return;
  let rs = CACHE[s + '|resume'];
  if (!rs) { try { rs = CACHE[s + '|resume'] = await get(`/api/resume?symbol=${encodeURIComponent(s)}`); } catch (e) { rs = { profil: null, insights: [], erreur: e.message }; } }
  if (!still(s, tab)) return;
  const a = (u, t) => `<a class="lk" href="${esc(u)}" target="_blank" rel="noopener">${t} ↗</a>`;
  const liens = [];
  if (info && info.tv_dossiers) liens.push(a(info.tv_dossiers, 'Dossiers sur TradingView (présentations, transcriptions)'));
  if (info && info.google_earnings) liens.push(a(info.google_earnings, 'Résultats sur Google Finance'));
  if (info && info.website) liens.push(a(info.website, 'Site de la société'));
  const auj = new Date().toISOString().slice(0, 10), ea = (info && info.earnings) || [], qs = (info && info.quarters) || [], dev = (info && info.currency) || '';
  let h = liens.length ? `<p class="empty">${liens.join(' · ')}</p>` : '';
  h += '<p><b>1. Profil de la société</b>' + (rs.profil_source ? ` <small>(${esc(rs.profil_source)})</small>` : '') + '</p>'
    + (rs.profil ? `<p>${esc(rs.profil)}</p>` : vide('Profil indisponible pour ce titre' + (rs.erreur ? ' : ' + esc(rs.erreur) : '') + '.'));
  h += '<p><b>2. Résumé des résultats</b>' + (rs.insights_source ? ` <small>(${esc(rs.insights_source)})</small>` : '') + '</p>'
    + (rs.insights && rs.insights.length ? '<ul>' + rs.insights.map(i => `<li><b>${esc(i.titre)} :</b> ${esc(i.texte)}</li>`).join('') + '</ul>'
      : vide('Résumé des résultats indisponible pour ce titre.'));
  if (ea.length) h += '<p><b>Résultats (BPA) : publiés et à venir</b></p>' + table(['Date', 'BPA estimé', 'BPA publié', 'Surprise'],
    ea.map(e => [esc(e.date) + (e.rep == null && e.date >= auj ? ' <small>(à venir)</small>' : ''), fnum(e.est), fnum(e.rep), pc(e.sur)]));
  if (qs.length) h += `<p><b>Derniers trimestres</b> <small>(millions${dev ? ' de ' + esc(dev) : ''})</small></p>` + table(['Trimestre clos le', 'Chiffre d’affaires', 'Résultat net'],
    qs.map(q => [esc(q.date), mio(q.rev), mio(q.net)]));
  const ys = (info && info.years) || [];
  if (ys.length) h += `<p><b>Derniers exercices</b> <small>(millions${dev ? ' de ' + esc(dev) : ''})</small></p>` + table(['Exercice clos le', 'Chiffre d’affaires', 'Résultat net'],
    ys.map(q => [esc(q.date), mio(q.rev), mio(q.net)]));
  if (ea.filter(e => e.rep != null || e.date < auj).length < 2) h += vide('Historique des publications incomplet pour ce titre : les données gratuites sont peu fiables pour certaines sociétés françaises. La liste complète (résultats, présentations, transcriptions) est sur les Dossiers TradingView ci-dessus.');
  if (!ea.length && !qs.length && !ys.length) h += vide('Yahoo Finance ne fournit pas de résultats pour ce titre : utilisez le lien TradingView ci-dessus.');
  if (docs.docs.length) {
    const formes = [...new Set(docs.docs.map(d => d.form))];
    h += `<p><b>Dépôts réglementaires</b> <small>${esc(docs.societe)} · SEC EDGAR · ${a(docs.liste, 'liste complète')}</small></p>
      <div class="sub" id="fsub"><button class="on" data-f="">Tous</button>${formes.map(f => `<button data-f="${esc(f)}">${esc(f)}</button>`).join('')}</div><div id="fdoc"></div>`;
  } else if (docs.note) h += vide(esc(docs.note));
  $('#fbody').innerHTML = h;
  if (docs.docs.length) {
    const draw = f => $('#fdoc').innerHTML = table(['Date', 'Type', 'Description', 'Document'], docs.docs.filter(d => !f || d.form === f).map(d =>
      [esc(d.date), `<b>${esc(d.form)}</b><br><small>${esc(d.type)}</small>`, esc(d.desc), d.url ? a(d.url, 'Ouvrir') : '']));
    draw('');
    $('#fsub').onclick = e => { const b = e.target.closest('button'); if (!b) return; document.querySelectorAll('#fsub button').forEach(x => x.classList.toggle('on', x === b)); draw(b.dataset.f); };
  }
}

/* ---- Données techniques (calculées ici : oscillateurs, moyennes mobiles, pivots) ---- */
const TF = { '15m':['15 min', 59], '1h':['1 heure', 400], '1d':['1 jour', 900], '1wk':['1 semaine', 3650], '1mo':['1 mois', 'max'] };
let TFS = '1d';
const last = a => a[a.length - 1];
function techCalc(b) {
  const O = b.map(r => r[1]), H = b.map(r => r[2]), L = b.map(r => r[3]), C = b.map(r => r[4]), V = b.map(r => r[5]), n = C.length, i = n - 1;
  const g = a => a[i], g1 = a => a[i-1], g2 = a => a[i-2], ok = (...v) => v.every(x => x != null);
  const rsiA = (c, p) => { const u = c.map((v,k)=>k?Math.max(v-c[k-1],0):null), d = c.map((v,k)=>k?Math.max(c[k-1]-v,0):null), au = rma(u,p), ad = rma(d,p);
    return au.map((v,k)=>v==null||ad[k]==null?null:ad[k]===0?100:100-100/(1+v/ad[k])); };
  const stoA = (c, h, l, p) => { const hi = hh(h,p), lo = ll(l,p); return c.map((v,k)=>hi[k]==null||hi[k]===lo[k]?null:100*(v-lo[k])/(hi[k]-lo[k])); };
  const rsi = rsiA(C,14);
  const k = sma(stoA(C,H,L,14),3), d = sma(k,3);
  const tp = C.map((v,x)=>(H[x]+L[x]+v)/3), tm = sma(tp,20), cci = tm.map((m,x)=>{ if (m==null) return null; let s=0; for (let y=x-19;y<=x;y++) s+=Math.abs(tp[y]-m); return s ? (tp[x]-m)/(0.015*s/20) : null; });
  const up = [null], dn = [null]; for (let x=1;x<n;x++){ const u=H[x]-H[x-1], dd=L[x-1]-L[x]; up.push(u>dd&&u>0?u:0); dn.push(dd>u&&dd>0?dd:0); }
  const tr = rma(trf({H,L,C}).map((v,x)=>x?v:null),14), pdi = rma(up,14).map((v,x)=>v==null||!tr[x]?null:100*v/tr[x]), mdi = rma(dn,14).map((v,x)=>v==null||!tr[x]?null:100*v/tr[x]);
  const adx = rma(pdi.map((v,x)=>v==null||mdi[x]==null||v+mdi[x]===0?null:100*Math.abs(v-mdi[x])/(v+mdi[x])),14);
  const med = H.map((v,x)=>(v+L[x])/2), s34 = sma(med,34), ao = sma(med,5).map((v,x)=>{ const w = s34[x]; return v==null||w==null?null:v-w; });
  const mom = C.map((v,x)=>x>=10?v-C[x-10]:null);
  const mf = ema(C,12), ms = ema(C,26), macd = mf.map((v,x)=>v==null||ms[x]==null?null:v-ms[x]), sig = ema(macd,9);
  const sr = stoA(rsi,rsi,rsi,14), srk = sma(sr,3), srd = sma(srk,3);
  const h14 = hh(H,14), l14 = ll(L,14), wr = C.map((v,x)=>{ const h = h14[x], l = l14[x]; return h==null||h===l?null:-100*(h-v)/(h-l); });
  const e13 = ema(C,13), bbp = C.map((v,x)=>e13[x]==null?null:(H[x]-e13[x])+(L[x]-e13[x]));
  const bp = C.map((v,x)=>x?v-Math.min(L[x],C[x-1]):null), trr = C.map((v,x)=>x?Math.max(H[x],C[x-1])-Math.min(L[x],C[x-1]):null);
  const avg = p => { const a = roll(bp,p,(x,y)=>x+y), b2 = roll(trr,p,(x,y)=>x+y); return a.map((v,x)=>v==null||!b2[x]?null:v/b2[x]); };
  const a7 = avg(7), a14 = avg(14), a28 = avg(28), uo = a7.map((v,x)=>v==null||a14[x]==null||a28[x]==null?null:100*(4*v+2*a14[x]+a28[x])/7);
  const osc = [];
  const add = (nom, a, fmt, act) => osc.push({ nom, v:g(a), act: g(a) == null || act === false ? null : act });
  add('RSI (14)', rsi, 0, ok(g(rsi),g1(rsi)) && (g(rsi)<30&&g(rsi)>g1(rsi) ? 1 : g(rsi)>70&&g(rsi)<g1(rsi) ? -1 : 0));
  add('Stochastique %K (14, 3, 3)', k, 0, ok(g(k),g(d)) && (g(k)<20&&g(d)<20&&g(k)>g(d) ? 1 : g(k)>80&&g(d)>80&&g(k)<g(d) ? -1 : 0));
  add('CCI (20)', cci, 0, ok(g(cci),g1(cci)) && (g(cci)<-100&&g(cci)>g1(cci) ? 1 : g(cci)>100&&g(cci)<g1(cci) ? -1 : 0));
  add('ADX (14)', adx, 0, ok(g(adx),g(pdi),g(mdi),g1(pdi),g1(mdi)) && (g(adx)>20&&g1(pdi)<g1(mdi)&&g(pdi)>g(mdi) ? 1 : g(adx)>20&&g1(pdi)>g1(mdi)&&g(pdi)<g(mdi) ? -1 : 0));
  add('Oscillateur Awesome', ao, 0, ok(g(ao),g1(ao),g2(ao)) && ((g(ao)>0&&g1(ao)<0)||(g(ao)>0&&g1(ao)>0&&g(ao)>g1(ao)&&g2(ao)>g1(ao)) ? 1 : (g(ao)<0&&g1(ao)>0)||(g(ao)<0&&g1(ao)<0&&g(ao)<g1(ao)&&g2(ao)<g1(ao)) ? -1 : 0));
  add('Momentum (10)', mom, 0, ok(g(mom),g1(mom)) && (g(mom)>g1(mom) ? 1 : g(mom)<g1(mom) ? -1 : 0));
  add('MACD (12, 26)', macd, 0, ok(g(macd),g(sig)) && (g(macd)>g(sig) ? 1 : g(macd)<g(sig) ? -1 : 0));
  add('Stochastique RSI rapide (3, 3, 14, 14)', srk, 0, ok(g(srk),g(srd)) && (g(srk)<20&&g(srd)<20&&g(srk)>g(srd) ? 1 : g(srk)>80&&g(srd)>80&&g(srk)<g(srd) ? -1 : 0));
  add('%R de Williams (14)', wr, 0, ok(g(wr),g1(wr)) && (g(wr)<-80&&g(wr)>g1(wr) ? 1 : g(wr)>-20&&g(wr)<g1(wr) ? -1 : 0));
  add('Bull Bear Power', bbp, 0, ok(g(bbp),g1(bbp),g(e13),g1(e13)) && (g(e13)>g1(e13)&&g(bbp)<0&&g(bbp)>g1(bbp) ? 1 : g(e13)<g1(e13)&&g(bbp)>0&&g(bbp)<g1(bbp) ? -1 : 0));
  add('Oscillateur ultime (7, 14, 28)', uo, 0, ok(g(uo)) && (g(uo)>70 ? 1 : g(uo)<30 ? -1 : 0));
  const ma = [], c = g(C);
  [10,20,30,50,100,200].forEach(p => { const e = g(ema(C,p)), m = g(sma(C,p));
    ma.push({ nom:`Moyenne mobile exponentielle (${p})`, v:e, act:e == null ? null : e < c ? 1 : e > c ? -1 : 0 });
    ma.push({ nom:`Moyenne mobile simple (${p})`, v:m, act:m == null ? null : m < c ? 1 : m > c ? -1 : 0 }); });
  const bl = (() => { const h = hh(H,26)[i], l = ll(L,26)[i]; return h == null ? null : (h + l) / 2; })();
  ma.push({ nom:'Ichimoku : ligne de base (9, 26, 52, 26)', v:bl, act:bl == null ? null : bl < c ? 1 : bl > c ? -1 : 0 });
  const vw = (() => { if (n < 20) return null; let a = 0, bb = 0; for (let x = n-20; x < n; x++) { a += C[x]*V[x]; bb += V[x]; } return bb ? a/bb : null; })();
  ma.push({ nom:'Moyenne mobile pondérée par le volume (20)', v:vw, act:vw == null ? null : vw < c ? 1 : vw > c ? -1 : 0 });
  const hm = (() => { const w1 = wma(C,4), w2 = wma(C,9), df = w1.map((v,x)=>v==null||w2[x]==null?null:2*v-w2[x]); return g(wma(df,3)); })();
  ma.push({ nom:'Moyenne mobile de Hull (9)', v:hm, act:hm == null ? null : hm < c ? 1 : hm > c ? -1 : 0 });
  const piv = n >= 2 ? (() => { const h = H[i-1], l = L[i-1], cl = C[i-1], o = O[i], r = h - l, p = (h+l+cl)/3;
    const wp = (h+l+2*cl)/4, x = cl < o ? h+2*l+cl : cl > o ? 2*h+l+cl : h+l+2*cl;
    return { 'Classique':[l-2*(h-p), p-r, 2*p-h, p, 2*p-l, p+r, h+2*(p-l)], 'Fibonacci':[p-r, p-.618*r, p-.382*r, p, p+.382*r, p+.618*r, p+r],
      'Camarilla':[cl-1.1/4*r, cl-1.1/6*r, cl-1.1/12*r, cl, cl+1.1/12*r, cl+1.1/6*r, cl+1.1/4*r],
      'Woodie':[l-2*(h-wp), wp-h+l, 2*wp-h, wp, 2*wp-l, wp+h-l, h+2*(wp-l)], 'DM':[null, null, x/2-h, x/4, x/2-l, null, null] }; })() : null;
  return { osc, ma, piv, cur:c };
}
const score = arr => { const t = arr.filter(x => x.act != null); return { b:t.filter(x=>x.act>0).length, s:t.filter(x=>x.act<0).length, n:t.filter(x=>x.act===0).length, r:t.length ? t.reduce((a,x)=>a+x.act,0)/t.length : 0 }; };
const verdict = r => r > .5 ? 'Achat fort' : r > .1 ? 'Achat' : r >= -.1 ? 'Neutre' : r >= -.5 ? 'Vente' : 'Vente forte';
function gauge(titre, sc) {
  const P = (f, rad) => [100 + rad*Math.cos(f), 100 - rad*Math.sin(f)], cols = ['#ef5350','#ef9a9a','#b0bec5','#80cbc4','#26a69a'];
  const arcs = cols.map((c, k) => { const [x1,y1] = P(Math.PI - k*Math.PI/5, 80), [x2,y2] = P(Math.PI - (k+1)*Math.PI/5 + .02, 80);
    return `<path d="M${x1} ${y1} A80 80 0 0 1 ${x2} ${y2}" stroke="${c}" stroke-width="12" fill="none"/>`; }).join('');
  const [nx, ny] = P(Math.PI - Math.PI*(sc.r + 1)/2, 66), col = sc.r > .1 ? '#26a69a' : sc.r < -.1 ? '#ef5350' : '#6b7280';
  return `<figure><figcaption>${titre}</figcaption><svg viewBox="0 0 200 112">${arcs}<line x1="100" y1="100" x2="${nx}" y2="${ny}" stroke="#1c2230" stroke-width="3" stroke-linecap="round"/><circle cx="100" cy="100" r="5" fill="#1c2230"/></svg>
    <div class="lab" style="color:${col}">${verdict(sc.r)}</div><div class="cnt"><span><b>${sc.s}</b>Vente</span><span><b>${sc.n}</b>Neutre</span><span><b>${sc.b}</b>Achat</span></div></figure>`;
}
const actLab = a => a == null ? '–' : a > 0 ? '<span class="up">Achat</span>' : a < 0 ? '<span class="dn">Vente</span>' : 'Neutre';
async function tabTech() {
  const s = CURS, tab = FS, k = `${s}|tech|${TFS}`; $('#fbody').innerHTML = vide('Chargement…');
  try { CACHE[k] = CACHE[k] || (await get(`/api/history?symbol=${encodeURIComponent(s)}&days=${TF[TFS][1]}&interval=${TFS}`)).bars; }
  catch (e) { if (still(s, tab)) $('#fbody').innerHTML = vide('Données indisponibles : ' + esc(e.message)); return; }
  if (!still(s, tab)) return;
  const t = techCalc(CACHE[k]), so = score(t.osc), sm = score(t.ma), st = score([...t.osc, ...t.ma]), cur = t.cur;
  const row = x => [esc(x.nom), fnum(x.v, 3), actLab(x.act)];
  const pv = t.piv ? `<h4>Points pivots</h4>` + table(['', ...Object.keys(t.piv)], ['S3','S2','S1','P','R1','R2','R3'].map((l, r) => [`<b>${l}</b>`, ...Object.values(t.piv).map(v => fnum(v[r], 3))])) : '';
  $('#fbody').innerHTML = `<div class="sub" id="ftf">${Object.entries(TF).map(([k2, v]) => `<button data-i="${k2}" class="${k2 === TFS ? 'on' : ''}">${v[0]}</button>`).join('')}</div>
    <div class="gg">${gauge('Oscillateurs', so)}${gauge('Résumé', st)}${gauge('Moyennes mobiles', sm)}</div>
    <h4>Oscillateurs</h4>${table(['Nom', 'Valeur', 'Action'], t.osc.map(row))}
    <h4>Moyennes mobiles <small>(cours : ${fnum(cur, 3)})</small></h4>${table(['Nom', 'Valeur', 'Action'], t.ma.map(row))}${pv}
    <p class="empty">Règles de décision reprises de la méthode publique de TradingView ; calcul sur les ${CACHE[k].length} dernières bougies de l’intervalle choisi (une moyenne trop longue pour l’historique disponible reste vide).</p>`;
  $('#ftf').onclick = e => { const b = e.target.closest('button'); if (b) { TFS = b.dataset.i; tabTech(); } };
}

/* ---- Prévisions (Yahoo Finance) ---- */
const PER = { '0q':'Trimestre en cours', '+1q':'Trimestre suivant', '0y':'Année en cours', '+1y':'Année suivante', '+5y':'5 prochaines années', '-5y':'5 dernières années' };
const RECL = [['strongBuy','Achat fort','#1b8f7f'], ['buy','Achat','#26a69a'], ['hold','Conserver','#b0bec5'], ['sell','Vente','#ef9a9a'], ['strongSell','Vente forte','#ef5350']];
async function tabPrev() {
  const s = CURS, tab = FS, k = s + '|prev'; $('#fbody').innerHTML = vide('Chargement…');
  try { CACHE[k] = CACHE[k] || await get('/api/forecast?symbol=' + encodeURIComponent(s)); }
  catch (e) { if (still(s, tab)) $('#fbody').innerHTML = vide('Prévisions indisponibles : ' + esc(e.message)); return; }
  if (!still(s, tab)) return;
  const j = CACHE[k], c = j.cible || {}, cur = j.currency ? ' ' + esc(j.currency) : '';
  let h = '';
  if (c.mean != null) {
    const lo = c.low, hi = c.high, span = (hi - lo) || 1, pos = v => Math.max(0, Math.min(100, (v - lo) / span * 100)).toFixed(1) + '%';
    h += `<h4>Objectif de cours (12 mois)</h4><div class="kv"><div><small>Cours actuel</small>${fnum(c.current)}${cur}</div><div><small>Moyen</small>${fnum(c.mean)}${cur}</div><div><small>Médian</small>${fnum(c.median)}${cur}</div>
      <div><small>Potentiel (moyen)</small>${c.current ? pc((c.mean / c.current - 1) * 100) : '–'}</div><div><small>Bas</small>${fnum(lo)}${cur}</div><div><small>Haut</small>${fnum(hi)}${cur}</div></div>
      <div class="bar2">${c.current != null ? `<i style="left:${pos(c.current)}" title="Cours"></i><em style="left:${pos(c.current)}">Cours ${fnum(c.current)}</em>` : ''}</div>`;
  }
  if (j.recos.length) {
    h += `<h4>Recommandations des analystes${j.reco ? ' · consensus : ' + esc(({ strong_buy:'Achat fort', buy:'Achat', hold:'Conserver', underperform:'Sous-performance', sell:'Vente', strong_sell:'Vente forte' })[j.reco] || j.reco) : ''}${j.n_analystes ? ' · ' + fnum(j.n_analystes, 0) + ' analystes' : ''}</h4>`
      + table(['Période', 'Répartition', ...RECL.map(r => r[1])], j.recos.map(r => { const tot = RECL.reduce((a, x) => a + (r[x[0]] || 0), 0) || 1;
        return [esc({ '0m':'Ce mois', '-1m':'Il y a 1 mois', '-2m':'Il y a 2 mois', '-3m':'Il y a 3 mois' }[r.period] || r.period || ''),
          `<div class="stk">${RECL.map(x => `<span style="width:${(r[x[0]] || 0) / tot * 100}%;background:${x[2]}"></span>`).join('')}</div>`, ...RECL.map(x => fnum(r[x[0]], 0))]; }));
  }
  if (j.eps.length) h += '<h4>Bénéfice par action estimé</h4>' + table(['Période', 'Moyenne', 'Bas', 'Haut', 'Il y a un an', 'Analystes', 'Croissance'],
    j.eps.map(r => [esc(PER[r.period] || r.period || ''), fnum(r.avg), fnum(r.low), fnum(r.high), fnum(r.yearAgoEps), fnum(r.numberOfAnalysts, 0), pc(r.growth == null ? null : r.growth * 100)]));
  if (j.ca.length) h += '<h4>Chiffre d’affaires estimé</h4>' + table(['Période', 'Moyenne', 'Bas', 'Haut', 'Il y a un an', 'Analystes', 'Croissance'],
    j.ca.map(r => [esc(PER[r.period] || r.period || ''), fbig(r.avg), fbig(r.low), fbig(r.high), fbig(r.yearAgoRevenue), fnum(r.numberOfAnalysts, 0), pc(r.growth == null ? null : r.growth * 100)]));
  if (j.hist.length) h += '<h4>Bénéfices publiés vs attentes</h4>' + table(['Trimestre', 'Attendu', 'Publié', 'Écart', 'Surprise'],
    j.hist.map(r => { const sur = r.epsEstimate ? (r.epsActual - r.epsEstimate) / Math.abs(r.epsEstimate) * 100 : null; return [esc(r.quarter || Object.values(r)[0] || ''), fnum(r.epsEstimate), fnum(r.epsActual), fnum(r.epsDifference), pc(sur)]; }));
  if (j.croissance.length) h += '<h4>Croissance attendue</h4>' + table(['Période', ...Object.keys(j.croissance[0]).slice(1).map(x => esc(({ stock:'Titre', industry:'Industrie', sector:'Secteur', index:'Indice' })[x] || x))],
    j.croissance.map(r => { const v = Object.values(r); return [esc(PER[v[0]] || v[0]), ...v.slice(1).map(x => pc(x == null ? null : x * 100))]; }));
  if (j.revisions.length) h += '<h4>Dernières révisions d’analystes</h4>' + table(['Date', 'Société', 'Avant', 'Après', 'Action', 'Objectif'],
    j.revisions.map(r => [esc(Object.values(r)[0]), esc(r.Firm || ''), esc(r.FromGrade || ''), esc(r.ToGrade || ''), esc(r.Action || ''), r.currentPriceTarget != null ? fnum(r.currentPriceTarget) : '']));
  $('#fbody').innerHTML = h || vide('Aucune donnée.');
}

/* ---- Saisonniers (calculés sur l'historique mensuel) ---- */
const MOIS = ['Janv.', 'Févr.', 'Mars', 'Avr.', 'Mai', 'Juin', 'Juil.', 'Août', 'Sept.', 'Oct.', 'Nov.', 'Déc.'];
const med = a => { const b = a.filter(x => x != null).sort((x, y) => x - y); return b.length ? (b.length % 2 ? b[(b.length - 1) / 2] : (b[b.length / 2 - 1] + b[b.length / 2]) / 2) : null; };
function heat(v) { if (v == null) return ''; const a = Math.min(Math.abs(v) / 12, 1) * .55 + .08; return `background:${v >= 0 ? `rgba(38,166,154,${a})` : `rgba(239,83,80,${a})`}`; }
async function tabSaison() {
  const s = CURS, tab = FS, k = s + '|saison'; $('#fbody').innerHTML = vide('Chargement…');
  try { CACHE[k] = CACHE[k] || (await get(`/api/history?symbol=${encodeURIComponent(s)}&days=max&interval=1mo`)).bars; }
  catch (e) { if (still(s, tab)) $('#fbody').innerHTML = vide('Historique indisponible : ' + esc(e.message)); return; }
  if (!still(s, tab)) return;
  const bars = CACHE[k], Y = {};
  bars.forEach((r, i) => { if (!i) return; const d = new Date(r[0] * 1000), y = d.getUTCFullYear(), m = d.getUTCMonth(); (Y[y] = Y[y] || Array(12).fill(null))[m] = (r[4] / bars[i-1][4] - 1) * 100; });
  const ys = Object.keys(Y).map(Number).sort((a, b) => b - a);
  if (ys.length < 2) { $('#fbody').innerHTML = vide('Historique insuffisant.'); return; }
  const moy = MOIS.map((_, m) => { const v = ys.map(y => Y[y][m]).filter(x => x != null); return v.length ? v.reduce((a, b) => a + b, 0) / v.length : null; });
  const mdn = MOIS.map((_, m) => med(ys.map(y => Y[y][m]))), pos = MOIS.map((_, m) => { const v = ys.map(y => Y[y][m]).filter(x => x != null); return v.length ? v.filter(x => x > 0).length / v.length * 100 : null; });
  const cum = y => { let c = 1; return Y[y].map(v => v == null ? null : (c *= 1 + v / 100, (c - 1) * 100)); };
  const rec = ys.slice(0, 10), W = 640, Hh = 240, all = rec.flatMap(y => cum(y)).filter(v => v != null), mn = Math.min(0, ...all), mx = Math.max(0, ...all), X = m => 40 + m * (W - 60) / 11, Yv = v => 10 + (mx - v) / ((mx - mn) || 1) * (Hh - 40);
  const pal = ['#1d4ed8', '#e53935', '#43a047', '#fb8c00', '#8e24aa', '#00897b', '#6d4c41', '#d81b60', '#546e7a', '#9e9d24'];
  const lines = rec.map((y, k2) => { const c = cum(y), p = c.map((v, m) => v == null ? null : `${X(m)},${Yv(v)}`).filter(Boolean).join(' ');
    return `<polyline points="${p}" fill="none" stroke="${pal[k2]}" stroke-width="${k2 ? 1.2 : 2.4}" opacity="${k2 ? .75 : 1}"/>`; }).join('');
  const mAvg = Math.max(...moy.map(v => Math.abs(v || 0)), 1), bw = (W - 60) / 12;
  const bars2 = moy.map((v, m) => v == null ? '' : `<rect x="${40 + m * bw + 6}" y="${v >= 0 ? 100 - v / mAvg * 80 : 100}" width="${bw - 12}" height="${Math.abs(v) / mAvg * 80}" fill="${v >= 0 ? '#26a69a' : '#ef5350'}"/><text x="${40 + m * bw + bw / 2}" y="${v >= 0 ? 96 - v / mAvg * 80 : 112 + Math.abs(v) / mAvg * 80}" font-size="10" text-anchor="middle" fill="#6b7280">${fnum(v, 1)}</text>`).join('');
  $('#fbody').innerHTML = `<h4>Performance cumulée depuis le 1er janvier (10 dernières années)</h4>
    <svg viewBox="0 0 ${W} ${Hh}" width="100%"><line x1="40" x2="${W - 20}" y1="${Yv(0)}" y2="${Yv(0)}" stroke="#cbd5e1"/>${lines}${MOIS.map((l, m) => `<text x="${X(m)}" y="${Hh - 6}" font-size="10" text-anchor="middle" fill="#6b7280">${l}</text>`).join('')}
    <text x="4" y="${Yv(mx) + 4}" font-size="10" fill="#6b7280">${fnum(mx, 0)} %</text><text x="4" y="${Yv(mn) + 4}" font-size="10" fill="#6b7280">${fnum(mn, 0)} %</text></svg>
    <div class="sub">${rec.map((y, k2) => `<span style="color:${pal[k2]};font-weight:600">● ${y}</span>`).join(' &nbsp;')}</div>
    <h4>Rendement mensuel moyen (%)</h4><svg viewBox="0 0 ${W} 215" width="100%"><line x1="40" x2="${W - 20}" y1="100" y2="100" stroke="#cbd5e1"/>${bars2}${MOIS.map((l, m) => `<text x="${40 + m * bw + bw / 2}" y="210" font-size="10" text-anchor="middle" fill="#6b7280">${l}</text>`).join('')}</svg>
    <h4>Rendements mensuels par année (%)</h4><div class="scr"><table><tr><th>Année</th>${MOIS.map(m => `<th>${m}</th>`).join('')}</tr>
    <tr><td><b>Moyenne</b></td>${moy.map(v => `<td class="hm" style="${heat(v)}">${fnum(v, 1)}</td>`).join('')}</tr><tr><td><b>Médiane</b></td>${mdn.map(v => `<td class="hm" style="${heat(v)}">${fnum(v, 1)}</td>`).join('')}</tr>
    <tr><td><b>% de hausses</b></td>${pos.map(v => `<td class="hm">${v == null ? '–' : fnum(v, 0) + ' %'}</td>`).join('')}</tr>
    ${ys.slice(0, 25).map(y => `<tr><td>${y}</td>${Y[y].map(v => `<td class="hm" style="${heat(v)}">${fnum(v, 1)}</td>`).join('')}</tr>`).join('')}</table></div>
    <p class="empty">Calculé sur l’historique mensuel complet disponible (${ys.length} années), clôture du mois contre clôture du mois précédent.</p>`;
}

/* ---- Cadre « fiche » : 6 onglets ---- */
function drawFiche() {
  popClose();
  document.querySelectorAll('#fbtns button').forEach(b => b.classList.toggle('on', !$('#fiche').hidden && b.dataset.s === FS));
  if ($('#fiche').hidden) return;
  const onglets = { finances:() => tabTv('financials'), actus:tabActus, dossiers:tabDossiers, tech:tabTech, prev:tabPrev, saison:tabSaison };
  (onglets[FS] || onglets.finances)();
}
$('#fbtns').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  if (!$('#fiche').hidden && FS === b.dataset.s && CURS === ST.sym) { closeFiche(); return; }   // re-clic = fermer
  if ($('#fiche').hidden || CURS !== ST.sym) showFiche(ST.sym, ST.name || ST.sym, b.dataset.s);
  else { FS = b.dataset.s; drawFiche(); }
});
function closeFiche() { freq++; $('#fiche').hidden = true; $('#fbody').innerHTML = ''; drawFiche(); }
function refreshFiche() { if (!$('#fiche').hidden && CURS !== ST.sym) showFiche(ST.sym, ST.name || ST.sym, FS); }
async function showFiche(s, n, tab) {
  const my = ++freq; CURS = s; CURJ = null; FS = tab || FS;
  $('#fiche').hidden = false; $('#fnm').textContent = `${n} (${s})`;
  $('#fgf').hidden = $('#fge').hidden = true;
  drawFiche();
  try {
    const j = await infoSym(); if (my !== freq) return;
    if (j.google) { $('#fgf').href = j.google; $('#fgf').hidden = false; }
    if (j.google_earnings) { $('#fge').href = j.google_earnings; $('#fge').hidden = false; }
  } catch (e) { /* les onglets calculés ici fonctionnent sans la fiche Yahoo */ }
}
$('#fx').addEventListener('click', closeFiche);
const FICHE_SYM = () => CURS;
const split = $('#split');
split.addEventListener('pointerdown', e => { split.setPointerCapture(e.pointerId); split.classList.add('drag'); document.body.classList.add('dragging'); });
split.addEventListener('pointermove', e => {
  if (!split.hasPointerCapture(e.pointerId)) return;
  UI.w[UI.tab] = Math.round(Math.max(240, Math.min(innerWidth - e.clientX, innerWidth * .8))); setW(UI.w[UI.tab]);
});
const finDrag = () => { split.classList.remove('drag'); document.body.classList.remove('dragging'); uiSave(); };
split.addEventListener('pointerup', finDrag); split.addEventListener('pointercancel', finDrag);
split.addEventListener('dblclick', () => { UI.w[UI.tab] = UI.tab === 'perf' ? 580 : UI.tab === 'screener' ? 720 : 300; setW(UI.w[UI.tab]); uiSave(); });
addEventListener('resize', () => setW(UI.w[UI.tab]));

/* ================= Clic droit : menu des indicateurs ================= */
const CM = $('#cm'), NB = t => ST.inds.filter(i => i.type === t).length;
function openParams(it) {
  if (it.type === 'cmp') { const s = (prompt('Nouveau symbole à comparer :', it.p.s || '') || '').trim().toUpperCase(); if (s) { it.p.s = s; apply(); } return; }
  setTab('ind'); side();
  const c = document.querySelector(`.card[data-id="${it.id}"]`);
  if (c) { c.scrollIntoView({ block:'center' }); c.classList.add('flash'); setTimeout(() => c.classList.remove('flash'), 1600); }
}
const apply = () => { side(); build(true); save(); };
let CMP = 0;                                                       // graphique sur lequel le clic droit a eu lieu
function menuAdd(where) {
  const pn = ST.layout === 3 ? CMP : 'all';
  const ent = k => ({ label:IND[k].n, badge:NB(k) ? '×' + NB(k) : '', run:() => addAt(k, where, pn) });
  return [{ lab:'★ Favoris' }, ...FAV.map(ent), { sep:1 }, { lab:'Autres indicateurs' }, ...Object.keys(IND).filter(k => !FAV.includes(k)).sort((a, b) => IND[a].n.localeCompare(IND[b].n, 'fr')).map(ent)];
}
function menuItems() {
  const k = CMP, tri = ST.layout === 3, mine = ST.inds.filter(it => forPanel(it, k));
  const act = mine.map(it => ({ label:IND[it.type].n + (it.on ? '' : ' (masqué)'),
    badge:(tri ? (pnList(it).length === 3 ? 'les 3 · ' : pnList(it).length === 1 ? 'ce graphique · ' : '2 graphiques · ') : '') + (it.pos === 'over' ? 'graphique' : 'dessous'), nov:1, sub:[
    { label:it.on ? 'Masquer' : 'Afficher', run:() => { it.on = !it.on; apply(); ensureEps(); } },
    ...(tri ? [pnList(it).length === 3 ? { label:'Garder seulement sur ce graphique', run:() => { it.pn = k; apply(); } }
                              : { label:'Afficher sur les 3 graphiques', run:() => { it.pn = 'all'; apply(); } }] : []),
    { label:it.pos === 'over' ? 'Déplacer sous le graphique' : 'Déplacer sur le graphique', run:() => { it.pos = it.pos === 'over' ? 'pane' : 'over'; apply(); } },
    { label:'Paramètres…', run:() => openParams(it) },
    { sep:1 },
    { label:'Supprimer', run:() => { ST.inds = ST.inds.filter(x => x !== it); apply(); } } ] }));
  return [
    ...(tri ? [{ lab:`Graphique ${k + 1} · bougies de ${IVL[PN[k].iv]}` }] : []),
    { label:tri ? 'Ajouter sur ce graphique' : 'Ajouter sur le graphique', sub:menuAdd('over') },
    { label:tri ? 'Ajouter sous ce graphique' : 'Ajouter sous le graphique', sub:menuAdd('pane') },
    { sep:1 },
    mine.length ? { label:`Indicateurs actifs (${mine.length})`, nov:1, sub:act } : { label:'Aucun indicateur actif', dis:1 },
    { sep:1 },
    { label:'Ajuster l’échelle (tout afficher)', run:() => PN[k].chart && PN[k].chart.timeScale().fitContent() },
    mine.length ? { label:tri ? 'Supprimer les indicateurs affichés ici' : 'Supprimer tous les indicateurs', run:() => { ST.inds = ST.inds.filter(it => !mine.includes(it)); apply(); } } : null,
  ].filter(Boolean);
}
function cmEl(items) {
  const m = document.createElement('div'); m.className = 'cmenu';
  items.forEach(o => {
    const d = document.createElement('div');
    if (o.sep) { d.className = 'cmsep'; m.appendChild(d); return; }
    if (o.lab) { d.className = 'cmlab'; d.textContent = o.lab; m.appendChild(d); return; }
    d.className = 'cmi' + (o.dis ? ' dis' : '');
    d.innerHTML = `<span>${esc(o.label)}</span>${o.badge ? `<em class="bd">${esc(o.badge)}</em>` : ''}${o.sub ? '<span class="ar">▸</span>' : ''}`;
    if (o.sub) {
      const s = cmEl(o.sub); if (o.nov) s.classList.add('nov'); d.appendChild(s);
      d.addEventListener('mouseenter', () => { s.style.top = '-5px'; requestAnimationFrame(() => { const r = s.getBoundingClientRect(); if (r.bottom > innerHeight - 6) s.style.top = (-5 - (r.bottom - innerHeight + 8)) + 'px'; }); });
    } else if (o.run) d.addEventListener('click', e => { e.stopPropagation(); cmClose(); o.run(); });
    m.appendChild(d);
  });
  return m;
}
function cmClose() { CM.hidden = true; CM.innerHTML = ''; }
function cmOpen(x, y, k) {
  CMP = k || 0; CM.innerHTML = ''; CM.appendChild(cmEl(menuItems())); CM.hidden = false; CM.classList.toggle('left', x + 480 > innerWidth);
  const r = CM.firstChild.getBoundingClientRect();
  CM.style.left = Math.max(4, Math.min(x, innerWidth - r.width - 4)) + 'px'; CM.style.top = Math.max(4, Math.min(y, innerHeight - r.height - 4)) + 'px';
}

CM.addEventListener('contextmenu', e => e.preventDefault());
addEventListener('pointerdown', e => { if (!CM.hidden && !CM.contains(e.target)) cmClose(); }, true);
addEventListener('keydown', e => { if (e.key === 'Escape') cmClose(); });
addEventListener('resize', cmClose);

/* ================= Outils de dessin (barre latérale gauche) =================
   Les dessins sont enregistrés par titre, en (date, prix) : ils restent à leur place quand on change de durée de bougie. */
const DKEY = 'graphique-boursier-dessins';
const DR = (() => { try { return JSON.parse(localStorage.getItem(DKEY)) || {}; } catch (e) { return {}; } })();
const DS = { tool:'cursor', last:{}, draft:null, sel:null, hov:null, ver:0, hist:[], drag:null, block:false, sym:'' };
const curDr = () => DR[ST.sym] || (DR[ST.sym] = []);
function drSave() { DS.ver++; try { const o = {}; Object.keys(DR).forEach(k => { if (DR[k].length) o[k] = DR[k]; }); localStorage.setItem(DKEY, JSON.stringify(o)); } catch (e) {} }
const drSnap = () => { DS.hist.push(JSON.stringify(curDr())); if (DS.hist.length > 40) DS.hist.shift(); };
const LS = [[], [6, 4], [2, 3]];
const FIB = [[0,'#787b86'],[.236,'#f23645'],[.382,'#ff9800'],[.5,'#4caf50'],[.618,'#089981'],[.786,'#00bcd4'],[1,'#787b86'],[1.618,'#2962ff'],[2.618,'#f23645']];
const TOOLS = [
  { g:'cur', items:[['cursor','Curseur'],['measure','Règle (mesure)']] },
  { g:'lin', items:[['trend','Ligne de tendance'],['ray','Rayon'],['ext','Ligne étendue'],['hline','Ligne horizontale'],['hray','Rayon horizontal'],['vline','Ligne verticale'],['arrow','Flèche']] },
  { g:'chn', items:[['chan','Canal parallèle'],['pitch','Fourche d’Andrews'],['rect','Rectangle'],['sr','Zone de support / résistance']] },
  { g:'fib', items:['FIBONACCI',['fib','Retracement de Fibonacci'],['fibext','Extension de Fib basée sur la tendance'],['fibch','Canal de Fibonacci'],['fibtz','Fuseau horaire de Fibonacci'],['fibfan','Éventail de résistance de Fibonacci'],['fibcirc','Cercles de Fibonacci'],'GANN',['gannfan','Éventail de Gann'],['gannbox','Boîte de Gann']] },
  { g:'txt', items:[['text','Texte'],['brush','Pinceau']] },
];
const NP = { cursor:0, measure:2, trend:2, ray:2, ext:2, hline:1, hray:1, vline:1, arrow:2, chan:3, pitch:3, rect:2, sr:2, fib:2, fibext:3, fibch:3, fibtz:2, fibfan:2, fibcirc:2, gannfan:2, gannbox:2, text:1, brush:'free' };
const NAME = {}; TOOLS.forEach(t => t.items.forEach(it => { if (Array.isArray(it)) NAME[it[0]] = it[1]; }));
const ICON = {
  cursor:'<path d="M12 4v16M4 12h16"/>', measure:'<rect x="3" y="9" width="18" height="6" rx="1"/><path d="M7 9v3M11 9v2M15 9v3M19 9v2"/>',
  trend:'<path d="M4 19L20 5"/><circle cx="4" cy="19" r="1.7"/><circle cx="20" cy="5" r="1.7"/>', ray:'<path d="M4 18L21 6"/><circle cx="4" cy="18" r="1.7"/>',
  ext:'<path d="M2 20L22 4"/><circle cx="9" cy="14.5" r="1.7"/><circle cx="15" cy="9.5" r="1.7"/>', hline:'<path d="M3 12h18"/><circle cx="12" cy="12" r="1.7"/>',
  hray:'<path d="M5 12h16"/><circle cx="5" cy="12" r="1.7"/>', vline:'<path d="M12 3v18"/><circle cx="12" cy="12" r="1.7"/>', arrow:'<path d="M5 19L19 5M19 5h-7M19 5v7"/>',
  chan:'<path d="M3 14L17 4M7 21L21 11"/>', pitch:'<path d="M4 20L20 4M9 20L21 11M3 12L12 4"/>', rect:'<rect x="4" y="6" width="16" height="12" rx="1"/>',
  sr:'<rect x="3" y="8" width="18" height="8" fill="currentColor" fill-opacity=".22"/><path d="M3 8h18M3 16h18"/>', fib:'<path d="M4 5h16M4 10h16M4 15h16M4 20h16"/>',
  fibext:'<path d="M4 20L9 11L13 15M13 15h8M13 8h8"/>', fibch:'<path d="M3 16L17 4M6 20L21 8M10 21L22 13"/>', fibtz:'<path d="M5 4v16M9 4v16M13 4v16M21 4v16"/>',
  fibfan:'<path d="M4 20L20 5M4 20L20 10M4 20L20 15"/>', fibcirc:'<circle cx="12" cy="12" r="8"/><circle cx="12" cy="12" r="4.5"/>', gannfan:'<path d="M4 20L20 4M4 20L20 11M4 20L20 16M4 20L11 4"/>',
  gannbox:'<rect x="4" y="4" width="16" height="16"/><path d="M4 12h16M12 4v16M4 20L20 4"/>', text:'<path d="M6 6h12M12 6v13"/>', brush:'<path d="M4 20c4 0 4-4 6-4s2 2 4 0L20 6"/>',
  mag:'<path d="M6 4v8a6 6 0 0 0 12 0V4h-4v8a2 2 0 0 1-4 0V4z"/>', keep:'<path d="M4 20l1-4L16 5l3 3L8 19z"/><path d="M15 20h6"/>',
  lock:'<rect x="6" y="11" width="12" height="9" rx="1"/><path d="M8 11V8a4 4 0 0 1 8 0v3"/>', eye:'<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',
  trash:'<path d="M5 7h14M9 7V4h6v3M7 7l1 13h8l1-13"/>', aut:'<path d="M4 20L11 13M16 3l1.2 3.3L20.5 7.5l-3.3 1.2L16 12l-1.2-3.3L11.5 7.5l3.3-1.2z"/>',
};
const svg = k => `<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round">${ICON[k]}</svg>`;
const SENS = ['faible', 'moyenne', 'forte'], SENSK = [8, 5, 3];

/* ---- conversions date/prix <-> pixels ---- */
const stepOf = X => X._st || (X._st = (() => { const d = []; for (let i = Math.max(1, X.T.length - 60); i < X.T.length; i++) d.push(X.T[i] - X.T[i-1]); d.sort((a, b) => a - b); return d[d.length >> 1] || 86400; })());
function t2l(X, t) {
  const T = X.T, n = T.length; if (!n) return 0;
  if (t >= T[n-1]) return n - 1 + (t - T[n-1]) / stepOf(X); if (t <= T[0]) return (t - T[0]) / stepOf(X);
  let lo = 0, hi = n - 1; while (hi - lo > 1) { const m = (lo + hi) >> 1; if (T[m] <= t) lo = m; else hi = m; }
  return lo + (t - T[lo]) / (T[hi] - T[lo]);
}
function l2t(X, l) {
  const T = X.T, n = T.length; if (l >= n - 1) return T[n-1] + (l - (n - 1)) * stepOf(X); if (l <= 0) return T[0] + l * stepOf(X);
  const i = Math.floor(l); return T[i] + (l - i) * (T[i+1] - T[i]);
}
function pgeom(P) { let H = 0; try { H = P.chart.panes()[0].getHeight(); } catch (e) {} return { W:P.chart.timeScale().width(), H:H || P.cel.clientHeight }; }
const xOf = (P, t) => P.chart.timeScale().logicalToCoordinate(t2l(P.X, t));
const yOf = (P, p) => P.candle.priceToCoordinate(p);
function ptOf(P, x, y) {
  const l = P.chart.timeScale().coordinateToLogical(x), p = P.candle.coordinateToPrice(y);
  return l == null || p == null ? null : { t:Math.round(l2t(P.X, l)), p };
}
function snapPt(P, x, y) {                                                  // aimant : accroche à l'ouverture / haut / bas / clôture de la bougie voisine
  const pt = ptOf(P, x, y); if (!pt || !UI.mag) return pt;
  const X = P.X, l = P.chart.timeScale().coordinateToLogical(x), i = Math.round(l); if (i < 0 || i >= X.T.length) return pt;
  let best = null, bd = 24;
  [X.O[i], X.H[i], X.L[i], X.C[i]].forEach(v => { const yy = yOf(P, v); if (yy != null && Math.abs(yy - y) < bd) { bd = Math.abs(yy - y); best = v; } });
  return best == null ? pt : { t:X.T[i], p:best };
}

/* ---- géométrie de chaque outil (utilisée pour dessiner ET pour détecter les clics) ---- */
function geom(P, d, G) {
  const o = { seg:[], fill:[], circ:[], lab:[], pts:[] };
  const pp = o.pts = d.pts.map(q => { const x = xOf(P, q.t), y = yOf(P, q.p); return x == null || y == null ? null : { x, y }; });
  if (!pp.length || pp.some(q => !q)) return o;
  const [a, b, c] = pp, col = d.color, W = G.W, H = G.H;
  const far = (u, v, k) => { const dx = v.x - u.x, dy = v.y - u.y, m = k * 1e5 / (Math.hypot(dx, dy) || 1); return { x:u.x + dx * m, y:u.y + dy * m }; };
  const line = (u, v, cl, ls, w) => o.seg.push({ a:u, b:v, c:cl || col, ls:ls ?? d.ls, w:w ?? d.w });
  const ray = (u, v, cl) => line(u, far(u, v, 1), cl, 0, 1);
  const poly = (ps, cl, al, sel) => o.fill.push({ poly:ps, c:cl || col, al, sel });
  const lab = (x, y, t, cl, ex) => o.lab.push({ x, y, t, c:cl || col, ...ex });
  const pr = i => d.pts[i].p, fm = v => v.toLocaleString('fr-FR', { maximumFractionDigits:4 });
  const rect = (u, v) => [{ x:u.x, y:u.y }, { x:v.x, y:u.y }, { x:v.x, y:v.y }, { x:u.x, y:v.y }];
  const edges = ps => ps.forEach((q, i) => line(q, ps[(i + 1) % ps.length]));
  const head = (u, v, cl) => { const an = Math.atan2(v.y - u.y, v.x - u.x); [-.45, .45].forEach(s => line(v, { x:v.x - 11 * Math.cos(an + s), y:v.y - 11 * Math.sin(an + s) }, cl, 0)); };
  switch (d.type) {
    case 'trend': line(a, b); break;
    case 'ray': line(a, far(a, b, 1)); break;
    case 'ext': line(far(a, b, -1), far(a, b, 1)); break;
    case 'arrow': line(a, b); head(a, b); break;
    case 'hline': line({ x:0, y:a.y }, { x:W, y:a.y }); lab(W + 2, a.y, fm(pr(0)), col, { box:1, out:1 }); break;
    case 'hray': line(a, { x:W, y:a.y }); lab(W + 2, a.y, fm(pr(0)), col, { box:1, out:1 }); break;
    case 'vline': line({ x:a.x, y:0 }, { x:a.x, y:H }); break;
    case 'rect': { const ps = rect(a, b); poly(ps, col, .12, 1); edges(ps); break; }
    case 'sr': { const t = Math.min(a.y, b.y), bt = Math.max(a.y, b.y), x1 = Math.min(a.x, W - 2);
      poly([{ x:x1, y:t }, { x:W, y:t }, { x:W, y:bt }, { x:x1, y:bt }], col, .16, 1); line({ x:x1, y:t }, { x:W, y:t }); line({ x:x1, y:bt }, { x:W, y:bt });
      lab(x1 + 4, t + 10, `${fm(Math.max(pr(0), pr(1)))} – ${fm(Math.min(pr(0), pr(1)))}`, col); break; }
    case 'chan': { const dy = c.y - (a.y + (b.y - a.y) * (c.x - a.x) / ((b.x - a.x) || 1e-9)), a2 = { x:a.x, y:a.y + dy }, b2 = { x:b.x, y:b.y + dy };
      poly([a, b, b2, a2], col, .1, 1); line(a, b); line(a2, b2); line({ x:a.x, y:a.y + dy / 2 }, { x:b.x, y:b.y + dy / 2 }, col, 2, 1); break; }
    case 'pitch': { const m = { x:(b.x + c.x) / 2, y:(b.y + c.y) / 2 }, v = { x:m.x - a.x, y:m.y - a.y };
      const fb = far(b, { x:b.x + v.x, y:b.y + v.y }, 1), fc = far(c, { x:c.x + v.x, y:c.y + v.y }, 1);
      poly([b, fb, fc, c], col, .08); line(a, far(a, m, 1)); line(b, fb); line(c, fc); line(b, c, col, 2, 1); break; }
    case 'fib': { const lv = FIB.slice(0, 8), x1 = Math.min(a.x, b.x), pv = r => pr(1) - (pr(1) - pr(0)) * r, ys = lv.map(([r]) => yOf(P, pv(r)));
      lv.forEach(([r, cl], i) => { const y = ys[i]; if (y == null) return; line({ x:x1, y }, { x:W, y }, cl, 0, 1); lab(x1 + 4, y - 7, `${r} (${fm(pv(r))})`, cl);
        if (i && ys[i-1] != null) poly([{ x:x1, y:ys[i-1] }, { x:W, y:ys[i-1] }, { x:W, y }, { x:x1, y }], cl, .07); });
      line(a, b, '#787b86', 2, 1); break; }
    case 'fibext': { const lv = [[0,'#787b86'],[.618,'#089981'],[1,'#787b86'],[1.272,'#ff9800'],[1.618,'#2962ff'],[2,'#4caf50'],[2.618,'#f23645']], dv = pr(1) - pr(0);
      lv.forEach(([r, cl]) => { const p = pr(2) + dv * r, y = yOf(P, p); if (y == null) return; line({ x:c.x, y }, { x:W, y }, cl, 0, 1); lab(c.x + 4, y - 7, `${r} (${fm(p)})`, cl); });
      line(a, b, '#787b86', 2, 1); line(b, c, '#787b86', 2, 1); break; }
    case 'fibch': { const dy = c.y - (a.y + (b.y - a.y) * (c.x - a.x) / ((b.x - a.x) || 1e-9)), a2 = { x:a.x, y:a.y + dy }, b2 = { x:b.x, y:b.y + dy };
      poly([a, far(a, b, 1), far(a2, b2, 1), a2], col, .06);
      [0,.236,.382,.5,.618,.786,1,1.618,2.618].forEach((r, i) => ray({ x:a.x, y:a.y + dy * r }, { x:b.x, y:b.y + dy * r }, FIB[i][1])); break; }
    case 'fibtz': { const dx = b.x - a.x; if (!dx) break;
      [0,1,2,3,5,8,13,21,34,55,89].forEach(n => { const x = a.x + dx * n; if (x < -50 || x > W + 50) return; line({ x, y:0 }, { x, y:H }, '#2962ff', 2, 1); lab(x + 3, 12, String(n), '#2962ff'); }); break; }
    case 'fibfan': { [.25,.382,.5,.618,.75,1].forEach((r, i) => { const t = { x:b.x, y:a.y + (b.y - a.y) * r }, cl = FIB[Math.min(i + 2, 7)][1]; ray(a, t, cl); lab(t.x + 3, t.y, String(r), cl); }); break; }
    case 'fibcirc': { const m = { x:(a.x + b.x) / 2, y:(a.y + b.y) / 2 }, R = Math.hypot(b.x - a.x, b.y - a.y) / 2;
      [.236,.382,.5,.618,.786,1,1.618].forEach((r, i) => o.circ.push({ x:m.x, y:m.y, r:R * r, c:FIB[i + 1][1], ls:0, w:1 })); break; }
    case 'gannfan': { const dx = b.x - a.x, dy = b.y - a.y;
      [[1/8,'1×8'],[1/4,'1×4'],[1/3,'1×3'],[1/2,'1×2'],[1,'1×1'],[2,'2×1'],[3,'3×1'],[4,'4×1'],[8,'8×1']].forEach(([r, t], i) => { const tg = { x:a.x + dx, y:a.y + dy * r }, cl = r === 1 ? col : FIB[(i % 7) + 1][1];
        line(a, far(a, tg, 1), cl, 0, r === 1 ? 2 : 1); lab(tg.x + 3, tg.y, t, cl); }); break; }
    case 'gannbox': { const ps = rect(a, b); poly(ps, col, .05, 1); edges(ps);
      [.25,.382,.5,.618,.75].forEach(r => { const x = a.x + (b.x - a.x) * r, y = a.y + (b.y - a.y) * r; line({ x, y:a.y }, { x, y:b.y }, col, 2, 1); line({ x:a.x, y }, { x:b.x, y }, col, 2, 1); });
      line(a, b, col, 1, 1); line({ x:b.x, y:a.y }, { x:a.x, y:b.y }, col, 1, 1); break; }
    case 'text': lab(a.x, a.y, d.text || '', col, { txt:1 }); break;
    case 'brush': for (let i = 1; i < pp.length; i++) line(pp[i-1], pp[i]); break;
    case 'measure': { const dp = pr(1) - pr(0), pc = pr(0) ? dp / pr(0) * 100 : 0, bars = Math.round(t2l(P.X, d.pts[1].t) - t2l(P.X, d.pts[0].t)), cl = dp >= 0 ? '#2962ff' : '#f23645';
      poly(rect(a, b), cl, .12, 1); line(a, b, cl, 0, 1); head(a, b, cl);
      lab(Math.max(a.x, b.x) + 6, b.y, `${dp >= 0 ? '+' : ''}${fm(dp)} (${pc.toFixed(2)} %) · ${bars} barres`, cl, { box:1 }); break; }
  }
  return o;
}
function paintG(ctx, g, G, hot) {
  ctx.save(); ctx.beginPath(); ctx.rect(0, 0, G.W, G.H); ctx.clip();
  g.fill.forEach(f => { ctx.globalAlpha = f.al; ctx.fillStyle = f.c; ctx.beginPath(); f.poly.forEach((q, i) => i ? ctx.lineTo(q.x, q.y) : ctx.moveTo(q.x, q.y)); ctx.closePath(); ctx.fill(); });
  ctx.globalAlpha = 1;
  g.seg.forEach(s => { ctx.strokeStyle = s.c; ctx.lineWidth = (s.w || 1) + (hot ? .6 : 0); ctx.setLineDash(LS[s.ls || 0]); ctx.beginPath(); ctx.moveTo(s.a.x, s.a.y); ctx.lineTo(s.b.x, s.b.y); ctx.stroke(); });
  g.circ.forEach(s => { ctx.strokeStyle = s.c; ctx.lineWidth = s.w; ctx.setLineDash([]); ctx.beginPath(); ctx.arc(s.x, s.y, Math.min(s.r, 1e5), 0, 7); ctx.stroke(); });
  ctx.setLineDash([]); g.lab.filter(l => !l.out).forEach(l => paintLab(ctx, l)); ctx.restore();
  g.lab.filter(l => l.out).forEach(l => paintLab(ctx, l));
}
function paintLab(ctx, l) {
  ctx.font = l.txt ? '600 14px system-ui, sans-serif' : '11px system-ui, sans-serif'; ctx.textBaseline = 'middle'; const w = ctx.measureText(l.t).width;
  if (l.box) { ctx.fillStyle = l.c; ctx.fillRect(l.x, l.y - 8, w + 8, 16); ctx.fillStyle = '#fff'; ctx.fillText(l.t, l.x + 4, l.y); }
  else { ctx.fillStyle = l.c; ctx.fillText(l.t, l.x, l.y); }
}
function distSeg(px, py, s) {
  const dx = s.b.x - s.a.x, dy = s.b.y - s.a.y, L = dx * dx + dy * dy; let t = L ? ((px - s.a.x) * dx + (py - s.a.y) * dy) / L : 0; t = Math.max(0, Math.min(1, t));
  return Math.hypot(px - (s.a.x + t * dx), py - (s.a.y + t * dy));
}
function inPoly(px, py, ps) { let r = false; for (let i = 0, j = ps.length - 1; i < ps.length; j = i++) { const a = ps[i], b = ps[j]; if ((a.y > py) !== (b.y > py) && px < (b.x - a.x) * (py - a.y) / (b.y - a.y) + a.x) r = !r; } return r; }
function hitTest(g, d, x, y, sel) {
  if (sel && d.type !== 'brush') for (let k = 0; k < g.pts.length; k++) if (g.pts[k] && Math.hypot(g.pts[k].x - x, g.pts[k].y - y) <= 8) return 'p' + k;
  let best = 1e9; g.seg.forEach(s => { best = Math.min(best, distSeg(x, y, s)); }); g.circ.forEach(c => { best = Math.min(best, Math.abs(Math.hypot(x - c.x, y - c.y) - c.r)); });
  if (best <= 6) return 'b';
  if (g.fill.some(f => f.sel && inPoly(x, y, f.poly))) return 'b';
  if (g.lab.some(l => l.txt && x >= l.x - 2 && x <= l.x + l.t.length * 8 && Math.abs(y - l.y) <= 11)) return 'b';
  return null;
}
function pick(P, x, y, G) {
  if (UI.hide) return null;
  const order = curDr().slice().reverse(); if (DS.sel) { const k = order.findIndex(d => d.id === DS.sel); if (k > 0) order.unshift(order.splice(k, 1)[0]); }
  for (const d of order) { const part = hitTest(geom(P, d, G), d, x, y, d.id === DS.sel); if (part) return { d, part }; }
  return null;
}

/* ---- détection automatique : zones de support / résistance, canal, lignes de tendance ---- */
function srZones(X, k) {
  const n = X.C.length; if (n < 30) return [];
  const hi = pivA(X.H, k, true), lo = pivA(X.L, k, false), a = rma(trf(X), 14)[n-1] || X.C[n-1] * .01, tol = Math.max(a * .6, X.C[n-1] * .002);
  const pv = [...hi.map(i => ({ i, p:X.H[i] })), ...lo.map(i => ({ i, p:X.L[i] }))].filter(q => q.i >= n - 700).sort((u, v) => u.p - v.p);
  const cl = []; let c = null;
  pv.forEach(q => { if (c && q.p - c.lo <= tol * 1.5) { c.m.push(q); c.hi = q.p; } else { c = { m:[q], lo:q.p, hi:q.p }; cl.push(c); } });
  const last = X.C[n-1];
  return cl.filter(z => z.m.length >= 2).map(z => { const mid = (z.lo + z.hi) / 2, th = Math.max(z.hi - z.lo, a * .3);
      return { lo:mid - th / 2, hi:mid + th / 2, n:z.m.length, i0:Math.min(...z.m.map(q => q.i)), score:z.m.reduce((s, q) => s + .5 + .5 * q.i / n, 0) }; })
    .sort((u, v) => v.score - u.score).slice(0, 6).map(z => ({ ...z, role:last > z.hi ? 'S' : last < z.lo ? 'R' : 'Z' }));
}
function autoGeoms(P, G) {
  const X = P.X, n = X.C.length, ts = P.chart.timeScale(), lr = ts.getVisibleLogicalRange(), out = [], k = SENSK[UI.sens ?? 1];
  const g0 = () => ({ seg:[], fill:[], circ:[], lab:[], pts:[] });
  if (UI.auto.sr) {
    if (!P.aSR || P.aSR.X !== X || P.aSR.k !== k) P.aSR = { X, k, z:srZones(X, k) };
    P.aSR.z.forEach(z => { const g = g0(), col = z.role === 'S' ? '#089981' : z.role === 'R' ? '#f23645' : '#ff9800', xa = ts.logicalToCoordinate(z.i0), y1 = yOf(P, z.hi), y2 = yOf(P, z.lo);
      if (xa == null || y1 == null || y2 == null) return; const x0 = Math.max(xa, 0);
      g.fill.push({ poly:[{ x:x0, y:y1 }, { x:G.W, y:y1 }, { x:G.W, y:y2 }, { x:x0, y:y2 }], c:col, al:.16 });
      g.seg.push({ a:{ x:x0, y:y1 }, b:{ x:G.W, y:y1 }, c:col, ls:0, w:1 }, { a:{ x:x0, y:y2 }, b:{ x:G.W, y:y2 }, c:col, ls:0, w:1 });
      g.lab.push({ x:G.W - 74, y:y1 - 7, t:`${z.role === 'S' ? 'Support' : z.role === 'R' ? 'Résistance' : 'Zone'} ×${z.n}`, c:col }); out.push(g); });
  }
  if (UI.auto.ch && lr) {
    const i0 = Math.max(0, Math.floor(lr.from)), i1 = Math.min(n - 1, Math.ceil(lr.to)), m = i1 - i0 + 1;
    if (m >= 15) {
      let sy = 0, sxy = 0; for (let i = 0; i < m; i++) { sy += X.C[i0 + i]; sxy += i * X.C[i0 + i]; }
      const sx = m * (m - 1) / 2, sxx = (m - 1) * m * (2 * m - 1) / 6, b = (m * sxy - sx * sy) / (m * sxx - sx * sx), c0 = (sy - b * sx) / m;
      let up = -Infinity, dn = Infinity; for (let i = 0; i < m; i++) { const ln = c0 + b * i; up = Math.max(up, X.H[i0 + i] - ln); dn = Math.min(dn, X.L[i0 + i] - ln); }
      const e = m + Math.round(m * .12), pt = (i, off) => { const x = ts.logicalToCoordinate(i0 + i), y = yOf(P, c0 + b * i + off); return x == null || y == null ? null : { x, y }; };
      const A = pt(0, up), B = pt(e, up), C = pt(0, dn), D = pt(e, dn), M1 = pt(0, (up + dn) / 2), M2 = pt(e, (up + dn) / 2), g = g0();
      if (A && B && C && D && M1 && M2) { const col = b >= 0 ? '#2962ff' : '#e91e63';
        g.fill.push({ poly:[A, B, D, C], c:col, al:.07 }); g.seg.push({ a:A, b:B, c:col, ls:0, w:1.5 }, { a:C, b:D, c:col, ls:0, w:1.5 }, { a:M1, b:M2, c:col, ls:2, w:1 });
        g.lab.push({ x:A.x + 6, y:A.y - 9, t:`Canal auto · ${b >= 0 ? '+' : ''}${(b / c0 * 100).toFixed(2).replace('.', ',')} %/barre`, c:col }); out.push(g); }
    }
  }
  if (UI.auto.tl) {
    if (!P.aTL || P.aTL.X !== X || P.aTL.k !== k) P.aTL = { X, k, hi:pivA(X.H, k, true).filter(i => i >= n - 400), lo:pivA(X.L, k, false).filter(i => i >= n - 400) };
    const two = (ix, V) => { for (let j = ix.length - 1; j > 0; j--) if (ix[j] - ix[j-1] >= k * 2) return [ix[j-1], ix[j]]; return null; };
    [[P.aTL.hi, X.H, '#f23645'], [P.aTL.lo, X.L, '#089981']].forEach(([ix, V, col]) => { const t = two(ix, V); if (!t) return;
      const u = { x:ts.logicalToCoordinate(t[0]), y:yOf(P, V[t[0]]) }, v = { x:ts.logicalToCoordinate(t[1]), y:yOf(P, V[t[1]]) };
      if ([u.x, u.y, v.x, v.y].some(z => z == null)) return; const dx = v.x - u.x, dy = v.y - u.y, m = 1e5 / (Math.hypot(dx, dy) || 1), g = g0();
      g.seg.push({ a:u, b:{ x:u.x + dx * m, y:u.y + dy * m }, c:col, ls:1, w:1.5 }); out.push(g); });
  }
  return out;
}
function drawVP(ctx, P, G, it) {
  const X = P.X, lr = P.chart.timeScale().getVisibleLogicalRange(); if (!lr) return;
  const i0 = Math.max(0, Math.ceil(lr.from)), i1 = Math.min(X.T.length - 1, Math.floor(lr.to)); if (i1 <= i0) return;
  let lo = Infinity, hi = -Infinity; for (let i = i0; i <= i1; i++) { lo = Math.min(lo, X.L[i]); hi = Math.max(hi, X.H[i]); }
  const R = Math.round(it.p.rows), st = (hi - lo) / R; if (!(st > 0)) return;
  const up = Array(R).fill(0), dn = Array(R).fill(0);
  for (let i = i0; i <= i1; i++) { const r0 = Math.min(R - 1, Math.floor((X.L[i] - lo) / st)), r1 = Math.min(R - 1, Math.floor((X.H[i] - lo) / st)), sh = X.V[i] / (r1 - r0 + 1); for (let r = r0; r <= r1; r++) (X.C[i] >= X.O[i] ? up : dn)[r] += sh; }
  const mx = Math.max(...up.map((v, r) => v + dn[r])) || 1, MW = G.W * it.p.w / 100;
  ctx.save(); ctx.beginPath(); ctx.rect(0, 0, G.W, G.H); ctx.clip();
  for (let r = 0; r < R; r++) { const y1 = yOf(P, lo + (r + 1) * st), y2 = yOf(P, lo + r * st); if (y1 == null || y2 == null) continue; const h = Math.max(1, Math.abs(y2 - y1) - 1), wu = up[r] / mx * MW, wd = dn[r] / mx * MW;
    ctx.globalAlpha = .38; ctx.fillStyle = it.c[0]; ctx.fillRect(0, y1, wu, h); ctx.fillStyle = it.c[1]; ctx.fillRect(wu, y1, wd, h); }
  ctx.restore();
}

/* ---- boucle de rendu : on ne redessine que si quelque chose a bougé ---- */
function drDraw(P) {
  const ts = P.chart.timeScale(), lr = ts.getVisibleLogicalRange(), G = pgeom(P), w = P.cel.clientWidth, h = P.cel.clientHeight, last = P.X.C[P.X.C.length - 1];
  const ya = yOf(P, last), yb = yOf(P, last * 1.37);
  const sig = [lr && lr.from.toFixed(3), lr && lr.to.toFixed(3), w, h, G.H, G.W, ya && ya.toFixed(1), yb && yb.toFixed(1), DS.ver, UI.hide, UI.dark, P.cvk].join('|');
  if (sig === P.cvSig) return; P.cvSig = sig;
  const cv = P.cv, dpr = devicePixelRatio || 1; if (cv.width !== Math.round(w * dpr) || cv.height !== Math.round(h * dpr)) { cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr); cv.style.width = w + 'px'; cv.style.height = h + 'px'; }
  const ctx = cv.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  if (ya == null || !lr) return;
  ST.inds.filter(it => it.type === 'vp' && it.on && forPanel(it, P.i)).forEach(it => drawVP(ctx, P, G, it));
  autoGeoms(P, G).forEach(g => paintG(ctx, g, G, false));
  if (UI.hide) return;
  curDr().forEach(d => { const g = geom(P, d, G), sel = d.id === DS.sel; paintG(ctx, g, G, sel || d.id === DS.hov);
    if (sel) { ctx.save(); ctx.beginPath(); ctx.rect(-8, -8, G.W + 16, G.H + 16); ctx.clip();
      if (d.type !== 'brush') g.pts.forEach(q => { if (!q) return; ctx.fillStyle = '#fff'; ctx.strokeStyle = d.color; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(q.x, q.y, 5, 0, 7); ctx.fill(); ctx.stroke(); }); ctx.restore(); } });
}
function drLoop() {
  if (DS.sym !== ST.sym) { DS.sym = ST.sym; DS.sel = null; DS.draft = null; DS.hist = []; DS.ver++; }
  if (DS.dverShown !== DS.ver) { DS.dverShown = DS.ver; dbarUpdate(); }
  PN.forEach((P, k) => { if (k < nAct() && P.chart && P.X && P.cv) { try { drDraw(P); } catch (e) {} } });
  requestAnimationFrame(drLoop);
}

/* ---- souris : création, sélection, déplacement ---- */
function newDrawing(type, pt) { return { id:Date.now() + Math.random(), type, pts:[pt], color:UI.dcol || '#2962ff', w:UI.dw || 2, ls:UI.dls || 0, text:'' }; }
function finishDraw() {
  const d = DS.draft && DS.draft.d; DS.draft = null; if (d) { DS.sel = d.id; drSave(); }
  if (!UI.keep) setTool('cursor');
}
function cancelDraft() { if (DS.draft) { const L = curDr(), i = L.indexOf(DS.draft.d); if (i >= 0) L.splice(i, 1); DS.draft = null; DS.hist.pop(); DS.ver++; } }
function rel(P, e) { const r = P.cel.getBoundingClientRect(); return { x:e.clientX - r.left, y:e.clientY - r.top }; }
function drDown(P, e) {
  const { x, y } = rel(P, e), G = pgeom(P);
  if (x < 0 || x > G.W || y < 0 || y > G.H) return false;
  if (DS.draft && DS.draft.P !== P) cancelDraft();
  if (DS.draft) {
    const D = DS.draft, d = D.d, pt = snapPt(P, x, y); if (!pt) return true;
    if (D.k === 'free') return true;
    d.pts[D.k] = pt; if (D.k + 1 < NP[d.type]) { d.pts.push({ ...pt }); D.k++; D.moved = false; D.x0 = x; D.y0 = y; DS.ver++; } else finishDraw();
    return true;
  }
  if (DS.tool !== 'cursor') {
    const pt = snapPt(P, x, y); if (!pt) return false; drSnap();
    const T = DS.tool, d = newDrawing(T, pt), np = NP[T];
    if (T === 'text') { const t = prompt('Texte à afficher :'); if (!t) { DS.hist.pop(); return true; } d.text = t; d.color = UI.dcol || '#2962ff'; curDr().push(d); DS.draft = { d, P }; finishDraw(); return true; }
    curDr().push(d);
    if (np === 1) { DS.draft = { d, P }; finishDraw(); }
    else if (np === 'free') DS.draft = { d, P, k:'free' };
    else { d.pts.push({ ...pt }); DS.draft = { d, P, k:1, x0:x, y0:y, moved:false }; }
    DS.ver++; return true;
  }
  const h = pick(P, x, y, G);
  if (!h) { if (DS.sel) { DS.sel = null; DS.ver++; } return false; }
  DS.sel = h.d.id; DS.ver++;
  if (!h.d.lock && !UI.lock) { drSnap(); DS.drag = { P, d:h.d, part:h.part, x0:x, y0:y, orig:JSON.parse(JSON.stringify(h.d.pts)) }; }
  return true;
}
function drMove(P, e) {
  const { x, y } = rel(P, e), G = pgeom(P);
  if (DS.draft && DS.draft.P === P) {
    const D = DS.draft, d = D.d, pt = snapPt(P, x, y); if (!pt) return;
    if (D.k === 'free') { if (e.buttons & 1) { const q = d.pts[d.pts.length - 1], a = xOf(P, q.t), b = yOf(P, q.p); if (Math.hypot(a - x, b - y) > 3) { d.pts.push(pt); DS.ver++; } } }
    else { d.pts[D.k] = pt; if (Math.hypot(x - D.x0, y - D.y0) > 6) D.moved = true; DS.ver++; }
    return;
  }
  if (DS.drag || DS.tool !== 'cursor') return;
  const h = x >= 0 && x <= G.W && y >= 0 && y <= G.H ? pick(P, x, y, G) : null, id = h ? h.d.id : null;
  if (id !== DS.hov) { DS.hov = id; DS.ver++; }
  P.el.classList.toggle('mv', !!h && h.part === 'b'); P.el.classList.toggle('pt', !!h && h.part !== 'b');
}
addEventListener('pointermove', e => {
  const D = DS.drag; if (!D) return; const { x, y } = rel(D.P, e), P = D.P;
  if (D.part === 'b') { D.d.pts = D.orig.map(q => ptOf(P, xOf(P, q.t) + x - D.x0, yOf(P, q.p) + y - D.y0) || q); }
  else { const pt = snapPt(P, x, y); if (pt) D.d.pts[+D.part.slice(1)] = pt; }
  DS.ver++;
}, true);
addEventListener('pointerup', () => {
  if (DS.drag) { DS.drag = null; drSave(); }
  const D = DS.draft;
  if (D) {
    if (D.k === 'free') finishDraw();
    else if (D.moved && D.k === 1) { if (NP[D.d.type] === 2) finishDraw(); else { D.d.pts.push({ ...D.d.pts[1] }); D.k = 2; D.moved = false; DS.ver++; } }
  }
  setTimeout(() => { DS.block = false; }, 0);
}, true);
function drawInit(P) {
  P.cv = document.createElement('canvas'); P.cv.className = 'dcv'; P.cel.appendChild(P.cv);
  const stop = e => { if (DS.block) e.stopPropagation(); };
  ['mousedown', 'touchstart'].forEach(t => P.cel.addEventListener(t, stop, true));
  P.cel.addEventListener('pointerdown', e => { DS.block = false; if (e.button !== 0 || !P.chart || !P.X) return; if (drDown(P, e)) { DS.block = true; e.stopPropagation(); } }, true);
  P.cel.addEventListener('pointermove', e => { if (P.chart && P.X) drMove(P, e); }, true);
  P.cel.addEventListener('contextmenu', e => { if (DS.tool !== 'cursor' || DS.draft) { e.preventDefault(); e.stopPropagation(); cancelDraft(); setTool('cursor'); } }, true);
  P.cel.addEventListener('dblclick', e => {
    if (!P.chart || !P.X) return; const { x, y } = rel(P, e), h = pick(P, x, y, pgeom(P));
    if (h && h.d.type === 'text') { const t = prompt('Texte :', h.d.text); if (t) { drSnap(); h.d.text = t; drSave(); } }
  }, true);
}

/* ---- barre d'outils, menus déroulants, propriétés ---- */
function setTool(t) {
  if (DS.draft) cancelDraft(); DS.tool = t; DS.ver++;
  PN.forEach(P => { P.el.classList.toggle('dm', t !== 'cursor'); if (t !== 'cursor') P.el.classList.remove('mv', 'pt'); });
  TOOLS.forEach(g => { if (g.g !== 'cur' && g.items.some(it => Array.isArray(it) && it[0] === t)) UI.lastT[g.g] = t; });
  tbRefresh(); closeFly();
}
function tbRefresh() {
  document.querySelectorAll('#dtools .tb[data-g]:not(#tb-aut)').forEach(b => {
    const grp = TOOLS.find(x => x.g === b.dataset.g), its = grp.items.filter(Array.isArray), inG = its.some(it => it[0] === DS.tool);
    const cur = inG ? DS.tool : (UI.lastT[grp.g] || its[0][0]);
    b.classList.toggle('on', inG); b.innerHTML = svg(cur) + (its.length > 1 ? '<span class="arw">▸</span>' : ''); b.title = NAME[cur];
  });
  const set = (id, on) => { const b = $(id); if (b) b.classList.toggle('on', !!on); };
  set('#tb-mag', UI.mag); set('#tb-keep', UI.keep); set('#tb-lock', UI.lock); set('#tb-hide', UI.hide); set('#tb-aut', UI.auto.sr || UI.auto.ch || UI.auto.tl);
}
const FLY = $('#dfly');
function closeFly() { FLY.hidden = true; FLY.innerHTML = ''; FLY.dataset.g = ''; }
function openFly(g, btn) {
  if (!FLY.hidden && FLY.dataset.g === g) { closeFly(); return; }
  let h = '';
  if (g === 'aut') {
    const row = (k, t, on) => `<div class="fi" data-a="${k}"><span class="ck">${on ? '✓' : ''}</span><span>${t}</span></div>`;
    h = '<div class="fl">DÉTECTION AUTOMATIQUE</div>' + row('sr', 'Zones de support / résistance', UI.auto.sr) + row('ch', 'Canal de tendance (zone visible)', UI.auto.ch) + row('tl', 'Lignes de tendance', UI.auto.tl)
      + `<div class="fi" data-a="sens"><span class="ck">⇅</span><span>Sensibilité des pivots : <b>${SENS[UI.sens ?? 1]}</b></span></div>`;
  } else h = TOOLS.find(x => x.g === g).items.map(it => Array.isArray(it) ? `<div class="fi${DS.tool === it[0] ? ' on' : ''}" data-t="${it[0]}">${svg(it[0])}<span>${it[1]}</span></div>` : `<div class="fl">${it}</div>`).join('');
  FLY.innerHTML = h; FLY.dataset.g = g; FLY.hidden = false; const r = btn.getBoundingClientRect(); FLY.style.left = (r.right + 4) + 'px'; FLY.style.top = Math.max(4, Math.min(r.top, innerHeight - FLY.offsetHeight - 6)) + 'px';
}
function dbarUpdate() {
  const d = curDr().find(x => x.id === DS.sel), bar = $('#dbar'); bar.hidden = !d || UI.hide; if (!d) return;
  $('#dbc').value = d.color; $('#dbw').value = String(d.w); $('#dbl').value = String(d.ls); $('#dbk').classList.toggle('on', !!d.lock);
}
function initChrome() {
  const box = $('#dtools');
  box.innerHTML = TOOLS.map(g => `<button class="tb" data-g="${g.g}"></button>`).join('')
    + '<button class="tb" id="tb-aut" title="Détection automatique (supports, résistances, canaux)" data-g="aut">' + svg('aut') + '<span class="arw">▸</span></button><div class="tbsep"></div>'
    + [['mag', 'Aimant : accrocher aux bougies'], ['keep', 'Rester en mode dessin'], ['lock', 'Verrouiller tous les dessins'], ['hide', 'Masquer / afficher les dessins']].map(([k, t]) => `<button class="tb" id="tb-${k}" title="${t}">${svg(k === 'hide' ? 'eye' : k)}</button>`).join('')
    + `<button class="tb" id="tb-del" title="Supprimer tous les dessins de ce titre">${svg('trash')}</button>`;
  box.addEventListener('click', e => {
    const b = e.target.closest('.tb'); if (!b) return; const g = b.dataset.g;
    if (g) { const grp = TOOLS.find(x => x.g === g); if (g === 'aut' || e.target.closest('.arw')) openFly(g, b); else if (grp.g === 'cur') setTool('cursor'); else setTool(UI.lastT[g] || grp.items.find(Array.isArray)[0]); return; }
    if (b.id === 'tb-del') { if (curDr().length && confirm('Supprimer tous les dessins de ' + ST.sym + ' ?')) { drSnap(); DR[ST.sym] = []; DS.sel = null; drSave(); } return; }
    const k = b.id.slice(3); UI[k] = UI[k] ? 0 : 1; uiSave(); DS.ver++; tbRefresh(); dbarUpdate();
  });
  FLY.addEventListener('click', e => {
    const f = e.target.closest('.fi'); if (!f) return;
    if (f.dataset.t) { setTool(f.dataset.t); return; }
    const a = f.dataset.a; if (a === 'sens') UI.sens = ((UI.sens ?? 1) + 1) % 3; else UI.auto[a] = UI.auto[a] ? 0 : 1;
    PN.forEach(P => { P.aSR = null; P.aTL = null; }); uiSave(); DS.ver++; tbRefresh(); const b = $('#tb-aut'); FLY.dataset.g = ''; openFly('aut', b);
  });
  addEventListener('pointerdown', e => { if (!FLY.hidden && !FLY.contains(e.target) && !e.target.closest('#dtools')) closeFly(); }, true);
  $('#ltbx').addEventListener('click', () => { UI.ltb = UI.ltb ? 0 : 1; applyLtb(); uiSave(); });
  const bar = $('#dbar'), sel = () => curDr().find(x => x.id === DS.sel);
  const upd = fn => { const d = sel(); if (!d) return; drSnap(); fn(d); drSave(); };
  $('#dbc').addEventListener('input', e => { UI.dcol = e.target.value; upd(d => { d.color = UI.dcol; }); uiSave(); });
  $('#dbw').addEventListener('change', e => { UI.dw = +e.target.value; upd(d => { d.w = UI.dw; }); uiSave(); });
  $('#dbl').addEventListener('change', e => { UI.dls = +e.target.value; upd(d => { d.ls = UI.dls; }); uiSave(); });
  $('#dbk').addEventListener('click', () => upd(d => { d.lock = !d.lock; }));
  $('#dbd').addEventListener('click', () => { const d = sel(); if (!d) return; drSnap(); const c = JSON.parse(JSON.stringify(d)); c.id = Date.now() + Math.random(); c.pts.forEach(q => { q.p *= 1.01; }); curDr().push(c); DS.sel = c.id; drSave(); });
  $('#dbx').addEventListener('click', () => { const d = sel(); if (!d) return; drSnap(); DR[ST.sym] = curDr().filter(x => x !== d); DS.sel = null; drSave(); });
  addEventListener('keydown', e => {
    const tg = (document.activeElement || {}).tagName; if (/INPUT|SELECT|TEXTAREA/.test(tg)) return;
    if (e.key === 'Escape') { if (DS.draft) cancelDraft(); setTool('cursor'); DS.sel = null; DS.ver++; }
    else if ((e.key === 'Delete' || e.key === 'Backspace') && DS.sel) { const d = sel(); if (d && !d.lock) { drSnap(); DR[ST.sym] = curDr().filter(x => x !== d); DS.sel = null; drSave(); e.preventDefault(); } }
    else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z' && DS.hist.length) { DR[ST.sym] = JSON.parse(DS.hist.pop()); DS.sel = null; drSave(); e.preventDefault(); }
  });
  $('#cup').value = UI.cup; $('#cdn').value = UI.cdn;
  [['#cup', 'cup'], ['#cdn', 'cdn']].forEach(([s, k]) => $(s).addEventListener('input', e => { UI[k] = e.target.value; uiSave(); clearTimeout(ctm); ctm = setTimeout(() => build(true), 60); }));
  $('#theme').addEventListener('click', () => { UI.dark = UI.dark ? 0 : 1; layUI(); build(true); uiSave(); $('#theme').textContent = UI.dark ? '☀' : '☾'; });
  $('#theme').textContent = UI.dark ? '☀' : '☾';
  applyLtb(); tbRefresh(); requestAnimationFrame(drLoop);
}
function applyLtb() { $('#ltb').classList.toggle('col', !UI.ltb); $('#ltbx').textContent = UI.ltb ? '‹' : '›'; $('#ltbx').title = UI.ltb ? 'Replier la barre d’outils' : 'Déplier la barre d’outils'; closeFly(); }

/* ================= Démarrage ================= */
mkPanels();
if (!restore()) defaults();
uiRestore(); syncReg(); initChrome(); applyPane();
layUI();
PN.forEach((P, i) => { P.iv = ST.ivs[i]; });
syncUI(); side(); load();
</script>
</body>
</html>
"""


if __name__ == "__main__":
    if "--verifier-listes" in sys.argv:
        verifier_listes()
        sys.exit()
    serveur = None
    for port in range(PORT, PORT + 10):          # une ancienne instance peut occuper 8765 : on prend le port suivant
        try:
            serveur = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            continue
    if serveur is None:
        sys.exit(f"Aucun port libre entre {PORT} et {PORT + 9} : fermez les anciennes fenêtres du script.")
    url = f"http://127.0.0.1:{port}"
    print(f"Graphique (v12 : screener TradingView, outils de dessin, indicateurs) disponible sur {url}  (Ctrl+C pour arrêter)")
    if port != PORT:
        print(f"Note : le port {PORT} était déjà pris par une ancienne instance (fermez-la pour éviter la confusion).")
    threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        serveur.serve_forever()
    except KeyboardInterrupt:
        print("\nArrêt.")