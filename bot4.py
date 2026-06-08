import os
import json
import random
import asyncio
import re
import shutil
import threading
import unicodedata
import calendar
import io
import textwrap
import atexit
import base64
from collections import Counter
from pathlib import Path
from datetime import datetime
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote
from urllib import error as urlerror
from urllib import request as urlrequest

import aiohttp
import discord
from discord.ext import commands, tasks
from dotenv import load_dotenv
from google import genai

try:
    from PIL import Image, ImageDraw, ImageFont
except ImportError:
    Image = ImageDraw = ImageFont = None


# ==============================================================================
# CONFIGURAÇÃO
# ==============================================================================

load_dotenv()

DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
COMMAND_PREFIX = os.getenv("PREFIX", "!")
_SCRIPT_DIR = Path(__file__).resolve().parent
_DATA_DIR = Path(os.getenv("BOT_DATA_DIR", _SCRIPT_DIR)).expanduser().resolve()
_DATA_DIR.mkdir(parents=True, exist_ok=True)
DATA_FILE = Path(os.getenv("BOT_DATA_FILE", _DATA_DIR / "dados_bot.json")).expanduser().resolve()
BACKUP_FILE = DATA_FILE.with_name(f"{DATA_FILE.stem}.backup.json")
_dados_lock = threading.Lock()
SUPABASE_URL = os.getenv("SUPABASE_URL", "").rstrip("/")
SUPABASE_KEY = os.getenv("SUPABASE_KEY", "")
JSONBIN_BIN_ID = os.getenv("JSONBIN_BIN_ID", "")
JSONBIN_API_KEY = os.getenv("JSONBIN_API_KEY", "")
BOT_DATA_URL = os.getenv("BOT_DATA_URL", "")
BOT_DATA_SAVE_URL = os.getenv("BOT_DATA_SAVE_URL", BOT_DATA_URL)
BOT_DATA_TOKEN = os.getenv("BOT_DATA_TOKEN", "")
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN", "")
GITHUB_REPO = os.getenv("GITHUB_REPO", os.getenv("GITHUB_REPOSITORY", ""))
GITHUB_BRANCH = os.getenv("GITHUB_BRANCH", "main")
GITHUB_DATA_PATH = os.getenv("GITHUB_DATA_PATH", "dados_bot.json")
_github_file_sha: Optional[str] = None
_ultimo_snapshot: Optional[str] = None
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")
VAZIO_ALFABETO = "❌ Vazio"

if not DISCORD_TOKEN:
    raise RuntimeError("Falta DISCORD_TOKEN no ficheiro .env")
if not GEMINI_API_KEY:
    raise RuntimeError("Falta GEMINI_API_KEY no ficheiro .env")

ai_client = genai.Client(api_key=GEMINI_API_KEY)

META_ANUAL = 80
MESES_ORDEM = [
    "Janeiro", "Fevereiro", "Março", "Abril", "Maio", "Junho",
    "Julho", "Agosto", "Setembro", "Outubro", "Novembro", "Dezembro"
]
SEPARADOR_LIVRO = " - "
NOTAS_DISPONIVEIS = [i * 0.25 for i in range(1, 21)]
READMORE_API_URL = os.getenv("READMORE_API_URL", "https://readmore.onrender.com")


# ==============================================================================
# PERSISTÊNCIA
# ==============================================================================

def estado_inicial() -> Dict[str, Any]:
    return {
        "livros_lidos": [],
        "review_em_andamento": {},
        "lembretes_metas": [],
        "sugestoes_vistas": [],
        "sorteios_mes": {},
        "tbr_por_mes": {
            "Geral": [],
            "Janeiro": [], "Fevereiro": [], "Março": [], "Abril": [],
            "Maio": [], "Junho": [], "Julho": [], "Agosto": [],
            "Setembro": [], "Outubro": [], "Novembro": [], "Dezembro": []
        },
        "desafio_alfabeto": {letra: VAZIO_ALFABETO for letra in "ABCDEFGHIJKLMNOPQRSTUVWXYZ"}
    }


def normalizar_tbr_por_mes(tbr: Any) -> Dict[str, List[str]]:
    base = estado_inicial()["tbr_por_mes"]
    if not isinstance(tbr, dict):
        return {mes: list(livros) for mes, livros in base.items()}

    resultado = {mes: list(base[mes]) for mes in base}
    for mes, livros in tbr.items():
        if mes not in resultado:
            continue
        if isinstance(livros, list):
            resultado[mes] = [str(livro) for livro in livros if str(livro).strip()]
        else:
            resultado[mes] = []
    return resultado


def aplicar_dados_carregados(bruto: Dict[str, Any]) -> Dict[str, Any]:
    base = estado_inicial()
    base.update(bruto)
    base["tbr_por_mes"] = normalizar_tbr_por_mes(bruto.get("tbr_por_mes"))
    base["desafio_alfabeto"] = {
        **estado_inicial()["desafio_alfabeto"],
        **(bruto.get("desafio_alfabeto") if isinstance(bruto.get("desafio_alfabeto"), dict) else {}),
    }
    base["sugestoes_vistas"] = list(bruto.get("sugestoes_vistas", []))
    base["sorteios_mes"] = dict(bruto.get("sorteios_mes", {}))
    base["livros_lidos"] = migrar_livros_lidos(bruto.get("livros_lidos", []))
    base["lembretes_metas"] = list(bruto.get("lembretes_metas", []))
    base["review_em_andamento"] = dict(bruto.get("review_em_andamento", {}))
    return base


def _ler_ficheiro_dados(ficheiro: Path) -> Dict[str, Any]:
    with open(ficheiro, "r", encoding="utf-8") as f:
        bruto = json.load(f)
    if not isinstance(bruto, dict):
        raise ValueError("Formato inválido")
    return aplicar_dados_carregados(bruto)


def em_nuvem() -> bool:
    return any(
        os.getenv(var)
        for var in ("RENDER", "RAILWAY_ENVIRONMENT", "DYNO", "FLY_APP_NAME", "K_SERVICE", "VERCEL")
    )


def modo_armazenamento() -> str:
    if GITHUB_TOKEN and GITHUB_REPO:
        return "github"
    if SUPABASE_URL and SUPABASE_KEY:
        return "supabase"
    if JSONBIN_BIN_ID and JSONBIN_API_KEY:
        return "jsonbin"
    if BOT_DATA_URL:
        return "url"
    return "local"


def _snapshot_dados() -> str:
    return json.dumps(dados, sort_keys=True, ensure_ascii=False)


def _github_headers() -> Dict[str, str]:
    return {
        "Authorization": f"Bearer {GITHUB_TOKEN}",
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }


def _parse_github_repo() -> Tuple[str, str]:
    repo = GITHUB_REPO.strip()
    if "/" not in repo:
        raise ValueError("GITHUB_REPO deve estar no formato owner/repo")
    owner, nome = repo.split("/", 1)
    return owner.strip(), nome.strip()


def carregar_github() -> Dict[str, Any]:
    global _github_file_sha
    owner, repo = _parse_github_repo()
    url = (
        f"https://api.github.com/repos/{owner}/{repo}/contents/"
        f"{quote(GITHUB_DATA_PATH)}?ref={quote(GITHUB_BRANCH)}"
    )
    try:
        payload = _pedido_http("GET", url, cabecalhos=_github_headers())
    except urlerror.HTTPError as erro:
        if erro.code == 404:
            _github_file_sha = None
            return estado_inicial()
        raise

    if not isinstance(payload, dict):
        return estado_inicial()

    _github_file_sha = payload.get("sha")
    conteudo_b64 = str(payload.get("content", "")).replace("\n", "")
    if not conteudo_b64:
        return estado_inicial()

    bruto = json.loads(base64.b64decode(conteudo_b64).decode("utf-8"))
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_github() -> None:
    global _github_file_sha
    owner, repo = _parse_github_repo()
    url = f"https://api.github.com/repos/{owner}/{repo}/contents/{quote(GITHUB_DATA_PATH)}"
    conteudo = json.dumps(dados, ensure_ascii=False, indent=2)
    corpo: Dict[str, Any] = {
        "message": f"chore(bot): atualizar {GITHUB_DATA_PATH}",
        "content": base64.b64encode(conteudo.encode("utf-8")).decode("ascii"),
        "branch": GITHUB_BRANCH,
    }
    if _github_file_sha:
        corpo["sha"] = _github_file_sha

    payload = _pedido_http("PUT", url, corpo=corpo, cabecalhos=_github_headers())
    if isinstance(payload, dict) and isinstance(payload.get("content"), dict):
        _github_file_sha = payload["content"].get("sha", _github_file_sha)


def _pedido_http(
    metodo: str,
    url: str,
    corpo: Optional[Dict[str, Any]] = None,
    cabecalhos: Optional[Dict[str, str]] = None,
    timeout: int = 20,
) -> Any:
    cabecalhos = cabecalhos or {}
    dados_bytes = None
    if corpo is not None:
        dados_bytes = json.dumps(corpo).encode("utf-8")
        cabecalhos.setdefault("Content-Type", "application/json")

    pedido = urlrequest.Request(url, data=dados_bytes, headers=cabecalhos, method=metodo)
    with urlrequest.urlopen(pedido, timeout=timeout) as resposta:
        texto = resposta.read().decode("utf-8")
        if not texto.strip():
            return None
        return json.loads(texto)


def carregar_supabase() -> Dict[str, Any]:
    url = f"{SUPABASE_URL}/rest/v1/bot_state?id=eq.1&select=data"
    cabecalhos = {
        "apikey": SUPABASE_KEY,
        "Authorization": f"Bearer {SUPABASE_KEY}",
    }
    payload = _pedido_http("GET", url, cabecalhos=cabecalhos)
    if not payload:
        return estado_inicial()
    if isinstance(payload, list) and payload:
        bruto = payload[0].get("data", {})
    elif isinstance(payload, dict):
        bruto = payload.get("data", payload)
    else:
        return estado_inicial()
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_supabase() -> None:
    url = f"{SUPABASE_URL}/rest/v1/bot_state?id=eq.1"
    cabecalhos = {
        "apikey": SUPABASE_KEY,
        "Authorization": f"Bearer {SUPABASE_KEY}",
        "Prefer": "return=minimal",
    }
    try:
        _pedido_http("PATCH", url, corpo={"data": dados}, cabecalhos=cabecalhos)
    except urlerror.HTTPError as erro:
        if erro.code != 404:
            raise
        criar_url = f"{SUPABASE_URL}/rest/v1/bot_state"
        cabecalhos["Prefer"] = "resolution=merge-duplicates"
        _pedido_http("POST", criar_url, corpo={"id": 1, "data": dados}, cabecalhos=cabecalhos)


def carregar_jsonbin() -> Dict[str, Any]:
    url = f"https://api.jsonbin.io/v3/b/{JSONBIN_BIN_ID}/latest"
    cabecalhos = {"X-Master-Key": JSONBIN_API_KEY}
    payload = _pedido_http("GET", url, cabecalhos=cabecalhos)
    if not isinstance(payload, dict):
        return estado_inicial()
    bruto = payload.get("record", payload)
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_jsonbin() -> None:
    url = f"https://api.jsonbin.io/v3/b/{JSONBIN_BIN_ID}"
    cabecalhos = {
        "X-Master-Key": JSONBIN_API_KEY,
        "Content-Type": "application/json",
    }
    _pedido_http("PUT", url, corpo=dados, cabecalhos=cabecalhos)


def carregar_url() -> Dict[str, Any]:
    cabecalhos = {}
    if BOT_DATA_TOKEN:
        cabecalhos["Authorization"] = f"Bearer {BOT_DATA_TOKEN}"
    payload = _pedido_http("GET", BOT_DATA_URL, cabecalhos=cabecalhos)
    if not isinstance(payload, dict):
        return estado_inicial()
    return aplicar_dados_carregados(payload)


def guardar_url() -> None:
    cabecalhos = {}
    if BOT_DATA_TOKEN:
        cabecalhos["Authorization"] = f"Bearer {BOT_DATA_TOKEN}"
    _pedido_http("PUT", BOT_DATA_SAVE_URL, corpo=dados, cabecalhos=cabecalhos)


def _guardar_local() -> None:
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    temp = DATA_FILE.with_suffix(".tmp.json")
    conteudo = json.dumps(dados, ensure_ascii=False, indent=2)
    temp.write_text(conteudo, encoding="utf-8")
    if DATA_FILE.exists():
        shutil.copy2(DATA_FILE, BACKUP_FILE)
    temp.replace(DATA_FILE)


def carregar_dados() -> Dict[str, Any]:
    modo = modo_armazenamento()

    if modo == "github":
        try:
            estado = carregar_github()
            print(f"🐙 Dados carregados do GitHub: {GITHUB_REPO}/{GITHUB_DATA_PATH}")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha GitHub, a tentar local: {erro}")
    elif modo == "supabase":
        try:
            estado = carregar_supabase()
            print("☁️ Dados carregados do Supabase.")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha Supabase, a tentar local: {erro}")
    elif modo == "jsonbin":
        try:
            estado = carregar_jsonbin()
            print("☁️ Dados carregados do JSONBin.")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha JSONBin, a tentar local: {erro}")
    elif modo == "url":
        try:
            estado = carregar_url()
            print(f"☁️ Dados carregados de: {BOT_DATA_URL}")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha URL remota, a tentar local: {erro}")

    for ficheiro in (DATA_FILE, BACKUP_FILE):
        if not ficheiro.exists():
            continue
        try:
            estado = _ler_ficheiro_dados(ficheiro)
            print(f"📂 Dados carregados de: {ficheiro}")
            return estado
        except (OSError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha ao ler {ficheiro}: {erro}")

    if em_nuvem() and modo == "local":
        print(
            "⚠️ ATENÇÃO: Bot na nuvem sem armazenamento remoto. "
            "A TBR perde-se a cada reinício/deploy. Configura GitHub, Supabase ou JSONBin."
        )
    else:
        print(f"📂 Ficheiro novo — a criar em: {DATA_FILE}")
    return estado_inicial()


def guardar_dados() -> None:
    global _ultimo_snapshot
    with _dados_lock:
        snapshot = _snapshot_dados()
        if snapshot == _ultimo_snapshot:
            return

        modo = modo_armazenamento()
        erro_remoto = None

        if modo == "github":
            try:
                guardar_github()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "supabase":
            try:
                guardar_supabase()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "jsonbin":
            try:
                guardar_jsonbin()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "url":
            try:
                guardar_url()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro

        if modo == "local" or not erro_remoto:
            try:
                _guardar_local()
            except OSError as erro:
                if modo == "local":
                    raise
                print(f"⚠️ Cache local indisponível: {erro}")

        if erro_remoto:
            raise RuntimeError(f"Falha ao guardar no remoto ({modo}): {erro_remoto}") from erro_remoto

        _ultimo_snapshot = snapshot


def resumo_persistencia() -> str:
    total_tbr = sum(len(v) for v in dados.get("tbr_por_mes", {}).values())
    modo = modo_armazenamento()
    linhas = [f"Modo: **{modo}**", f"TBR: **{total_tbr}** livros | Lidos: **{len(dados.get('livros_lidos', []))}**"]

    if modo == "github":
        linhas.append(f"Repositório: `{GITHUB_REPO}` · ficheiro `{GITHUB_DATA_PATH}` · branch `{GITHUB_BRANCH}`")
    elif modo == "local":
        linhas.append(f"Ficheiro local: `{DATA_FILE}`")
        if em_nuvem():
            linhas.append(
                "⚠️ **Bot na nuvem com disco temporário** — os dados apagam-se ao reiniciar. "
                "Configura **GitHub** (usa `!armazenamento`)."
            )
    elif modo == "supabase":
        linhas.append(f"Remoto: `{SUPABASE_URL}` (tabela `bot_state`)")
    elif modo == "jsonbin":
        linhas.append(f"Remoto: JSONBin `{JSONBIN_BIN_ID}`")
    elif modo == "url":
        linhas.append(f"Remoto: `{BOT_DATA_URL}`")

    return "\n".join(linhas)


# ==============================================================================
# HELPERS
# ==============================================================================

def migrar_livros_lidos(livros: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    resultado = []
    for livro in livros:
        if not isinstance(livro, dict):
            continue
        copia = dict(livro)
        titulo = str(copia.get("titulo", "")).strip()
        if SEPARADOR_LIVRO not in titulo and copia.get("autor"):
            copia["titulo"] = formatar_livro(titulo, str(copia["autor"]))
        if "nota" not in copia and copia.get("estrelas") not in (None, "Sem avaliação"):
            copia["nota"] = estrelas_para_nota(str(copia.get("estrelas", "")))
        if "data_leitura" not in copia:
            copia["data_leitura"] = copia.get("data_leitura", "")
        resultado.append(copia)
    return resultado


def formatar_livro(titulo: str, autor: str) -> str:
    titulo = titulo.strip()
    autor = autor.strip()
    if SEPARADOR_LIVRO in titulo:
        return titulo
    if not autor:
        raise ValueError("autor_obrigatorio")
    return f"{titulo}{SEPARADOR_LIVRO}{autor}"


def parsear_livro(texto: str) -> Tuple[str, str]:
    texto = texto.strip()
    if SEPARADOR_LIVRO not in texto:
        raise ValueError("autor_obrigatorio")
    titulo, autor = texto.rsplit(SEPARADOR_LIVRO, 1)
    titulo, autor = titulo.strip(), autor.strip()
    if not titulo or not autor:
        raise ValueError("autor_obrigatorio")
    return titulo, autor


def livro_completo(texto: str) -> str:
    if SEPARADOR_LIVRO in texto:
        return texto.strip()
    raise ValueError("autor_obrigatorio")


def estrelas_para_texto(nota: float) -> str:
    if nota <= 0:
        return "Sem avaliação"
    cheias = int(nota)
    resto = round(nota - cheias, 2)
    texto = "⭐" * cheias
    if resto == 0.25:
        texto += "¼"
    elif resto == 0.5:
        texto += "½"
    elif resto == 0.75:
        texto += "¾"
    elif resto > 0:
        texto += f" ({nota})"
    return texto or f"{nota}⭐"


def estrelas_para_nota(estrelas: str) -> float:
    if not estrelas or estrelas == "Sem avaliação":
        return 0.0
    nota = estrelas.count("⭐")
    if "¼" in estrelas:
        nota += 0.25
    elif "½" in estrelas:
        nota += 0.5
    elif "¾" in estrelas:
        nota += 0.75
    return float(nota)


def nota_valida(nota: float) -> bool:
    return nota in NOTAS_DISPONIVEIS


def livro_ja_lido(titulo_completo: str) -> bool:
    alvo = titulo_completo.lower().strip()
    return any(l.get("titulo", "").lower().strip() == alvo for l in dados["livros_lidos"])


def nota_do_livro(livro: Dict[str, Any]) -> float:
    nota = livro.get("nota")
    if isinstance(nota, (int, float)) and nota > 0:
        return float(nota)
    return estrelas_para_nota(str(livro.get("estrelas", "")))


def livros_bem_avaliados(minimo: float = 4.0) -> List[Dict[str, Any]]:
    resultado = []
    for livro in dados["livros_lidos"]:
        titulo = str(livro.get("titulo", "")).strip()
        if not titulo:
            continue
        nota = nota_do_livro(livro)
        if nota >= minimo:
            resultado.append({**livro, "nota": nota})
    return resultado


def sorteio_mes_ativo(mes: str) -> Optional[Dict[str, Any]]:
    info = dados["sorteios_mes"].get(mes)
    if not info:
        return None
    livros = info.get("livros", [])
    lidos = {l.lower().strip() for l in info.get("lidos", [])}
    pendentes = [l for l in livros if l.lower().strip() not in lidos]
    if pendentes:
        info["pendentes"] = pendentes
        return info
    return None


def marcar_livro_sorteio_lido(titulo_completo: str) -> List[str]:
    meses_desbloqueados = []
    alvo = titulo_completo.lower().strip()
    for mes, info in dados["sorteios_mes"].items():
        livros = [l.lower().strip() for l in info.get("livros", [])]
        if alvo in livros:
            lidos = info.setdefault("lidos", [])
            if titulo_completo not in lidos and alvo not in {x.lower().strip() for x in lidos}:
                for livro in info.get("livros", []):
                    if livro.lower().strip() == alvo:
                        lidos.append(livro)
                        break
            pendentes = [l for l in info.get("livros", []) if l.lower().strip() not in {x.lower().strip() for x in lidos}]
            if not pendentes:
                meses_desbloqueados.append(mes)
    return meses_desbloqueados


async def obter_canal_discord(canal_id: int) -> Optional[discord.abc.Messageable]:
    canal = bot.get_channel(canal_id)
    if canal:
        return canal
    try:
        return await bot.fetch_channel(canal_id)
    except (discord.NotFound, discord.HTTPException):
        return None


async def pesquisar_open_library(query: str) -> Optional[Dict[str, Any]]:
    url = f"https://openlibrary.org/search.json?q={quote(query)}&limit=1"
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=12)) as resp:
                if resp.status != 200:
                    return None
                payload = await resp.json()
    except (aiohttp.ClientError, asyncio.TimeoutError, json.JSONDecodeError):
        return None

    docs = payload.get("docs", [])
    if not docs:
        return None

    doc = docs[0]
    autores = doc.get("author_name", [])
    return {
        "titulo": doc.get("title", query),
        "autor": autores[0] if autores else "Desconhecido",
        "genero": ", ".join(doc.get("subject", [])[:3]) or "N/D",
        "paginas": doc.get("number_of_pages_median") or doc.get("number_of_pages", 0),
        "ano": doc.get("first_publish_year", "N/D"),
        "capa": f"https://covers.openlibrary.org/b/id/{doc['cover_i']}-L.jpg" if doc.get("cover_i") else "",
        "fonte": "Open Library",
    }


async def pesquisar_readmore(query: str) -> Optional[Dict[str, Any]]:
    if not READMORE_API_URL:
        return None
    endpoints = [
        f"{READMORE_API_URL.rstrip('/')}/books/search?q={quote(query)}",
        f"{READMORE_API_URL.rstrip('/')}/api/books/search?q={quote(query)}",
    ]
    try:
        async with aiohttp.ClientSession() as session:
            for url in endpoints:
                try:
                    async with session.get(url, timeout=aiohttp.ClientTimeout(total=8)) as resp:
                        if resp.status != 200:
                            continue
                        payload = await resp.json()
                except (aiohttp.ClientError, asyncio.TimeoutError):
                    continue

                livros = payload if isinstance(payload, list) else payload.get("results", payload.get("books", []))
                if not livros:
                    continue
                livro = livros[0]
                return {
                    "titulo": livro.get("title", livro.get("titulo", query)),
                    "autor": livro.get("author", livro.get("autor", "Desconhecido")),
                    "genero": livro.get("genre", livro.get("genero", "N/D")),
                    "paginas": livro.get("pages", livro.get("paginas", 0)),
                    "ano": livro.get("year", livro.get("ano", "N/D")),
                    "capa": livro.get("cover", livro.get("capa", "")),
                    "fonte": "ReadMore",
                }
    except Exception:
        return None
    return None


async def obter_info_livro(query: str) -> Dict[str, Any]:
    readmore = await pesquisar_readmore(query)
    if readmore:
        return readmore
    open_lib = await pesquisar_open_library(query)
    if open_lib:
        return open_lib
    return {
        "titulo": query,
        "autor": "Desconhecido",
        "genero": "N/D",
        "paginas": 0,
        "ano": "N/D",
        "capa": "",
        "fonte": "IA",
    }


def normalizar_categoria(categoria: str) -> str:
    categoria = categoria.strip().capitalize()
    return categoria


def livros_tbr_flat() -> List[str]:
    return [livro for lista in dados["tbr_por_mes"].values() for livro in lista]


def buscar_livro_case_insensitive(lista: List[str], alvo: str) -> Optional[str]:
    alvo_lower = alvo.lower().strip()
    for item in lista:
        if item.lower().strip() == alvo_lower:
            return item
    return None


def adicionar_livro_a_tbr_mes(livro: str, mes: str) -> str:
    existente_no_mes = buscar_livro_case_insensitive(dados["tbr_por_mes"][mes], livro)
    if existente_no_mes:
        return f"📌 **{existente_no_mes}** já estava na TBR de **{mes}**."

    removido_de = []
    titulo_a_guardar = livro

    for categoria, lista in dados["tbr_por_mes"].items():
        if categoria == mes:
            continue

        existente = buscar_livro_case_insensitive(lista, livro)
        if existente:
            lista.remove(existente)
            removido_de.append(categoria)
            titulo_a_guardar = existente

    dados["tbr_por_mes"][mes].append(titulo_a_guardar)

    if removido_de:
        return (
            f"📚 **{titulo_a_guardar}** foi movido da TBR de "
            f"**{', '.join(removido_de)}** para **{mes}**."
        )

    return f"📚 **{titulo_a_guardar}** foi adicionado automaticamente à TBR de **{mes}**."


def canal_nome_seguro(base: str) -> str:
    texto = unicodedata.normalize("NFKD", base.lower().strip())
    texto = "".join(ch for ch in texto if not unicodedata.combining(ch))
    texto = re.sub(r"\s+", "-", texto)
    return "".join(ch for ch in texto if ch.isalnum() or ch == "-")


def hoje_str() -> str:
    return datetime.now().strftime("%d/%m/%Y")


def este_ano() -> str:
    return datetime.now().strftime("%Y")


def extrair_texto_gemini(response: Any) -> str:
    texto = getattr(response, "text", None)
    if texto:
        return texto.strip()
    return ""


def gemini_text(prompt: str) -> str:
    response = ai_client.models.generate_content(
        model=GEMINI_MODEL,
        contents=prompt
    )
    return extrair_texto_gemini(response)


def gemini_json(prompt: str) -> Dict[str, Any]:
    response = ai_client.models.generate_content(
        model=GEMINI_MODEL,
        contents=prompt,
        config={"response_mime_type": "application/json"}
    )
    texto = extrair_texto_gemini(response)
    texto = re.sub(r"^```(?:json)?\s*|\s*```$", "", texto.strip(), flags=re.IGNORECASE)
    if "{" in texto and "}" in texto:
        texto = texto[texto.find("{"):texto.rfind("}") + 1]
    return json.loads(texto)


async def enviar_mensagem_longa(canal: discord.abc.Messageable, texto: str, limite: int = 1900) -> None:
    partes = []
    bloco_atual = ""

    for linha in texto.splitlines():
        if len(bloco_atual) + len(linha) + 1 > limite:
            partes.append(bloco_atual)
            bloco_atual = linha
        else:
            bloco_atual = f"{bloco_atual}\n{linha}" if bloco_atual else linha

    if bloco_atual:
        partes.append(bloco_atual)

    for parte in partes:
        await canal.send(parte)


def data_valida(data_texto: str) -> bool:
    try:
        datetime.strptime(data_texto, "%d/%m/%Y")
        return True
    except (TypeError, ValueError):
        return False


def numero_mes(mes: str) -> int:
    return MESES_ORDEM.index(normalizar_categoria(mes)) + 1


def carregar_fonte(tamanho: int, negrito: bool = False):
    if ImageFont is None:
        return None

    nomes = ["arialbd.ttf", "segoeuib.ttf"] if negrito else ["arial.ttf", "segoeui.ttf"]
    for nome in nomes:
        try:
            return ImageFont.truetype(nome, tamanho)
        except OSError:
            continue
    return ImageFont.load_default()


def desenhar_calendario_leituras(mes: str, ano: int) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    mes_num = numero_mes(mes)
    metas_por_dia: Dict[int, List[str]] = {}

    for lembrete in dados["lembretes_metas"]:
        try:
            data = datetime.strptime(lembrete.get("data", ""), "%d/%m/%Y")
        except (TypeError, ValueError):
            continue

        if data.month == mes_num and data.year == ano:
            texto = f"{lembrete.get('livro', 'Livro')}: {lembrete.get('meta', '')}".strip()
            metas_por_dia.setdefault(data.day, []).append(texto)

    largura, altura = 1400, 1000
    margem = 60
    topo = 150
    largura_celula = (largura - margem * 2) // 7
    altura_celula = 115

    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)

    fonte_titulo = carregar_fonte(46, negrito=True)
    fonte_dia_semana = carregar_fonte(24, negrito=True)
    fonte_numero = carregar_fonte(24, negrito=True)
    fonte_meta = carregar_fonte(17)
    fonte_rodape = carregar_fonte(18)

    titulo = f"Leituras conjuntas - {normalizar_categoria(mes)} {ano}"
    draw.text((margem, 45), titulo, fill="#3b2f2f", font=fonte_titulo)
    draw.text((margem, 105), "Metas guardadas pelo comando !meta", fill="#7b5d4a", font=fonte_rodape)

    dias_semana = ["Seg", "Ter", "Qua", "Qui", "Sex", "Sáb", "Dom"]
    for idx, dia in enumerate(dias_semana):
        x = margem + idx * largura_celula
        draw.rounded_rectangle(
            (x, topo, x + largura_celula - 8, topo + 42),
            radius=8,
            fill="#583d72"
        )
        draw.text((x + 18, topo + 9), dia, fill="#ffffff", font=fonte_dia_semana)

    semanas = calendar.monthcalendar(ano, mes_num)
    y_inicio = topo + 55

    for linha, semana in enumerate(semanas):
        for coluna, dia in enumerate(semana):
            x1 = margem + coluna * largura_celula
            y1 = y_inicio + linha * altura_celula
            x2 = x1 + largura_celula - 8
            y2 = y1 + altura_celula - 8
            fill = "#ffffff" if dia else "#f3e7dc"
            draw.rounded_rectangle((x1, y1, x2, y2), radius=10, fill=fill, outline="#d7c4b5", width=2)

            if not dia:
                continue

            draw.text((x1 + 12, y1 + 10), str(dia), fill="#3b2f2f", font=fonte_numero)

            metas = metas_por_dia.get(dia, [])
            texto_y = y1 + 42
            for meta in metas[:2]:
                for linha_meta in textwrap.wrap(meta, width=24)[:3]:
                    draw.text((x1 + 12, texto_y), linha_meta, fill="#315f58", font=fonte_meta)
                    texto_y += 20
            if len(metas) > 2:
                draw.text((x1 + 12, y2 - 24), f"+{len(metas) - 2} meta(s)", fill="#8a4f2d", font=fonte_meta)

    if not metas_por_dia:
        draw.text(
            (margem, altura - 85),
            "Ainda não há metas de leitura conjunta guardadas para este mês.",
            fill="#8a4f2d",
            font=fonte_rodape
        )

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def desenhar_grafico_barras(
    titulo: str,
    etiquetas: List[str],
    valores: List[int],
    cor: str = "#583d72",
    largura: int = 1200,
    altura: int = 700,
) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)
    fonte_titulo = carregar_fonte(36, negrito=True)
    fonte_label = carregar_fonte(20)
    fonte_valor = carregar_fonte(18, negrito=True)

    draw.text((50, 30), titulo, fill="#3b2f2f", font=fonte_titulo)

    if not valores or max(valores, default=0) == 0:
        draw.text((50, 120), "Sem dados suficientes para este período.", fill="#8a4f2d", font=fonte_label)
    else:
        max_valor = max(valores)
        base_y = altura - 80
        area_largura = largura - 140
        barra_largura = max(40, area_largura // max(len(valores), 1) - 20)
        inicio_x = 70

        for idx, (etiqueta, valor) in enumerate(zip(etiquetas, valores)):
            x = inicio_x + idx * (barra_largura + 20)
            altura_barra = int((valor / max_valor) * (altura - 220)) if max_valor else 0
            y_top = base_y - altura_barra
            draw.rounded_rectangle((x, y_top, x + barra_largura, base_y), radius=8, fill=cor)
            draw.text((x, base_y + 10), etiqueta[:14], fill="#3b2f2f", font=fonte_label)
            draw.text((x, y_top - 28), str(valor), fill="#315f58", font=fonte_valor)

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def desenhar_resumo_anual(ano: int, stats: Dict[str, Any]) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    largura, altura = 1400, 1000
    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)
    fonte_titulo = carregar_fonte(44, negrito=True)
    fonte_sec = carregar_fonte(28, negrito=True)
    fonte_txt = carregar_fonte(22)

    draw.text((60, 40), f"Resumo de Leituras {ano}", fill="#3b2f2f", font=fonte_titulo)
    draw.text((60, 110), f"Total de livros: {stats.get('total_livros', 0)}", fill="#583d72", font=fonte_sec)
    draw.text((60, 160), f"Páginas lidas: {stats.get('total_paginas', 0)}", fill="#315f58", font=fonte_sec)

    autor_top = stats.get("autor_top", ("N/D", 0))
    genero_top = stats.get("genero_top", ("N/D", 0))
    draw.text((60, 240), "Autor mais lido", fill="#8a4f2d", font=fonte_sec)
    draw.text((60, 285), f"{autor_top[0]} ({autor_top[1]} livros)", fill="#3b2f2f", font=fonte_txt)

    draw.text((60, 360), "Género dominante", fill="#8a4f2d", font=fonte_sec)
    draw.text((60, 405), f"{genero_top[0]} ({genero_top[1]} livros)", fill="#3b2f2f", font=fonte_txt)

    y = 500
    draw.text((60, y), "Top autores", fill="#8a4f2d", font=fonte_sec)
    y += 45
    for autor, qtd in stats.get("top_autores", [])[:5]:
        draw.text((80, y), f"• {autor}: {qtd}", fill="#3b2f2f", font=fonte_txt)
        y += 34

    y = 500
    draw.text((720, y), "Top géneros", fill="#8a4f2d", font=fonte_sec)
    y += 45
    for genero, qtd in stats.get("top_generos", [])[:5]:
        draw.text((740, y), f"• {genero}: {qtd}", fill="#3b2f2f", font=fonte_txt)
        y += 34

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def estatisticas_mes(mes: str, ano: int) -> Dict[str, Any]:
    mes_num = numero_mes(mes)
    livros_mes = []
    for livro in dados["livros_lidos"]:
        data_txt = livro.get("data_leitura", "")
        try:
            data = datetime.strptime(data_txt, "%d/%m/%Y")
        except (TypeError, ValueError):
            continue
        if data.month == mes_num and data.year == ano:
            livros_mes.append(livro)

    paginas = sum(int(l.get("paginas", 0) or 0) for l in livros_mes)
    autores = [parsear_livro(l["titulo"])[1] for l in livros_mes if SEPARADOR_LIVRO in l.get("titulo", "")]
    generos = [l.get("genero", "N/D") for l in livros_mes if l.get("genero")]

    return {
        "livros": livros_mes,
        "total_livros": len(livros_mes),
        "paginas": paginas,
        "autores_unicos": len(set(autores)),
        "generos_unicos": len(set(generos)),
        "contagem_autores": Counter(autores).most_common(5),
        "contagem_generos": Counter(generos).most_common(5),
    }


def estatisticas_ano(ano: int) -> Dict[str, Any]:
    livros_ano = []
    for livro in dados["livros_lidos"]:
        data_txt = livro.get("data_leitura", "")
        try:
            data = datetime.strptime(data_txt, "%d/%m/%Y")
        except (TypeError, ValueError):
            if str(ano) in data_txt:
                livros_ano.append(livro)
            continue
        if data.year == ano:
            livros_ano.append(livro)

    autores = []
    generos = []
    paginas = 0
    for livro in livros_ano:
        paginas += int(livro.get("paginas", 0) or 0)
        if SEPARADOR_LIVRO in livro.get("titulo", ""):
            autores.append(parsear_livro(livro["titulo"])[1])
        if livro.get("genero"):
            generos.append(livro["genero"])

    contagem_autores = Counter(autores)
    contagem_generos = Counter(generos)
    autor_top = contagem_autores.most_common(1)[0] if contagem_autores else ("N/D", 0)
    genero_top = contagem_generos.most_common(1)[0] if contagem_generos else ("N/D", 0)

    return {
        "total_livros": len(livros_ano),
        "total_paginas": paginas,
        "autor_top": autor_top,
        "genero_top": genero_top,
        "top_autores": contagem_autores.most_common(5),
        "top_generos": contagem_generos.most_common(5),
    }


async def garantir_canal(guild: discord.Guild, nome: str) -> discord.TextChannel:
    canal = discord.utils.get(guild.text_channels, name=nome)
    if canal:
        return canal
    return await guild.create_text_channel(nome)


# ==============================================================================
# DETECÇÃO DE SÉRIE
# ==============================================================================

async def detetar_e_agendar_serie(titulo_livro: str, mes_origem: str, canal: discord.abc.Messageable) -> List[str]:
    """
    Deteta se um livro pertence a uma série e agenda os próximos nos meses seguintes.
    Retorna lista de mensagens de confirmação.
    """
    prompt = f"""
O utilizador adicionou o livro "{titulo_livro}" para leitura em "{mes_origem}".
Se este livro fizer parte de uma série literária conhecida, identifica os próximos livros da série (máximo 3).
Responde apenas em JSON válido:
{{"sequencias": ["Nome do Livro 2 - Autor", "Nome do Livro 3 - Autor", "Nome do Livro 4 - Autor"]}}
Se não for uma série ou não houver sequências conhecidas, responde:
{{"sequencias": []}}
"""
    try:
        resposta = gemini_json(prompt)
        sequencias = resposta.get("sequencias", [])
        
        if not sequencias:
            return []
        
        idx_mes_atual = MESES_ORDEM.index(mes_origem) if mes_origem in MESES_ORDEM else datetime.now().month - 1
        if mes_origem == "Geral":
            idx_mes_atual = datetime.now().month - 1
        
        mensagens = []
        
        for i, proximo_livro in enumerate(sequencias):
            idx_destino = (idx_mes_atual + 1 + i) % 12
            mes_destino = MESES_ORDEM[idx_destino]
            
            ja_existe = any(proximo_livro.lower().strip() == x.lower().strip() for x in livros_tbr_flat())
            
            if not ja_existe:
                dados["tbr_por_mes"][mes_destino].append(proximo_livro)
                mensagens.append(f"• **{proximo_livro}** agendado para **{mes_destino}**")
        
        if mensagens:
            guardar_dados()
        return mensagens
        
    except Exception as e:
        print(f"Erro ao detetar série: {e}")
        return []


# ==============================================================================
# DESAFIO A-Z CORRIGIDO
# ==============================================================================

ARTIGOS_BANIDOS = {
    "o", "a", "os", "as", "um", "uma", "uns", "umas",
    "the", "a", "an"
}


def analisar_titulo_alfabeto(titulo: str):
    titulo_limpo = titulo.strip()
    
    if not titulo_limpo:
        return {"status": "INVALIDO", "letra": None}
    
    palavras = re.split(r'[\s\-–—]+', titulo_limpo)
    
    primeira_palavra = None
    for palavra in palavras:
        palavra_limpa = palavra.lower().strip('.,!?;:\'"()[]{}')
        if palavra_limpa and palavra_limpa not in ARTIGOS_BANIDOS:
            primeira_palavra = palavra
            break
    
    if not primeira_palavra:
        for palavra in palavras:
            if palavra.strip('.,!?;:\'"()[]{}'):
                primeira_palavra = palavra
                break
    
    if not primeira_palavra:
        return {"status": "INVALIDO", "letra": None}
    
    for ch in primeira_palavra:
        if ch.isalpha():
            return {"status": "OK", "letra": ch.upper()}
    
    return {"status": "INVALIDO", "letra": None}


dados = carregar_dados()
_ultimo_snapshot = _snapshot_dados()
if modo_armazenamento() == "local" and not DATA_FILE.exists():
    guardar_dados()


def _guardar_ao_sair() -> None:
    try:
        guardar_dados()
        print(f"💾 Dados guardados ({modo_armazenamento()}).")
    except OSError as erro:
        print(f"⚠️ Erro ao guardar ao sair: {erro}")


atexit.register(_guardar_ao_sair)


# ==============================================================================
# BOT
# ==============================================================================

intents = discord.Intents.default()
intents.message_content = True


class LeituraBot(commands.Bot):
    async def setup_hook(self) -> None:
        self.add_view(ViewSugestoes([], []))
        self.add_view(ViewMarcarSugestoes([]))

    async def close(self) -> None:
        guardar_dados()
        await super().close()


bot = LeituraBot(command_prefix=COMMAND_PREFIX, intents=intents)


@tasks.loop(minutes=2)
async def autosave_loop():
    guardar_dados()


@autosave_loop.before_loop
async def antes_autosave():
    await bot.wait_until_ready()


@bot.event
async def on_ready():
    print(f"👑 {bot.user} está online.")
    print(f"💾 {resumo_persistencia().replace('**', '')}")
    if not verificar_lembretes_loop.is_running():
        verificar_lembretes_loop.start()
    if not resumos_automaticos_loop.is_running():
        resumos_automaticos_loop.start()
    if not autosave_loop.is_running():
        autosave_loop.start()
    if not verificar_lc_concluidas.is_running():
        verificar_lc_concluidas.start()
    await enviar_lembretes_pendentes_hoje()


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot:
        return

    user_id = str(message.author.id)
    if user_id in dados["review_em_andamento"]:
        if not message.content.startswith(COMMAND_PREFIX):
            review = dados["review_em_andamento"][user_id]
            texto = message.content.strip()
            if texto:
                review.setdefault("desabafos", []).append(texto)
            for anexo in message.attachments:
                if anexo.content_type and anexo.content_type.startswith("image/"):
                    review.setdefault("anexos", []).append(anexo.url)
                    review.setdefault("desabafos", []).append(f"[Print de mensagem: {anexo.url}]")
                else:
                    review.setdefault("desabafos", []).append(f"[Anexo: {anexo.url}]")
            guardar_dados()
            await message.add_reaction("📝")

    await bot.process_commands(message)


@bot.event
async def on_command_error(ctx: commands.Context, error: commands.CommandError):
    if isinstance(error, commands.MissingRequiredArgument):
        exemplos = {
            "addtbr": '`!addtbr "Título - Autor"` ou `!addtbr Junho "Título - Autor"`',
            "remtbr": "`!remtbr Geral Nome do Livro`",
            "tbr": "`!tbr Junho` ou `!tbr Junho 3`",
            "meta": '`!meta Junho "Nome do Livro" dia 7 até cap. 10, dia 14 até cap. 22`',
            "lido": "`!lido Nome do Livro`",
            "remalfabeto": "`!remalfabeto A`",
            "addletra": '`!addletra A "Título - Autor"`',
            "avaliar": "`!avaliar 3.5` (aceita 0.25 em 0.25 até 5)",
            "reavaliar": '`!reavaliar "Título - Autor" 4.5`',
            "editar": '`!editar "Título Antigo" Novo Título - Novo Autor`',
            "remover": '`!remover "Título - Autor"`',
            "removerlc": '`!removerlc "Título - Autor"`',
            "buscar": '`!buscar "palavra"`',
            "desabafar": '`!desabafar "Título - Autor"`',
            "editmeta": '`!editmeta "Título - Autor" dia 7 até cap. 10`',
            "livroinfo": "`!livroinfo Título - Autor`",
            "resumomes": "`!resumomes Junho`",
            "resumoano": "`!resumoano 2026`",
            "remlido": "`!remlido Nome do Livro`",
            "review": "`!review Nome do Livro`",
            "entrevista": "`!entrevista Personagem pergunta`",
            "ressaca": "`!ressaca Nome do Livro`",
            "teoria": "`!teoria a tua teoria aqui`",
            "vibe": "`!vibe Nome do Livro`",
            "sprint": "`!sprint 25`",
        }
        nome_comando = ctx.command.name if ctx.command else ""
        exemplo = exemplos.get(nome_comando, f"`{COMMAND_PREFIX}guia`")
        await ctx.send(f"❌ Falta informação no comando.\nExemplo: {exemplo}")
        return

    if isinstance(error, commands.BadArgument):
        await ctx.send("❌ Um dos valores não está no formato certo. Usa `!guia` para ver exemplos.")
        return

    raise error


# ==============================================================================
# VIEWS E BOTÕES
# ==============================================================================

class BotaoSugestao(discord.ui.Button):
    def __init__(self, titulo_livro: str):
        super().__init__(
            label=f"➕ TBR: {titulo_livro[:55]}",
            style=discord.ButtonStyle.primary,
            custom_id=f"tbr_add::{titulo_livro[:80]}",
        )
        self.titulo_livro = titulo_livro

    async def callback(self, interaction: discord.Interaction):
        tudo_na_tbr = [l.lower() for l in livros_tbr_flat()]
        if self.titulo_livro.lower() in tudo_na_tbr:
            await interaction.response.send_message(
                f"🤔 *{self.titulo_livro}* já está na tua TBR.",
                ephemeral=True
            )
            return

        dados["tbr_por_mes"]["Geral"].append(self.titulo_livro)
        guardar_dados()

        self.disabled = True
        self.style = discord.ButtonStyle.success
        self.label = "✅ Adicionado"

        await interaction.response.edit_message(view=self.view)
        await interaction.followup.send(
            f"📦 **{self.titulo_livro}** foi adicionado à lista **Geral**.",
            ephemeral=True
        )


class BotaoMarcarSugestoes(discord.ui.Button):
    def __init__(self, titulos: List[str]):
        super().__init__(
            label="✅ Já vi estas sugestões",
            style=discord.ButtonStyle.secondary,
            custom_id=f"sugestoes_vistas::{hash(tuple(titulos)) & 0xFFFFFFFF}",
        )
        self.titulos = titulos

    async def callback(self, interaction: discord.Interaction):
        vistos = {v.lower().strip() for v in dados.setdefault("sugestoes_vistas", [])}
        novos = 0
        for titulo in self.titulos:
            chave = titulo.lower().strip()
            if chave not in vistos:
                dados["sugestoes_vistas"].append(titulo)
                vistos.add(chave)
                novos += 1
        guardar_dados()

        self.disabled = True
        self.label = "✅ Sugestões arquivadas"
        await interaction.response.edit_message(view=self.view)
        await interaction.followup.send(
            f"📚 Arquivou **{novos}** sugestão(ões). Não voltarão a ser recomendadas.",
            ephemeral=True,
        )


class ViewMarcarSugestoes(discord.ui.View):
    def __init__(self, titulos: List[str]):
        super().__init__(timeout=None)
        if titulos:
            self.add_item(BotaoMarcarSugestoes(titulos))


class ViewSugestoes(discord.ui.View):
    def __init__(self, livros_sugeridos: List[str], titulos_arquivo: Optional[List[str]] = None):
        super().__init__(timeout=None)
        for livro in livros_sugeridos:
            self.add_item(BotaoSugestao(livro))
        if titulos_arquivo:
            self.add_item(BotaoMarcarSugestoes(titulos_arquivo))


class SelectAvaliacao(discord.ui.Select):
    def __init__(self, titulo_livro: str, autor_id: int):
        opcoes = [
            discord.SelectOption(label=f"{nota:g} estrelas", value=str(nota), emoji="⭐")
            for nota in NOTAS_DISPONIVEIS
        ]
        super().__init__(
            placeholder="Escolhe a avaliação (0.25 a 5)",
            min_values=1,
            max_values=1,
            options=opcoes,
            custom_id=f"avaliar::{titulo_livro[:60]}::{autor_id}",
        )
        self.titulo_livro = titulo_livro
        self.autor_id = autor_id

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.autor_id:
            await interaction.response.send_message(
                "❌ Só quem registou este livro pode avaliá-lo por aqui.",
                ephemeral=True,
            )
            return

        nota = float(self.values[0])
        livro_encontrado = None
        for livro in dados["livros_lidos"]:
            if livro.get("titulo", "").lower().strip() == self.titulo_livro.lower().strip():
                livro_encontrado = livro
                break

        if not livro_encontrado:
            await interaction.response.send_message(
                "❌ Já não encontrei esse livro no histórico.",
                ephemeral=True,
            )
            return

        livro_encontrado["nota"] = nota
        livro_encontrado["estrelas"] = estrelas_para_texto(nota)
        guardar_dados()

        for item in self.view.children:
            item.disabled = True

        await interaction.response.edit_message(
            content=(
                f"🎨 Avaliação guardada para **{self.titulo_livro}**: "
                f"{livro_encontrado['estrelas']}"
            ),
            view=self.view,
        )


class ViewAvaliacao(discord.ui.View):
    def __init__(self, titulo_livro: str, autor_id: int):
        super().__init__(timeout=86400)
        self.add_item(SelectAvaliacao(titulo_livro, autor_id))


class ViewConfirmarDuplicado(discord.ui.View):
    def __init__(self, livro_novo: str, livro_existente: str, categoria: str, user_id: int):
        super().__init__(timeout=60)
        self.livro_novo = livro_novo
        self.livro_existente = livro_existente
        self.categoria = categoria
        self.user_id = user_id

    @discord.ui.button(label="✅ Sim, adicionar mesmo assim", style=discord.ButtonStyle.danger)
    async def confirmar_adicao(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("❌ Este menu não é para ti!", ephemeral=True)
            return
        
        dados["tbr_por_mes"][self.categoria].append(self.livro_novo)
        guardar_dados()
        
        self.disable_all_buttons()
        await interaction.response.edit_message(
            content=f"📅 **{self.livro_novo}** foi adicionado a **{self.categoria}** mesmo sendo similar a **{self.livro_existente}**.",
            view=self
        )

    @discord.ui.button(label="❌ Não, cancelar", style=discord.ButtonStyle.secondary)
    async def cancelar_adicao(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("❌ Este menu não é para ti!", ephemeral=True)
            return
        
        self.disable_all_buttons()
        await interaction.response.edit_message(
            content=f"❌ Adição de **{self.livro_novo}** cancelada.",
            view=self
        )

    def disable_all_buttons(self):
        for child in self.children:
            child.disabled = True


class ViewManterSerie(discord.ui.View):
    def __init__(self, livro_atual: str, livros_serie: List[str], meses_agendados: List[str], canal_id: int):
        super().__init__(timeout=86400)
        self.livro_atual = livro_atual
        self.livros_serie = livros_serie
        self.meses_agendados = meses_agendados
        self.canal_id = canal_id

    @discord.ui.button(label="✅ Sim, manter os próximos livros", style=discord.ButtonStyle.success)
    async def manter_serie(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_message(
            f"📚 OK! Os próximos livros da série **{self.livro_atual}** permanecem na TBR:\n"
            + "\n".join(f"• {livro} ({mes})" for livro, mes in zip(self.livros_serie, self.meses_agendados)),
            ephemeral=False
        )
        self.disable_all_buttons()
        await interaction.edit_original_response(view=self)

    @discord.ui.button(label="❌ Não, remover os próximos livros", style=discord.ButtonStyle.danger)
    async def remover_serie(self, interaction: discord.Interaction, button: discord.ui.Button):
        removidos = []
        for livro, mes in zip(self.livros_serie, self.meses_agendados):
            if livro in dados["tbr_por_mes"][mes]:
                dados["tbr_por_mes"][mes].remove(livro)
                removidos.append(f"• {livro} ({mes})")
        
        guardar_dados()
        
        await interaction.response.send_message(
            f"🗑️ Livros seguintes da série **{self.livro_atual}** foram removidos da TBR:\n"
            + "\n".join(removidos),
            ephemeral=False
        )
        self.disable_all_buttons()
        await interaction.edit_original_response(view=self)

    def disable_all_buttons(self):
        for child in self.children:
            child.disabled = True


class ViewConfirmarLido(discord.ui.View):
    def __init__(self, livro: str, autor: str, canal_id: int):
        super().__init__(timeout=86400)
        self.livro = livro
        self.autor = autor
        self.canal_id = canal_id
        self.livros_serie = []
        self.meses_agendados = []

    async def detetar_serie_pos_lido(self, interaction: discord.Interaction):
        prompt = f"""
O utilizador acabou de ler o livro "{self.livro}".
Se este livro fizer parte de uma série literária conhecida, identifica os PRÓXIMOS livros da série (máximo 3) que ainda não foram lidos.
Responde apenas em JSON válido:
{{"sequencias": ["Nome do Livro 2 - Autor", "Nome do Livro 3 - Autor", "Nome do Livro 4 - Autor"]}}
Se não houver sequências ou a série já tiver terminado, responde:
{{"sequencias": []}}
"""
        try:
            resposta = gemini_json(prompt)
            sequencias = resposta.get("sequencias", [])
            
            if not sequencias:
                return []
            
            livros_nao_lidos = []
            for seq in sequencias:
                if not livro_ja_lido(seq):
                    livros_nao_lidos.append(seq)
            
            if not livros_nao_lidos:
                return []
            
            mes_atual = MESES_ORDEM[datetime.now().month - 1]
            idx_mes_atual = MESES_ORDEM.index(mes_atual)
            mensagens = []
            
            for i, proximo_livro in enumerate(livros_nao_lidos[:3]):
                idx_destino = (idx_mes_atual + 1 + i) % 12
                mes_destino = MESES_ORDEM[idx_destino]
                
                ja_existe = any(proximo_livro.lower().strip() == x.lower().strip() for x in livros_tbr_flat())
                
                if not ja_existe:
                    dados["tbr_por_mes"][mes_destino].append(proximo_livro)
                    self.livros_serie.append(proximo_livro)
                    self.meses_agendados.append(mes_destino)
                    mensagens.append(f"• **{proximo_livro}** agendado para **{mes_destino}**")
            
            guardar_dados()
            return mensagens
            
        except Exception as e:
            print(f"Erro ao detetar série pós-leitura: {e}")
            return []

    @discord.ui.button(label="✅ Sim, marcar como lido", style=discord.ButtonStyle.success)
    async def confirmar_lido(self, interaction: discord.Interaction, button: discord.ui.Button):
        if livro_ja_lido(self.livro):
            await interaction.response.send_message(
                f"📚 **{self.livro}** já estava registado como lido!",
                ephemeral=True
            )
            self.disable_all_buttons()
            await interaction.edit_original_response(view=self)
            return
        
        info = await obter_info_livro(self.livro)
        try:
            titulo_curto, autor = parsear_livro(self.livro)
        except ValueError:
            titulo_curto = self.livro
            autor = self.autor or "Desconhecido"
        
        novo_livro = {
            "titulo": self.livro,
            "autor": autor,
            "estrelas": "Sem avaliação",
            "nota": 0.0,
            "genero": info.get("genero", "N/D"),
            "paginas": int(info.get("paginas", 0) or 0),
            "data_leitura": hoje_str(),
            "fonte_metadados": info.get("fonte", "IA"),
            "lc_automatico": True
        }
        
        dados["livros_lidos"].append(novo_livro)
        
        for chave, lista in dados["tbr_por_mes"].items():
            for item in lista[:]:
                if item.lower().strip() == self.livro.lower().strip():
                    lista.remove(item)
                    break
                item_norm = unicodedata.normalize('NFKD', item.lower()).encode('ASCII', 'ignore').decode()
                livro_norm = unicodedata.normalize('NFKD', self.livro.lower()).encode('ASCII', 'ignore').decode()
                if item_norm == livro_norm:
                    lista.remove(item)
                    break
        
        resultado = analisar_titulo_alfabeto(titulo_curto)
        aviso_alfabeto = ""
        if resultado["status"] == "OK":
            letra = resultado["letra"]
            if letra in dados["desafio_alfabeto"] and dados["desafio_alfabeto"][letra] == VAZIO_ALFABETO:
                dados["desafio_alfabeto"][letra] = self.livro
                aviso_alfabeto = f"\n🔤 Letra **{letra}** conquistada no A-Z!"
        
        mensagens_serie = await self.detetar_serie_pos_lido(interaction)
        
        guardar_dados()
        total_lidos = len(dados["livros_lidos"])
        
        resposta_msg = f"✅ **{self.livro}** foi adicionado aos lidos!{aviso_alfabeto}\n"
        resposta_msg += f"📊 Progresso anual: {total_lidos}/{META_ANUAL} livros.\n\n"
        
        if mensagens_serie:
            resposta_msg += f"🧬 **Série detetada!** Queres manter os próximos livros na TBR?\n"
            resposta_msg += "\n".join(mensagens_serie)
            
            view = ViewManterSerie(self.livro, self.livros_serie, self.meses_agendados, self.canal_id)
            await interaction.response.send_message(resposta_msg, view=view, ephemeral=False)
        else:
            resposta_msg += f"⭐ Não te esqueças de avaliar o livro com `!avaliar` ou `!reavaliar`!"
            await interaction.response.send_message(resposta_msg, ephemeral=False)
        
        self.disable_all_buttons()
        await interaction.edit_original_response(view=self)

    @discord.ui.button(label="❌ Não, marcar depois", style=discord.ButtonStyle.secondary)
    async def adiar_lido(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_message(
            f"📝 OK! Podes marcar **{self.livro}** como lido mais tarde com `!lido \"{self.livro}\"`.",
            ephemeral=True
        )
        self.disable_all_buttons()
        await interaction.edit_original_response(view=self)

    def disable_all_buttons(self):
        for child in self.children:
            child.disabled = True


# ==============================================================================
# NOVO COMANDO: DESABAFAR (para emoções e conversas)
# ==============================================================================

@bot.command(name="desabafar", help="Regista emoções, reações e conversas sobre um livro para a review. Ex: !desabafar \"Título - Autor\"")
async def iniciar_desabafo(ctx: commands.Context, *, titulo_livro: str):
    """Inicia um modo de captura de emoções e conversas para a review"""
    user_id = str(ctx.author.id)
    
    # Verificar se já existe uma review em andamento para este livro
    if user_id in dados["review_em_andamento"]:
        return await ctx.send(
            f"⚠️ Já tens uma review em andamento para **{dados['review_em_andamento'][user_id]['titulo']}**.\n"
            f"Termina com `!gerar` ou usa `!desabafar` para um livro diferente."
        )
    
    dados["review_em_andamento"][user_id] = {
        "titulo": titulo_livro,
        "desabafos": [],  # emoções, rants, teorias
        "conversas": [],  # prints de conversas
        "anexos": [],
        "tipo": "desabafo"
    }
    guardar_dados()
    
    await ctx.send(
        f"💭 **Modo Desabafo ativado para: *{titulo_livro}***\n\n"
        f"**Podes fazer 3 coisas:**\n"
        f"1️⃣ **Escrever emoções/sensações** - manda mensagens normais com o que sentes\n"
        f"2️⃣ **Enviar prints de conversas** - anexa imagens de debates com amigos\n"
        f"3️⃣ **Mencionar mensagens** - responde a uma mensagem com `!mencionar`\n\n"
        f"Quando terminares, usa `!gerar` para criar a review com tudo capturado! 🎨"
    )


@bot.command(name="mencionar", help="Adiciona uma mensagem específica à tua review. Responde à mensagem que queres capturar.")
async def adicionar_mensagem_review(ctx: commands.Context):
    """Adiciona a mensagem referenciada à review em andamento"""
    user_id = str(ctx.author.id)
    
    if user_id not in dados["review_em_andamento"]:
        return await ctx.send("❌ Não tens nenhuma review/desabafo em andamento. Usa `!desabafar \"Título - Autor\"` primeiro.")
    
    # Verificar se há mensagem referenciada
    if not ctx.message.reference:
        return await ctx.send("❌ Responde a uma mensagem que queres capturar! Exemplo: clica em responder a uma mensagem e usa `!mencionar`")
    
    try:
        msg_referencia = await ctx.channel.fetch_message(ctx.message.reference.message_id)
    except (discord.NotFound, discord.HTTPException):
        return await ctx.send("❌ Não consegui encontrar a mensagem referenciada.")
    
    review = dados["review_em_andamento"][user_id]
    
    # Formatar a mensagem capturada
    autor = msg_referencia.author.display_name
    conteudo = msg_referencia.content if msg_referencia.content else "[Sem texto - apenas anexos]"
    data = msg_referencia.created_at.strftime("%d/%m/%Y %H:%M")
    
    entrada = f"📝 **{autor}** ({data}): {conteudo}"
    
    # Adicionar anexos se houver
    if msg_referencia.attachments:
        for anexo in msg_referencia.attachments:
            if anexo.content_type and anexo.content_type.startswith("image/"):
                entrada += f"\n   📎 Print: {anexo.url}"
                review.setdefault("anexos", []).append(anexo.url)
    
    review.setdefault("conversas", []).append(entrada)
    guardar_dados()
    
    await ctx.send(f"✅ Mensagem de **{autor}** adicionada à tua review! (+1 conversa capturada)")
    await ctx.message.add_reaction("📥")


# ==============================================================================
# COMANDOS DE EDIÇÃO, REMOÇÃO E BUSCA
# ==============================================================================

@bot.command(name="editar", help="Edita título ou autor de um livro. Ex: !editar \"Título antigo\" novo título - novo autor")
async def editar_livro(ctx: commands.Context, *, argumentos: str):
    argumentos = argumentos.strip()
    
    match_aspas = re.match(r'"([^"]+)"\s+(.+)', argumentos)
    
    if not match_aspas:
        return await ctx.send(
            "❌ Uso correto:\n"
            "`!editar \"Título Antigo - Autor Antigo\" Novo Título - Novo Autor`\n"
            "`!editar \"Título Antigo\" Novo Título - Autor`\n\n"
            "O título antigo deve estar entre aspas."
        )
    
    titulo_antigo_raw = match_aspas.group(1).strip()
    resto = match_aspas.group(2).strip()
    
    if SEPARADOR_LIVRO in resto:
        partes = resto.rsplit(SEPARADOR_LIVRO, 1)
        titulo_novo = partes[0].strip()
        autor_novo = partes[1].strip()
    else:
        titulo_novo = resto
        autor_novo = None
    
    livro_encontrado = None
    titulo_antigo_normalizado = titulo_antigo_raw.lower().strip()
    
    for livro in dados["livros_lidos"]:
        titulo_livro = livro.get("titulo", "").lower().strip()
        if (titulo_livro == titulo_antigo_normalizado or
            titulo_antigo_normalizado in titulo_livro or
            titulo_livro in titulo_antigo_normalizado):
            livro_encontrado = livro
            break
    
    if not livro_encontrado:
        sugestoes = []
        for livro in dados["livros_lidos"][-8:]:
            sugestoes.append(f"• {livro.get('titulo', 'Desconhecido')}")
        
        await ctx.send(
            f"❌ Não encontrei **{titulo_antigo_raw}** no histórico.\n\n"
            f"**Livros recentes:**\n" + "\n".join(sugestoes) + "\n\n"
            f"Usa `!buscar \"palavra\"` para encontrar o nome exato."
        )
        return
    
    titulo_antigo_completo = livro_encontrado.get("titulo", "")
    autor_antigo = livro_encontrado.get("autor", "")
    
    if autor_novo is None:
        if titulo_novo:
            novo_titulo_completo = formatar_livro(titulo_novo, autor_antigo)
        else:
            novo_titulo_completo = titulo_antigo_completo
            autor_novo = autor_antigo
    else:
        if titulo_novo:
            novo_titulo_completo = formatar_livro(titulo_novo, autor_novo)
        else:
            try:
                titulo_antigo_curto, _ = parsear_livro(titulo_antigo_completo)
                novo_titulo_completo = formatar_livro(titulo_antigo_curto, autor_novo)
            except ValueError:
                novo_titulo_completo = f"{titulo_antigo_completo.split(SEPARADOR_LIVRO)[0]}{SEPARADOR_LIVRO}{autor_novo}"
    
    livro_encontrado["titulo"] = novo_titulo_completo
    livro_encontrado["autor"] = autor_novo if autor_novo else autor_antigo
    
    for letra, livro_alfabeto in dados["desafio_alfabeto"].items():
        if livro_alfabeto == titulo_antigo_completo:
            dados["desafio_alfabeto"][letra] = novo_titulo_completo
            break
    
    for categoria, lista in dados["tbr_por_mes"].items():
        for i, item in enumerate(lista):
            if item == titulo_antigo_completo:
                lista[i] = novo_titulo_completo
    
    for lembrete in dados["lembretes_metas"]:
        if lembrete.get("livro") == titulo_antigo_completo:
            lembrete["livro"] = novo_titulo_completo
            if autor_novo:
                lembrete["autor"] = autor_novo
    
    for mes, info in dados["sorteios_mes"].items():
        livros = info.get("livros", [])
        for i, livro in enumerate(livros):
            if livro == titulo_antigo_completo:
                livros[i] = novo_titulo_completo
        lidos = info.get("lidos", [])
        for i, livro in enumerate(lidos):
            if livro == titulo_antigo_completo:
                lidos[i] = novo_titulo_completo
    
    guardar_dados()
    
    mensagem = f"✏️ **Livro atualizado com sucesso!**\n\n"
    mensagem += f"📖 **Título antigo:** {titulo_antigo_completo}\n"
    mensagem += f"📖 **Título novo:** {novo_titulo_completo}\n"
    
    if autor_novo and autor_novo != autor_antigo:
        mensagem += f"👤 **Autor antigo:** {autor_antigo}\n"
        mensagem += f"👤 **Autor novo:** {autor_novo}\n"
    
    mensagem += f"\n✅ Atualizado em: histórico, TBR, desafios, sorteios e lembretes."
    
    await ctx.send(mensagem)


@bot.command(name="remover", help="Remove um livro do histórico (lidos), TBR e LCs. Ex: !remover \"Título - Autor\"")
async def remover_livro_completo(ctx: commands.Context, *, livro: str):
    try:
        livro_completo_txt = livro_completo(livro)
    except ValueError:
        livro_completo_txt = livro.strip()
    
    existe_historico = any(l.get("titulo", "").lower().strip() == livro_completo_txt.lower().strip() 
                          for l in dados["livros_lidos"])
    
    existe_tbr = any(livro_completo_txt.lower().strip() == item.lower().strip() 
                    for item in livros_tbr_flat())
    
    existe_lc = any(l.get("livro", "").lower().strip() == livro_completo_txt.lower().strip() 
                   for l in dados["lembretes_metas"])
    
    if not (existe_historico or existe_tbr or existe_lc):
        return await ctx.send(f"❌ Não encontrei **{livro_completo_txt}** em lado nenhum.")
    
    await ctx.send(
        f"⚠️ Vou remover **{livro_completo_txt}** de:\n"
        f"• Histórico de leituras\n"
        f"• Desafio A-Z\n"
        f"• TBR\n"
        f"• Leituras conjuntas\n"
        f"• Sorteios\n\n"
        f"Tens a certeza? Responde com `sim` em 30 segundos."
    )
    
    def check(m):
        return m.author == ctx.author and m.content.lower() in ["sim", "s", "yes", "y"]
    
    try:
        await bot.wait_for('message', timeout=30, check=check)
    except asyncio.TimeoutError:
        return await ctx.send("❌ Operação cancelada por timeout.")
    
    dados["livros_lidos"] = [
        l for l in dados["livros_lidos"]
        if l.get("titulo", "").lower().strip() != livro_completo_txt.lower().strip()
    ]
    
    for letra, livro_alfabeto in dados["desafio_alfabeto"].items():
        if livro_alfabeto.lower().strip() == livro_completo_txt.lower().strip():
            dados["desafio_alfabeto"][letra] = VAZIO_ALFABETO
    
    for categoria in dados["tbr_por_mes"]:
        dados["tbr_por_mes"][categoria] = [
            item for item in dados["tbr_por_mes"][categoria]
            if item.lower().strip() != livro_completo_txt.lower().strip()
        ]
    
    dados["lembretes_metas"] = [
        l for l in dados["lembretes_metas"]
        if l.get("livro", "").lower().strip() != livro_completo_txt.lower().strip()
    ]
    
    for mes, info in dados["sorteios_mes"].items():
        info["livros"] = [
            l for l in info.get("livros", [])
            if l.lower().strip() != livro_completo_txt.lower().strip()
        ]
        info["lidos"] = [
            l for l in info.get("lidos", [])
            if l.lower().strip() != livro_completo_txt.lower().strip()
        ]
    
    guardar_dados()
    
    await ctx.send(
        f"🗑️ **{livro_completo_txt}** foi removido com sucesso!\n\n"
        f"Podes adicionar a versão correta com `!addtbr \"Título Correto - Autor Correto\"`"
    )


@bot.command(name="removerlc", help="Remove um livro de todas as leituras conjuntas (metas/lembretes). Ex: !removerlc \"Título - Autor\"")
async def remover_livro_das_lc(ctx: commands.Context, *, livro: str):
    try:
        livro_completo_txt = livro_completo(livro)
    except ValueError:
        livro_completo_txt = livro.strip()
    
    lembretes_encontrados = []
    for lembrete in dados["lembretes_metas"]:
        livro_lembrete = lembrete.get("livro", "")
        if (livro_lembrete.lower().strip() == livro_completo_txt.lower().strip() or
            unicodedata.normalize('NFKD', livro_lembrete.lower()).encode('ASCII', 'ignore').decode() ==
            unicodedata.normalize('NFKD', livro_completo_txt.lower()).encode('ASCII', 'ignore').decode()):
            lembretes_encontrados.append(lembrete)
    
    if not lembretes_encontrados:
        return await ctx.send(f"❌ Não encontrei metas/lembretes para o livro **{livro_completo_txt}**.")
    
    await ctx.send(
        f"⚠️ Vou remover **{len(lembretes_encontrados)}** lembrete(s) da LC de **{livro_completo_txt}**.\n"
        f"Tens a certeza? Responde com `sim` em 30 segundos."
    )
    
    def check(m):
        return m.author == ctx.author and m.content.lower() in ["sim", "s", "yes", "y"]
    
    try:
        await bot.wait_for('message', timeout=30, check=check)
    except asyncio.TimeoutError:
        return await ctx.send("❌ Operação cancelada por timeout.")
    
    dados["lembretes_metas"] = [
        l for l in dados["lembretes_metas"]
        if l.get("livro", "").lower().strip() != livro_completo_txt.lower().strip()
    ]
    
    for mes, info in dados["sorteios_mes"].items():
        if livro_completo_txt in info.get("livros", []):
            info["livros"].remove(livro_completo_txt)
        if livro_completo_txt in info.get("lidos", []):
            info["lidos"].remove(livro_completo_txt)
    
    guardar_dados()
    
    await ctx.send(
        f"🗑️ **{livro_completo_txt}** foi removido de todas as leituras conjuntas.\n"
        f"Lembretes removidos: **{len(lembretes_encontrados)}**\n\n"
        f"Se ainda estiver na TBR, usa `!remtbr Geral \"{livro_completo_txt}\"` para remover."
    )


@bot.command(name="buscar", help="Busca livros no histórico por título ou autor. Ex: !buscar Quarta Asa")
async def buscar_livro(ctx: commands.Context, *, termo: str):
    termo_busca = termo.lower().strip()
    resultados = []
    
    for livro in dados["livros_lidos"]:
        titulo = livro.get("titulo", "").lower()
        autor = livro.get("autor", "").lower()
        
        if termo_busca in titulo or termo_busca in autor:
            resultados.append(livro)
    
    if not resultados:
        return await ctx.send(f"❌ Não encontrei nenhum livro com **{termo}**.")
    
    linhas = []
    for i, livro in enumerate(resultados[:10], 1):
        estrelas = livro.get("estrelas", "Sem avaliação")
        linhas.append(f"{i}. {livro.get('titulo', 'Sem título')} — {estrelas}")
    
    if len(resultados) > 10:
        linhas.append(f"\n... e mais {len(resultados) - 10} resultado(s).")
    
    await enviar_mensagem_longa(ctx, f"🔍 **Resultados para '{termo}':**\n\n" + "\n".join(linhas))


@bot.command(name="autores", help="Lista todos os autores dos livros lidos.")
async def listar_autores(ctx: commands.Context):
    autores = set()
    for livro in dados["livros_lidos"]:
        autor = livro.get("autor", "")
        if autor:
            autores.add(autor)
        else:
            try:
                _, autor = parsear_livro(livro.get("titulo", ""))
                autores.add(autor)
            except ValueError:
                pass
    
    if not autores:
        return await ctx.send("📭 Ainda não tens autores registados.")
    
    autores_ordenados = sorted(autores)
    msg = f"📚 **Autores registados ({len(autores_ordenados)}):**\n"
    msg += "\n".join(f"• {autor}" for autor in autores_ordenados)
    
    await enviar_mensagem_longa(ctx, msg)


# ==============================================================================
# COMANDOS DO DESAFIO A-Z
# ==============================================================================

@bot.command(name="addletra", help="Adiciona uma letra ao desafio A-Z manualmente (para livros lidos antes do bot). Ex: !addletra A \"Título - Autor\"")
async def adicionar_letra_alfabeto(ctx: commands.Context, letra: str, *, livro: str):
    letra = letra.strip().upper()
    
    if len(letra) != 1 or letra not in dados["desafio_alfabeto"]:
        return await ctx.send("❌ Letra inválida. Usa apenas uma letra de A a Z.")
    
    try:
        titulo_completo = livro_completo(livro)
    except ValueError:
        titulo_completo = livro.strip()
    
    if dados["desafio_alfabeto"][letra] != VAZIO_ALFABETO:
        return await ctx.send(
            f"⚠️ A letra **{letra}** já está preenchida com:\n"
            f"📖 **{dados['desafio_alfabeto'][letra]}**\n\n"
            f"Usa `!remalfabeto {letra}` primeiro se quiseres substituir."
        )
    
    livro_existe = livro_ja_lido(titulo_completo)
    
    dados["desafio_alfabeto"][letra] = titulo_completo
    guardar_dados()
    
    preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
    
    msg = f"🔤 **Letra {letra}** adicionada ao desafio A-Z com:\n📖 {titulo_completo}\n"
    if not livro_existe:
        msg += f"\n⚠️ Este livro **não está no teu histórico de leituras**. Se foi lido, regista-o com `!lido \"{titulo_completo}\"`."
    else:
        msg += f"\n✅ Este livro já consta no teu histórico."
    
    msg += f"\n\n📊 Progresso atual: **{preenchidas}/26** letras."
    
    await ctx.send(msg)


# ==============================================================================
# COMANDO: REAVALIAR
# ==============================================================================

@bot.command(name="reavaliar", help="Reavalia um livro já lido. Ex: !reavaliar \"Título - Autor\" 4.5")
async def reavaliar_livro(ctx: commands.Context, *, argumentos: str):
    partes = argumentos.rsplit(' ', 1)
    
    if len(partes) < 2:
        return await ctx.send(
            "❌ Uso correto: `!reavaliar \"Título - Autor\" 4.5`\n"
            "A nota deve ser entre 0.25 e 5, em passos de 0.25."
        )
    
    titulo_candidato = partes[0].strip()
    try:
        nota = float(partes[1].strip())
    except ValueError:
        return await ctx.send("❌ Nota inválida. Exemplo: `4.5` ou `3.75`")
    
    if not nota_valida(nota):
        return await ctx.send("❌ A nota deve ser entre 0.25 e 5, em passos de 0.25.")
    
    titulo_alvo = titulo_candidato.lower().strip()
    livro_encontrado = None
    
    for livro in dados["livros_lidos"]:
        titulo_livro = livro.get("titulo", "").lower().strip()
        if titulo_livro == titulo_alvo:
            livro_encontrado = livro
            break
    
    if not livro_encontrado:
        for livro in dados["livros_lidos"]:
            titulo_livro = livro.get("titulo", "").lower().strip()
            if titulo_livro.startswith(titulo_alvo) or titulo_alvo.startswith(titulo_livro):
                livro_encontrado = livro
                break
    
    if not livro_encontrado:
        sugestoes = []
        for livro in dados["livros_lidos"][-5:]:
            sugestoes.append(f"• {livro.get('titulo', 'Desconhecido')}")
        
        sugestoes_texto = "\n".join(sugestoes) if sugestoes else "Nenhum livro encontrado no histórico."
        return await ctx.send(
            f"❌ Não encontrei o livro **{titulo_candidato}** no teu histórico.\n\n"
            f"**Últimos livros lidos:**\n{sugestoes_texto}\n\n"
            f"Usa o nome exato como aparece em `!historico`."
        )
    
    nota_antiga = livro_encontrado.get("nota", 0.0)
    estrelas_antigas = livro_encontrado.get("estrelas", "Sem avaliação")
    
    livro_encontrado["nota"] = nota
    livro_encontrado["estrelas"] = estrelas_para_texto(nota)
    guardar_dados()
    
    await ctx.send(
        f"🔄 **Avaliação atualizada!**\n"
        f"📖 {livro_encontrado.get('titulo', 'Livro')}\n"
        f"⭐ Antiga: {estrelas_antigas} → ⭐ Nova: {livro_encontrado['estrelas']}"
    )


# ==============================================================================
# COMANDO: GERAR REVIEW (ATUALIZADO PARA SUPORTAR DESABAFOS E CONVERSAS)
# ==============================================================================

@bot.command(name="gerar", help="Gera a legenda final da review de Bookstagram a partir dos teus desabafos e conversas.")
async def gerar_review(ctx: commands.Context):
    user_id = str(ctx.author.id)

    if user_id not in dados["review_em_andamento"]:
        return await ctx.send("❌ Não tens nenhuma review em andamento. Usa `!desabafar \"Título - Autor\"` ou `!review \"Título - Autor\"` primeiro.")

    review = dados["review_em_andamento"][user_id]
    titulo = review["titulo"]
    desabafos = review.get("desabafos", [])
    conversas = review.get("conversas", [])
    anexos = review.get("anexos", [])
    tipo = review.get("tipo", "review")

    if not desabafos and not conversas and not anexos:
        return await ctx.send("❌ Ainda não tens nenhum apontamento, desabafo ou conversa guardada para esta review.")

    # Preparar o conteúdo para a IA
    conteudo = ""
    
    if desabafos:
        conteudo += "**SENTIMENTOS E EMOÇÕES:**\n- " + "\n- ".join(desabafos) + "\n\n"
    
    if conversas:
        conteudo += "**CONVERSAS E DEBATES:**\n- " + "\n- ".join(conversas) + "\n\n"
    
    if anexos:
        conteudo += "**ANEXOS/PRINTS:**\n- " + "\n- ".join(anexos) + "\n\n"

    prompt = f"""
Create a structured, aesthetic and emotional Bookstagram caption in European Portuguese (pt-PT) or English.
The reader is sharing their experience with the book '{titulo}'.

Here is everything they captured during their reading journey:

{conteudo}

Instructions:
- Capture the authentic emotions and reactions
- If there are conversations/debates, include interesting quotes or arguments
- Make it feel personal and engaging, like a real reader sharing their journey
- Keep the tone natural and passionate
- Include emojis and line breaks for Instagram aesthetic
- Maximum 2000 characters

Write only the caption, no extra text.
"""

    try:
        res = gemini_text(prompt)
        
        mensagem_final = f"✨ **LEGENDA PARA O INSTAGRAM PRONTA!** ✨\n\n{res}"
        
        if len(mensagem_final) > 1900:
            # Dividir em partes se for muito longo
            await enviar_mensagem_longa(ctx, mensagem_final)
        else:
            await ctx.send(mensagem_final)
        
        if anexos:
            await ctx.send("📎 **Prints e anexos incluídos na review:**\n" + "\n".join(anexos[:5]))
            if len(anexos) > 5:
                await ctx.send(f"(+ {len(anexos) - 5} anexos adicionais)")
        
        # Limpar a review em andamento
        del dados["review_em_andamento"][user_id]
        guardar_dados()
        
        await ctx.send("🎨 Review finalizada! Tudo o que capturaste foi usado. Podes começar uma nova review com `!desabafar` quando quiseres.")
        
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar legenda: {e}")


# ==============================================================================
# COMANDO: GUIA (ATUALIZADO COM NOVOS COMANDOS)
# ==============================================================================

@bot.command(name="dadosficheiro", help="Mostra onde os dados do bot são guardados.")
async def mostrar_dados_ficheiro(ctx: commands.Context):
    await ctx.send(f"💾 **Persistência do bot**\n{resumo_persistencia()}")


@bot.command(name="armazenamento", help="Explica como persistir dados na nuvem.")
async def ajuda_armazenamento(ctx: commands.Context):
    embed = discord.Embed(
        title="☁️ Armazenamento na nuvem",
        description=(
            "Se o bot corre em **Render, Railway, Fly.io**, etc., o disco é **temporário** — "
            "a TBR apaga-se a cada reinício. Usa armazenamento remoto:"
        ),
        color=discord.Color.blue(),
    )
    embed.add_field(
        name="Opção 1 — GitHub (ideal se o bot já está no GitHub)",
        value=(
            "1. GitHub → Settings → Developer settings → Personal access tokens\n"
            "2. Cria token com permissão **Contents** (read/write) no repositório\n"
            "3. Opcional: adiciona `dados_bot.json` ao repo (pode começar vazio `{}`)\n"
            "4. Nas variáveis da nuvem:\n"
            "`GITHUB_TOKEN` → o token\n"
            "`GITHUB_REPO` → `utilizador/nome-do-repo`\n"
            "Opcional: `GITHUB_BRANCH` (default `main`), `GITHUB_DATA_PATH` (default `dados_bot.json`)"
        ),
        inline=False,
    )
    embed.add_field(
        name="Opção 2 — Supabase",
        value=(
            "1. Projeto em [supabase.com](https://supabase.com) + tabela `bot_state`\n"
            "2. Variáveis: `SUPABASE_URL` e `SUPABASE_KEY`"
        ),
        inline=False,
    )
    embed.add_field(
        name="Opção 3 — JSONBin",
        value="Variáveis: `JSONBIN_BIN_ID` e `JSONBIN_API_KEY`",
        inline=False,
    )
    embed.add_field(
        name="Estado atual",
        value=resumo_persistencia(),
        inline=False,
    )
    await ctx.send(embed=embed)


@bot.command(name="guia", help="Mostra o guia completo de comandos do bot.")
async def enviar_guia(ctx: commands.Context):
    p = COMMAND_PREFIX
    embed = discord.Embed(
        title="📖 GUIA DO COSMO",
        description=(
            "Bot de leituras com TBR, leituras conjuntas, desafios e Bookstagram.\n"
            f"**Formato obrigatório dos livros:** `\"Título - Autor\"`"
        ),
        color=discord.Color.purple(),
    )
    embed.add_field(
        name="📚 TBR e Planeamento",
        value=(
            f"`{p}addtbr` — Adiciona um livro à TBR (deteta séries automaticamente!)\n"
            f"• `{p}addtbr \"Quarta Asa - Rebecca Yarros\"`\n"
            f"• `{p}addtbr Junho \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}remtbr` — Remove um livro de uma categoria da TBR.\n"
            f"• `{p}remtbr Geral \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}verbar` — Mostra toda a TBR organizada por mês.\n\n"
            f"`{p}tbr` — Sorteia a TBR do mês, coloca leituras no calendário e **tranca** "
            f"até leres todos os livros sorteados.\n"
            f"• `{p}tbr Junho` · `{p}tbr Junho 3` (3 extras da Geral)\n\n"
            f"`{p}livroinfo` — Pesquisa metadados (ReadMore/Open Library).\n"
            f"• `{p}livroinfo \"Quarta Asa - Rebecca Yarros\"`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📅 Leituras Conjuntas",
        value=(
            f"`{p}meta` — Cria uma LC: adiciona à TBR, abre tópico, gera cronograma, "
            f"calendário visual (imagem) e lembretes diários.\n"
            f"• `{p}meta Junho \"Quarta Asa - Rebecca Yarros\" dia 7 até cap. 10, dia 14 até cap. 22`\n\n"
            f"`{p}editmeta` — Corrige metas de uma LC já criada (inclui autor).\n"
            f"• `{p}editmeta \"Quarta Asa - Rebecca Yarros\" dia 7 até cap. 12, dia 20 fim`\n\n"
            f"`{p}calendariolc` — Gera imagem do calendário mensal com todas as metas.\n"
            f"• `{p}calendariolc` · `{p}calendariolc Junho`\n\n"
            f"`{p}removerlc` — Remove um livro de todas as LCs.\n"
            f"• `{p}removerlc \"Título - Autor\"`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🏆 Desafios e Leituras",
        value=(
            f"`{p}lido` — Regista livro como lido, remove de **todas** as TBR, "
            f"atualiza A-Z e abre menu de avaliação (0.25 a 5 estrelas).\n"
            f"• `{p}lido \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}avaliar` — Avalia o último livro lido (0.25 em 0.25).\n"
            f"• `{p}avaliar 4.5` · `{p}avaliar 3.75`\n\n"
            f"`{p}reavaliar` — Reavalia um livro já lido.\n"
            f"• `{p}reavaliar \"Quarta Asa - Rebecca Yarros\" 4.5`\n\n"
            f"`{p}editar` — Edita título e/ou autor de um livro.\n"
            f"• `{p}editar \"Título Antigo - Autor\" Novo Título - Novo Autor`\n\n"
            f"`{p}remover` — Remove livro de TODOS os lugares (histórico, TBR, LCs).\n"
            f"• `{p}remover \"Título - Autor\"`\n\n"
            f"`{p}buscar` — Busca livros no histórico por título ou autor.\n"
            f"• `{p}buscar \"palavra\"`\n\n"
            f"`{p}addletra` — Adiciona letra ao A-Z manualmente.\n"
            f"• `{p}addletra A \"Título - Autor\"`\n\n"
            f"`{p}desafios` — Painel geral: meta anual, A-Z, avaliações e TBR.\n"
            f"`{p}alfabeto` — Progresso do desafio A-Z.\n"
            f"`{p}remalfabeto` — Limpa uma letra do A-Z. · `{p}remalfabeto Q`\n"
            f"`{p}historico` — Histórico de leituras com género e páginas.\n"
            f"`{p}remlido` — Remove um livro dos lidos.\n"
            f"`{p}autores` — Lista todos os autores registados."
        ),
        inline=False,
    )
    embed.add_field(
        name="✨ Recomendações",
        value=(
            f"`{p}recomendar` — Gera 3 sugestões com base nos livros avaliados com **4⭐ ou mais** "
            f"(pt-PT ou inglês), com ficha técnica, capa e botões para TBR.\n\n"
            f"**Botão** `✅ Já vi estas sugestões` — Arquiva para não voltarem a aparecer.\n\n"
            f"`{p}marcarsugestoes` — Arquiva sugestões manualmente.\n"
            f"• `{p}marcarsugestoes Livro A - Autor | Livro B - Autor`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📸 Bookstagram & Desabafos",
        value=(
            f"`{p}desabafar` — Modo para capturar emoções, reações e prints de conversas.\n"
            f"• `{p}desabafar \"Título - Autor\"`\n\n"
            f"`{p}mencionar` — Adiciona uma mensagem específica à review (responde à mensagem).\n\n"
            f"`{p}review` — Modo bloco de notas tradicional.\n"
            f"• `{p}review \"Título - Autor\"`\n\n"
            f"`{p}gerar` — Gera a legenda final com IA (usa tudo o que capturaste).\n\n"
            f"`{p}trend` — Ideias de posts/reels. · `{p}trend \"Livro - Autor\"`\n"
            f"`{p}vibe` — Moodboard estético para fotos. · `{p}vibe \"Livro - Autor\"`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📊 Resumos e Estatísticas",
        value=(
            f"`{p}resumomes` — Gráfico do mês: livros, páginas, autores e géneros.\n"
            f"• `{p}resumomes` · `{p}resumomes Junho`\n\n"
            f"`{p}resumoano` — Apresentação visual anual: autor mais lido, páginas e géneros.\n"
            f"• `{p}resumoano` · `{p}resumoano 2026`\n\n"
            "_Resumos automáticos: dia 1 (mês anterior) e 2 de janeiro (ano anterior)._"
        ),
        inline=False,
    )
    embed.add_field(
        name="🎲 Extras",
        value=(
            f"`{p}entrevista` — Entrevista uma personagem fictícia.\n"
            f"• `{p}entrevista Rhysanda O que pensas da Feyre?`\n\n"
            f"`{p}ressaca` — Sugestões para ressaca literária.\n"
            f"`{p}teoria` — Reage à tua teoria sem spoilers.\n"
            f"`{p}sprint` — Sprint de leitura com temporizador. · `{p}sprint 25`"
        ),
        inline=False,
    )
    embed.add_field(
        name="☁️ Nuvem",
        value=f"`{p}dadosficheiro` · `{p}armazenamento`",
        inline=False,
    )
    embed.set_footer(text=f"Prefixo atual: {COMMAND_PREFIX} · Usa {COMMAND_PREFIX}guia para rever este painel")
    await ctx.send(embed=embed)


# ==============================================================================
# COMANDO: RECOMENDAR
# ==============================================================================

@bot.command(name="recomendar", help="Sugere livros com base nos teus lidos avaliados com 4⭐ ou mais.")
async def curadoria_inteligente(ctx: commands.Context):
    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só pode ser usado dentro de um servidor.")

    favoritos = livros_bem_avaliados(minimo=4.0)
    if not favoritos:
        return await ctx.send(
            "📭 Ainda não tens livros avaliados com **4 estrelas ou mais**.\n"
            "Regista leituras com `!lido \"Título - Autor\"` e avalia com o menu de estrelas ou `!avaliar 4.5`."
        )

    nome_canal_sugestoes = "sugestoes-leitura"
    canal_sugestoes = await garantir_canal(guild, nome_canal_sugestoes)

    await ctx.send(
        f"🔍 A preparar sugestões com base em **{len(favoritos)}** livro(s) bem avaliado(s) "
        f"em {canal_sugestoes.mention}..."
    )

    tbr_atual = livros_tbr_flat()
    vistos = dados.get("sugestoes_vistas", [])

    linhas_favoritos = []
    for livro in favoritos:
        genero = livro.get("genero", "N/D")
        linhas_favoritos.append(
            f"- {livro['titulo']} ({livro['nota']:g}⭐, género: {genero})"
        )
    favs_texto = "\n".join(linhas_favoritos)
    tbr_texto = ", ".join(tbr_atual) if tbr_atual else "Nenhum"
    vistos_texto = ", ".join(vistos) if vistos else "Nenhum"

    prompt = f"""
You are a literary curator.
The reader loved these books (rated 4 stars or higher). Suggest NEW books with similar tone, genre, pacing and emotional impact:
{favs_texto}

Rules:
- Recommend books similar to the highly-rated titles above (authors, subgenres, themes, vibe).
- Do NOT suggest books already in this TBR list: [{tbr_texto}].
- Do NOT suggest books already shown and dismissed: [{vistos_texto}].

Write all descriptive text in European Portuguese (pt-PT) OR English — never Brazilian Portuguese.

Respond only with valid JSON in this structure:
{{
  "livros": [
    {{
      "titulo": "Book Title",
      "autor": "Author Name",
      "data_publicacao": "Month/Year or DD/MM/YYYY",
      "genero": "Main Genre",
      "subgenero": "Subgenre",
      "porque_ler": "Short convincing text in pt-PT or English",
      "link_capa": "https://..."
    }}
  ]
}}

Suggest exactly 3 real books. Always include author and title separately.
"""

    try:
        resposta = gemini_json(prompt)
        livros_sugeridos = resposta.get("livros", [])

        if not livros_sugeridos:
            return await ctx.send("❌ Não consegui gerar sugestões válidas.")

        base_favoritos = "\n".join(f"• {l['titulo']} ({l['nota']:g}⭐)" for l in favoritos)
        await canal_sugestoes.send(
            "✨ **A TUA REVISTA LITERÁRIA PERSONALIZADA** ✨\n"
            "*Sugestões baseadas nos teus livros com 4⭐ ou mais:*\n"
            f"{base_favoritos}"
        )

        titulos_botoes = []

        for livro in livros_sugeridos:
            titulo = livro.get("titulo", "Sem título")
            autor = livro.get("autor", "Desconhecido")
            titulo_completo = formatar_livro(titulo, autor)
            data_publicacao = livro.get("data_publicacao", "Desconhecida")
            genero = livro.get("genero", "N/D")
            subgenero = livro.get("subgenero", "N/D")
            porque_ler = livro.get("porque_ler", "Uma sugestão alinhada com o teu gosto.")
            link_capa = livro.get("link_capa", "")

            if titulo_completo.lower().strip() in {v.lower().strip() for v in vistos}:
                continue

            titulos_botoes.append(titulo_completo)

            embed = discord.Embed(
                title=f"📖 {titulo_completo}",
                description=f"**Autor:** {autor}\n\n{porque_ler}",
                color=discord.Color.from_rgb(255, 182, 193)
            )
            embed.add_field(name="📅 Publicação", value=data_publicacao, inline=True)
            embed.add_field(name="🎭 Género", value=genero, inline=True)
            embed.add_field(name="🧬 Subgénero", value=subgenero, inline=True)

            if isinstance(link_capa, str) and link_capa.startswith("http"):
                embed.set_image(url=link_capa)

            embed.set_footer(text="Gostaste? Guarda na tua lista clicando no painel abaixo.")
            await canal_sugestoes.send(embed=embed)

        if not titulos_botoes:
            return await ctx.send("❌ Todas as sugestões geradas já tinham sido vistas antes.")

        await canal_sugestoes.send(
            "✨ **Adiciona as tuas escolhas instantaneamente:**",
            view=ViewSugestoes(titulos_botoes, titulos_botoes),
        )
        await ctx.send(f"✅ Painel visual gerado com sucesso em {canal_sugestoes.mention}.")

    except Exception as e:
        await ctx.send(f"❌ Erro ao processar recomendações: {e}")


# ==============================================================================
# TBR
# ==============================================================================

@bot.command(name="addtbr", help="Adiciona um livro à TBR geral ou mensal.")
async def adicionar_tbr_mes(ctx: commands.Context, categoria: Optional[str] = None, *, livro: Optional[str] = None):
    if not categoria:
        return await ctx.send("❌ Diz-me o livro que queres adicionar. Exemplo: `!addtbr Nome do Livro`")

    cat_sugerida = normalizar_categoria(categoria)

    if cat_sugerida in dados["tbr_por_mes"]:
        if not livro:
            return await ctx.send(
                f"❌ Falta o nome do livro para adicionar a **{cat_sugerida}**.\n"
                f'Exemplo: `!addtbr {cat_sugerida} "Título - Autor"`'
            )
        cat = cat_sugerida
        texto_livro = livro.strip()
    else:
        cat = "Geral"
        texto_livro = f"{categoria} {livro or ''}".strip()

    try:
        titulo_livro = livro_completo(texto_livro)
    except ValueError:
        return await ctx.send(
            '❌ O formato tem de incluir autor: **"Título - Autor"**.\n'
            'Exemplo: `!addtbr "Quarta Asa - Rebecca Yarros"`'
        )

    ja_existe = any(
        titulo_livro.lower().strip() == item.lower().strip()
        for item in livros_tbr_flat()
    )
    
    livro_similar = None
    if not ja_existe:
        for item in livros_tbr_flat():
            item_norm = unicodedata.normalize('NFKD', item.lower()).encode('ASCII', 'ignore').decode()
            livro_norm = unicodedata.normalize('NFKD', titulo_livro.lower()).encode('ASCII', 'ignore').decode()
            if item_norm == livro_norm:
                ja_existe = True
                livro_similar = item
                break
    
    if ja_existe:
        livro_similar = livro_similar if livro_similar else next((item for item in livros_tbr_flat() if item.lower().strip() == titulo_livro.lower().strip()), titulo_livro)
        view = ViewConfirmarDuplicado(titulo_livro, livro_similar, cat, ctx.author.id)
        await ctx.send(
            f"⚠️ **Atenção!** O livro **{titulo_livro}** é muito semelhante a:\n"
            f"📖 **{livro_similar}**\n\n"
            f"Queres mesmo adicionar na mesma?",
            view=view
        )
        return

    dados["tbr_por_mes"][cat].append(titulo_livro)
    guardar_dados()

    await ctx.send(f"📅 **{titulo_livro}** adicionado com sucesso a **{cat}**.")

    # Detetar série e agendar próximos livros
    await ctx.send("🔍 A verificar se pertence a uma série...")
    
    if cat == "Geral":
        mensagens = await detetar_e_agendar_serie(titulo_livro, "Geral", ctx.channel)
        if mensagens:
            await ctx.send(
                "🧬 **Série detetada!** Sequências agendadas automaticamente na TBR Geral:\n" +
                "\n".join(mensagens) +
                "\n\n💡 Dica: Se quiseres movê-las para meses específicos, usa `!addtbr Mês \"Livro - Autor\"`"
            )
        else:
            await ctx.send("📚 Não foi detetada uma série associada a este livro.")
    else:
        mensagens = await detetar_e_agendar_serie(titulo_livro, cat, ctx.channel)
        if mensagens:
            await ctx.send(
                "🧬 **Série detetada!** Sequências agendadas automaticamente:\n" +
                "\n".join(mensagens)
            )
        else:
            await ctx.send("📚 Não foi detetada uma série associada a este livro.")


@bot.command(name="tbr", help="Sorteia a TBR do mês, tranca até ler tudo e coloca no calendário.")
async def sortear_tbr_mes(ctx: commands.Context, mes: str, extras: int = 2):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    if extras < 0:
        return await ctx.send("❌ O número de extras não pode ser negativo.")

    sorteio_ativo = sorteio_mes_ativo(mes_cap)
    if sorteio_ativo:
        pendentes = sorteio_ativo.get("pendentes", sorteio_ativo.get("livros", []))
        lista = "\n".join(f"• {livro}" for livro in pendentes)
        return await ctx.send(
            f"🔒 O sorteio de **{mes_cap}** está trancado até leres todos os livros.\n"
            f"Faltam:\n{lista}\n\nUsa `!lido \"Título - Autor\"` à medida que fores terminando."
        )

    obrigatorios = list(dados["tbr_por_mes"][mes_cap])
    obrigatorios_norm = {livro.lower().strip() for livro in obrigatorios}
    geral_disponivel = [
        livro
        for livro in dados["tbr_por_mes"]["Geral"]
        if livro.lower().strip() not in obrigatorios_norm
    ]
    extras_sorteados = random.sample(geral_disponivel, min(extras, len(geral_disponivel)))
    livros_sorteio = obrigatorios + extras_sorteados

    if not livros_sorteio:
        return await ctx.send(f"📭 Não tens livros planeados para {mes_cap} nem na lista Geral.")

    dados["sorteios_mes"][mes_cap] = {
        "livros": livros_sorteio,
        "lidos": [],
        "data_sorteio": hoje_str(),
        "ano": int(este_ano()),
    }
    guardar_dados()

    ano = int(este_ano())
    mes_num = numero_mes(mes_cap)
    _, dias_no_mes = calendar.monthrange(ano, mes_num)
    dias_uteis = [d for d in range(1, dias_no_mes + 1) if calendar.weekday(ano, mes_num, d) < 5]
    if not dias_uteis:
        dias_uteis = list(range(1, dias_no_mes + 1))

    passo = max(1, len(dias_uteis) // max(len(livros_sorteio), 1))
    for idx, livro in enumerate(livros_sorteio):
        dia = dias_uteis[min(idx * passo, len(dias_uteis) - 1)]
        data_meta = f"{dia:02d}/{mes_num:02d}/{ano}"
        dados["lembretes_metas"].append({
            "data": data_meta,
            "livro": livro,
            "meta": f"Iniciar/concluir leitura de {livro}",
            "canal_id": ctx.channel.id,
            "avisado": False,
            "tipo": "sorteio_tbr",
        })

    guardar_dados()

    mensagem = f"🎲 **TBR de {mes_cap} sorteada e trancada**\n"
    mensagem += "\n📌 **Livros deste mês:**\n"
    mensagem += "\n".join(f"• {livro}" for livro in livros_sorteio)
    mensagem += "\n\n🔒 Novo sorteio só depois de marcares todos como lidos com `!lido`."

    await enviar_mensagem_longa(ctx, mensagem)

    if Image is not None:
        try:
            imagem = desenhar_calendario_leituras(mes_cap, ano)
            ficheiro = discord.File(imagem, filename=f"tbr-{mes_cap.lower()}-{ano}.png")
            await ctx.send(f"🗓️ Calendário de leituras de **{mes_cap}**:", file=ficheiro)
        except Exception:
            pass


@bot.command(name="verbar", help="Mostra toda a TBR organizada por mês.")
async def ver_tbr_completa(ctx: commands.Context):
    mensagem = f"📋 **PLANEAMENTO DE TBR ({este_ano()})** 📋\n"

    if dados["tbr_por_mes"]["Geral"]:
        mensagem += f"\n🌎 **Geral:** {', '.join(dados['tbr_por_mes']['Geral'])}"

    for mes in MESES_ORDEM:
        if dados["tbr_por_mes"][mes]:
            mensagem += f"\n📅 **{mes}**: {', '.join(dados['tbr_por_mes'][mes])}"

    await enviar_mensagem_longa(ctx, mensagem)


@bot.command(name="remtbr", help="Remove um livro da TBR.")
async def remover_tbr_mes(ctx: commands.Context, categoria: str, *, livro: str):
    cat = normalizar_categoria(categoria)

    if cat not in dados["tbr_por_mes"]:
        return await ctx.send("❌ Categoria inválida.")

    existente = buscar_livro_case_insensitive(dados["tbr_por_mes"][cat], livro)
    if not existente:
        return await ctx.send(f"❌ *{livro}* não foi encontrado em **{cat}**.")

    dados["tbr_por_mes"][cat].remove(existente)
    guardar_dados()
    await ctx.send(f"🗑️ *{existente}* removido com sucesso de **{cat}**.")


# ==============================================================================
# METAS E LEMBRETES (SEM CALENDÁRIO FEIO)
# ==============================================================================

@bot.command(
    name="meta",
    help='Cria metas de leitura conjunta. Ex.: !meta Junho "Quarta Asa - Rebecca Yarros" dia 7 até cap. 10',
)
async def definir_meta_lc(ctx: commands.Context, mes: str, livro: str, *, cronograma: str):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    try:
        livro_completo_txt = livro_completo(livro)
        titulo_curto, autor = parsear_livro(livro_completo_txt)
    except ValueError:
        return await ctx.send(
            '❌ Usa o formato **"Título - Autor"**.\n'
            'Exemplo: `!meta Junho "Quarta Asa - Rebecca Yarros" dia 7 até cap. 10`'
        )

    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só funciona dentro de um servidor.")

    mensagem_tbr = adicionar_livro_a_tbr_mes(livro_completo_txt, mes_cap)
    guardar_dados()

    nome_canal_mes = canal_nome_seguro(mes_cap)
    canal_mes = await garantir_canal(guild, nome_canal_mes)

    mensagem_ancora = await canal_mes.send(
        f"📚 **LEITURA CONJUNTA: {titulo_curto.upper()}** 📚\n👤 **Autor:** {autor}"
    )
    topico_livro = await canal_mes.create_thread(
        name=f"livro-{canal_nome_seguro(livro_completo_txt)[:70]}",
        message=mensagem_ancora,
    )

    await ctx.send(f"{mensagem_tbr}\n🔮 A organizar cronograma em {topico_livro.mention}...")

    prompt = f"""
You are a joint reading assistant. Create a reading schedule for "{livro_completo_txt}" in {mes_cap} {este_ano()}.

Reader instructions:
"{cronograma}"

Rules:
1. Extract the goals with their specific dates.
2. Each goal should have a date (DD/MM format) and a short description.
3. Write the descriptions in European Portuguese (pt-PT) or English — never Brazilian Portuguese.

Respond only with valid JSON in this structure:
{{
  "metas": [ {{"data": "DD/MM/{este_ano()}", "texto": "Short goal description"}} ],
  "nota": "Brief explanation of the schedule (optional)"
}}
"""

    try:
        resposta = gemini_json(prompt)
        metas = resposta.get("metas", [])
        nota = resposta.get("nota", "")

        if nota:
            await enviar_mensagem_longa(topico_livro, f"ℹ️ {nota}")

        lembretes_criados = 0

        for m in metas:
            data_meta = str(m.get("data", "")).strip()
            texto_meta = str(m.get("texto", "")).strip()
            if not data_valida(data_meta) or not texto_meta:
                continue

            dados["lembretes_metas"].append({
                "data": data_meta,
                "livro": livro_completo_txt,
                "autor": autor,
                "meta": texto_meta,
                "canal_id": topico_livro.id,
                "thread_id": topico_livro.id,
                "avisado": False,
                "tipo": "lc",
            })
            lembretes_criados += 1

        guardar_dados()

        if Image is not None:
            try:
                imagem = desenhar_calendario_leituras(mes_cap, int(este_ano()))
                ficheiro = discord.File(imagem, filename=f"lc-{mes_cap.lower()}-{este_ano()}.png")
                await topico_livro.send("🗓️ **Calendário visual do mês:**", file=ficheiro)
            except Exception:
                pass

        await ctx.send(
            f"✅ Metas guardadas com sucesso para {topico_livro.mention}. "
            f"Lembretes criados: **{lembretes_criados}**.\n"
            f"Usa `!calendariolc {mes_cap}` para gerar o calendário visual novamente."
        )

    except Exception as e:
        await ctx.send(f"❌ Erro ao processar metas: {e}")


async def enviar_lembretes_pendentes_hoje() -> None:
    data_hoje = datetime.now().strftime("%d/%m/%Y")
    alterado = False

    for lembrete in dados["lembretes_metas"]:
        if lembrete.get("data") != data_hoje or lembrete.get("avisado"):
            continue

        canal_id = lembrete.get("thread_id") or lembrete.get("canal_id")
        if not canal_id:
            continue

        canal = await obter_canal_discord(int(canal_id))
        if not canal:
            continue

        try:
            await canal.send(
                f"🔔 **METAS DE HOJE!**\n"
                f"Livro: **{lembrete.get('livro', 'Livro')}**\n"
                f"📖 **Meta:** {lembrete.get('meta', '')}\n"
                f"Boas leituras!"
            )
            lembrete["avisado"] = True
            alterado = True
        except discord.HTTPException:
            continue

    if alterado:
        guardar_dados()


@tasks.loop(minutes=5)
async def verificar_lembretes_loop():
    await enviar_lembretes_pendentes_hoje()


@verificar_lembretes_loop.before_loop
async def antes_lembretes():
    await bot.wait_until_ready()


@tasks.loop(hours=6)
async def resumos_automaticos_loop():
    agora = datetime.now()
    
    if agora.day == 1 and agora.hour == 10:
        mes_anterior_idx = agora.month - 2
        if mes_anterior_idx < 0:
            mes_anterior_idx = 11
            ano = agora.year - 1
        else:
            ano = agora.year
        mes_nome = MESES_ORDEM[mes_anterior_idx]
        for guild in bot.guilds:
            canal = discord.utils.get(guild.text_channels, name="sugestoes-leitura")
            if canal and Image is not None:
                stats = estatisticas_mes(mes_nome, ano)
                if stats["total_livros"] > 0:
                    img = desenhar_grafico_barras(
                        f"Resumo de {mes_nome} {ano}",
                        ["Livros", "Páginas", "Autores", "Géneros"],
                        [stats["total_livros"], stats["paginas"], stats["autores_unicos"], stats["generos_unicos"]],
                    )
                    await canal.send(
                        f"📊 **Resumo de leituras - {mes_nome} {ano}**\n"
                        f"Total de livros: {stats['total_livros']}\n"
                        f"Páginas lidas: {stats['paginas']}\n"
                        f"Autores distintos: {stats['autores_unicos']}\n"
                        f"Géneros diferentes: {stats['generos_unicos']}",
                        file=discord.File(img, filename=f"resumo-{mes_nome.lower()}.png")
                    )

    if agora.month == 1 and agora.day == 2 and agora.hour == 10:
        ano_anterior = agora.year - 1
        for guild in bot.guilds:
            canal = discord.utils.get(guild.text_channels, name="sugestoes-leitura")
            if canal and Image is not None:
                stats = estatisticas_ano(ano_anterior)
                if stats["total_livros"] > 0:
                    img = desenhar_resumo_anual(ano_anterior, stats)
                    await canal.send(
                        f"🏆 **Resumo Anual {ano_anterior}** 🏆\n"
                        f"Livros lidos: {stats['total_livros']}\n"
                        f"Páginas lidas: {stats['total_paginas']}\n"
                        f"Autor mais lido: {stats['autor_top'][0]} ({stats['autor_top'][1]} livros)\n"
                        f"Género dominante: {stats['genero_top'][0]} ({stats['genero_top'][1]} livros)",
                        file=discord.File(img, filename=f"resumo-anual-{ano_anterior}.png")
                    )


@resumos_automaticos_loop.before_loop
async def antes_resumos():
    await bot.wait_until_ready()


@tasks.loop(hours=1)
async def verificar_lc_concluidas():
    data_hoje = datetime.now().strftime("%d/%m/%Y")
    
    livros_lc = {}
    for lembrete in dados["lembretes_metas"]:
        if lembrete.get("tipo") != "lc":
            continue
        livro = lembrete.get("livro")
        if livro not in livros_lc:
            livros_lc[livro] = {
                "lembretes": [],
                "canal_id": lembrete.get("thread_id") or lembrete.get("canal_id"),
                "autor": lembrete.get("autor", ""),
                "total_metas": 0,
                "metas_cumpridas": 0
            }
        livros_lc[livro]["lembretes"].append(lembrete)
    
    for livro, info in livros_lc.items():
        info["total_metas"] = len(info["lembretes"])
        
        metas_cumpridas = 0
        for lembrete in info["lembretes"]:
            try:
                data_meta = datetime.strptime(lembrete["data"], "%d/%m/%Y")
                data_hoje_dt = datetime.now()
                if data_meta.date() <= data_hoje_dt.date():
                    metas_cumpridas += 1
            except (TypeError, ValueError):
                pass
        
        if info.get("notificado") or metas_cumpridas < info["total_metas"]:
            continue
        
        info["notificado"] = True
        
        canal = await obter_canal_discord(int(info["canal_id"]))
        if not canal:
            continue
        
        if livro_ja_lido(livro):
            await canal.send(
                f"📚 **LC CONCLUÍDA!**\n"
                f"O livro **{livro}** já está registado como lido. 🎉"
            )
            continue
        
        view = ViewConfirmarLido(livro, info["autor"], info["canal_id"])
        await canal.send(
            f"🎉 **PARABÉNS! A leitura conjunta de '{livro}' foi concluída!** 🎉\n\n"
            f"Todas as metas foram cumpridas. Queres registar este livro como lido?",
            view=view
        )


@verificar_lc_concluidas.before_loop
async def antes_verificar_lc():
    await bot.wait_until_ready()


@bot.command(name="editmeta", help='Edita metas de uma LC existente. Ex.: !editmeta "Título - Autor" dia 7 até cap. 10')
async def editar_meta_lc(ctx: commands.Context, livro: str, *, cronograma: str):
    try:
        livro_completo_txt = livro_completo(livro)
        _, autor = parsear_livro(livro_completo_txt)
    except ValueError:
        return await ctx.send('❌ Usa o formato **"Título - Autor"**.')

    lembretes_livro = [
        l for l in dados["lembretes_metas"]
        if l.get("livro", "").lower().strip() == livro_completo_txt.lower().strip() and l.get("tipo") == "lc"
    ]
    if not lembretes_livro:
        return await ctx.send("❌ Não encontrei metas de leitura conjunta para esse livro.")

    meses_encontrados = set()
    for l in lembretes_livro:
        try:
            data = datetime.strptime(l["data"], "%d/%m/%Y")
            meses_encontrados.add(MESES_ORDEM[data.month - 1])
        except (TypeError, ValueError, IndexError):
            pass
    mes_cap = next(iter(meses_encontrados), MESES_ORDEM[datetime.now().month - 1])

    dados["lembretes_metas"] = [
        l for l in dados["lembretes_metas"]
        if not (l.get("livro", "").lower().strip() == livro_completo_txt.lower().strip() and l.get("tipo") == "lc")
    ]

    canal_id = lembretes_livro[0].get("thread_id") or lembretes_livro[0].get("canal_id")
    prompt = f"""
Create an updated reading schedule for "{livro_completo_txt}" in {mes_cap} {este_ano()}.

New instructions:
"{cronograma}"

Rules:
1. Extract the goals with their specific dates.
2. Each goal should have a date (DD/MM format) and a short description.
3. Write the descriptions in European Portuguese (pt-PT) or English.

JSON only:
{{
  "metas": [ {{"data": "DD/MM/{este_ano()}", "texto": "Short goal description"}} ],
  "nota": "Brief explanation (optional)"
}}
"""

    try:
        resposta = gemini_json(prompt)
        metas = resposta.get("metas", [])
        nota = resposta.get("nota", "")

        canal = await obter_canal_discord(int(canal_id)) if canal_id else ctx.channel
        if canal and nota:
            await enviar_mensagem_longa(canal, f"ℹ️ {nota}")

        criados = 0
        for m in metas:
            data_meta = str(m.get("data", "")).strip()
            texto_meta = str(m.get("texto", "")).strip()
            if not data_valida(data_meta) or not texto_meta:
                continue
            dados["lembretes_metas"].append({
                "data": data_meta,
                "livro": livro_completo_txt,
                "autor": autor,
                "meta": texto_meta,
                "canal_id": canal_id,
                "thread_id": canal_id,
                "avisado": False,
                "tipo": "lc",
            })
            criados += 1

        guardar_dados()

        if Image is not None:
            try:
                imagem = desenhar_calendario_leituras(mes_cap, int(este_ano()))
                ficheiro = discord.File(imagem, filename=f"lc-edit-{mes_cap.lower()}.png")
                await ctx.send("🗓️ **Calendário visual atualizado:**", file=ficheiro)
            except Exception:
                pass

        await ctx.send(f"✅ Metas atualizadas para **{livro_completo_txt}**. Novos lembretes: **{criados}**.")
    except Exception as e:
        await ctx.send(f"❌ Erro ao editar metas: {e}")


@bot.command(name="calendariolc", help="Cria uma imagem do calendário mensal das leituras conjuntas.")
async def calendario_leituras_conjuntas(ctx: commands.Context, mes: Optional[str] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar a biblioteca de imagem. Usa: `pip install Pillow`")

    mes_alvo = normalizar_categoria(mes) if mes else MESES_ORDEM[datetime.now().month - 1]
    if mes_alvo not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido. Exemplo: `!calendariolc Junho`")

    ano = int(este_ano())

    try:
        imagem = desenhar_calendario_leituras(mes_alvo, ano)
    except Exception as e:
        return await ctx.send(f"❌ Erro ao criar calendário: {e}")

    ficheiro = discord.File(imagem, filename=f"leituras-conjuntas-{mes_alvo.lower()}-{ano}.png")
    await ctx.send(
        f"🗓️ **Calendário de leituras conjuntas - {mes_alvo} {ano}**",
        file=ficheiro
    )


# ==============================================================================
# LIDOS / A-Z / HISTÓRICO
# ==============================================================================

@bot.command(name="lido", help='Regista um livro como lido. Formato: "Título - Autor".')
async def livro_lido(ctx: commands.Context, *, titulo_livro: str):
    try:
        titulo_completo = livro_completo(titulo_livro)
        titulo_curto, autor = parsear_livro(titulo_completo)
    except ValueError:
        return await ctx.send(
            '❌ O formato tem de incluir autor: **"Título - Autor"**.\n'
            'Exemplo: `!lido "Quarta Asa - Rebecca Yarros"`'
        )

    ja_existe = livro_ja_lido(titulo_completo)
    if ja_existe:
        return await ctx.send(f"⚠️ O livro **{titulo_completo}** já está registado como lido.")

    info = await obter_info_livro(titulo_completo)
    novo_livro = {
        "titulo": titulo_completo,
        "autor": autor,
        "estrelas": "Sem avaliação",
        "nota": 0.0,
        "genero": info.get("genero", "N/D"),
        "paginas": int(info.get("paginas", 0) or 0),
        "data_leitura": hoje_str(),
        "fonte_metadados": info.get("fonte", "IA"),
    }

    dados["livros_lidos"].append(novo_livro)

    removido_de = []
    for chave, lista in dados["tbr_por_mes"].items():
        for item in lista[:]:
            if item.lower().strip() == titulo_completo.lower().strip():
                lista.remove(item)
                removido_de.append(chave)
                break
            item_norm = unicodedata.normalize('NFKD', item.lower()).encode('ASCII', 'ignore').decode()
            livro_norm = unicodedata.normalize('NFKD', titulo_completo.lower()).encode('ASCII', 'ignore').decode()
            if item_norm == livro_norm:
                lista.remove(item)
                removido_de.append(chave)
                break

    meses_desbloqueados = marcar_livro_sorteio_lido(titulo_completo)
    aviso_remocao = f" (removido de: {', '.join(removido_de)})" if removido_de else ""
    aviso_sorteio = ""
    if meses_desbloqueados:
        aviso_sorteio = f"\n🔓 Sorteio desbloqueado em: **{', '.join(meses_desbloqueados)}**."

    await ctx.send(f"✍️ A registar '{titulo_completo}' e a validar o Desafio A-Z...")

    resultado = analisar_titulo_alfabeto(titulo_curto)
    aviso_alfabeto = ""

    if resultado["status"] == "BANIDO":
        aviso_alfabeto = "\n🔤 **Desafio A-Z:** Título começado por artigo. Não conta. ❌"
    elif resultado["status"] == "OK":
        letra = resultado["letra"]

        if letra in dados["desafio_alfabeto"]:
            if dados["desafio_alfabeto"][letra] == VAZIO_ALFABETO:
                dados["desafio_alfabeto"][letra] = titulo_completo
                aviso_alfabeto = f"\n🔤 **Desafio A-Z:** Letra **{letra}** conquistada! 🎉"
            else:
                aviso_alfabeto = (
                    f"\n🔤 **Desafio A-Z:** A letra **{letra}** já se encontrava preenchida "
                    f"por **{dados['desafio_alfabeto'][letra]}**."
                )
    else:
        aviso_alfabeto = "\n⚠️ Não foi possível determinar uma letra válida para o desafio."

    guardar_dados()
    total_lidos = len(dados["livros_lidos"])

    await ctx.send(
        f"📚 **{titulo_completo}** adicionado aos lidos!{aviso_remocao}{aviso_sorteio}{aviso_alfabeto}\n"
        f"📊 Progresso Anual: {total_lidos}/{META_ANUAL} livros em {este_ano()}.\n"
        f"📎 Metadados via **{info.get('fonte', 'IA')}**.\n"
        f"Escolhe a avaliação:",
        view=ViewAvaliacao(titulo_completo, ctx.author.id),
    )


@bot.command(name="alfabeto", help="Mostra o progresso do desafio A-Z.")
async def ver_desafio_alfabeto(ctx: commands.Context):
    preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
    msg = f"🔤 **DESAFIO A A Z ({este_ano()})**\n📊 Progresso Geral: **{preenchidas}/26** letras completadas.\n\n"

    for letra, livro in dados["desafio_alfabeto"].items():
        icon = "🟢" if livro != VAZIO_ALFABETO else "⚫"
        msg += f"{icon} **{letra}**: {livro}\n"

    await ctx.send(msg)


@bot.command(name="desafios", help="Mostra o progresso geral dos desafios de leitura.")
async def ver_progresso_desafios(ctx: commands.Context):
    total_lidos = len(dados["livros_lidos"])
    percentagem_anual = min(100, round((total_lidos / META_ANUAL) * 100))

    letras_preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
    percentagem_az = round((letras_preenchidas / 26) * 100)
    letras_em_falta = [letra for letra, livro in dados["desafio_alfabeto"].items() if livro == VAZIO_ALFABETO]

    total_tbr = len(livros_tbr_flat())
    metas_ativas = sum(1 for lembrete in dados["lembretes_metas"] if not lembrete.get("avisado", False))
    livros_avaliados = sum(
        1
        for livro in dados["livros_lidos"]
        if livro.get("estrelas") and livro.get("estrelas") != "Sem avaliação"
    )

    embed = discord.Embed(
        title=f"🏆 PROGRESSO DOS DESAFIOS ({este_ano()})",
        color=discord.Color.gold()
    )
    embed.add_field(
        name="📚 Meta anual",
        value=f"**{total_lidos}/{META_ANUAL}** livros lidos ({percentagem_anual}%)",
        inline=False
    )
    embed.add_field(
        name="🔤 Desafio A-Z",
        value=(
            f"**{letras_preenchidas}/26** letras completas ({percentagem_az}%).\n"
            f"Faltam: {', '.join(letras_em_falta) if letras_em_falta else 'nenhuma 🎉'}"
        ),
        inline=False
    )
    embed.add_field(
        name="⭐ Avaliações",
        value=f"**{livros_avaliados}/{total_lidos}** livros lidos avaliados.",
        inline=False
    )
    embed.add_field(
        name="📅 Leituras conjuntas",
        value=f"**{metas_ativas}** metas futuras/pendentes guardadas.",
        inline=False
    )
    embed.add_field(
        name="📌 TBR",
        value=f"**{total_tbr}** livros por ler no planeamento.",
        inline=False
    )
    embed.set_footer(text="Usa !alfabeto para ver o detalhe letra a letra.")

    await ctx.send(embed=embed)


@bot.command(name="remalfabeto", help="Remove um livro de uma letra do desafio A-Z.")
async def remover_do_alfabeto(ctx: commands.Context, letra: str):
    letra = letra.strip().upper()

    if len(letra) != 1 or letra not in dados["desafio_alfabeto"]:
        return await ctx.send("❌ Letra inválida. Usa apenas uma letra de A a Z. Exemplo: `!remalfabeto B`")

    livro_atual = dados["desafio_alfabeto"][letra]

    if livro_atual == VAZIO_ALFABETO:
        preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
        return await ctx.send(
            f"⚫ A letra **{letra}** já estava vazia.\n"
            f"Progresso atual do A-Z: **{preenchidas}/26**. Usa `!alfabeto` para ver a lista completa."
        )

    dados["desafio_alfabeto"][letra] = VAZIO_ALFABETO
    guardar_dados()

    preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)

    await ctx.send(
        f"🗑️ A letra **{letra}** foi limpa com sucesso.\n"
        f"Livro removido: **{livro_atual}**\n"
        f"Progresso atual do A-Z: **{preenchidas}/26**."
    )


@bot.command(name="avaliar", help="Avalia o último livro lido (0.25 a 5, de 0.25 em 0.25).")
async def avaliar_livro(ctx: commands.Context, nota: float):
    if not dados["livros_lidos"]:
        return await ctx.send("❌ Ainda não registaste nenhum livro lido para avaliar.")

    if not nota_valida(nota):
        return await ctx.send("❌ A nota deve ser entre 0.25 e 5, em passos de 0.25.")

    dados["livros_lidos"][-1]["nota"] = nota
    dados["livros_lidos"][-1]["estrelas"] = estrelas_para_texto(nota)
    guardar_dados()
    await ctx.send(f"🎨 Avaliação guardada com sucesso: {dados['livros_lidos'][-1]['estrelas']}")


@bot.command(name="remlido")
async def remover_lido(ctx: commands.Context, *, titulo_livro: str):
    encontrado = None

    for livro in dados["livros_lidos"]:
        if livro.get("titulo", "").lower().strip() == titulo_livro.lower().strip():
            encontrado = livro
            break

    if not encontrado:
        return await ctx.send("❌ Livro não encontrado.")

    dados["livros_lidos"].remove(encontrado)

    letras_limpas = []
    titulo_encontrado = encontrado.get("titulo", titulo_livro)
    for letra, livro_alfabeto in dados["desafio_alfabeto"].items():
        if str(livro_alfabeto).lower().strip() == titulo_encontrado.lower().strip():
            dados["desafio_alfabeto"][letra] = VAZIO_ALFABETO
            letras_limpas.append(letra)

    guardar_dados()

    aviso_alfabeto = ""
    if letras_limpas:
        aviso_alfabeto = f"\n🔤 Também removi do Desafio A-Z: **{', '.join(letras_limpas)}**."

    await ctx.send(
        f"🗑️ Livro removido: **{titulo_encontrado}**{aviso_alfabeto}"
    )


@bot.command(name="historico", help="Mostra o histórico de leituras.")
async def mostrar_historico(ctx: commands.Context):
    if not dados["livros_lidos"]:
        return await ctx.send("📭 O teu histórico de leituras ainda está vazio.")

    linhas = []
    for i, l in enumerate(dados["livros_lidos"], 1):
        genero = l.get("genero", "")
        paginas = l.get("paginas", 0)
        extra = ""
        if genero and genero != "N/D":
            extra += f" | {genero}"
        if paginas:
            extra += f" | {paginas} págs."
        linhas.append(
            f"{i}. {l.get('titulo', 'Sem título')} — {l.get('estrelas', 'Sem avaliação')}{extra}"
        )
    await enviar_mensagem_longa(ctx, f"📜 **HISTÓRICO DE LEITURAS** 📜\n\n" + "\n".join(linhas))


@bot.command(name="marcarsugestoes", help="Marca sugestões como já vistas para não voltarem a aparecer.")
async def marcar_sugestoes_vistas(ctx: commands.Context, *, titulos: str):
    novos = 0
    vistos = {v.lower().strip() for v in dados.setdefault("sugestoes_vistas", [])}
    for titulo in [t.strip() for t in titulos.split("|") if t.strip()]:
        if titulo.lower() not in vistos:
            dados["sugestoes_vistas"].append(titulo)
            vistos.add(titulo.lower())
            novos += 1
    guardar_dados()
    await ctx.send(f"✅ **{novos}** sugestão(ões) arquivada(s).")


# ==============================================================================
# BOOKSTAGRAM / EXTRAS
# ==============================================================================

@bot.command(name="trend", help="Gera ideias de posts ou reels de Bookstagram.")
async def sugerir_trends_bookstagram(ctx: commands.Context, *, livro_foco: str = None):
    ultimo = (
        dados["livros_lidos"][-1].get("titulo", "um romance ou fantasia em voga")
        if dados["livros_lidos"]
        else "um romance ou fantasia em voga"
    )
    livro_alvo = livro_foco if livro_foco else ultimo

    await ctx.send(f"📸 A analisar ideias para: **{livro_alvo}**...")
    prompt = (
        f"Gera 3 ideias criativas de posts ou reels estéticos de Bookstagram com base em trends de {este_ano()} "
        f"para o livro '{livro_alvo}' em português de Portugal. Adiciona sugestões de áudio e hashtags."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"✨ **TRENDS INSTAGRAM** ✨\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar trends: {e}")


@bot.command(name="entrevista", help="Entrevista uma personagem fictícia.")
async def entrevistar_personagem(ctx: commands.Context, personagem: str, *, pergunta: str):
    await ctx.send(f"🔮 A invocar o espírito de {personagem}...")

    prompt = (
        f"Assume integralmente a personalidade da personagem fictícia '{personagem}'. "
        f"Responde estritamente na primeira pessoa, em português de Portugal. "
        f"Pergunta: '{pergunta}'"
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"**[{personagem}]:** {res}")
    except Exception as e:
        await ctx.send(f"❌ Erro na entrevista: {e}")


@bot.command(name="ressaca", help="Sugere leituras para curar ressaca literária.")
async def curar_ressaca(ctx: commands.Context, *, livro_destruidor: str):
    prompt = (
        f"O leitor está em ressaca literária após ler '{livro_destruidor}'. "
        f"Sugere duas opções de livros reais, leves e cativantes, justificando em português de Portugal."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"🩺 **DIAGNÓSTICO PARA RESSACA LITERÁRIA**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar sugestões: {e}")


@bot.command(name="teoria", help="Reage à tua teoria de leitura sem spoilers confirmados.")
async def avaliar_teoria(ctx: commands.Context, *, teoria_leitora: str):
    prompt = (
        f"Uma leitora partilhou esta teoria sobre os rumos de uma história: '{teoria_leitora}'. "
        f"Reage como uma fã empolgada, sem spoilers confirmados, em português de Portugal."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"💭 **AVALIAÇÃO DA TUA TEORIA:**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao avaliar teoria: {e}")


@bot.command(name="vibe", help="Gera uma estética visual e temática para um livro.")
async def gerar_estetica(ctx: commands.Context, *, nome_livro: str):
    prompt = (
        f"Cria um guia compacto de estética literária para o livro '{nome_livro}' "
        f"(cenários, cores, objetos marcantes), ideal para fotos de Bookstagram."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"📸 **BOOKSTAGRAM MOODBOARD VIBE:**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar vibe: {e}")


@bot.command(name="livroinfo", help="Pesquisa metadados via ReadMore/Open Library.")
async def info_livro(ctx: commands.Context, *, consulta: str):
    await ctx.send(f"🔍 A pesquisar **{consulta}**...")
    info = await obter_info_livro(consulta)
    embed = discord.Embed(
        title=f"📖 {info.get('titulo', consulta)}",
        description=f"**Autor:** {info.get('autor', 'Desconhecido')}",
        color=discord.Color.teal(),
    )
    embed.add_field(name="Género", value=info.get("genero", "N/D"), inline=True)
    embed.add_field(name="Páginas", value=str(info.get("paginas", 0) or "N/D"), inline=True)
    embed.add_field(name="Ano", value=str(info.get("ano", "N/D")), inline=True)
    embed.add_field(name="Fonte", value=info.get("fonte", "IA"), inline=True)
    if info.get("capa"):
        embed.set_thumbnail(url=info["capa"])
    await ctx.send(embed=embed)


@bot.command(name="resumomes", help="Gera gráfico das leituras de um mês.")
async def resumo_mensal(ctx: commands.Context, mes: Optional[str] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar Pillow: `pip install Pillow`")

    mes_alvo = normalizar_categoria(mes) if mes else MESES_ORDEM[datetime.now().month - 1]
    if mes_alvo not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido. Exemplo: `!resumomes Junho`")

    ano = int(este_ano())
    stats = estatisticas_mes(mes_alvo, ano)
    if stats["total_livros"] == 0:
        return await ctx.send(f"📭 Sem leituras registadas em **{mes_alvo} {ano}**.")

    img = desenhar_grafico_barras(
        f"Resumo de {mes_alvo} {ano}",
        ["Livros", "Páginas", "Autores", "Géneros"],
        [stats["total_livros"], stats["paginas"], stats["autores_unicos"], stats["generos_unicos"]],
    )
    detalhe = (
        f"📊 **{mes_alvo} {ano}**\n"
        f"Livros: **{stats['total_livros']}** | Páginas: **{stats['paginas']}**\n"
        f"Autores distintos: **{stats['autores_unicos']}** | Géneros: **{stats['generos_unicos']}**"
    )
    await ctx.send(detalhe, file=discord.File(img, filename=f"resumo-{mes_alvo.lower()}.png"))


@bot.command(name="resumoano", help="Apresentação visual do ano de leituras.")
async def resumo_anual(ctx: commands.Context, ano: Optional[int] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar Pillow: `pip install Pillow`")

    ano_alvo = ano or int(este_ano())
    stats = estatisticas_ano(ano_alvo)
    if stats["total_livros"] == 0:
        return await ctx.send(f"📭 Sem leituras registadas em **{ano_alvo}**.")

    img = desenhar_resumo_anual(ano_alvo, stats)
    await ctx.send(
        f"🏆 **Resumo anual {ano_alvo}** — {stats['total_livros']} livros, "
        f"{stats['total_paginas']} páginas.",
        file=discord.File(img, filename=f"resumo-anual-{ano_alvo}.png"),
    )


@bot.command(name="sprint", help="Inicia um sprint de leitura com temporizador.")
async def sprint_leitura(ctx: commands.Context, minutes: int):
    if minutes <= 0:
        return await ctx.send("❌ O tempo deve ser superior a 0 minutos.")

    await ctx.send(
        f"⏱️ **Sprint de Leitura começado!**\n"
        f"Foco total durante **{minutes}** minutos. Boas páginas! 📖"
    )
    await asyncio.sleep(minutes * 60)
    await ctx.send(
        f"🔔 **FIM DO SPRINT!** {ctx.author.mention}, o tempo acabou! "
        f"Quantas páginas conseguiste ler?"
    )


# ==============================================================================
# RUN
# ==============================================================================

if __name__ == "__main__":
    bot.run(DISCORD_TOKEN)
load_dotenv()

DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY")
COMMAND_PREFIX = os.getenv("PREFIX", "!")
_SCRIPT_DIR = Path(__file__).resolve().parent
_DATA_DIR = Path(os.getenv("BOT_DATA_DIR", _SCRIPT_DIR)).expanduser().resolve()
_DATA_DIR.mkdir(parents=True, exist_ok=True)
DATA_FILE = Path(os.getenv("BOT_DATA_FILE", _DATA_DIR / "dados_bot.json")).expanduser().resolve()
BACKUP_FILE = DATA_FILE.with_name(f"{DATA_FILE.stem}.backup.json")
_dados_lock = threading.Lock()
SUPABASE_URL = os.getenv("SUPABASE_URL", "").rstrip("/")
SUPABASE_KEY = os.getenv("SUPABASE_KEY", "")
JSONBIN_BIN_ID = os.getenv("JSONBIN_BIN_ID", "")
JSONBIN_API_KEY = os.getenv("JSONBIN_API_KEY", "")
BOT_DATA_URL = os.getenv("BOT_DATA_URL", "")
BOT_DATA_SAVE_URL = os.getenv("BOT_DATA_SAVE_URL", BOT_DATA_URL)
BOT_DATA_TOKEN = os.getenv("BOT_DATA_TOKEN", "")
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN", "")
GITHUB_REPO = os.getenv("GITHUB_REPO", os.getenv("GITHUB_REPOSITORY", ""))
GITHUB_BRANCH = os.getenv("GITHUB_BRANCH", "main")
GITHUB_DATA_PATH = os.getenv("GITHUB_DATA_PATH", "dados_bot.json")
_github_file_sha: Optional[str] = None
_ultimo_snapshot: Optional[str] = None
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")
VAZIO_ALFABETO = "❌ Vazio"

if not DISCORD_TOKEN:
    raise RuntimeError("Falta DISCORD_TOKEN no ficheiro .env")
if not GEMINI_API_KEY:
    raise RuntimeError("Falta GEMINI_API_KEY no ficheiro .env")

ai_client = genai.Client(api_key=GEMINI_API_KEY)

META_ANUAL = 80
MESES_ORDEM = [
    "Janeiro", "Fevereiro", "Março", "Abril", "Maio", "Junho",
    "Julho", "Agosto", "Setembro", "Outubro", "Novembro", "Dezembro"
]
SEPARADOR_LIVRO = " - "
NOTAS_DISPONIVEIS = [i * 0.25 for i in range(1, 21)]
READMORE_API_URL = os.getenv("READMORE_API_URL", "https://readmore.onrender.com")


# ==============================================================================
# PERSISTÊNCIA
# ==============================================================================

def estado_inicial() -> Dict[str, Any]:
    return {
        "livros_lidos": [],
        "review_em_andamento": {},
        "lembretes_metas": [],
        "sugestoes_vistas": [],
        "sorteios_mes": {},
        "tbr_por_mes": {
            "Geral": [],
            "Janeiro": [], "Fevereiro": [], "Março": [], "Abril": [],
            "Maio": [], "Junho": [], "Julho": [], "Agosto": [],
            "Setembro": [], "Outubro": [], "Novembro": [], "Dezembro": []
        },
        "desafio_alfabeto": {letra: VAZIO_ALFABETO for letra in "ABCDEFGHIJKLMNOPQRSTUVWXYZ"}
    }


def normalizar_tbr_por_mes(tbr: Any) -> Dict[str, List[str]]:
    base = estado_inicial()["tbr_por_mes"]
    if not isinstance(tbr, dict):
        return {mes: list(livros) for mes, livros in base.items()}

    resultado = {mes: list(base[mes]) for mes in base}
    for mes, livros in tbr.items():
        if mes not in resultado:
            continue
        if isinstance(livros, list):
            resultado[mes] = [str(livro) for livro in livros if str(livro).strip()]
        else:
            resultado[mes] = []
    return resultado


def aplicar_dados_carregados(bruto: Dict[str, Any]) -> Dict[str, Any]:
    base = estado_inicial()
    base.update(bruto)
    base["tbr_por_mes"] = normalizar_tbr_por_mes(bruto.get("tbr_por_mes"))
    base["desafio_alfabeto"] = {
        **estado_inicial()["desafio_alfabeto"],
        **(bruto.get("desafio_alfabeto") if isinstance(bruto.get("desafio_alfabeto"), dict) else {}),
    }
    base["sugestoes_vistas"] = list(bruto.get("sugestoes_vistas", []))
    base["sorteios_mes"] = dict(bruto.get("sorteios_mes", {}))
    base["livros_lidos"] = migrar_livros_lidos(bruto.get("livros_lidos", []))
    base["lembretes_metas"] = list(bruto.get("lembretes_metas", []))
    base["review_em_andamento"] = dict(bruto.get("review_em_andamento", {}))
    return base


def _ler_ficheiro_dados(ficheiro: Path) -> Dict[str, Any]:
    with open(ficheiro, "r", encoding="utf-8") as f:
        bruto = json.load(f)
    if not isinstance(bruto, dict):
        raise ValueError("Formato inválido")
    return aplicar_dados_carregados(bruto)


def em_nuvem() -> bool:
    return any(
        os.getenv(var)
        for var in ("RENDER", "RAILWAY_ENVIRONMENT", "DYNO", "FLY_APP_NAME", "K_SERVICE", "VERCEL")
    )


def modo_armazenamento() -> str:
    if GITHUB_TOKEN and GITHUB_REPO:
        return "github"
    if SUPABASE_URL and SUPABASE_KEY:
        return "supabase"
    if JSONBIN_BIN_ID and JSONBIN_API_KEY:
        return "jsonbin"
    if BOT_DATA_URL:
        return "url"
    return "local"


def _snapshot_dados() -> str:
    return json.dumps(dados, sort_keys=True, ensure_ascii=False)


def _github_headers() -> Dict[str, str]:
    return {
        "Authorization": f"Bearer {GITHUB_TOKEN}",
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }


def _parse_github_repo() -> Tuple[str, str]:
    repo = GITHUB_REPO.strip()
    if "/" not in repo:
        raise ValueError("GITHUB_REPO deve estar no formato owner/repo")
    owner, nome = repo.split("/", 1)
    return owner.strip(), nome.strip()


def carregar_github() -> Dict[str, Any]:
    global _github_file_sha
    owner, repo = _parse_github_repo()
    url = (
        f"https://api.github.com/repos/{owner}/{repo}/contents/"
        f"{quote(GITHUB_DATA_PATH)}?ref={quote(GITHUB_BRANCH)}"
    )
    try:
        payload = _pedido_http("GET", url, cabecalhos=_github_headers())
    except urlerror.HTTPError as erro:
        if erro.code == 404:
            _github_file_sha = None
            return estado_inicial()
        raise

    if not isinstance(payload, dict):
        return estado_inicial()

    _github_file_sha = payload.get("sha")
    conteudo_b64 = str(payload.get("content", "")).replace("\n", "")
    if not conteudo_b64:
        return estado_inicial()

    bruto = json.loads(base64.b64decode(conteudo_b64).decode("utf-8"))
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_github() -> None:
    global _github_file_sha
    owner, repo = _parse_github_repo()
    url = f"https://api.github.com/repos/{owner}/{repo}/contents/{quote(GITHUB_DATA_PATH)}"
    conteudo = json.dumps(dados, ensure_ascii=False, indent=2)
    corpo: Dict[str, Any] = {
        "message": f"chore(bot): atualizar {GITHUB_DATA_PATH}",
        "content": base64.b64encode(conteudo.encode("utf-8")).decode("ascii"),
        "branch": GITHUB_BRANCH,
    }
    if _github_file_sha:
        corpo["sha"] = _github_file_sha

    payload = _pedido_http("PUT", url, corpo=corpo, cabecalhos=_github_headers())
    if isinstance(payload, dict) and isinstance(payload.get("content"), dict):
        _github_file_sha = payload["content"].get("sha", _github_file_sha)


def _pedido_http(
    metodo: str,
    url: str,
    corpo: Optional[Dict[str, Any]] = None,
    cabecalhos: Optional[Dict[str, str]] = None,
    timeout: int = 20,
) -> Any:
    cabecalhos = cabecalhos or {}
    dados_bytes = None
    if corpo is not None:
        dados_bytes = json.dumps(corpo).encode("utf-8")
        cabecalhos.setdefault("Content-Type", "application/json")

    pedido = urlrequest.Request(url, data=dados_bytes, headers=cabecalhos, method=metodo)
    with urlrequest.urlopen(pedido, timeout=timeout) as resposta:
        texto = resposta.read().decode("utf-8")
        if not texto.strip():
            return None
        return json.loads(texto)


def carregar_supabase() -> Dict[str, Any]:
    url = f"{SUPABASE_URL}/rest/v1/bot_state?id=eq.1&select=data"
    cabecalhos = {
        "apikey": SUPABASE_KEY,
        "Authorization": f"Bearer {SUPABASE_KEY}",
    }
    payload = _pedido_http("GET", url, cabecalhos=cabecalhos)
    if not payload:
        return estado_inicial()
    if isinstance(payload, list) and payload:
        bruto = payload[0].get("data", {})
    elif isinstance(payload, dict):
        bruto = payload.get("data", payload)
    else:
        return estado_inicial()
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_supabase() -> None:
    url = f"{SUPABASE_URL}/rest/v1/bot_state?id=eq.1"
    cabecalhos = {
        "apikey": SUPABASE_KEY,
        "Authorization": f"Bearer {SUPABASE_KEY}",
        "Prefer": "return=minimal",
    }
    try:
        _pedido_http("PATCH", url, corpo={"data": dados}, cabecalhos=cabecalhos)
    except urlerror.HTTPError as erro:
        if erro.code != 404:
            raise
        criar_url = f"{SUPABASE_URL}/rest/v1/bot_state"
        cabecalhos["Prefer"] = "resolution=merge-duplicates"
        _pedido_http("POST", criar_url, corpo={"id": 1, "data": dados}, cabecalhos=cabecalhos)


def carregar_jsonbin() -> Dict[str, Any]:
    url = f"https://api.jsonbin.io/v3/b/{JSONBIN_BIN_ID}/latest"
    cabecalhos = {"X-Master-Key": JSONBIN_API_KEY}
    payload = _pedido_http("GET", url, cabecalhos=cabecalhos)
    if not isinstance(payload, dict):
        return estado_inicial()
    bruto = payload.get("record", payload)
    if not isinstance(bruto, dict):
        return estado_inicial()
    return aplicar_dados_carregados(bruto)


def guardar_jsonbin() -> None:
    url = f"https://api.jsonbin.io/v3/b/{JSONBIN_BIN_ID}"
    cabecalhos = {
        "X-Master-Key": JSONBIN_API_KEY,
        "Content-Type": "application/json",
    }
    _pedido_http("PUT", url, corpo=dados, cabecalhos=cabecalhos)


def carregar_url() -> Dict[str, Any]:
    cabecalhos = {}
    if BOT_DATA_TOKEN:
        cabecalhos["Authorization"] = f"Bearer {BOT_DATA_TOKEN}"
    payload = _pedido_http("GET", BOT_DATA_URL, cabecalhos=cabecalhos)
    if not isinstance(payload, dict):
        return estado_inicial()
    return aplicar_dados_carregados(payload)


def guardar_url() -> None:
    cabecalhos = {}
    if BOT_DATA_TOKEN:
        cabecalhos["Authorization"] = f"Bearer {BOT_DATA_TOKEN}"
    _pedido_http("PUT", BOT_DATA_SAVE_URL, corpo=dados, cabecalhos=cabecalhos)


def _guardar_local() -> None:
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    temp = DATA_FILE.with_suffix(".tmp.json")
    conteudo = json.dumps(dados, ensure_ascii=False, indent=2)
    temp.write_text(conteudo, encoding="utf-8")
    if DATA_FILE.exists():
        shutil.copy2(DATA_FILE, BACKUP_FILE)
    temp.replace(DATA_FILE)


def carregar_dados() -> Dict[str, Any]:
    modo = modo_armazenamento()

    if modo == "github":
        try:
            estado = carregar_github()
            print(f"🐙 Dados carregados do GitHub: {GITHUB_REPO}/{GITHUB_DATA_PATH}")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha GitHub, a tentar local: {erro}")
    elif modo == "supabase":
        try:
            estado = carregar_supabase()
            print("☁️ Dados carregados do Supabase.")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha Supabase, a tentar local: {erro}")
    elif modo == "jsonbin":
        try:
            estado = carregar_jsonbin()
            print("☁️ Dados carregados do JSONBin.")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha JSONBin, a tentar local: {erro}")
    elif modo == "url":
        try:
            estado = carregar_url()
            print(f"☁️ Dados carregados de: {BOT_DATA_URL}")
            return estado
        except (OSError, urlerror.URLError, urlerror.HTTPError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha URL remota, a tentar local: {erro}")

    for ficheiro in (DATA_FILE, BACKUP_FILE):
        if not ficheiro.exists():
            continue
        try:
            estado = _ler_ficheiro_dados(ficheiro)
            print(f"📂 Dados carregados de: {ficheiro}")
            return estado
        except (OSError, json.JSONDecodeError, ValueError, TypeError) as erro:
            print(f"⚠️ Falha ao ler {ficheiro}: {erro}")

    if em_nuvem() and modo == "local":
        print(
            "⚠️ ATENÇÃO: Bot na nuvem sem armazenamento remoto. "
            "A TBR perde-se a cada reinício/deploy. Configura GitHub, Supabase ou JSONBin."
        )
    else:
        print(f"📂 Ficheiro novo — a criar em: {DATA_FILE}")
    return estado_inicial()


def guardar_dados() -> None:
    global _ultimo_snapshot
    with _dados_lock:
        snapshot = _snapshot_dados()
        if snapshot == _ultimo_snapshot:
            return

        modo = modo_armazenamento()
        erro_remoto = None

        if modo == "github":
            try:
                guardar_github()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "supabase":
            try:
                guardar_supabase()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "jsonbin":
            try:
                guardar_jsonbin()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro
        elif modo == "url":
            try:
                guardar_url()
            except (OSError, urlerror.URLError, urlerror.HTTPError) as erro:
                erro_remoto = erro

        if modo == "local" or not erro_remoto:
            try:
                _guardar_local()
            except OSError as erro:
                if modo == "local":
                    raise
                print(f"⚠️ Cache local indisponível: {erro}")

        if erro_remoto:
            raise RuntimeError(f"Falha ao guardar no remoto ({modo}): {erro_remoto}") from erro_remoto

        _ultimo_snapshot = snapshot


def resumo_persistencia() -> str:
    total_tbr = sum(len(v) for v in dados.get("tbr_por_mes", {}).values())
    modo = modo_armazenamento()
    linhas = [f"Modo: **{modo}**", f"TBR: **{total_tbr}** livros | Lidos: **{len(dados.get('livros_lidos', []))}**"]

    if modo == "github":
        linhas.append(f"Repositório: `{GITHUB_REPO}` · ficheiro `{GITHUB_DATA_PATH}` · branch `{GITHUB_BRANCH}`")
    elif modo == "local":
        linhas.append(f"Ficheiro local: `{DATA_FILE}`")
        if em_nuvem():
            linhas.append(
                "⚠️ **Bot na nuvem com disco temporário** — os dados apagam-se ao reiniciar. "
                "Configura **GitHub** (usa `!armazenamento`)."
            )
    elif modo == "supabase":
        linhas.append(f"Remoto: `{SUPABASE_URL}` (tabela `bot_state`)")
    elif modo == "jsonbin":
        linhas.append(f"Remoto: JSONBin `{JSONBIN_BIN_ID}`")
    elif modo == "url":
        linhas.append(f"Remoto: `{BOT_DATA_URL}`")

    return "\n".join(linhas)


# ==============================================================================
# HELPERS
# ==============================================================================

def migrar_livros_lidos(livros: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    resultado = []
    for livro in livros:
        if not isinstance(livro, dict):
            continue
        copia = dict(livro)
        titulo = str(copia.get("titulo", "")).strip()
        if SEPARADOR_LIVRO not in titulo and copia.get("autor"):
            copia["titulo"] = formatar_livro(titulo, str(copia["autor"]))
        if "nota" not in copia and copia.get("estrelas") not in (None, "Sem avaliação"):
            copia["nota"] = estrelas_para_nota(str(copia.get("estrelas", "")))
        if "data_leitura" not in copia:
            copia["data_leitura"] = copia.get("data_leitura", "")
        resultado.append(copia)
    return resultado


def formatar_livro(titulo: str, autor: str) -> str:
    titulo = titulo.strip()
    autor = autor.strip()
    if SEPARADOR_LIVRO in titulo:
        return titulo
    if not autor:
        raise ValueError("autor_obrigatorio")
    return f"{titulo}{SEPARADOR_LIVRO}{autor}"


def parsear_livro(texto: str) -> Tuple[str, str]:
    texto = texto.strip()
    if SEPARADOR_LIVRO not in texto:
        raise ValueError("autor_obrigatorio")
    titulo, autor = texto.rsplit(SEPARADOR_LIVRO, 1)
    titulo, autor = titulo.strip(), autor.strip()
    if not titulo or not autor:
        raise ValueError("autor_obrigatorio")
    return titulo, autor


def livro_completo(texto: str) -> str:
    if SEPARADOR_LIVRO in texto:
        return texto.strip()
    raise ValueError("autor_obrigatorio")


def estrelas_para_texto(nota: float) -> str:
    if nota <= 0:
        return "Sem avaliação"
    cheias = int(nota)
    resto = round(nota - cheias, 2)
    texto = "⭐" * cheias
    if resto == 0.25:
        texto += "¼"
    elif resto == 0.5:
        texto += "½"
    elif resto == 0.75:
        texto += "¾"
    elif resto > 0:
        texto += f" ({nota})"
    return texto or f"{nota}⭐"


def estrelas_para_nota(estrelas: str) -> float:
    if not estrelas or estrelas == "Sem avaliação":
        return 0.0
    nota = estrelas.count("⭐")
    if "¼" in estrelas:
        nota += 0.25
    elif "½" in estrelas:
        nota += 0.5
    elif "¾" in estrelas:
        nota += 0.75
    return float(nota)


def nota_valida(nota: float) -> bool:
    return nota in NOTAS_DISPONIVEIS


def livro_ja_lido(titulo_completo: str) -> bool:
    alvo = titulo_completo.lower().strip()
    return any(l.get("titulo", "").lower().strip() == alvo for l in dados["livros_lidos"])


def nota_do_livro(livro: Dict[str, Any]) -> float:
    nota = livro.get("nota")
    if isinstance(nota, (int, float)) and nota > 0:
        return float(nota)
    return estrelas_para_nota(str(livro.get("estrelas", "")))


def livros_bem_avaliados(minimo: float = 4.0) -> List[Dict[str, Any]]:
    resultado = []
    for livro in dados["livros_lidos"]:
        titulo = str(livro.get("titulo", "")).strip()
        if not titulo:
            continue
        nota = nota_do_livro(livro)
        if nota >= minimo:
            resultado.append({**livro, "nota": nota})
    return resultado


def sorteio_mes_ativo(mes: str) -> Optional[Dict[str, Any]]:
    info = dados["sorteios_mes"].get(mes)
    if not info:
        return None
    livros = info.get("livros", [])
    lidos = {l.lower().strip() for l in info.get("lidos", [])}
    pendentes = [l for l in livros if l.lower().strip() not in lidos]
    if pendentes:
        info["pendentes"] = pendentes
        return info
    return None


def marcar_livro_sorteio_lido(titulo_completo: str) -> List[str]:
    meses_desbloqueados = []
    alvo = titulo_completo.lower().strip()
    for mes, info in dados["sorteios_mes"].items():
        livros = [l.lower().strip() for l in info.get("livros", [])]
        if alvo in livros:
            lidos = info.setdefault("lidos", [])
            if titulo_completo not in lidos and alvo not in {x.lower().strip() for x in lidos}:
                for livro in info.get("livros", []):
                    if livro.lower().strip() == alvo:
                        lidos.append(livro)
                        break
            pendentes = [l for l in info.get("livros", []) if l.lower().strip() not in {x.lower().strip() for x in lidos}]
            if not pendentes:
                meses_desbloqueados.append(mes)
    return meses_desbloqueados


async def obter_canal_discord(canal_id: int) -> Optional[discord.abc.Messageable]:
    canal = bot.get_channel(canal_id)
    if canal:
        return canal
    try:
        return await bot.fetch_channel(canal_id)
    except (discord.NotFound, discord.HTTPException):
        return None


async def pesquisar_open_library(query: str) -> Optional[Dict[str, Any]]:
    url = f"https://openlibrary.org/search.json?q={quote(query)}&limit=1"
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=12)) as resp:
                if resp.status != 200:
                    return None
                payload = await resp.json()
    except (aiohttp.ClientError, asyncio.TimeoutError, json.JSONDecodeError):
        return None

    docs = payload.get("docs", [])
    if not docs:
        return None

    doc = docs[0]
    autores = doc.get("author_name", [])
    return {
        "titulo": doc.get("title", query),
        "autor": autores[0] if autores else "Desconhecido",
        "genero": ", ".join(doc.get("subject", [])[:3]) or "N/D",
        "paginas": doc.get("number_of_pages_median") or doc.get("number_of_pages", 0),
        "ano": doc.get("first_publish_year", "N/D"),
        "capa": f"https://covers.openlibrary.org/b/id/{doc['cover_i']}-L.jpg" if doc.get("cover_i") else "",
        "fonte": "Open Library",
    }


async def pesquisar_readmore(query: str) -> Optional[Dict[str, Any]]:
    if not READMORE_API_URL:
        return None
    endpoints = [
        f"{READMORE_API_URL.rstrip('/')}/books/search?q={quote(query)}",
        f"{READMORE_API_URL.rstrip('/')}/api/books/search?q={quote(query)}",
    ]
    try:
        async with aiohttp.ClientSession() as session:
            for url in endpoints:
                try:
                    async with session.get(url, timeout=aiohttp.ClientTimeout(total=8)) as resp:
                        if resp.status != 200:
                            continue
                        payload = await resp.json()
                except (aiohttp.ClientError, asyncio.TimeoutError):
                    continue

                livros = payload if isinstance(payload, list) else payload.get("results", payload.get("books", []))
                if not livros:
                    continue
                livro = livros[0]
                return {
                    "titulo": livro.get("title", livro.get("titulo", query)),
                    "autor": livro.get("author", livro.get("autor", "Desconhecido")),
                    "genero": livro.get("genre", livro.get("genero", "N/D")),
                    "paginas": livro.get("pages", livro.get("paginas", 0)),
                    "ano": livro.get("year", livro.get("ano", "N/D")),
                    "capa": livro.get("cover", livro.get("capa", "")),
                    "fonte": "ReadMore",
                }
    except Exception:
        return None
    return None


async def obter_info_livro(query: str) -> Dict[str, Any]:
    readmore = await pesquisar_readmore(query)
    if readmore:
        return readmore
    open_lib = await pesquisar_open_library(query)
    if open_lib:
        return open_lib
    return {
        "titulo": query,
        "autor": "Desconhecido",
        "genero": "N/D",
        "paginas": 0,
        "ano": "N/D",
        "capa": "",
        "fonte": "IA",
    }


def normalizar_categoria(categoria: str) -> str:
    categoria = categoria.strip().capitalize()
    return categoria


def livros_tbr_flat() -> List[str]:
    return [livro for lista in dados["tbr_por_mes"].values() for livro in lista]


def buscar_livro_case_insensitive(lista: List[str], alvo: str) -> Optional[str]:
    alvo_lower = alvo.lower().strip()
    for item in lista:
        if item.lower().strip() == alvo_lower:
            return item
    return None


def adicionar_livro_a_tbr_mes(livro: str, mes: str) -> str:
    existente_no_mes = buscar_livro_case_insensitive(dados["tbr_por_mes"][mes], livro)
    if existente_no_mes:
        return f"📌 **{existente_no_mes}** já estava na TBR de **{mes}**."

    removido_de = []
    titulo_a_guardar = livro

    for categoria, lista in dados["tbr_por_mes"].items():
        if categoria == mes:
            continue

        existente = buscar_livro_case_insensitive(lista, livro)
        if existente:
            lista.remove(existente)
            removido_de.append(categoria)
            titulo_a_guardar = existente

    dados["tbr_por_mes"][mes].append(titulo_a_guardar)

    if removido_de:
        return (
            f"📚 **{titulo_a_guardar}** foi movido da TBR de "
            f"**{', '.join(removido_de)}** para **{mes}**."
        )

    return f"📚 **{titulo_a_guardar}** foi adicionado automaticamente à TBR de **{mes}**."


def canal_nome_seguro(base: str) -> str:
    texto = unicodedata.normalize("NFKD", base.lower().strip())
    texto = "".join(ch for ch in texto if not unicodedata.combining(ch))
    texto = re.sub(r"\s+", "-", texto)
    return "".join(ch for ch in texto if ch.isalnum() or ch == "-")


def hoje_str() -> str:
    return datetime.now().strftime("%d/%m/%Y")


def este_ano() -> str:
    return datetime.now().strftime("%Y")


def extrair_texto_gemini(response: Any) -> str:
    texto = getattr(response, "text", None)
    if texto:
        return texto.strip()
    return ""


def gemini_text(prompt: str) -> str:
    response = ai_client.models.generate_content(
        model=GEMINI_MODEL,
        contents=prompt
    )
    return extrair_texto_gemini(response)


def gemini_json(prompt: str) -> Dict[str, Any]:
    response = ai_client.models.generate_content(
        model=GEMINI_MODEL,
        contents=prompt,
        config={"response_mime_type": "application/json"}
    )
    texto = extrair_texto_gemini(response)
    texto = re.sub(r"^```(?:json)?\s*|\s*```$", "", texto.strip(), flags=re.IGNORECASE)
    if "{" in texto and "}" in texto:
        texto = texto[texto.find("{"):texto.rfind("}") + 1]
    return json.loads(texto)


async def enviar_mensagem_longa(canal: discord.abc.Messageable, texto: str, limite: int = 1900) -> None:
    partes = []
    bloco_atual = ""

    for linha in texto.splitlines():
        if len(bloco_atual) + len(linha) + 1 > limite:
            partes.append(bloco_atual)
            bloco_atual = linha
        else:
            bloco_atual = f"{bloco_atual}\n{linha}" if bloco_atual else linha

    if bloco_atual:
        partes.append(bloco_atual)

    for parte in partes:
        await canal.send(parte)


def data_valida(data_texto: str) -> bool:
    try:
        datetime.strptime(data_texto, "%d/%m/%Y")
        return True
    except (TypeError, ValueError):
        return False


def numero_mes(mes: str) -> int:
    return MESES_ORDEM.index(normalizar_categoria(mes)) + 1


def carregar_fonte(tamanho: int, negrito: bool = False):
    if ImageFont is None:
        return None

    nomes = ["arialbd.ttf", "segoeuib.ttf"] if negrito else ["arial.ttf", "segoeui.ttf"]
    for nome in nomes:
        try:
            return ImageFont.truetype(nome, tamanho)
        except OSError:
            continue
    return ImageFont.load_default()


def desenhar_calendario_leituras(mes: str, ano: int) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    mes_num = numero_mes(mes)
    metas_por_dia: Dict[int, List[str]] = {}

    for lembrete in dados["lembretes_metas"]:
        try:
            data = datetime.strptime(lembrete.get("data", ""), "%d/%m/%Y")
        except (TypeError, ValueError):
            continue

        if data.month == mes_num and data.year == ano:
            texto = f"{lembrete.get('livro', 'Livro')}: {lembrete.get('meta', '')}".strip()
            metas_por_dia.setdefault(data.day, []).append(texto)

    largura, altura = 1400, 1000
    margem = 60
    topo = 150
    largura_celula = (largura - margem * 2) // 7
    altura_celula = 115

    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)

    fonte_titulo = carregar_fonte(46, negrito=True)
    fonte_dia_semana = carregar_fonte(24, negrito=True)
    fonte_numero = carregar_fonte(24, negrito=True)
    fonte_meta = carregar_fonte(17)
    fonte_rodape = carregar_fonte(18)

    titulo = f"Leituras conjuntas - {normalizar_categoria(mes)} {ano}"
    draw.text((margem, 45), titulo, fill="#3b2f2f", font=fonte_titulo)
    draw.text((margem, 105), "Metas guardadas pelo comando !meta", fill="#7b5d4a", font=fonte_rodape)

    dias_semana = ["Seg", "Ter", "Qua", "Qui", "Sex", "Sáb", "Dom"]
    for idx, dia in enumerate(dias_semana):
        x = margem + idx * largura_celula
        draw.rounded_rectangle(
            (x, topo, x + largura_celula - 8, topo + 42),
            radius=8,
            fill="#583d72"
        )
        draw.text((x + 18, topo + 9), dia, fill="#ffffff", font=fonte_dia_semana)

    semanas = calendar.monthcalendar(ano, mes_num)
    y_inicio = topo + 55

    for linha, semana in enumerate(semanas):
        for coluna, dia in enumerate(semana):
            x1 = margem + coluna * largura_celula
            y1 = y_inicio + linha * altura_celula
            x2 = x1 + largura_celula - 8
            y2 = y1 + altura_celula - 8
            fill = "#ffffff" if dia else "#f3e7dc"
            draw.rounded_rectangle((x1, y1, x2, y2), radius=10, fill=fill, outline="#d7c4b5", width=2)

            if not dia:
                continue

            draw.text((x1 + 12, y1 + 10), str(dia), fill="#3b2f2f", font=fonte_numero)

            metas = metas_por_dia.get(dia, [])
            texto_y = y1 + 42
            for meta in metas[:2]:
                for linha_meta in textwrap.wrap(meta, width=24)[:3]:
                    draw.text((x1 + 12, texto_y), linha_meta, fill="#315f58", font=fonte_meta)
                    texto_y += 20
            if len(metas) > 2:
                draw.text((x1 + 12, y2 - 24), f"+{len(metas) - 2} meta(s)", fill="#8a4f2d", font=fonte_meta)

    if not metas_por_dia:
        draw.text(
            (margem, altura - 85),
            "Ainda não há metas de leitura conjunta guardadas para este mês.",
            fill="#8a4f2d",
            font=fonte_rodape
        )

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def desenhar_grafico_barras(
    titulo: str,
    etiquetas: List[str],
    valores: List[int],
    cor: str = "#583d72",
    largura: int = 1200,
    altura: int = 700,
) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)
    fonte_titulo = carregar_fonte(36, negrito=True)
    fonte_label = carregar_fonte(20)
    fonte_valor = carregar_fonte(18, negrito=True)

    draw.text((50, 30), titulo, fill="#3b2f2f", font=fonte_titulo)

    if not valores or max(valores, default=0) == 0:
        draw.text((50, 120), "Sem dados suficientes para este período.", fill="#8a4f2d", font=fonte_label)
    else:
        max_valor = max(valores)
        base_y = altura - 80
        area_largura = largura - 140
        barra_largura = max(40, area_largura // max(len(valores), 1) - 20)
        inicio_x = 70

        for idx, (etiqueta, valor) in enumerate(zip(etiquetas, valores)):
            x = inicio_x + idx * (barra_largura + 20)
            altura_barra = int((valor / max_valor) * (altura - 220)) if max_valor else 0
            y_top = base_y - altura_barra
            draw.rounded_rectangle((x, y_top, x + barra_largura, base_y), radius=8, fill=cor)
            draw.text((x, base_y + 10), etiqueta[:14], fill="#3b2f2f", font=fonte_label)
            draw.text((x, y_top - 28), str(valor), fill="#315f58", font=fonte_valor)

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def desenhar_resumo_anual(ano: int, stats: Dict[str, Any]) -> io.BytesIO:
    if Image is None or ImageDraw is None:
        raise RuntimeError("A biblioteca Pillow não está instalada.")

    largura, altura = 1400, 1000
    imagem = Image.new("RGB", (largura, altura), "#fff8f1")
    draw = ImageDraw.Draw(imagem)
    fonte_titulo = carregar_fonte(44, negrito=True)
    fonte_sec = carregar_fonte(28, negrito=True)
    fonte_txt = carregar_fonte(22)

    draw.text((60, 40), f"Resumo de Leituras {ano}", fill="#3b2f2f", font=fonte_titulo)
    draw.text((60, 110), f"Total de livros: {stats.get('total_livros', 0)}", fill="#583d72", font=fonte_sec)
    draw.text((60, 160), f"Páginas lidas: {stats.get('total_paginas', 0)}", fill="#315f58", font=fonte_sec)

    autor_top = stats.get("autor_top", ("N/D", 0))
    genero_top = stats.get("genero_top", ("N/D", 0))
    draw.text((60, 240), "Autor mais lido", fill="#8a4f2d", font=fonte_sec)
    draw.text((60, 285), f"{autor_top[0]} ({autor_top[1]} livros)", fill="#3b2f2f", font=fonte_txt)

    draw.text((60, 360), "Género dominante", fill="#8a4f2d", font=fonte_sec)
    draw.text((60, 405), f"{genero_top[0]} ({genero_top[1]} livros)", fill="#3b2f2f", font=fonte_txt)

    y = 500
    draw.text((60, y), "Top autores", fill="#8a4f2d", font=fonte_sec)
    y += 45
    for autor, qtd in stats.get("top_autores", [])[:5]:
        draw.text((80, y), f"• {autor}: {qtd}", fill="#3b2f2f", font=fonte_txt)
        y += 34

    y = 500
    draw.text((720, y), "Top géneros", fill="#8a4f2d", font=fonte_sec)
    y += 45
    for genero, qtd in stats.get("top_generos", [])[:5]:
        draw.text((740, y), f"• {genero}: {qtd}", fill="#3b2f2f", font=fonte_txt)
        y += 34

    buffer = io.BytesIO()
    imagem.save(buffer, format="PNG")
    buffer.seek(0)
    return buffer


def estatisticas_mes(mes: str, ano: int) -> Dict[str, Any]:
    mes_num = numero_mes(mes)
    livros_mes = []
    for livro in dados["livros_lidos"]:
        data_txt = livro.get("data_leitura", "")
        try:
            data = datetime.strptime(data_txt, "%d/%m/%Y")
        except (TypeError, ValueError):
            continue
        if data.month == mes_num and data.year == ano:
            livros_mes.append(livro)

    paginas = sum(int(l.get("paginas", 0) or 0) for l in livros_mes)
    autores = [parsear_livro(l["titulo"])[1] for l in livros_mes if SEPARADOR_LIVRO in l.get("titulo", "")]
    generos = [l.get("genero", "N/D") for l in livros_mes if l.get("genero")]

    return {
        "livros": livros_mes,
        "total_livros": len(livros_mes),
        "paginas": paginas,
        "autores_unicos": len(set(autores)),
        "generos_unicos": len(set(generos)),
        "contagem_autores": Counter(autores).most_common(5),
        "contagem_generos": Counter(generos).most_common(5),
    }


def estatisticas_ano(ano: int) -> Dict[str, Any]:
    livros_ano = []
    for livro in dados["livros_lidos"]:
        data_txt = livro.get("data_leitura", "")
        try:
            data = datetime.strptime(data_txt, "%d/%m/%Y")
        except (TypeError, ValueError):
            if str(ano) in data_txt:
                livros_ano.append(livro)
            continue
        if data.year == ano:
            livros_ano.append(livro)

    autores = []
    generos = []
    paginas = 0
    for livro in livros_ano:
        paginas += int(livro.get("paginas", 0) or 0)
        if SEPARADOR_LIVRO in livro.get("titulo", ""):
            autores.append(parsear_livro(livro["titulo"])[1])
        if livro.get("genero"):
            generos.append(livro["genero"])

    contagem_autores = Counter(autores)
    contagem_generos = Counter(generos)
    autor_top = contagem_autores.most_common(1)[0] if contagem_autores else ("N/D", 0)
    genero_top = contagem_generos.most_common(1)[0] if contagem_generos else ("N/D", 0)

    return {
        "total_livros": len(livros_ano),
        "total_paginas": paginas,
        "autor_top": autor_top,
        "genero_top": genero_top,
        "top_autores": contagem_autores.most_common(5),
        "top_generos": contagem_generos.most_common(5),
    }


async def garantir_canal(guild: discord.Guild, nome: str) -> discord.TextChannel:
    canal = discord.utils.get(guild.text_channels, name=nome)
    if canal:
        return canal
    return await guild.create_text_channel(nome)


# ==============================================================================
# DESAFIO A-Z CORRIGIDO
# ==============================================================================

ARTIGOS_BANIDOS = {
    # Português Europeu
    "o", "a", "os", "as", "um", "uma", "uns", "umas",
    # Inglês
    "the", "a", "an"
}


def analisar_titulo_alfabeto(titulo: str):
    """
    Analisa o título para o desafio A-Z.
    Remove artigos definidos (pt-PT ou inglês) e pega na primeira letra da primeira palavra significativa.
    """
    titulo_limpo = titulo.strip()
    
    if not titulo_limpo:
        return {"status": "INVALIDO", "letra": None}
    
    # Separar por espaços e pontuação comum
    palavras = re.split(r'[\s\-–—]+', titulo_limpo)
    
    # Encontrar a primeira palavra que não é artigo
    primeira_palavra = None
    for palavra in palavras:
        palavra_limpa = palavra.lower().strip('.,!?;:\'"()[]{}')
        if palavra_limpa and palavra_limpa not in ARTIGOS_BANIDOS:
            primeira_palavra = palavra
            break
    
    if not primeira_palavra:
        # Se todas as palavras são artigos, tenta a primeira não vazia
        for palavra in palavras:
            if palavra.strip('.,!?;:\'"()[]{}'):
                primeira_palavra = palavra
                break
    
    if not primeira_palavra:
        return {"status": "INVALIDO", "letra": None}
    
    # Encontrar a primeira letra da primeira palavra
    for ch in primeira_palavra:
        if ch.isalpha():
            return {"status": "OK", "letra": ch.upper()}
    
    return {"status": "INVALIDO", "letra": None}


dados = carregar_dados()
_ultimo_snapshot = _snapshot_dados()
if modo_armazenamento() == "local" and not DATA_FILE.exists():
    guardar_dados()


def _guardar_ao_sair() -> None:
    try:
        guardar_dados()
        print(f"💾 Dados guardados ({modo_armazenamento()}).")
    except OSError as erro:
        print(f"⚠️ Erro ao guardar ao sair: {erro}")


atexit.register(_guardar_ao_sair)


# ==============================================================================
# BOT
# ==============================================================================

intents = discord.Intents.default()
intents.message_content = True


class LeituraBot(commands.Bot):
    async def setup_hook(self) -> None:
        self.add_view(ViewSugestoes([], []))
        self.add_view(ViewMarcarSugestoes([]))

    async def close(self) -> None:
        guardar_dados()
        await super().close()


bot = LeituraBot(command_prefix=COMMAND_PREFIX, intents=intents)


@tasks.loop(minutes=2)
async def autosave_loop():
    guardar_dados()


@autosave_loop.before_loop
async def antes_autosave():
    await bot.wait_until_ready()


@bot.event
async def on_ready():
    print(f"👑 {bot.user} está online.")
    print(f"💾 {resumo_persistencia().replace('**', '')}")
    if not verificar_lembretes_loop.is_running():
        verificar_lembretes_loop.start()
    if not resumos_automaticos_loop.is_running():
        resumos_automaticos_loop.start()
    if not autosave_loop.is_running():
        autosave_loop.start()
    await enviar_lembretes_pendentes_hoje()


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot:
        return

    user_id = str(message.author.id)
    if user_id in dados["review_em_andamento"]:
        if not message.content.startswith(COMMAND_PREFIX):
            review = dados["review_em_andamento"][user_id]
            texto = message.content.strip()
            if texto:
                review.setdefault("desabafos", []).append(texto)
            for anexo in message.attachments:
                if anexo.content_type and anexo.content_type.startswith("image/"):
                    review.setdefault("anexos", []).append(anexo.url)
                    review.setdefault("desabafos", []).append(f"[Print de mensagem: {anexo.url}]")
                else:
                    review.setdefault("desabafos", []).append(f"[Anexo: {anexo.url}]")
            guardar_dados()
            await message.add_reaction("📝")

    await bot.process_commands(message)


@bot.event
async def on_command_error(ctx: commands.Context, error: commands.CommandError):
    if isinstance(error, commands.MissingRequiredArgument):
        exemplos = {
            "addtbr": '`!addtbr "Título - Autor"` ou `!addtbr Junho "Título - Autor"`',
            "remtbr": "`!remtbr Geral Nome do Livro`",
            "tbr": "`!tbr Junho` ou `!tbr Junho 3`",
            "meta": '`!meta Junho "Nome do Livro" dia 7 até cap. 10, dia 14 até cap. 22`',
            "lido": "`!lido Nome do Livro`",
            "remalfabeto": "`!remalfabeto A`",
            "avaliar": "`!avaliar 3.5` (aceita 0.25 em 0.25 até 5)",
            "reavaliar": '`!reavaliar "Título - Autor" 4.5`',
            "editarautor": '`!editarautor "Título - Autor Antigo" "Autor Correto"`',
            "editmeta": '`!editmeta "Título - Autor" dia 7 até cap. 10`',
            "livroinfo": "`!livroinfo Título - Autor`",
            "resumomes": "`!resumomes Junho`",
            "resumoano": "`!resumoano 2026`",
            "remlido": "`!remlido Nome do Livro`",
            "review": "`!review Nome do Livro`",
            "entrevista": "`!entrevista Personagem pergunta`",
            "ressaca": "`!ressaca Nome do Livro`",
            "teoria": "`!teoria a tua teoria aqui`",
            "vibe": "`!vibe Nome do Livro`",
            "sprint": "`!sprint 25`",
        }
        nome_comando = ctx.command.name if ctx.command else ""
        exemplo = exemplos.get(nome_comando, f"`{COMMAND_PREFIX}guia`")
        await ctx.send(f"❌ Falta informação no comando.\nExemplo: {exemplo}")
        return

    if isinstance(error, commands.BadArgument):
        await ctx.send("❌ Um dos valores não está no formato certo. Usa `!guia` para ver exemplos.")
        return

    raise error


# ==============================================================================
# VIEWS E BOTÕES
# ==============================================================================

class BotaoSugestao(discord.ui.Button):
    def __init__(self, titulo_livro: str):
        super().__init__(
            label=f"➕ TBR: {titulo_livro[:55]}",
            style=discord.ButtonStyle.primary,
            custom_id=f"tbr_add::{titulo_livro[:80]}",
        )
        self.titulo_livro = titulo_livro

    async def callback(self, interaction: discord.Interaction):
        tudo_na_tbr = [l.lower() for l in livros_tbr_flat()]
        if self.titulo_livro.lower() in tudo_na_tbr:
            await interaction.response.send_message(
                f"🤔 *{self.titulo_livro}* já está na tua TBR.",
                ephemeral=True
            )
            return

        dados["tbr_por_mes"]["Geral"].append(self.titulo_livro)
        guardar_dados()

        self.disabled = True
        self.style = discord.ButtonStyle.success
        self.label = "✅ Adicionado"

        await interaction.response.edit_message(view=self.view)
        await interaction.followup.send(
            f"📦 **{self.titulo_livro}** foi adicionado à lista **Geral**.",
            ephemeral=True
        )


class BotaoMarcarSugestoes(discord.ui.Button):
    def __init__(self, titulos: List[str]):
        super().__init__(
            label="✅ Já vi estas sugestões",
            style=discord.ButtonStyle.secondary,
            custom_id=f"sugestoes_vistas::{hash(tuple(titulos)) & 0xFFFFFFFF}",
        )
        self.titulos = titulos

    async def callback(self, interaction: discord.Interaction):
        vistos = {v.lower().strip() for v in dados.setdefault("sugestoes_vistas", [])}
        novos = 0
        for titulo in self.titulos:
            chave = titulo.lower().strip()
            if chave not in vistos:
                dados["sugestoes_vistas"].append(titulo)
                vistos.add(chave)
                novos += 1
        guardar_dados()

        self.disabled = True
        self.label = "✅ Sugestões arquivadas"
        await interaction.response.edit_message(view=self.view)
        await interaction.followup.send(
            f"📚 Arquivou **{novos}** sugestão(ões). Não voltarão a ser recomendadas.",
            ephemeral=True,
        )


class ViewMarcarSugestoes(discord.ui.View):
    def __init__(self, titulos: List[str]):
        super().__init__(timeout=None)
        if titulos:
            self.add_item(BotaoMarcarSugestoes(titulos))


class ViewSugestoes(discord.ui.View):
    def __init__(self, livros_sugeridos: List[str], titulos_arquivo: Optional[List[str]] = None):
        super().__init__(timeout=None)
        for livro in livros_sugeridos:
            self.add_item(BotaoSugestao(livro))
        if titulos_arquivo:
            self.add_item(BotaoMarcarSugestoes(titulos_arquivo))


class SelectAvaliacao(discord.ui.Select):
    def __init__(self, titulo_livro: str, autor_id: int):
        opcoes = [
            discord.SelectOption(label=f"{nota:g} estrelas", value=str(nota), emoji="⭐")
            for nota in NOTAS_DISPONIVEIS
        ]
        super().__init__(
            placeholder="Escolhe a avaliação (0.25 a 5)",
            min_values=1,
            max_values=1,
            options=opcoes,
            custom_id=f"avaliar::{titulo_livro[:60]}::{autor_id}",
        )
        self.titulo_livro = titulo_livro
        self.autor_id = autor_id

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.autor_id:
            await interaction.response.send_message(
                "❌ Só quem registou este livro pode avaliá-lo por aqui.",
                ephemeral=True,
            )
            return

        nota = float(self.values[0])
        livro_encontrado = None
        for livro in dados["livros_lidos"]:
            if livro.get("titulo", "").lower().strip() == self.titulo_livro.lower().strip():
                livro_encontrado = livro
                break

        if not livro_encontrado:
            await interaction.response.send_message(
                "❌ Já não encontrei esse livro no histórico.",
                ephemeral=True,
            )
            return

        livro_encontrado["nota"] = nota
        livro_encontrado["estrelas"] = estrelas_para_texto(nota)
        guardar_dados()

        for item in self.view.children:
            item.disabled = True

        await interaction.response.edit_message(
            content=(
                f"🎨 Avaliação guardada para **{self.titulo_livro}**: "
                f"{livro_encontrado['estrelas']}"
            ),
            view=self.view,
        )


class ViewAvaliacao(discord.ui.View):
    def __init__(self, titulo_livro: str, autor_id: int):
        super().__init__(timeout=86400)
        self.add_item(SelectAvaliacao(titulo_livro, autor_id))


# ==============================================================================
# COMANDO: GUIA (ATUALIZADO)
# ==============================================================================

@bot.command(name="dadosficheiro", help="Mostra onde os dados do bot são guardados.")
async def mostrar_dados_ficheiro(ctx: commands.Context):
    await ctx.send(f"💾 **Persistência do bot**\n{resumo_persistencia()}")


@bot.command(name="armazenamento", help="Explica como persistir dados na nuvem.")
async def ajuda_armazenamento(ctx: commands.Context):
    embed = discord.Embed(
        title="☁️ Armazenamento na nuvem",
        description=(
            "Se o bot corre em **Render, Railway, Fly.io**, etc., o disco é **temporário** — "
            "a TBR apaga-se a cada reinício. Usa armazenamento remoto:"
        ),
        color=discord.Color.blue(),
    )
    embed.add_field(
        name="Opção 1 — GitHub (ideal se o bot já está no GitHub)",
        value=(
            "1. GitHub → Settings → Developer settings → Personal access tokens\n"
            "2. Cria token com permissão **Contents** (read/write) no repositório\n"
            "3. Opcional: adiciona `dados_bot.json` ao repo (pode começar vazio `{}`)\n"
            "4. Nas variáveis da nuvem:\n"
            "`GITHUB_TOKEN` → o token\n"
            "`GITHUB_REPO` → `utilizador/nome-do-repo`\n"
            "Opcional: `GITHUB_BRANCH` (default `main`), `GITHUB_DATA_PATH` (default `dados_bot.json`)"
        ),
        inline=False,
    )
    embed.add_field(
        name="Opção 2 — Supabase",
        value=(
            "1. Projeto em [supabase.com](https://supabase.com) + tabela `bot_state`\n"
            "2. Variáveis: `SUPABASE_URL` e `SUPABASE_KEY`"
        ),
        inline=False,
    )
    embed.add_field(
        name="Opção 3 — JSONBin",
        value="Variáveis: `JSONBIN_BIN_ID` e `JSONBIN_API_KEY`",
        inline=False,
    )
    embed.add_field(
        name="Estado atual",
        value=resumo_persistencia(),
        inline=False,
    )
    await ctx.send(embed=embed)


@bot.command(name="guia", help="Mostra o guia completo de comandos do bot.")
async def enviar_guia(ctx: commands.Context):
    p = COMMAND_PREFIX
    embed = discord.Embed(
        title="📖 GUIA DO COSMO",
        description=(
            "Bot de leituras com TBR, leituras conjuntas, desafios e Bookstagram.\n"
            f"**Formato obrigatório dos livros:** `\"Título - Autor\"`"
        ),
        color=discord.Color.purple(),
    )
    embed.add_field(
        name="📚 TBR e Planeamento",
        value=(
            f"`{p}addtbr` — Adiciona um livro à TBR Geral ou a um mês.\n"
            f"• `{p}addtbr \"Quarta Asa - Rebecca Yarros\"`\n"
            f"• `{p}addtbr Junho \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}remtbr` — Remove um livro de uma categoria da TBR.\n"
            f"• `{p}remtbr Geral \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}verbar` — Mostra toda a TBR organizada por mês.\n\n"
            f"`{p}tbr` — Sorteia a TBR do mês, coloca leituras no calendário e **tranca** "
            f"até leres todos os livros sorteados.\n"
            f"• `{p}tbr Junho` · `{p}tbr Junho 3` (3 extras da Geral)\n\n"
            f"`{p}livroinfo` — Pesquisa metadados (ReadMore/Open Library).\n"
            f"• `{p}livroinfo \"Quarta Asa - Rebecca Yarros\"`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📅 Leituras Conjuntas",
        value=(
            f"`{p}meta` — Cria uma LC: adiciona à TBR, abre tópico, gera cronograma, "
            f"calendário visual (imagem) e lembretes diários.\n"
            f"• `{p}meta Junho \"Quarta Asa - Rebecca Yarros\" dia 7 até cap. 10, dia 14 até cap. 22`\n\n"
            f"`{p}editmeta` — Corrige metas de uma LC já criada (inclui autor).\n"
            f"• `{p}editmeta \"Quarta Asa - Rebecca Yarros\" dia 7 até cap. 12, dia 20 fim`\n\n"
            f"`{p}calendariolc` — Gera imagem do calendário mensal com todas as metas.\n"
            f"• `{p}calendariolc` · `{p}calendariolc Junho`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🏆 Desafios e Leituras",
        value=(
            f"`{p}lido` — Regista livro como lido, remove de **todas** as TBR, "
            f"atualiza A-Z e abre menu de avaliação (0.25 a 5 estrelas).\n"
            f"• `{p}lido \"Quarta Asa - Rebecca Yarros\"`\n\n"
            f"`{p}avaliar` — Avalia o último livro lido (0.25 em 0.25).\n"
            f"• `{p}avaliar 4.5` · `{p}avaliar 3.75`\n\n"
            f"`{p}reavaliar` — Reavalia um livro já lido.\n"
            f"• `{p}reavaliar \"Quarta Asa - Rebecca Yarros\" 4.5`\n\n"
            f"`{p}editarautor` — Corrige o nome do autor de um livro.\n"
            f"• `{p}editarautor \"Quarta Asa - Rebecca\" \"Rebecca Yarros\"`\n\n"
            f"`{p}desafios` — Painel geral: meta anual, A-Z, avaliações e TBR.\n"
            f"`{p}alfabeto` — Progresso do desafio A-Z.\n"
            f"`{p}remalfabeto` — Limpa uma letra do A-Z. · `{p}remalfabeto Q`\n"
            f"`{p}historico` — Histórico de leituras com género e páginas.\n"
            f"`{p}remlido` — Remove um livro dos lidos."
        ),
        inline=False,
    )
    embed.add_field(
        name="✨ Recomendações",
        value=(
            f"`{p}recomendar` — Gera 3 sugestões com base nos livros avaliados com **4⭐ ou mais** "
            f"(pt-PT ou inglês), com ficha técnica, capa e botões para TBR.\n\n"
            f"**Botão** `✅ Já vi estas sugestões` — Arquiva para não voltarem a aparecer.\n\n"
            f"`{p}marcarsugestoes` — Arquiva sugestões manualmente.\n"
            f"• `{p}marcarsugestoes Livro A - Autor | Livro B - Autor`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📸 Bookstagram",
        value=(
            f"`{p}review` — Ativa modo bloco de notas para uma review.\n"
            f"Escreve rants, opiniões ou anexa **prints de mensagens** (imagens).\n\n"
            f"`{p}gerar` — Gera a legenda final da review com IA.\n"
            f"`{p}trend` — Ideias de posts/reels. · `{p}trend \"Livro - Autor\"`\n"
            f"`{p}vibe` — Moodboard estético para fotos. · `{p}vibe \"Livro - Autor\"`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📊 Resumos e Estatísticas",
        value=(
            f"`{p}resumomes` — Gráfico do mês: livros, páginas, autores e géneros.\n"
            f"• `{p}resumomes` · `{p}resumomes Junho`\n\n"
            f"`{p}resumoano` — Apresentação visual anual: autor mais lido, páginas e géneros.\n"
            f"• `{p}resumoano` · `{p}resumoano 2026`\n\n"
            "_Resumos automáticos: dia 1 (mês anterior) e 2 de janeiro (ano anterior)._"
        ),
        inline=False,
    )
    embed.add_field(
        name="🎲 Extras",
        value=(
            f"`{p}entrevista` — Entrevista uma personagem fictícia.\n"
            f"• `{p}entrevista Rhysanda O que pensas da Feyre?`\n\n"
            f"`{p}ressaca` — Sugestões para ressaca literária.\n"
            f"`{p}teoria` — Reage à tua teoria sem spoilers.\n"
            f"`{p}sprint` — Sprint de leitura com temporizador. · `{p}sprint 25`\n\n"
            f"`{p}autores` — Lista todos os autores registados."
        ),
        inline=False,
    )
    embed.add_field(
        name="☁️ Nuvem",
        value=f"`{p}dadosficheiro` · `{p}armazenamento`",
        inline=False,
    )
    embed.set_footer(text=f"Prefixo atual: {COMMAND_PREFIX} · Usa {COMMAND_PREFIX}guia para rever este painel")
    await ctx.send(embed=embed)


# ==============================================================================
# COMANDO: RECOMENDAR
# ==============================================================================

@bot.command(name="recomendar", help="Sugere livros com base nos teus lidos avaliados com 4⭐ ou mais.")
async def curadoria_inteligente(ctx: commands.Context):
    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só pode ser usado dentro de um servidor.")

    favoritos = livros_bem_avaliados(minimo=4.0)
    if not favoritos:
        return await ctx.send(
            "📭 Ainda não tens livros avaliados com **4 estrelas ou mais**.\n"
            "Regista leituras com `!lido \"Título - Autor\"` e avalia com o menu de estrelas ou `!avaliar 4.5`."
        )

    nome_canal_sugestoes = "sugestoes-leitura"
    canal_sugestoes = await garantir_canal(guild, nome_canal_sugestoes)

    await ctx.send(
        f"🔍 A preparar sugestões com base em **{len(favoritos)}** livro(s) bem avaliado(s) "
        f"em {canal_sugestoes.mention}..."
    )

    tbr_atual = livros_tbr_flat()
    vistos = dados.get("sugestoes_vistas", [])

    linhas_favoritos = []
    for livro in favoritos:
        genero = livro.get("genero", "N/D")
        linhas_favoritos.append(
            f"- {livro['titulo']} ({livro['nota']:g}⭐, género: {genero})"
        )
    favs_texto = "\n".join(linhas_favoritos)
    tbr_texto = ", ".join(tbr_atual) if tbr_atual else "Nenhum"
    vistos_texto = ", ".join(vistos) if vistos else "Nenhum"

    prompt = f"""
You are a literary curator.
The reader loved these books (rated 4 stars or higher). Suggest NEW books with similar tone, genre, pacing and emotional impact:
{favs_texto}

Rules:
- Recommend books similar to the highly-rated titles above (authors, subgenres, themes, vibe).
- Do NOT suggest books already in this TBR list: [{tbr_texto}].
- Do NOT suggest books already shown and dismissed: [{vistos_texto}].

Write all descriptive text in European Portuguese (pt-PT) OR English — never Brazilian Portuguese.

Respond only with valid JSON in this structure:
{{
  "livros": [
    {{
      "titulo": "Book Title",
      "autor": "Author Name",
      "data_publicacao": "Month/Year or DD/MM/YYYY",
      "genero": "Main Genre",
      "subgenero": "Subgenre",
      "porque_ler": "Short convincing text in pt-PT or English",
      "link_capa": "https://..."
    }}
  ]
}}

Suggest exactly 3 real books. Always include author and title separately.
"""

    try:
        resposta = gemini_json(prompt)
        livros_sugeridos = resposta.get("livros", [])

        if not livros_sugeridos:
            return await ctx.send("❌ Não consegui gerar sugestões válidas.")

        base_favoritos = "\n".join(f"• {l['titulo']} ({l['nota']:g}⭐)" for l in favoritos)
        await canal_sugestoes.send(
            "✨ **A TUA REVISTA LITERÁRIA PERSONALIZADA** ✨\n"
            "*Sugestões baseadas nos teus livros com 4⭐ ou mais:*\n"
            f"{base_favoritos}"
        )

        titulos_botoes = []

        for livro in livros_sugeridos:
            titulo = livro.get("titulo", "Sem título")
            autor = livro.get("autor", "Desconhecido")
            titulo_completo = formatar_livro(titulo, autor)
            data_publicacao = livro.get("data_publicacao", "Desconhecida")
            genero = livro.get("genero", "N/D")
            subgenero = livro.get("subgenero", "N/D")
            porque_ler = livro.get("porque_ler", "Uma sugestão alinhada com o teu gosto.")
            link_capa = livro.get("link_capa", "")

            if titulo_completo.lower().strip() in {v.lower().strip() for v in vistos}:
                continue

            titulos_botoes.append(titulo_completo)

            embed = discord.Embed(
                title=f"📖 {titulo_completo}",
                description=f"**Autor:** {autor}\n\n{porque_ler}",
                color=discord.Color.from_rgb(255, 182, 193)
            )
            embed.add_field(name="📅 Publicação", value=data_publicacao, inline=True)
            embed.add_field(name="🎭 Género", value=genero, inline=True)
            embed.add_field(name="🧬 Subgénero", value=subgenero, inline=True)

            if isinstance(link_capa, str) and link_capa.startswith("http"):
                embed.set_image(url=link_capa)

            embed.set_footer(text="Gostaste? Guarda na tua lista clicando no painel abaixo.")
            await canal_sugestoes.send(embed=embed)

        if not titulos_botoes:
            return await ctx.send("❌ Todas as sugestões geradas já tinham sido vistas antes.")

        await canal_sugestoes.send(
            "✨ **Adiciona as tuas escolhas instantaneamente:**",
            view=ViewSugestoes(titulos_botoes, titulos_botoes),
        )
        await ctx.send(f"✅ Painel visual gerado com sucesso em {canal_sugestoes.mention}.")

    except Exception as e:
        await ctx.send(f"❌ Erro ao processar recomendações: {e}")


# ==============================================================================
# TBR
# ==============================================================================

@bot.command(name="addtbr", help="Adiciona um livro à TBR geral ou mensal.")
async def adicionar_tbr_mes(ctx: commands.Context, categoria: Optional[str] = None, *, livro: Optional[str] = None):
    if not categoria:
        return await ctx.send("❌ Diz-me o livro que queres adicionar. Exemplo: `!addtbr Nome do Livro`")

    cat_sugerida = normalizar_categoria(categoria)

    if cat_sugerida in dados["tbr_por_mes"]:
        if not livro:
            return await ctx.send(
                f"❌ Falta o nome do livro para adicionar a **{cat_sugerida}**.\n"
                f'Exemplo: `!addtbr {cat_sugerida} "Título - Autor"`'
            )
        cat = cat_sugerida
        texto_livro = livro.strip()
    else:
        cat = "Geral"
        texto_livro = f"{categoria} {livro or ''}".strip()

    try:
        titulo_livro = livro_completo(texto_livro)
    except ValueError:
        return await ctx.send(
            '❌ O formato tem de incluir autor: **"Título - Autor"**.\n'
            'Exemplo: `!addtbr "Quarta Asa - Rebecca Yarros"`'
        )

    ja_existe = any(
        titulo_livro.lower().strip() == item.lower().strip()
        for item in livros_tbr_flat()
    )
    if ja_existe:
        return await ctx.send("🤔 Esse livro já está na tua TBR.")

    dados["tbr_por_mes"][cat].append(titulo_livro)
    guardar_dados()

    await ctx.send(f"📅 **{titulo_livro}** adicionado com sucesso a **{cat}**.")

    if cat != "Geral":
        await ctx.send("🔍 A verificar se pertence a uma série...")
        prompt = f"""
O utilizador adicionou "{titulo_livro}" ao mês "{cat}".
Se for uma série literária conhecida, responde em JSON válido:
{{"sequencias": ["Livro 2", "Livro 3"]}}
Máximo 3 livros.
Se não for série, responde:
{{"sequencias": []}}
"""
        try:
            resposta = gemini_json(prompt)
            sequencias = resposta.get("sequencias", [])

            if sequencias:
                idx_mes_atual = MESES_ORDEM.index(cat)
                mensagens = []

                for i, proximo_livro in enumerate(sequencias):
                    idx_destino = (idx_mes_atual + 1 + i) % 12
                    mes_destino = MESES_ORDEM[idx_destino]
                    if not any(proximo_livro.lower() == x.lower() for x in livros_tbr_flat()):
                        dados["tbr_por_mes"][mes_destino].append(proximo_livro)
                        mensagens.append(f"• **{proximo_livro}** agendado para **{mes_destino}**")

                guardar_dados()

                if mensagens:
                    await ctx.send(
                        "🧬 **Série detetada!** Sequências agendadas automaticamente:\n" +
                        "\n".join(mensagens)
                    )
        except Exception:
            await ctx.send("⚠️ Não consegui validar a série deste livro, mas ele foi adicionado à TBR.")


@bot.command(name="tbr", help="Sorteia a TBR do mês, tranca até ler tudo e coloca no calendário.")
async def sortear_tbr_mes(ctx: commands.Context, mes: str, extras: int = 2):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    if extras < 0:
        return await ctx.send("❌ O número de extras não pode ser negativo.")

    sorteio_ativo = sorteio_mes_ativo(mes_cap)
    if sorteio_ativo:
        pendentes = sorteio_ativo.get("pendentes", sorteio_ativo.get("livros", []))
        lista = "\n".join(f"• {livro}" for livro in pendentes)
        return await ctx.send(
            f"🔒 O sorteio de **{mes_cap}** está trancado até leres todos os livros.\n"
            f"Faltam:\n{lista}\n\nUsa `!lido \"Título - Autor\"` à medida que fores terminando."
        )

    obrigatorios = list(dados["tbr_por_mes"][mes_cap])
    obrigatorios_norm = {livro.lower().strip() for livro in obrigatorios}
    geral_disponivel = [
        livro
        for livro in dados["tbr_por_mes"]["Geral"]
        if livro.lower().strip() not in obrigatorios_norm
    ]
    extras_sorteados = random.sample(geral_disponivel, min(extras, len(geral_disponivel)))
    livros_sorteio = obrigatorios + extras_sorteados

    if not livros_sorteio:
        return await ctx.send(f"📭 Não tens livros planeados para {mes_cap} nem na lista Geral.")

    dados["sorteios_mes"][mes_cap] = {
        "livros": livros_sorteio,
        "lidos": [],
        "data_sorteio": hoje_str(),
        "ano": int(este_ano()),
    }
    guardar_dados()

    ano = int(este_ano())
    mes_num = numero_mes(mes_cap)
    _, dias_no_mes = calendar.monthrange(ano, mes_num)
    dias_uteis = [d for d in range(1, dias_no_mes + 1) if calendar.weekday(ano, mes_num, d) < 5]
    if not dias_uteis:
        dias_uteis = list(range(1, dias_no_mes + 1))

    passo = max(1, len(dias_uteis) // max(len(livros_sorteio), 1))
    for idx, livro in enumerate(livros_sorteio):
        dia = dias_uteis[min(idx * passo, len(dias_uteis) - 1)]
        data_meta = f"{dia:02d}/{mes_num:02d}/{ano}"
        dados["lembretes_metas"].append({
            "data": data_meta,
            "livro": livro,
            "meta": f"Iniciar/concluir leitura de {livro}",
            "canal_id": ctx.channel.id,
            "avisado": False,
            "tipo": "sorteio_tbr",
        })

    guardar_dados()

    mensagem = f"🎲 **TBR de {mes_cap} sorteada e trancada**\n"
    mensagem += "\n📌 **Livros deste mês:**\n"
    mensagem += "\n".join(f"• {livro}" for livro in livros_sorteio)
    mensagem += "\n\n🔒 Novo sorteio só depois de marcares todos como lidos com `!lido`."

    await enviar_mensagem_longa(ctx, mensagem)

    if Image is not None:
        try:
            imagem = desenhar_calendario_leituras(mes_cap, ano)
            ficheiro = discord.File(imagem, filename=f"tbr-{mes_cap.lower()}-{ano}.png")
            await ctx.send(f"🗓️ Calendário de leituras de **{mes_cap}**:", file=ficheiro)
        except Exception:
            pass


@bot.command(name="verbar", help="Mostra toda a TBR organizada por mês.")
async def ver_tbr_completa(ctx: commands.Context):
    mensagem = f"📋 **PLANEAMENTO DE TBR ({este_ano()})** 📋\n"

    if dados["tbr_por_mes"]["Geral"]:
        mensagem += f"\n🌎 **Geral:** {', '.join(dados['tbr_por_mes']['Geral'])}"

    for mes in MESES_ORDEM:
        if dados["tbr_por_mes"][mes]:
            mensagem += f"\n📅 **{mes}**: {', '.join(dados['tbr_por_mes'][mes])}"

    await enviar_mensagem_longa(ctx, mensagem)


@bot.command(name="remtbr", help="Remove um livro da TBR.")
async def remover_tbr_mes(ctx: commands.Context, categoria: str, *, livro: str):
    cat = normalizar_categoria(categoria)

    if cat not in dados["tbr_por_mes"]:
        return await ctx.send("❌ Categoria inválida.")

    existente = buscar_livro_case_insensitive(dados["tbr_por_mes"][cat], livro)
    if not existente:
        return await ctx.send(f"❌ *{livro}* não foi encontrado em **{cat}**.")

    dados["tbr_por_mes"][cat].remove(existente)
    guardar_dados()
    await ctx.send(f"🗑️ *{existente}* removido com sucesso de **{cat}**.")


# ==============================================================================
# METAS E LEMBRETES
# ==============================================================================

@bot.command(
    name="meta",
    help='Cria metas de leitura conjunta. Ex.: !meta Junho "Quarta Asa - Rebecca Yarros" dia 7 até cap. 10',
)
async def definir_meta_lc(ctx: commands.Context, mes: str, livro: str, *, cronograma: str):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    try:
        livro_completo_txt = livro_completo(livro)
        titulo_curto, autor = parsear_livro(livro_completo_txt)
    except ValueError:
        return await ctx.send(
            '❌ Usa o formato **"Título - Autor"**.\n'
            'Exemplo: `!meta Junho "Quarta Asa - Rebecca Yarros" dia 7 até cap. 10`'
        )

    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só funciona dentro de um servidor.")

    mensagem_tbr = adicionar_livro_a_tbr_mes(livro_completo_txt, mes_cap)
    guardar_dados()

    nome_canal_mes = canal_nome_seguro(mes_cap)
    canal_mes = await garantir_canal(guild, nome_canal_mes)

    mensagem_ancora = await canal_mes.send(
        f"📚 **LEITURA CONJUNTA: {titulo_curto.upper()}** 📚\n👤 **Autor:** {autor}"
    )
    topico_livro = await canal_mes.create_thread(
        name=f"livro-{canal_nome_seguro(livro_completo_txt)[:70]}",
        message=mensagem_ancora,
    )

    await ctx.send(f"{mensagem_tbr}\n🔮 A organizar cronograma em {topico_livro.mention}...")

    prompt = f"""
You are a joint reading assistant. Create a reading calendar for "{livro_completo_txt}" in {mes_cap} {este_ano()}.

Reader instructions:
"{cronograma}"

Formatting rules:
1. Build a Monday-Sunday calendar grid in Markdown.
2. Place goals on the correct dates.
3. Leave empty days blank or with a dash.
4. Write in European Portuguese (pt-PT) or English — never Brazilian Portuguese.

Respond only in JSON:
{{
  "calendario_visual": "Markdown calendar grid",
  "metas": [ {{"data": "DD/MM/{este_ano()}", "texto": "Short goal"}} ],
  "nota": "Brief explanation"
}}
"""

    try:
        resposta = gemini_json(prompt)
        metas = resposta.get("metas", [])
        nota = resposta.get("nota", "")

        if nota:
            await enviar_mensagem_longa(topico_livro, f"ℹ️ {nota}")

        lembretes_criados = 0

        for m in metas:
            data_meta = str(m.get("data", "")).strip()
            texto_meta = str(m.get("texto", "")).strip()
            if not data_valida(data_meta) or not texto_meta:
                continue

            dados["lembretes_metas"].append({
                "data": data_meta,
                "livro": livro_completo_txt,
                "autor": autor,
                "meta": texto_meta,
                "canal_id": topico_livro.id,
                "thread_id": topico_livro.id,
                "avisado": False,
                "tipo": "lc",
            })
            lembretes_criados += 1

        guardar_dados()

        if Image is not None:
            try:
                imagem = desenhar_calendario_leituras(mes_cap, int(este_ano()))
                ficheiro = discord.File(imagem, filename=f"lc-{mes_cap.lower()}-{este_ano()}.png")
                await topico_livro.send("🗓️ **Calendário visual do mês:**", file=ficheiro)
            except Exception:
                pass

        await ctx.send(
            f"✅ Cronograma enviado com sucesso para {topico_livro.mention}. "
            f"Lembretes criados: **{lembretes_criados}**."
        )

    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar cronograma: {e}")


async def enviar_lembretes_pendentes_hoje() -> None:
    data_hoje = datetime.now().strftime("%d/%m/%Y")
    alterado = False

    for lembrete in dados["lembretes_metas"]:
        if lembrete.get("data") != data_hoje or lembrete.get("avisado"):
            continue

        canal_id = lembrete.get("thread_id") or lembrete.get("canal_id")
        if not canal_id:
            continue

        canal = await obter_canal_discord(int(canal_id))
        if not canal:
            continue

        try:
            await canal.send(
                f"🔔 **METAS DE HOJE!**\n"
                f"Livro: **{lembrete.get('livro', 'Livro')}**\n"
                f"📖 **Meta:** {lembrete.get('meta', '')}\n"
                f"Boas leituras!"
            )
            lembrete["avisado"] = True
            alterado = True
        except discord.HTTPException:
            continue

    if alterado:
        guardar_dados()


@tasks.loop(minutes=5)
async def verificar_lembretes_loop():
    await enviar_lembretes_pendentes_hoje()


@verificar_lembretes_loop.before_loop
async def antes_lembretes():
    await bot.wait_until_ready()


@tasks.loop(hours=6)
async def resumos_automaticos_loop():
    agora = datetime.now()
    if agora.day == 1 and agora.hour == 10:
        mes_anterior_idx = agora.month - 2
        if mes_anterior_idx < 0:
            mes_anterior_idx = 11
            ano = agora.year - 1
        else:
            ano = agora.year
        mes_nome = MESES_ORDEM[mes_anterior_idx]
        for guild in bot.guilds:
            canal = discord.utils.get(guild.text_channels, name="sugestoes-leitura")
            if canal and Image is not None:
                stats = estatisticas_mes(mes_nome, ano)
                if stats["total_livros"] > 0:
                    img = desenhar_grafico_barras(
                        f"Resumo de {mes_nome} {ano}",
                        ["Livros", "Páginas", "Autores", "Géneros"],
                        [stats["total_livros"], stats["paginas"], stats["autores_unicos"], stats["generos_unicos"]],
                    )
                    await canal.send(file=discord.File(img, filename=f"resumo-{mes_nome.lower()}.png"))

    if agora.month == 1 and agora.day == 2 and agora.hour == 10:
        ano_anterior = agora.year - 1
        for guild in bot.guilds:
            canal = discord.utils.get(guild.text_channels, name="sugestoes-leitura")
            if canal and Image is not None:
                stats = estatisticas_ano(ano_anterior)
                if stats["total_livros"] > 0:
                    img = desenhar_resumo_anual(ano_anterior, stats)
                    await canal.send(file=discord.File(img, filename=f"resumo-anual-{ano_anterior}.png"))


@resumos_automaticos_loop.before_loop
async def antes_resumos():
    await bot.wait_until_ready()


@bot.command(name="editmeta", help='Edita metas de uma LC existente. Ex.: !editmeta "Título - Autor" dia 7 até cap. 10')
async def editar_meta_lc(ctx: commands.Context, livro: str, *, cronograma: str):
    try:
        livro_completo_txt = livro_completo(livro)
        _, autor = parsear_livro(livro_completo_txt)
    except ValueError:
        return await ctx.send('❌ Usa o formato **"Título - Autor"**.')

    lembretes_livro = [
        l for l in dados["lembretes_metas"]
        if l.get("livro", "").lower().strip() == livro_completo_txt.lower().strip() and l.get("tipo") == "lc"
    ]
    if not lembretes_livro:
        return await ctx.send("❌ Não encontrei metas de leitura conjunta para esse livro.")

    meses_encontrados = set()
    for l in lembretes_livro:
        try:
            data = datetime.strptime(l["data"], "%d/%m/%Y")
            meses_encontrados.add(MESES_ORDEM[data.month - 1])
        except (TypeError, ValueError, IndexError):
            pass
    mes_cap = next(iter(meses_encontrados), MESES_ORDEM[datetime.now().month - 1])

    dados["lembretes_metas"] = [
        l for l in dados["lembretes_metas"]
        if not (l.get("livro", "").lower().strip() == livro_completo_txt.lower().strip() and l.get("tipo") == "lc")
    ]

    canal_id = lembretes_livro[0].get("thread_id") or lembretes_livro[0].get("canal_id")
    prompt = f"""
Update the joint reading calendar for "{livro_completo_txt}" in {mes_cap} {este_ano()}.

New instructions:
"{cronograma}"

Write in European Portuguese (pt-PT) or English.

JSON only:
{{
  "calendario_visual": "Markdown calendar grid",
  "metas": [ {{"data": "DD/MM/{este_ano()}", "texto": "Short goal"}} ],
  "nota": "Brief explanation"
}}
"""

    try:
        resposta = gemini_json(prompt)
        metas = resposta.get("metas", [])
        nota = resposta.get("nota", "")

        canal = await obter_canal_discord(int(canal_id)) if canal_id else ctx.channel
        if canal and nota:
            await enviar_mensagem_longa(canal, f"ℹ️ {nota}")

        criados = 0
        for m in metas:
            data_meta = str(m.get("data", "")).strip()
            texto_meta = str(m.get("texto", "")).strip()
            if not data_valida(data_meta) or not texto_meta:
                continue
            dados["lembretes_metas"].append({
                "data": data_meta,
                "livro": livro_completo_txt,
                "autor": autor,
                "meta": texto_meta,
                "canal_id": canal_id,
                "thread_id": canal_id,
                "avisado": False,
                "tipo": "lc",
            })
            criados += 1

        guardar_dados()

        if Image is not None:
            try:
                imagem = desenhar_calendario_leituras(mes_cap, int(este_ano()))
                ficheiro = discord.File(imagem, filename=f"lc-edit-{mes_cap.lower()}.png")
                await ctx.send("🗓️ Calendário visual atualizado:", file=ficheiro)
            except Exception:
                pass

        await ctx.send(f"✅ Metas atualizadas para **{livro_completo_txt}**. Novos lembretes: **{criados}**.")
    except Exception as e:
        await ctx.send(f"❌ Erro ao editar metas: {e}")


@bot.command(name="calendariolc", help="Cria uma imagem do calendário mensal das leituras conjuntas.")
async def calendario_leituras_conjuntas(ctx: commands.Context, mes: Optional[str] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar a biblioteca de imagem. Usa: `pip install Pillow`")

    mes_alvo = normalizar_categoria(mes) if mes else MESES_ORDEM[datetime.now().month - 1]
    if mes_alvo not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido. Exemplo: `!calendariolc Junho`")

    ano = int(este_ano())

    try:
        imagem = desenhar_calendario_leituras(mes_alvo, ano)
    except Exception as e:
        return await ctx.send(f"❌ Erro ao criar calendário: {e}")

    ficheiro = discord.File(imagem, filename=f"leituras-conjuntas-{mes_alvo.lower()}-{ano}.png")
    await ctx.send(
        f"🗓️ **Calendário de leituras conjuntas - {mes_alvo} {ano}**",
        file=ficheiro
    )


# ==============================================================================
# LIDOS / A-Z / HISTÓRICO
# ==============================================================================

@bot.command(name="lido", help='Regista um livro como lido. Formato: "Título - Autor".')
async def livro_lido(ctx: commands.Context, *, titulo_livro: str):
    try:
        titulo_completo = livro_completo(titulo_livro)
        titulo_curto, autor = parsear_livro(titulo_completo)
    except ValueError:
        return await ctx.send(
            '❌ O formato tem de incluir autor: **"Título - Autor"**.\n'
            'Exemplo: `!lido "Quarta Asa - Rebecca Yarros"`'
        )

    ja_existe = livro_ja_lido(titulo_completo)
    if ja_existe:
        return await ctx.send(f"⚠️ O livro **{titulo_completo}** já está registado como lido.")

    info = await obter_info_livro(titulo_completo)
    novo_livro = {
        "titulo": titulo_completo,
        "autor": autor,
        "estrelas": "Sem avaliação",
        "nota": 0.0,
        "genero": info.get("genero", "N/D"),
        "paginas": int(info.get("paginas", 0) or 0),
        "data_leitura": hoje_str(),
        "fonte_metadados": info.get("fonte", "IA"),
    }

    dados["livros_lidos"].append(novo_livro)

    removido_de = []
    for chave, lista in dados["tbr_por_mes"].items():
        encontrado = buscar_livro_case_insensitive(lista, titulo_completo)
        if encontrado:
            lista.remove(encontrado)
            removido_de.append(chave)

    meses_desbloqueados = marcar_livro_sorteio_lido(titulo_completo)
    aviso_remocao = f" (removido de: {', '.join(removido_de)})" if removido_de else ""
    aviso_sorteio = ""
    if meses_desbloqueados:
        aviso_sorteio = f"\n🔓 Sorteio desbloqueado em: **{', '.join(meses_desbloqueados)}**."

    await ctx.send(f"✍️ A registar '{titulo_completo}' e a validar o Desafio A-Z...")

    resultado = analisar_titulo_alfabeto(titulo_curto)
    aviso_alfabeto = ""

    if resultado["status"] == "BANIDO":
        aviso_alfabeto = "\n🔤 **Desafio A-Z:** Título começado por artigo. Não conta. ❌"
    elif resultado["status"] == "OK":
        letra = resultado["letra"]

        if letra in dados["desafio_alfabeto"]:
            if dados["desafio_alfabeto"][letra] == VAZIO_ALFABETO:
                dados["desafio_alfabeto"][letra] = titulo_completo
                aviso_alfabeto = f"\n🔤 **Desafio A-Z:** Letra **{letra}** conquistada! 🎉"
            else:
                aviso_alfabeto = (
                    f"\n🔤 **Desafio A-Z:** A letra **{letra}** já se encontrava preenchida "
                    f"por **{dados['desafio_alfabeto'][letra]}**."
                )
    else:
        aviso_alfabeto = "\n⚠️ Não foi possível determinar uma letra válida para o desafio."

    guardar_dados()
    total_lidos = len(dados["livros_lidos"])

    await ctx.send(
        f"📚 **{titulo_completo}** adicionado aos lidos!{aviso_remocao}{aviso_sorteio}{aviso_alfabeto}\n"
        f"📊 Progresso Anual: {total_lidos}/{META_ANUAL} livros em {este_ano()}.\n"
        f"📎 Metadados via **{info.get('fonte', 'IA')}**.\n"
        f"Escolhe a avaliação:",
        view=ViewAvaliacao(titulo_completo, ctx.author.id),
    )


@bot.command(name="alfabeto", help="Mostra o progresso do desafio A-Z.")
async def ver_desafio_alfabeto(ctx: commands.Context):
    preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
    msg = f"🔤 **DESAFIO A A Z ({este_ano()})**\n📊 Progresso Geral: **{preenchidas}/26** letras completadas.\n\n"

    for letra, livro in dados["desafio_alfabeto"].items():
        icon = "🟢" if livro != VAZIO_ALFABETO else "⚫"
        msg += f"{icon} **{letra}**: {livro}\n"

    await ctx.send(msg)


@bot.command(name="desafios", help="Mostra o progresso geral dos desafios de leitura.")
async def ver_progresso_desafios(ctx: commands.Context):
    total_lidos = len(dados["livros_lidos"])
    percentagem_anual = min(100, round((total_lidos / META_ANUAL) * 100))

    letras_preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
    percentagem_az = round((letras_preenchidas / 26) * 100)
    letras_em_falta = [letra for letra, livro in dados["desafio_alfabeto"].items() if livro == VAZIO_ALFABETO]

    total_tbr = len(livros_tbr_flat())
    metas_ativas = sum(1 for lembrete in dados["lembretes_metas"] if not lembrete.get("avisado", False))
    livros_avaliados = sum(
        1
        for livro in dados["livros_lidos"]
        if livro.get("estrelas") and livro.get("estrelas") != "Sem avaliação"
    )

    embed = discord.Embed(
        title=f"🏆 PROGRESSO DOS DESAFIOS ({este_ano()})",
        color=discord.Color.gold()
    )
    embed.add_field(
        name="📚 Meta anual",
        value=f"**{total_lidos}/{META_ANUAL}** livros lidos ({percentagem_anual}%)",
        inline=False
    )
    embed.add_field(
        name="🔤 Desafio A-Z",
        value=(
            f"**{letras_preenchidas}/26** letras completas ({percentagem_az}%).\n"
            f"Faltam: {', '.join(letras_em_falta) if letras_em_falta else 'nenhuma 🎉'}"
        ),
        inline=False
    )
    embed.add_field(
        name="⭐ Avaliações",
        value=f"**{livros_avaliados}/{total_lidos}** livros lidos avaliados.",
        inline=False
    )
    embed.add_field(
        name="📅 Leituras conjuntas",
        value=f"**{metas_ativas}** metas futuras/pendentes guardadas.",
        inline=False
    )
    embed.add_field(
        name="📌 TBR",
        value=f"**{total_tbr}** livros por ler no planeamento.",
        inline=False
    )
    embed.set_footer(text="Usa !alfabeto para ver o detalhe letra a letra.")

    await ctx.send(embed=embed)


@bot.command(name="remalfabeto", help="Remove um livro de uma letra do desafio A-Z.")
async def remover_do_alfabeto(ctx: commands.Context, letra: str):
    letra = letra.strip().upper()

    if len(letra) != 1 or letra not in dados["desafio_alfabeto"]:
        return await ctx.send("❌ Letra inválida. Usa apenas uma letra de A a Z. Exemplo: `!remalfabeto B`")

    livro_atual = dados["desafio_alfabeto"][letra]

    if livro_atual == VAZIO_ALFABETO:
        preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)
        return await ctx.send(
            f"⚫ A letra **{letra}** já estava vazia.\n"
            f"Progresso atual do A-Z: **{preenchidas}/26**. Usa `!alfabeto` para ver a lista completa."
        )

    dados["desafio_alfabeto"][letra] = VAZIO_ALFABETO
    guardar_dados()

    preenchidas = sum(1 for v in dados["desafio_alfabeto"].values() if v != VAZIO_ALFABETO)

    await ctx.send(
        f"🗑️ A letra **{letra}** foi limpa com sucesso.\n"
        f"Livro removido: **{livro_atual}**\n"
        f"Progresso atual do A-Z: **{preenchidas}/26**."
    )


@bot.command(name="avaliar", help="Avalia o último livro lido (0.25 a 5, de 0.25 em 0.25).")
async def avaliar_livro(ctx: commands.Context, nota: float):
    if not dados["livros_lidos"]:
        return await ctx.send("❌ Ainda não registaste nenhum livro lido para avaliar.")

    if not nota_valida(nota):
        return await ctx.send("❌ A nota deve ser entre 0.25 e 5, em passos de 0.25.")

    dados["livros_lidos"][-1]["nota"] = nota
    dados["livros_lidos"][-1]["estrelas"] = estrelas_para_texto(nota)
    guardar_dados()
    await ctx.send(f"🎨 Avaliação guardada com sucesso: {dados['livros_lidos'][-1]['estrelas']}")


# ==============================================================================
# NOVO COMANDO: REAVALIAR
# ==============================================================================

@bot.command(name="reavaliar", help="Reavalia um livro já lido. Ex: !reavaliar \"Título - Autor\" 4.5")
async def reavaliar_livro(ctx: commands.Context, *, argumentos: str):
    """
    Permite reavaliar um livro já registado como lido.
    Uso: !reavaliar "Título - Autor" 4.5
    Ou: !reavaliar Título - Autor 4.5
    """
    # Tentar extrair título e nota
    partes = argumentos.rsplit(' ', 1)
    
    if len(partes) < 2:
        return await ctx.send(
            "❌ Uso correto: `!reavaliar \"Título - Autor\" 4.5`\n"
            "A nota deve ser entre 0.25 e 5, em passos de 0.25."
        )
    
    titulo_candidato = partes[0].strip()
    try:
        nota = float(partes[1].strip())
    except ValueError:
        return await ctx.send("❌ Nota inválida. Exemplo: `4.5` ou `3.75`")
    
    if not nota_valida(nota):
        return await ctx.send("❌ A nota deve ser entre 0.25 e 5, em passos de 0.25.")
    
    # Tentar encontrar o livro no histórico
    titulo_alvo = titulo_candidato.lower().strip()
    livro_encontrado = None
    
    for livro in dados["livros_lidos"]:
        titulo_livro = livro.get("titulo", "").lower().strip()
        if titulo_livro == titulo_alvo:
            livro_encontrado = livro
            break
    
    if not livro_encontrado:
        # Tentar com separador se o utilizador não usou o formato completo
        for livro in dados["livros_lidos"]:
            titulo_livro = livro.get("titulo", "").lower().strip()
            if titulo_livro.startswith(titulo_alvo) or titulo_alvo.startswith(titulo_livro):
                livro_encontrado = livro
                break
    
    if not livro_encontrado:
        # Mostrar sugestões de livros parecidos
        sugestoes = []
        for livro in dados["livros_lidos"][-5:]:  # últimos 5 livros
            sugestoes.append(f"• {livro.get('titulo', 'Desconhecido')}")
        
        sugestoes_texto = "\n".join(sugestoes) if sugestoes else "Nenhum livro encontrado no histórico."
        return await ctx.send(
            f"❌ Não encontrei o livro **{titulo_candidato}** no teu histórico.\n\n"
            f"**Últimos livros lidos:**\n{sugestoes_texto}\n\n"
            f"Usa o nome exato como aparece em `!historico`."
        )
    
    nota_antiga = livro_encontrado.get("nota", 0.0)
    estrelas_antigas = livro_encontrado.get("estrelas", "Sem avaliação")
    
    # Atualizar avaliação
    livro_encontrado["nota"] = nota
    livro_encontrado["estrelas"] = estrelas_para_texto(nota)
    guardar_dados()
    
    await ctx.send(
        f"🔄 **Avaliação atualizada!**\n"
        f"📖 {livro_encontrado.get('titulo', 'Livro')}\n"
        f"⭐ Antiga: {estrelas_antigas} → ⭐ Nova: {livro_encontrado['estrelas']}"
    )


# ==============================================================================
# NOVO COMANDO: EDITAR AUTOR
# ==============================================================================

@bot.command(name="editarautor", help="Corrige o nome do autor de um livro. Ex: !editarautor \"Título - AutorErrado\" \"AutorCerto\"")
async def editar_autor_livro(ctx: commands.Context, *, argumentos: str):
    """
    Permite corrigir o nome do autor de um livro já registado.
    Uso: !editarautor "Título - AutorAntigo" "AutorNovo"
    """
    # Tentar extrair título completo e novo autor
    # Formato: "Título - AutorAntigo" "AutorNovo"
    padrao = r'"([^"]+)"\s+"([^"]+)"'
    match = re.match(padrao, argumentos)
    
    if not match:
        return await ctx.send(
            "❌ Uso correto: `!editarautor \"Título - Autor Antigo\" \"Autor Correto\"`\n"
            "Exemplo: `!editarautor \"Quarta Asa - Rebecca\" \"Rebecca Yarros\"`"
        )
    
    titulo_completo_antigo = match.group(1).strip()
    novo_autor = match.group(2).strip()
    
    if not novo_autor:
        return await ctx.send("❌ O novo autor não pode ficar vazio.")
    
    # Encontrar o livro no histórico
    livro_encontrado = None
    titulo_alvo = titulo_completo_antigo.lower().strip()
    
    for livro in dados["livros_lidos"]:
        if livro.get("titulo", "").lower().strip() == titulo_alvo:
            livro_encontrado = livro
            break
    
    if not livro_encontrado:
        # Tentar encontrar por correspondência parcial
        for livro in dados["livros_lidos"]:
            titulo_livro = livro.get("titulo", "").lower().strip()
            if titulo_livro.startswith(titulo_alvo) or titulo_alvo.startswith(titulo_livro):
                livro_encontrado = livro
                break
    
    if not livro_encontrado:
        sugestoes = []
        for livro in dados["livros_lidos"][-5:]:
            sugestoes.append(f"• {livro.get('titulo', 'Desconhecido')}")
        sugestoes_texto = "\n".join(sugestoes) if sugestoes else "Nenhum livro encontrado."
        return await ctx.send(
            f"❌ Não encontrei o livro **{titulo_completo_antigo}** no histórico.\n\n"
            f"**Últimos livros lidos:**\n{sugestoes_texto}"
        )
    
    titulo_antigo = livro_encontrado.get("titulo", "")
    autor_antigo = livro_encontrado.get("autor", "")
    
    # Construir novo título no formato "Título - Novo Autor"
    try:
        titulo_curto, _ = parsear_livro(titulo_antigo)
        novo_titulo_completo = formatar_livro(titulo_curto, novo_autor)
    except ValueError:
        # Se não conseguir parsear, usa o título original sem autor
        partes_titulo = titulo_antigo.split(SEPARADOR_LIVRO)
        titulo_curto = partes_titulo[0] if partes_titulo else titulo_antigo
        novo_titulo_completo = f"{titulo_curto}{SEPARADOR_LIVRO}{novo_autor}"
    
    # Atualizar o livro
    livro_encontrado["titulo"] = novo_titulo_completo
    livro_encontrado["autor"] = novo_autor
    
    # Também atualizar no desafio A-Z se o livro estiver lá
    for letra, livro_alfabeto in dados["desafio_alfabeto"].items():
        if livro_alfabeto == titulo_antigo:
            dados["desafio_alfabeto"][letra] = novo_titulo_completo
            break
    
    # Atualizar nas TBRs
    for categoria, lista in dados["tbr_por_mes"].items():
        for i, item in enumerate(lista):
            if item == titulo_antigo:
                lista[i] = novo_titulo_completo
    
    # Atualizar nos lembretes/metas
    for lembrete in dados["lembretes_metas"]:
        if lembrete.get("livro") == titulo_antigo:
            lembrete["livro"] = novo_titulo_completo
            if lembrete.get("autor") == autor_antigo:
                lembrete["autor"] = novo_autor
    
    # Atualizar nos sorteios
    for mes, info in dados["sorteios_mes"].items():
        livros = info.get("livros", [])
        for i, livro in enumerate(livros):
            if livro == titulo_antigo:
                livros[i] = novo_titulo_completo
        lidos = info.get("lidos", [])
        for i, livro in enumerate(lidos):
            if livro == titulo_antigo:
                lidos[i] = novo_titulo_completo
    
    guardar_dados()
    
    await ctx.send(
        f"✏️ **Autor corrigido com sucesso!**\n"
        f"📖 Título: {titulo_curto}\n"
        f"👤 Antigo autor: {autor_antigo}\n"
        f"👤 Novo autor: {novo_autor}\n\n"
        f"✅ O livro foi atualizado em todo o sistema (histórico, TBR, desafios, sorteios e lembretes)."
    )


# ==============================================================================
# NOVO COMANDO: AUTORES
# ==============================================================================

@bot.command(name="autores", help="Lista todos os autores dos livros lidos.")
async def listar_autores(ctx: commands.Context):
    """Lista todos os autores únicos dos livros lidos."""
    autores = set()
    for livro in dados["livros_lidos"]:
        autor = livro.get("autor", "")
        if autor:
            autores.add(autor)
        else:
            # Tentar extrair do título
            try:
                _, autor = parsear_livro(livro.get("titulo", ""))
                autores.add(autor)
            except ValueError:
                pass
    
    if not autores:
        return await ctx.send("📭 Ainda não tens autores registados.")
    
    autores_ordenados = sorted(autores)
    msg = f"📚 **Autores registados ({len(autores_ordenados)}):**\n"
    msg += "\n".join(f"• {autor}" for autor in autores_ordenados)
    
    await enviar_mensagem_longa(ctx, msg)


@bot.command(name="remlido")
async def remover_lido(ctx: commands.Context, *, titulo_livro: str):

    encontrado = None

    for livro in dados["livros_lidos"]:
        if livro.get("titulo", "").lower().strip() == titulo_livro.lower().strip():
            encontrado = livro
            break

    if not encontrado:
        return await ctx.send("❌ Livro não encontrado.")

    dados["livros_lidos"].remove(encontrado)

    letras_limpas = []
    titulo_encontrado = encontrado.get("titulo", titulo_livro)
    for letra, livro_alfabeto in dados["desafio_alfabeto"].items():
        if str(livro_alfabeto).lower().strip() == titulo_encontrado.lower().strip():
            dados["desafio_alfabeto"][letra] = VAZIO_ALFABETO
            letras_limpas.append(letra)

    guardar_dados()

    aviso_alfabeto = ""
    if letras_limpas:
        aviso_alfabeto = f"\n🔤 Também removi do Desafio A-Z: **{', '.join(letras_limpas)}**."

    await ctx.send(
        f"🗑️ Livro removido: **{titulo_encontrado}**{aviso_alfabeto}"
    )


@bot.command(name="historico", help="Mostra o histórico de leituras.")
async def mostrar_historico(ctx: commands.Context):
    if not dados["livros_lidos"]:
        return await ctx.send("📭 O teu histórico de leituras ainda está vazio.")

    linhas = []
    for i, l in enumerate(dados["livros_lidos"], 1):
        genero = l.get("genero", "")
        paginas = l.get("paginas", 0)
        extra = ""
        if genero and genero != "N/D":
            extra += f" | {genero}"
        if paginas:
            extra += f" | {paginas} págs."
        linhas.append(
            f"{i}. {l.get('titulo', 'Sem título')} — {l.get('estrelas', 'Sem avaliação')}{extra}"
        )
    await enviar_mensagem_longa(ctx, f"📜 **HISTÓRICO DE LEITURAS** 📜\n\n" + "\n".join(linhas))


@bot.command(name="marcarsugestoes", help="Marca sugestões como já vistas para não voltarem a aparecer.")
async def marcar_sugestoes_vistas(ctx: commands.Context, *, titulos: str):
    novos = 0
    vistos = {v.lower().strip() for v in dados.setdefault("sugestoes_vistas", [])}
    for titulo in [t.strip() for t in titulos.split("|") if t.strip()]:
        if titulo.lower() not in vistos:
            dados["sugestoes_vistas"].append(titulo)
            vistos.add(titulo.lower())
            novos += 1
    guardar_dados()
    await ctx.send(f"✅ **{novos}** sugestão(ões) arquivada(s).")


# ==============================================================================
# BOOKSTAGRAM / EXTRAS
# ==============================================================================

@bot.command(name="trend", help="Gera ideias de posts ou reels de Bookstagram.")
async def sugerir_trends_bookstagram(ctx: commands.Context, *, livro_foco: str = None):
    ultimo = (
        dados["livros_lidos"][-1].get("titulo", "um romance ou fantasia em voga")
        if dados["livros_lidos"]
        else "um romance ou fantasia em voga"
    )
    livro_alvo = livro_foco if livro_foco else ultimo

    await ctx.send(f"📸 A analisar ideias para: **{livro_alvo}**...")
    prompt = (
        f"Gera 3 ideias criativas de posts ou reels estéticos de Bookstagram com base em trends de {este_ano()} "
        f"para o livro '{livro_alvo}' em português de Portugal. Adiciona sugestões de áudio e hashtags."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"✨ **TRENDS INSTAGRAM** ✨\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar trends: {e}")


@bot.command(name="review", help="Inicia notas para gerar uma legenda de review.")
async def iniciar_review(ctx: commands.Context, *, titulo_livro: str):
    user_id = str(ctx.author.id)
    dados["review_em_andamento"][user_id] = {
        "titulo": titulo_livro,
        "desabafos": [],
        "anexos": [],
    }
    guardar_dados()

    await ctx.send(
        f"📸 **Modo Bloco de Notas ativado para: *{titulo_livro}***\n"
        f"Escreve rants, opiniões ou cola **prints de mensagens** (imagens) em mensagens normais.\n"
        f"Quando terminares, usa `!gerar`."
    )


@bot.command(name="gerar", help="Gera a legenda final da review de Bookstagram.")
async def gerar_review(ctx: commands.Context):
    user_id = str(ctx.author.id)

    if user_id not in dados["review_em_andamento"]:
        return await ctx.send("❌ Não tens nenhuma review em andamento.")

    review = dados["review_em_andamento"][user_id]
    titulo = review["titulo"]
    desabafos = review.get("desabafos", [])
    anexos = review.get("anexos", [])

    if not desabafos and not anexos:
        return await ctx.send("❌ Ainda não escreveste nenhum apontamento para essa review.")

    anexos_txt = "\n".join(f"- Print/anexo: {url}" for url in anexos)
    prompt = (
        f"Create a structured, aesthetic and emotional Bookstagram caption in European Portuguese (pt-PT) or English. "
        f"Use these notes and rants about '{titulo}':\n- " +
        "\n- ".join(desabafos) +
        (f"\n\nAttached screenshots/prints to consider:\n{anexos_txt}" if anexos_txt else "")
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"✨ **LEGENDA PARA O INSTAGRAM PRONTA:**\n\n{res}")
        if anexos:
            await ctx.send("📎 **Prints incluídos na review:**\n" + "\n".join(anexos))
        del dados["review_em_andamento"][user_id]
        guardar_dados()
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar legenda: {e}")


@bot.command(name="entrevista", help="Entrevista uma personagem fictícia.")
async def entrevistar_personagem(ctx: commands.Context, personagem: str, *, pergunta: str):
    await ctx.send(f"🔮 A invocar o espírito de {personagem}...")

    prompt = (
        f"Assume integralmente a personalidade da personagem fictícia '{personagem}'. "
        f"Responde estritamente na primeira pessoa, em português de Portugal. "
        f"Pergunta: '{pergunta}'"
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"**[{personagem}]:** {res}")
    except Exception as e:
        await ctx.send(f"❌ Erro na entrevista: {e}")


@bot.command(name="ressaca", help="Sugere leituras para curar ressaca literária.")
async def curar_ressaca(ctx: commands.Context, *, livro_destruidor: str):
    prompt = (
        f"O leitor está em ressaca literária após ler '{livro_destruidor}'. "
        f"Sugere duas opções de livros reais, leves e cativantes, justificando em português de Portugal."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"🩺 **DIAGNÓSTICO PARA RESSACA LITERÁRIA**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar sugestões: {e}")


@bot.command(name="teoria", help="Reage à tua teoria de leitura sem spoilers confirmados.")
async def avaliar_teoria(ctx: commands.Context, *, teoria_leitora: str):
    prompt = (
        f"Uma leitora partilhou esta teoria sobre os rumos de uma história: '{teoria_leitora}'. "
        f"Reage como uma fã empolgada, sem spoilers confirmados, em português de Portugal."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"💭 **AVALIAÇÃO DA TUA TEORIA:**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao avaliar teoria: {e}")


@bot.command(name="vibe", help="Gera uma estética visual e temática para um livro.")
async def gerar_estetica(ctx: commands.Context, *, nome_livro: str):
    prompt = (
        f"Cria um guia compacto de estética literária para o livro '{nome_livro}' "
        f"(cenários, cores, objetos marcantes), ideal para fotos de Bookstagram."
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"📸 **BOOKSTAGRAM MOODBOARD VIBE:**\n\n{res}")
    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar vibe: {e}")


@bot.command(name="livroinfo", help="Pesquisa metadados via ReadMore/Open Library.")
async def info_livro(ctx: commands.Context, *, consulta: str):
    await ctx.send(f"🔍 A pesquisar **{consulta}**...")
    info = await obter_info_livro(consulta)
    embed = discord.Embed(
        title=f"📖 {info.get('titulo', consulta)}",
        description=f"**Autor:** {info.get('autor', 'Desconhecido')}",
        color=discord.Color.teal(),
    )
    embed.add_field(name="Género", value=info.get("genero", "N/D"), inline=True)
    embed.add_field(name="Páginas", value=str(info.get("paginas", 0) or "N/D"), inline=True)
    embed.add_field(name="Ano", value=str(info.get("ano", "N/D")), inline=True)
    embed.add_field(name="Fonte", value=info.get("fonte", "IA"), inline=True)
    if info.get("capa"):
        embed.set_thumbnail(url=info["capa"])
    await ctx.send(embed=embed)


@bot.command(name="resumomes", help="Gera gráfico das leituras de um mês.")
async def resumo_mensal(ctx: commands.Context, mes: Optional[str] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar Pillow: `pip install Pillow`")

    mes_alvo = normalizar_categoria(mes) if mes else MESES_ORDEM[datetime.now().month - 1]
    if mes_alvo not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido. Exemplo: `!resumomes Junho`")

    ano = int(este_ano())
    stats = estatisticas_mes(mes_alvo, ano)
    if stats["total_livros"] == 0:
        return await ctx.send(f"📭 Sem leituras registadas em **{mes_alvo} {ano}**.")

    img = desenhar_grafico_barras(
        f"Resumo de {mes_alvo} {ano}",
        ["Livros", "Páginas", "Autores", "Géneros"],
        [stats["total_livros"], stats["paginas"], stats["autores_unicos"], stats["generos_unicos"]],
    )
    detalhe = (
        f"📊 **{mes_alvo} {ano}**\n"
        f"Livros: **{stats['total_livros']}** | Páginas: **{stats['paginas']}**\n"
        f"Autores distintos: **{stats['autores_unicos']}** | Géneros: **{stats['generos_unicos']}**"
    )
    await ctx.send(detalhe, file=discord.File(img, filename=f"resumo-{mes_alvo.lower()}.png"))


@bot.command(name="resumoano", help="Apresentação visual do ano de leituras.")
async def resumo_anual(ctx: commands.Context, ano: Optional[int] = None):
    if Image is None:
        return await ctx.send("❌ Falta instalar Pillow: `pip install Pillow`")

    ano_alvo = ano or int(este_ano())
    stats = estatisticas_ano(ano_alvo)
    if stats["total_livros"] == 0:
        return await ctx.send(f"📭 Sem leituras registadas em **{ano_alvo}**.")

    img = desenhar_resumo_anual(ano_alvo, stats)
    await ctx.send(
        f"🏆 **Resumo anual {ano_alvo}** — {stats['total_livros']} livros, "
        f"{stats['total_paginas']} páginas.",
        file=discord.File(img, filename=f"resumo-anual-{ano_alvo}.png"),
    )


@bot.command(name="sprint", help="Inicia um sprint de leitura com temporizador.")
async def sprint_leitura(ctx: commands.Context, minutes: int):
    if minutes <= 0:
        return await ctx.send("❌ O tempo deve ser superior a 0 minutos.")

    await ctx.send(
        f"⏱️ **Sprint de Leitura começado!**\n"
        f"Foco total durante **{minutes}** minutos. Boas páginas! 📖"
    )
    await asyncio.sleep(minutes * 60)
    await ctx.send(
        f"🔔 **FIM DO SPRINT!** {ctx.author.mention}, o tempo acabou! "
        f"Quantas páginas conseguiste ler?"
    )


# ==============================================================================
# RUN
# ==============================================================================

if __name__ == "__main__":
    bot.run(DISCORD_TOKEN)
