import os
import json
import random
import asyncio
import re
import unicodedata
import calendar
import io
import textwrap
from pathlib import Path
from datetime import datetime
from typing import Any, Dict, List, Optional

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
DATA_FILE = Path(__file__).with_name("dados_bot.json")
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


# ==============================================================================
# PERSISTÊNCIA
# ==============================================================================

def estado_inicial() -> Dict[str, Any]:
    return {
        "livros_lidos": [],
        "review_em_andamento": {},
        "lembretes_metas": [],
        "tbr_por_mes": {
            "Geral": [],
            "Janeiro": [], "Fevereiro": [], "Março": [], "Abril": [],
            "Maio": [], "Junho": [], "Julho": [], "Agosto": [],
            "Setembro": [], "Outubro": [], "Novembro": [], "Dezembro": []
        },
        "desafio_alfabeto": {letra: VAZIO_ALFABETO for letra in "ABCDEFGHIJKLMNOPQRSTUVWXYZ"}
    }


def carregar_dados() -> Dict[str, Any]:
    if DATA_FILE.exists():
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as f:
                dados = json.load(f)
            if not isinstance(dados, dict):
                return estado_inicial()
            base = estado_inicial()
            base.update(dados)
            base["tbr_por_mes"] = {
                **estado_inicial()["tbr_por_mes"],
                **dados.get("tbr_por_mes", {}),
            }
            base["desafio_alfabeto"] = {
                **estado_inicial()["desafio_alfabeto"],
                **dados.get("desafio_alfabeto", {}),
            }
            return base
        except (OSError, json.JSONDecodeError):
            return estado_inicial()
    return estado_inicial()


def guardar_dados() -> None:
    with open(DATA_FILE, "w", encoding="utf-8") as f:
        json.dump(dados, f, ensure_ascii=False, indent=2)


dados = carregar_dados()


# ==============================================================================
# HELPERS
# ==============================================================================

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


async def garantir_canal(guild: discord.Guild, nome: str) -> discord.TextChannel:
    canal = discord.utils.get(guild.text_channels, name=nome)
    if canal:
        return canal
    return await guild.create_text_channel(nome)


# ==============================================================================
# BOT
# ==============================================================================

intents = discord.Intents.default()
intents.message_content = True


class LeituraBot(commands.Bot):
    async def setup_hook(self) -> None:
        self.add_view(ViewSugestoes([]))


bot = LeituraBot(command_prefix=COMMAND_PREFIX, intents=intents)


@bot.event
async def on_ready():
    print(f"👑 {bot.user} está online.")
    if not verificar_lembretes_loop.is_running():
        verificar_lembretes_loop.start()


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot:
        return

    user_id = str(message.author.id)
    if user_id in dados["review_em_andamento"]:
        if not message.content.startswith(COMMAND_PREFIX):
            dados["review_em_andamento"][user_id]["desabafos"].append(message.content.strip())
            guardar_dados()
            await message.add_reaction("📝")

    await bot.process_commands(message)


@bot.event
async def on_command_error(ctx: commands.Context, error: commands.CommandError):
    if isinstance(error, commands.MissingRequiredArgument):
        exemplos = {
            "addtbr": "`!addtbr Nome do Livro` ou `!addtbr Junho Nome do Livro`",
            "remtbr": "`!remtbr Geral Nome do Livro`",
            "tbr": "`!tbr Junho` ou `!tbr Junho 3`",
            "meta": '`!meta Junho "Nome do Livro" dia 7 até cap. 10, dia 14 até cap. 22`',
            "lido": "`!lido Nome do Livro`",
            "remalfabeto": "`!remalfabeto A`",
            "avaliar": "`!avaliar 1` até `!avaliar 5`",
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


class ViewSugestoes(discord.ui.View):
    def __init__(self, livros_sugeridos: List[str]):
        super().__init__(timeout=None)
        for livro in livros_sugeridos:
            self.add_item(BotaoSugestao(livro))


class BotaoAvaliacao(discord.ui.Button):
    def __init__(self, titulo_livro: str, nota: int, autor_id: int):
        super().__init__(
            label=f"{nota} ⭐",
            style=discord.ButtonStyle.secondary,
        )
        self.titulo_livro = titulo_livro
        self.nota = nota
        self.autor_id = autor_id

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.autor_id:
            await interaction.response.send_message(
                "❌ Só quem registou este livro pode avaliá-lo por aqui.",
                ephemeral=True
            )
            return

        livro_encontrado = None
        for livro in dados["livros_lidos"]:
            if livro.get("titulo", "").lower().strip() == self.titulo_livro.lower().strip():
                livro_encontrado = livro
                break

        if not livro_encontrado:
            await interaction.response.send_message(
                "❌ Já não encontrei esse livro no histórico.",
                ephemeral=True
            )
            return

        livro_encontrado["estrelas"] = "⭐" * self.nota
        guardar_dados()

        for item in self.view.children:
            item.disabled = True
            if isinstance(item, BotaoAvaliacao) and item.nota == self.nota:
                item.style = discord.ButtonStyle.success

        await interaction.response.edit_message(
            content=(
                f"🎨 Avaliação guardada para **{self.titulo_livro}**: "
                f"{livro_encontrado['estrelas']}"
            ),
            view=self.view
        )


class ViewAvaliacao(discord.ui.View):
    def __init__(self, titulo_livro: str, autor_id: int):
        super().__init__(timeout=86400)
        for nota in range(1, 6):
            self.add_item(BotaoAvaliacao(titulo_livro, nota, autor_id))


# ==============================================================================
# COMANDO: GUIA
# ==============================================================================

@bot.command(name="guia", help="Mostra o guia completo de comandos do bot.")
async def enviar_guia(ctx: commands.Context):
    embed = discord.Embed(title="📖 GUIA DO COSMO", color=discord.Color.purple())
    embed.add_field(
        name="📚 TBR e Planeamento",
        value="`!addtbr`, `!remtbr`, `!verbar`, `!tbr`",
        inline=False
    )
    embed.add_field(
        name="📅 Leituras Conjuntas",
        value="`!meta [Mês] [Livro] [Cronograma]`, `!calendariolc [Mês]`",
        inline=False
    )
    embed.add_field(
        name="🏆 Desafios",
        value="`!lido`, botões de avaliação, `!desafios`, `!alfabeto`, `!remalfabeto`, `!historico`, `!avaliar`, `!remlido`",
        inline=False
    )
    embed.add_field(
        name="📸 Bookstagram",
        value="`!recomendar`, `!review`, `!gerar`, `!trend`, `!vibe`",
        inline=False
    )
    embed.add_field(
        name="✨ Extras",
        value="`!entrevista`, `!ressaca`, `!teoria`, `!sprint`",
        inline=False
    )
    embed.set_footer(text=f"Prefixo atual: {COMMAND_PREFIX}")
    await ctx.send(embed=embed)


# ==============================================================================
# COMANDO: RECOMENDAR
# ==============================================================================

@bot.command(name="recomendar", help="Gera sugestões literárias com ficha técnica e botões para TBR.")
async def curadoria_inteligente(ctx: commands.Context):
    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só pode ser usado dentro de um servidor.")

    nome_canal_sugestoes = "sugestoes-leitura"
    canal_sugestoes = await garantir_canal(guild, nome_canal_sugestoes)

    await ctx.send(f"🔍 A preparar sugestões em {canal_sugestoes.mention}...")

    livros_lidos = dados["livros_lidos"]
    favoritos = [
        l.get("titulo", "")
        for l in livros_lidos
        if l.get("titulo") and l.get("estrelas") in ["⭐⭐⭐⭐", "⭐⭐⭐⭐⭐"]
    ]
    tbr_atual = livros_tbr_flat()

    favs_texto = ", ".join(favoritos) if favoritos else "Romances, Fantasias e Thrillers marcantes"
    tbr_texto = ", ".join(tbr_atual) if tbr_atual else "Nenhum"

    prompt = f"""
Tu és uma curadora literária.
Baseia-te nos gostos da leitora: [{favs_texto}].
Não sugiras livros presentes nesta lista: [{tbr_texto}].

Responde apenas em JSON válido com esta estrutura:
{{
  "livros": [
    {{
      "titulo": "Nome do Livro",
      "autor": "Nome do Autor",
      "data_publicacao": "Mês/Ano ou DD/MM/AAAA",
      "genero": "Género Principal",
      "subgenero": "Subgénero",
      "porque_ler": "Texto curto e convincente em português de Portugal",
      "link_capa": "https://..."
    }}
  ]
}}

Sugere exatamente 3 livros reais.
"""

    try:
        resposta = gemini_json(prompt)
        livros_sugeridos = resposta.get("livros", [])

        if not livros_sugeridos:
            return await ctx.send("❌ Não consegui gerar sugestões válidas.")

        await canal_sugestoes.send(
            "✨ **A TUA REVISTA LITERÁRIA PERSONALIZADA** ✨\n"
            "*Aqui tens o teu radar de novidades e sugestões:*"
        )

        titulos_botoes = []

        for livro in livros_sugeridos:
            titulo = livro.get("titulo", "Sem título")
            autor = livro.get("autor", "Desconhecido")
            data_publicacao = livro.get("data_publicacao", "Desconhecida")
            genero = livro.get("genero", "N/D")
            subgenero = livro.get("subgenero", "N/D")
            porque_ler = livro.get("porque_ler", "Uma sugestão alinhada com o teu gosto.")
            link_capa = livro.get("link_capa", "")

            titulos_botoes.append(titulo)

            embed = discord.Embed(
                title=f"📖 {titulo}",
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

        await canal_sugestoes.send(
            "✨ **Adiciona as tuas escolhas instantaneamente:**",
            view=ViewSugestoes(titulos_botoes)
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
                f"Exemplo: `!addtbr {cat_sugerida} Nome do Livro`"
            )
        cat = cat_sugerida
        titulo_livro = livro.strip()
    else:
        cat = "Geral"
        titulo_livro = f"{categoria} {livro or ''}".strip()

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


@bot.command(name="tbr", help="Mostra a TBR prioritária do mês e sorteia extras da lista Geral.")
async def sortear_tbr_mes(ctx: commands.Context, mes: str, extras: int = 2):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    if extras < 0:
        return await ctx.send("❌ O número de extras não pode ser negativo.")

    obrigatorios = dados["tbr_por_mes"][mes_cap]
    obrigatorios_norm = {livro.lower().strip() for livro in obrigatorios}
    geral_disponivel = [
        livro
        for livro in dados["tbr_por_mes"]["Geral"]
        if livro.lower().strip() not in obrigatorios_norm
    ]
    extras_sorteados = random.sample(geral_disponivel, min(extras, len(geral_disponivel)))

    if not obrigatorios and not extras_sorteados:
        return await ctx.send(f"📭 Não tens livros planeados para {mes_cap} nem na lista Geral.")

    mensagem = f"🎲 **TBR de {mes_cap} com prioridade**\n"

    if obrigatorios:
        mensagem += "\n📌 **Obrigatórios / planeados para o mês:**\n"
        mensagem += "\n".join(f"• {livro}" for livro in obrigatorios)
    else:
        mensagem += "\n📌 **Obrigatórios / planeados para o mês:** nenhum."

    if extras_sorteados:
        mensagem += f"\n\n🌎 **Extras sorteados da Geral ({len(extras_sorteados)}):**\n"
        mensagem += "\n".join(f"• {livro}" for livro in extras_sorteados)
    elif extras:
        mensagem += "\n\n🌎 **Extras sorteados da Geral:** nenhum disponível."

    await enviar_mensagem_longa(ctx, mensagem)


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
    help='Cria metas de leitura conjunta. Ex.: !meta Junho "Quarta Asa" dia 7 até cap. 10, dia 14 até cap. 22',
)
async def definir_meta_lc(ctx: commands.Context, mes: str, livro: str, *, cronograma: str):
    mes_cap = normalizar_categoria(mes)
    if mes_cap not in MESES_ORDEM:
        return await ctx.send("❌ Mês inválido.")

    guild = ctx.guild
    if not guild:
        return await ctx.send("❌ Este comando só funciona dentro de um servidor.")

    mensagem_tbr = adicionar_livro_a_tbr_mes(livro, mes_cap)
    guardar_dados()

    nome_canal_mes = canal_nome_seguro(mes_cap)
    canal_mes = await garantir_canal(guild, nome_canal_mes)

    mensagem_ancora = await canal_mes.send(f"📚 **LEITURA CONJUNTA: {livro.upper()}** 📚")
    topico_livro = await canal_mes.create_thread(name=f"livro-{canal_nome_seguro(livro)[:70]}", message=mensagem_ancora)

    await ctx.send(f"{mensagem_tbr}\n🔮 A organizar cronograma em {topico_livro.mention}...")

    prompt = f"""
És uma assistente de leituras conjuntas. Cria um calendário para o livro "{livro}" no mês de {mes_cap} de {este_ano()}.

Instruções da leitora:
"{cronograma}"

Regras de formatação:
1. Desenha uma grelha de calendário de Segunda a Domingo (formato Markdown).
2. Coloca as metas nas datas corretas dentro da grelha.
3. Se um dia não tem meta, deixa vazio ou com um traço.
4. Usa português de Portugal.

Responde apenas em JSON com esta estrutura:
{{
  "calendario_visual": "Uma string contendo a grelha em Markdown (ex: | Seg | Ter | ... |\\n|---|---|...|\\n| | | 1 | 2... |)",
  "metas": [ {{"data": "DD/MM/{este_ano()}", "texto": "Meta curta"}} ],
  "nota": "Breve explicação"
}}
"""

    try:
        resposta = gemini_json(prompt)
        calendario = resposta.get(
            "calendario_visual",
            resposta.get("tabela_markdown", "Sem calendário disponível.")
        )
        metas = resposta.get("metas", [])
        nota = resposta.get("nota", "")

        await enviar_mensagem_longa(topico_livro, f"🗓️ **CALENDÁRIO VISUAL DE METAS**\n\n{calendario}")

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
                "livro": livro,
                "meta": texto_meta,
                "canal_id": topico_livro.id,
                "avisado": False
            })
            lembretes_criados += 1

        guardar_dados()
        await ctx.send(
            f"✅ Cronograma enviado com sucesso para {topico_livro.mention}. "
            f"Lembretes criados: **{lembretes_criados}**."
        )

    except Exception as e:
        await ctx.send(f"❌ Erro ao gerar cronograma: {e}")


@tasks.loop(minutes=1)
async def verificar_lembretes_loop():
    now = datetime.now()
    data_hoje = now.strftime("%d/%m/%Y")

    if now.hour == 9 and now.minute == 0:
        alterado = False
        for lembrete in dados["lembretes_metas"]:
            if lembrete["data"] == data_hoje and not lembrete["avisado"]:
                canal = bot.get_channel(lembrete["canal_id"])
                if canal:
                    await canal.send(
                        f"🔔 **METAS DE HOJE!**\n"
                        f"Livro: **{lembrete['livro']}**\n"
                        f"📖 **Meta:** {lembrete['meta']}\n"
                        f"Boas leituras!"
                    )
                    lembrete["avisado"] = True
                    alterado = True

        if alterado:
            guardar_dados()


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

ARTIGOS_BANIDOS = {"o", "a", "os", "as", "the"}

def analisar_titulo_alfabeto(titulo: str):
    titulo_limpo = titulo.strip()

    if not titulo_limpo:
        return {"status": "INVALIDO", "letra": None}

    palavras = titulo_limpo.split()
    if palavras and palavras[0].lower() in ARTIGOS_BANIDOS:
        return {"status": "BANIDO", "letra": None}

    for ch in titulo_limpo:
        if ch.isalpha():
            return {"status": "OK", "letra": ch.upper()}

    return {"status": "INVALIDO", "letra": None}

@bot.command(name="lido", help="Regista um livro como lido e atualiza o desafio A-Z.")
async def livro_lido(ctx: commands.Context, *, titulo_livro: str):

    ja_existe = any(
        livro.get("titulo", "").lower().strip() == titulo_livro.lower().strip()
        for livro in dados["livros_lidos"]
    )

    if ja_existe:
        return await ctx.send(
            f"⚠️ O livro **{titulo_livro}** já está registado como lido."
        )

    novo_livro = {
        "titulo": titulo_livro,
        "estrelas": "Sem avaliação"
    }

    dados["livros_lidos"].append(novo_livro)

    removido_de = []
    for chave, lista in dados["tbr_por_mes"].items():
        encontrado = buscar_livro_case_insensitive(lista, titulo_livro)
        if encontrado:
            lista.remove(encontrado)
            removido_de.append(chave)

    aviso_remocao = f" (removido de: {', '.join(removido_de)})" if removido_de else ""

    await ctx.send(f"✍️ A registar '{titulo_livro}' e a validar o Desafio A-Z...")

    resultado = analisar_titulo_alfabeto(titulo_livro)
    aviso_alfabeto = ""

    if resultado["status"] == "BANIDO":
        aviso_alfabeto = "\n🔤 **Desafio A-Z:** Título começado por artigo. Não conta. ❌"
    elif resultado["status"] == "OK":
        letra = resultado["letra"]

        if letra in dados["desafio_alfabeto"]:
            if dados["desafio_alfabeto"][letra] == VAZIO_ALFABETO:
                dados["desafio_alfabeto"][letra] = titulo_livro
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
        f"📚 **{titulo_livro}** adicionado aos lidos!{aviso_remocao}{aviso_alfabeto}\n"
        f"📊 Progresso Anual: {total_lidos}/{META_ANUAL} livros em {este_ano()}.\n"
        f"Escolhe a avaliação:",
        view=ViewAvaliacao(titulo_livro, ctx.author.id)
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

@bot.command(name="avaliar", help="Avalia o último livro lido com 1 a 5 estrelas.")
async def avaliar_livro(ctx: commands.Context, nota: int):
    if not dados["livros_lidos"]:
        return await ctx.send("❌ Ainda não registaste nenhum livro lido para avaliar.")

    if not 1 <= nota <= 5:
        return await ctx.send("❌ A nota deve ser entre 1 e 5.")

    dados["livros_lidos"][-1]["estrelas"] = "⭐" * nota
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

    msg = "\n".join(
        [
            f"{i}. {l.get('titulo', 'Sem título')} — {l.get('estrelas', 'Sem avaliação')}"
            for i, l in enumerate(dados["livros_lidos"], 1)
        ]
    )
    await enviar_mensagem_longa(ctx, f"📜 **HISTÓRICO DE LEITURAS** 📜\n\n{msg}")


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
        "desabafos": []
    }
    guardar_dados()

    await ctx.send(
        f"📸 **Modo Bloco de Notas ativado para: *{titulo_livro}***\n"
        f"Escreve as tuas opiniões em mensagens normais e, quando terminares, usa `!gerar`."
    )


@bot.command(name="gerar", help="Gera a legenda final da review de Bookstagram.")
async def gerar_review(ctx: commands.Context):
    user_id = str(ctx.author.id)

    if user_id not in dados["review_em_andamento"]:
        return await ctx.send("❌ Não tens nenhuma review em andamento.")

    review = dados["review_em_andamento"][user_id]
    titulo = review["titulo"]
    desabafos = review["desabafos"]

    if not desabafos:
        return await ctx.send("❌ Ainda não escreveste nenhum apontamento para essa review.")

    prompt = (
        f"Cria uma legenda estruturada, estética e emocional para o Bookstagram em português de Portugal, "
        f"baseando-te nestes desabafos sobre o livro '{titulo}':\n- " +
        "\n- ".join(desabafos)
    )

    try:
        res = gemini_text(prompt)
        await enviar_mensagem_longa(ctx, f"✨ **LEGENDA PARA O INSTAGRAM PRONTA:**\n\n{res}")
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

bot.run(DISCORD_TOKEN)
