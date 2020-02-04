# Application Name: Cephalon Schwa
# Author: Bunnyspa
VERSION = "1.10.12.3"

# Starchart info: VoiDGlitch and macdja38 in GitHub: github.com/VoiDGlitch/WarframeData
# Price check API: nexus-stats.com
# Wiki API: Wikia
# Raid API: https://trials.wf

import os
import traceback
import asyncio
import math
import datetime
import time
import json
import urllib.request
import urllib.error
import xml.etree.ElementTree as et
import discord
import logging
from difflib import SequenceMatcher
import re
from bs4 import BeautifulSoup
from bs4 import NavigableString
import hashlib

DEBUG = bool(os.getenv("BOT_DEBUG_TOKEN", ""))

if DEBUG: logging.basicConfig(level=logging.INFO)
else: logging.basicConfig(level=logging.WARNING)
logging.getLogger("discord").setLevel(logging.WARNING)

########## Constants ##########

LEN_LINE = 49
LIMIT_DTLINE = 50
LIMIT_RAIDRECENT = 7
PREFIX = (">" if DEBUG else "^")

PREFIX_ROLE = "ə"
ARROW_RIGHT = "⇒"
ARROW_DOWN = "⇓"
POINT = "•"

DATETIME_YMDHM = "%Y-%m-%d %H:%M"
DATETIME_YMDHMS = "%Y-%m-%d %H:%M:%S"

LANG_EN = "en"
LANG_KR = "kr"

EMOJI_POS         = "\U00002705"
EMOJI_NEG         = "\U0001F6AB"
EMOJI_QUESTION    = "\U00002753"
EMOJI_EXCLAMATION = "\U00002757"
EMOJI_FU          = "\U0001F595"
EMOJI_PONG        = "\U0001F3D3"
EMOJI_PIN         = "\U0001F4CC"
EMOJI_BELL        = "\U0001F514"
EMOJI_DAGGER      = "\U0001F5E1"
EMOJI_SWORD       = "\U00002694"
EMOJI_SUN         = "\U00002600"
EMOJI_MOON        = "\U0001F319"

URL_WF_MAIN = "https://www.warframe.com/"
URL_WF_WORLDSTATE = "http://content.warframe.com/dynamic/worldState.php"
URL_WF_RSS = "http://content.warframe.com/dynamic/rss.php"
URL_NEXUS_MAIN = "https://www.nexus-stats.com"
URL_NEXUS = "https://www.nexus-stats.com/api"
URL_WIKIA_PREFIX = "http://warframe.wikia.com/api/v1/Search/List?query="
URL_WIKIA_SUFFIX = "&limit=1"
URL_WFCD_DROPTABLE = "http://drops.warframestat.us/data/all.json"
URL_TRIALS_PREFIX = "https://api.trials.wf/api/player/pc/"
URL_TRIALS_SUFFIX = "/completed"

PASTEBIN_API_URL = "http://pastebin.com/api/api_post.php"
PASTEBIN_DEV_KEY = str(os.getenv("PASTEBIN_DEV_KEY", ""))

CHAR_UTF8 = "utf-8"
DATA_FOLDER = "data/"
with open(DATA_FOLDER + "art_deadeye" + ".txt", "r", encoding=CHAR_UTF8) as file: ART_DEADEYE = file.read()

KEYWORD_ALERT = ["alert","얼"]

########## ID ##########
# Discord Server, Channels, and Role ID data. Deleted for privacy.
DATA_CHAN = {"exception","",
             "feedback","",
             "item","",
             "itemBaro","",
             "itemBackup","",
             "delete","",
             "alert","",
             "cetus","",
             "event",""}

SERV_DATA = ""
DATA_ROLE_DEV = ""

########## Global Variables ##########

client = discord.Client()

class GlobalVariable:
  def __init__(self):
    ### file data
    self.nodeDict = {} # {nodeDataStr:nodeName}
    self.nodeMTypeDict = {} # {nodeDataStr:type}
    self.enkrDict = {} # {english:korean}
    self.ducatDict = {} # {item:{part:ducat}}
    ### web data
    self.dropDict = {} # {query:[(column, ndict(set)),...]}
    ### serv data
    self.itemDict = {} # {dStr:vStr}
    self.itemUploadSet = set() # {dStr+vStr}
    self.alertDict = {} # {servID:chanID}
    self.cetusDict = {} # {servID:chanID}
    self.deleteDict = {} # {chanID:day}
    self.eventDict = {} # {"servID|code|time":"userID|userID"}
    self.servData = {"item": self.itemDict,
                    "alert": self.alertDict,
                    "cetus": self.cetusDict,
                   "delete": self.deleteDict,
                    "event": self.eventDict}
g = GlobalVariable()

### Lock
lock_bpin = asyncio.Lock()
lock_alert = asyncio.Lock()
lock_cetus = asyncio.Lock()
lock_delete = asyncio.Lock()
lock_event = asyncio.Lock()

########## Helper Functions ##########

async def tryUntilWorks(func, *args):
  while True:
    try:
      await func(*args)
      break
    except Exception as e:
      logging.warning("tryUntilWorks:" + func.__name__ + ":" + type(e).__name__)
      await asyncio.sleep(5)

########## Web Readings ##########

def api(url):
  h = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/59.0.3071.115 Safari/537.36',
       'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
       'Accept-Charset': 'ISO-8859-1,utf-8;q=0.7,*;q=0.3',
       'Accept-Encoding': 'none',
       'Accept-Language': 'en-US,en;q=0.8',
       'Connection': 'keep-alive'}
  req = urllib.request.Request(url, headers=h)
  return urllib.request.urlopen(req).read().decode(CHAR_UTF8)

def api_json(url):
  return json.loads(api(url))

def wfAPI(): return api_json(URL_WF_WORLDSTATE)
def wfRSS(): return et.fromstring(api(URL_WF_RSS))
def wfPC(): return api_json(URL_NEXUS)

########## String ##########

##### Graphical length of string
def glen(string): return sum([(1.8 if re.match("[\u3131-\u3163\uac00-\ud7a3]", x) else 1) for x in string])

##### Add commas for thousand separators
def digitComma(value): return "{:,}".format(value)

##### Wrap
def wrap(prefix, text, suffix=None):
  if not suffix: suffix = prefix
  return prefix + text + suffix

def wrapQuote(text): return wrap("\"", text)
def wrapParen(text): return wrap("(", text, ")")
def wrapLink(text): return wrap("<", text, ">")

##### Unwrap
def unwrap(prefix, text, suffix=None):
  if not suffix: suffix = prefix
  if text.find(prefix) != -1 and text.find(suffix) != -1:
    return text[text.find(prefix) + 1:text.rfind(suffix)]
  return text

def unwrapQuote(text): return unwrap("\"", text)
def unwrapParen(text): return unwrap("(", text, ")")

##### Get right substring after last slash
def rstrSlash(text):
  if text.rfind("/") != -1:
    return text[text.rfind("/")+1:]
  return text

##### Get max length of string in a list
def maxGLen(strList):
  return max([glen(str(x)) for x in strList]) if strList else 0

##### L R
def lr(l, r):
  mLen = LEN_LINE - glen(l) - glen(r)
  return l + " "*max(round(mLen),1) + r

##### L M R
def lmr(l, m, r):
  halfLen = LEN_LINE / 2

  lLenF = halfLen - glen(l) - (glen(m)/2)
  lLenI = math.floor(math.ceil(lLenF*2)/2)

  rLenF = halfLen - glen(r) - (glen(m)/2)
  rLenI = math.ceil(math.floor(rLenF*2)/2)

  return l + " "*max(lLenI,1) + m + " "*max(rLenI,1) + r

##### L MMM R
def lmmmr(l, m1, m2, m3, r):
  halfLen = LEN_LINE / 2

  lLenF = halfLen - glen(l) - glen(m1) - (glen(m2)/2)
  lLenI = math.floor(math.ceil(lLenF*2)/2)

  rLenF = halfLen - glen(r) - glen(m3) - (glen(m2)/2)
  rLenI = math.ceil(math.floor(rLenF*2)/2)

  return l + " "*max(lLenI,1) + m1 + m2 + m3 + " "*max(rLenI,1) + r

##### Progress Bar
def progBar(p, l=LEN_LINE-2):
  if p < 0.0: p = 0.0
  if p > 1.0: p = 1.0
  progLen = int(p*l)
  left = "O" * (progLen - (1 if p == 1.0 else 0))
  right = "0" * (l - progLen - 1)
  return "[" + left + "|" + right + "]"

##### 3 tick MD (haskell)
def box1(text): return wrap("```", "haskell\n" + text)

##### 3 tick MD (apache)
def box2(text): return wrap("```", "apache\n" + text)

##### 3 tick MD (smalltalk)
def box3(text): return wrap("```", "smalltalk\n" + text)

##### 3 tick MD (none)
def box_data(text): return wrap("```", "\n" + text)

##### 1 tick MD
def mono(text): return wrap("`", text)

##### String similarity
def getSimStr(query, strSet):
  simR = -1.0
  simS = ""
  for s in strSet:
    r = SequenceMatcher(None, query.lower(), s.lower()).ratio()
    if simR < r:
      simR = r
      simS = s
  return simS

##### cardinal to ordinal
def ordinal(number):
  if number > 0:
    c = number % 100
    d = number % 10
    if (10 < c) and (c < 20): return str(number) + "th"
    elif d == 1: return str(number) + "st"
    elif d == 2: return str(number) + "nd"
    elif d == 3: return str(number) + "rd"
    else: return str(number) + "th"
  else: return str(number)

##### Convert seconds to dhms
def dhms(sec, kr=False):
  neg = ""
  if sec < 0:
    neg = "-"
    sec = -sec
  dayStr = ""
  hourStr = ""
  minStr = ""
  ### Day
  if sec//86400 > 0:
    dayStr = str(sec//86400) + ("일 " if kr else "d ")
  sec = sec % 86400
  ### Hour
  if sec//3600 > 0:
    hourStr = str(sec//3600) + ("시간 " if kr else "h ")
  sec = sec % 3600
  ### Min
  if sec//60 > 0:
    minStr = str(sec//60) + ("분 " if kr else "m ")
  sec = sec % 60
  ### Sec
  secStr = str(sec) + ("초" if kr else "s")
  return neg + dayStr + hourStr + minStr + secStr

def hash96(string):
  return hashlib.sha1(string.encode(CHAR_UTF8)).hexdigest()[:24]

def isFloat(value):
  try:
    float(value)
    return True
  except ValueError:
    return False

########## File Data ##########

##### Get a whole text from resources
def fileData_read(fileName):
  try:
    with open(DATA_FOLDER + fileName + ".txt", "r", encoding=CHAR_UTF8) as file:
      out = file.read()
      return out.replace("<p>", PREFIX)
  except FileNotFoundError: return ""

##### Get text lines without comments
def fileData_code(fileName):
  data = fileData_read(fileName)
  if not data: return []
  out = [x.split("#", 1)[0].strip() for x in data.splitlines()]
  return list(filter(None, out))

##### Get a specific line from the text
def fileData_line(fileName, query):
  for line in fileData_read(fileName).splitlines():
    if query in line:
      return line
  return ""

########## Discord Data ##########

##### "Unbox" data
def unbox_data(s):
  return list(filter(None, [x.strip("\n") for x in s.split("```")]))

##### Add data in server
async def servData_add(category, s):
  channel = client.get_channel(DATA_CHAN[category])
  ### Delete duplicate
  await servData_delete(category, s[:s.find("\n")])
  ### Message string
  await msg(channel, box_data(s))

##### Save backup item data
async def servData_backup(sl): # sl=True=save | sl=False=load
  fromChan = client.get_channel(DATA_CHAN[("item" if sl else "itemBackup")])
  toChan   = client.get_channel(DATA_CHAN[("itemBackup" if sl else "item")])
  await delmsgs(toChan)
  async for message in client.logs_from(fromChan, limit=1000, reverse=True):
    await msg(toChan, message.content)

##### Clean up data
async def servData_clean(category):
  data = set()
  channel = client.get_channel(DATA_CHAN[category])
  ### Messages in channel
  ds = []
  dls = []
  async for message in client.logs_from(channel, limit=1000, reverse=True):
    ### Data in message
    for d in unbox_data(message.content):
      # Save all except duplicates
      dl = d[:d.find("\n")]
      if dl not in dls:
        ds.append(d)
        dls.append(dl)
    await tryUntilWorks(delmsg, message)
  data = sorted(ds)
  s = ""
  await tryUntilWorks(msgs, channel, map(lambda x: box_data(x), data), "")

##### Delete data in server
async def servData_delete(category, data):
  channel = client.get_channel(DATA_CHAN[category])
  deleted = False
  if channel:
    ### Thru msgs
    async for message in client.logs_from(channel, limit=1000):
      lines = unbox_data(message.content)
      # Thru lines
      for e in lines:
        if data == e[:e.find("\n")]:
          deleted = True
          lines.remove(e)
          break
      # Delete data
      if deleted:
        m = "".join([box_data(x) for x in lines])
        if isMyMsg(message):
          await edit(message, m)
        else:
          await delmsg(message)
          await msg(channel, m)
        return True
  return False

##### Read all data and evaluate
async def servData_eval(category, default):
  channel = client.get_channel(DATA_CHAN[category])
  content = default
  async for message in client.logs_from(channel, limit=1000):
    lines = unbox_data(message.content)
    if type(default) == dict:
      for e in lines:
        en = e.splitlines()
        content[en[0]] = en[1]
    elif type(default) == set:
      for e in lines:
        content.add(e[:e.find("\n")])
  return content

##### See if ID is dev (admin in the server) ID
def servData_isDev(ID):
  member = client.get_server(SERV_DATA).get_member(ID)
  if not member: return False
  return (DATA_ROLE_DEV in [x.id for x in member.roles])

########## Conversions ##########

def convert_node(data, ID, command, faction):
  ### Attempt GitHub data
  if data in g.nodeDict: return g.nodeDict[data]
  ### Attempt RSS
  read = convert_read_RSS("node", ID, command, faction)
  if read: return read
  ### Give up
  return data

def convert_item(data, ID, command, faction):
  ### Attempt server data
  if data in g.itemDict: return g.itemDict[data]
  ### Attempt RSS
  read = convert_read_RSS("item", ID, command, faction)
  if read:
    g.itemDict[data] = read
    g.itemUploadSet.add(data + "\n" + read)
    return read
  ### Give up
  return rstrSlash(data)

def convert_mission(data):
  data = data[3:]
  match = {"INTEL":"Spy",
        "EXCAVATE":"Excavation",
       "TERRITORY":"Interception",
       "RETRIEVAL":"Hijack",
      "EVACUATION":"Defection",
   "EXTERMINATION":"Exterminate"}
  if data in match: return match[data]
  return data.replace("_", " ").title()

def convert_faction(data):
  data = data[3:]
  match = {"INFESTATION":"Infested"}
  if data in match: return match[data]
  return data.replace("_", " ").title()

def convert_fissure(data):
  data = data[-1:]
  match = {"1":"Lith", "2":"Meso", "3":"Neo", "4":"Axi"}
  if data in match: return match[data]
  return "Unknown"

def convert_sortieBoss(data):
  data = data[12:]
  match ={"VOR":"Captain Vor",
          "RUK":"General Sargas Ruk",
          "TYL":"Tyl Regor",
          "HEK":"Councilor Vay Hek",
          "NEF":"Nef Anyo",
         "ALAD":"Alad V",
         "KELA":"Kela De Thaym",
         "KRIL":"Lieutenant Lech Kril",
      "INFALAD":"Mutalist Alad V"}
  if data in match: return match[data]
  return data.replace("_", " ").title()

def convert_sortieMod(data):
  data = data[16:]
  match = {  "ARMOR":"Augmented Armor",
           "SHIELDS":"Augmented Shields",
            "IMPACT":"Physical Enhancement - Impact",
          "PUNCTURE":"Physical Enhancement - Puncture",
             "SLASH":"Physical Enhancement - Slash",
            "FREEZE":"Elemental Enhancement - Cold",
       "ELECTRICITY":"Elemental Enhancement - Electricity",
              "FIRE":"Elemental Enhancement - Heat",
            "POISON":"Elemental Enhancement - Toxin",
         "EXPLOSION":"Elemental Enhancement - Blast",
         "CORROSIVE":"Elemental Enhancement - Corrosive",
               "GAS":"Elemental Enhancement - Gas",
          "MAGNETIC":"Elemental Enhancement - Magnetic",
         "RADIATION":"Elemental Enhancement - Radiation",
             "VIRAL":"Elemental Enhancement - Viral",
        "RIFLE_ONLY":"Assault Rifle Only",
       "HAZARD_FIRE":"Fire Hazard",
       "HAZARD_COLD":"Extreme Cold",
        "HAZARD_ICE":"Cryogenic Leakage",
        "HAZARD_FOG":"Dense Fog",
  "HAZARD_RADIATION":"Radiation Hazard",
   "HAZARD_MAGNETIC":"Electromagnetic Anomalies",
        "LOW_ENERGY":"Energy Reduction",
            "EXIMUS":"Eximus Stronghold"}
  if data in match: return match[data]
  return data.replace("_", " ").title()

##### Read item/node from RSS
def convert_read_RSS(category, ID, command, faction):
  out = ""
  for i in wfRSS()[0]:
    if (i.tag == "item") and (i[0].text == ID):
      ### alert
      if command == "alert":
        info = i[1].text.split(" - ")
        ## Item
        if category == "item":
          itemInfo = info[0].split(" ")
          # Item name
          out = ""
          if itemInfo[0].endswith("x") and itemInfo[0][:-1].isdigit(): out = " ".join(itemInfo[1:-1])
          elif  itemInfo[-1].endswith(")"): out = " ".join(itemInfo[:-1])
          else: out = " ".join(itemInfo)
          # BP?
          if itemInfo[-1] == "(Blueprint)": out = out.title() + " BP"
          else: out = out.title()
        ## Node
        else:
          nodeInfo = info[-2]
          out = nodeInfo[:nodeInfo.index("(")].strip() + ", " + unwrapParen(nodeInfo)
      ### invasion
      else:
        info = i[2].text.split(" - ")
        side = info[0].split("VS.")
        ## Item
        if (category == "item"):
          # vs Infested
          if len(side) == 1:
            itemInfo = side[0].split(" ")
            if itemInfo[0].endswith("x") and itemInfo[0][:-1].isdigit(): out = " ".join(itemInfo[1:])
            else: out = " ".join(itemInfo)
          # vs Corpus/Grineer
          else:
            leftInfo = side[0]
            leftFaction = leftInfo[:leftInfo.index("(")].strip()
            leftItem = unwrapParen(leftInfo).split(" ")
            rightInfo = side[1]
            rightItem = unwrapParen(rightInfo).split(" ")
            if faction == leftFaction:
              if leftItem[0].endswith("x") and leftItem[0][:-1].isdigit(): out = " ".join(leftItem[1:])
              else: out = " ".join(leftItem)
            else:
              if rightItem[0].endswith("x") and rightItem[0][:-1].isdigit(): out = " ".join(rightItem[1:])
              else: out = " ".join(rightItem)
        ## node
        else:
          nodeInfo = info[-1]
          place = nodeInfo[:nodeInfo.index("(")].strip()
          if place.startswith("PHORID SPAWN"): place = place[13:]
          planet = unwrapParen(nodeInfo)
          out = place + ", " + planet
  return str(out).replace("Blueprint", "BP")

##### Convert item to list of alert roles
def convert_alert(data, ID, command, faction):
  ### Read alert.txt
  lines = fileData_code("alert")
  if not lines: return []
  itemName = convert("item", data, ID, command, faction)
  for line in lines:
    conv = line.split(":")
    if (len(line) > 1 and
        ((conv[0] in rstrSlash(data)) or
         (conv[0] in itemName))):
      return conv[1].split(",")
  return []

##### Translate converted string
def convert_kr(inStr):
  i = 0
  inStrs = inStr.split()
  outStrs = []
  ### Until end of string
  while i < len(inStrs):
    # J = end of string
    j = len(inStrs)
    ### While at least one word
    while j > i:
      ### If found, translate and move to next words
      sample = " ".join(inStrs[i:j])
      if sample in g.enkrDict.keys():
        outStrs.append(g.enkrDict[sample])
        i = j
        break
      ### If not found, decrease word count
      j -= 1
      ### If word count = 0, do not translate and move on
      if i == j:
        outStrs.append(inStrs[i])
        i += 1
        break
  return " ".join(outStrs)

##### Conversion from data string to readable string
def convert(category, data, ID=-1, command="", faction="", kr=False):
  out = ""
  if category == "node": out = convert_node(data, ID, command, faction)
  elif category == "item": out = convert_item(data, ID, command, faction)
  elif category == "mission": out = convert_mission(data)
  elif category == "faction": out = convert_faction(data)
  elif category == "fissure": out = convert_fissure(data)
  elif category == "sortieBoss": out = convert_sortieBoss(data)
  elif category == "sortieMod": out = convert_sortieMod(data)
  elif category == "alert": out = convert_alert(data, ID, command, faction)

  return (convert_kr(out) if kr else out)

########## Time ##########

def now_int(): return int(time.time())
def now_datetime(): return datetime.datetime.now()
def now_ymdhms(): return now_datetime().strftime(DATETIME_YMDHMS)

########## Discord ##########

async def msg(dest, text):
  if len(text) > 2000: logging.warning("msg:Size of text longer than 2000. Ignored.")
  elif text.strip():
    channel = dest
    if type(dest) == str: channel = client.get_channel(dest)
    if type(dest) == discord.Message: channel = dest.channel
    await client.send_message(channel, text.strip())
  else: logging.warning("msg:Size of text is 0.")

async def msgs(dest, texts, sep="\n", *, pre="", post="", box=-1):
  if box == 0: bx = lambda x: box_data(x)
  elif box == 1: bx = lambda x: box1(x)
  elif box == 2: bx = lambda x: box2(x)
  elif box == 3: bx = lambda x: box3(x)
  else: bx = lambda x: x
  out = ""
  pre += "\n"
  for text in texts:
    if len(pre+bx(out+sep+text)) > 2000:
      await msg(dest, pre+bx(out))
      pre = ""
      out = ""
    out += sep+text
    out = out.strip(sep)
  if out and len(pre+bx(out)+post) > 2000:
    if len(pre+bx(out)) > 2000:
      await msg(dest, pre)
      await msg(dest, bx(out))
    else:
      await msg(dest, pre + bx(out))
    await msg(dest, post)
  elif out:
    await msg(dest, pre + bx(out) + post)
  elif pre or post:
    if len(pre+post) > 2000:
      await msg(dest, pre)
      await msg(dest, post)
    else:
      await msg(dest, pre + post)

async def reply(message, text):
  mention = message.author.mention
  await msg(message, mention + ", " + text)

async def pvtmsg(message, text):
  await client.send_message(message.author, text.strip())

async def msg_urllibError(message, e, *, url="", query=""):
  if e.code // 100 == 4:
    if query: await msg(message, "I cannot find any results with" + mono(query) + ". Try a different one.")
    else: await msg(message, "I failed to connect to the server. Contact the developers about this problem.")
  if e.code // 100 == 5:
    if url: await msg(message, "The server seems to be offline. Go to " + wrapLink(url) + " to see if the server is really offline.")
    else: await msg(message, "The server seems to be offline.")

def msgText_forbidden(message, kr=False):
  if kr: return ("\n제게 " + mono(message.server.name) + "서버의 " + mono(message.channel.name) +
                 "채널에서 메세지를 보낼 권한이 없기 때문에 개인 메세지로 보냈습니다.")
  return ("\nPrivate message is sent because I do not have permission to send messages to " +
          mono(message.channel.name) + " Channel from " + mono(message.server.name) + " Server.")

async def msg_wait(message):
  text = "Please wait for a bit to process data and try " + mono(message.content) + " again."
  try: await msg(message, text)
  except discord.errors.Forbidden: await pvtmsg(message, text+msgText_forbidden(message))

async def msg_UNoPerm(message, kr=False):
  text = (mono(message.content) + "명령을 할 권한이 없습니다." if kr else
          "You do not have permission to perform " + mono(message.content) + ".")
  try: await msg(message, text)
  except discord.errors.Forbidden: await pvtmsg(message, text+msgText_forbidden(message, kr))

async def msg_PvtDisabled(message, kr=False):
  if isPvt(message):
    text = ("개인 메세지로 " + mono(message.content) + "명령을 쓸 수 없습니다." if kr else
            mono(message.content) + " is disabled in DM.")
    await msg(message, text)
  else: logging.error("msg_PvtDisabled:message is not private")

async def msg_INoPerm(message, kr=False):
  text = ("저한테 " + mono(message.content) + "명령을 실행할 권한이 없습니다." if kr else
          "I do not have permission to perform " + mono(message.content) + ".")
  try: await msg(message, text)
  except discord.errors.Forbidden: await pvtmsg(message, text+msgText_forbidden(message, kr))

async def msg_help(message, fileName, l):
  out = []
  for q in l:
    out.append(fileData_line(fileName, PREFIX + q))
  await msg(message, "\n".join(out))

async def edit(message, text):
  if text.strip(): await client.edit_message(message, text.strip())
  else: await delmsg(message)

async def react(message, emoji, essential=False):
  try: await client.add_reaction(message, emoji)
  except discord.errors.Forbidden:
    if essential: await msg(message, emoji)

async def embed(message, title="", desc="", url="", timestamp=discord.Embed.Empty,
                colour=0xFFFFFF, footer="", footericon="", image="", thumbnail="",
                author="", authorurl="", authoricon="", fields=[]):
  e = discord.Embed(title=title, description=desc, url=url, timestamp=timestamp, colour=colour)
  e.set_footer(text=footer, icon_url=footericon)
  e.set_image(url=image)
  e.set_thumbnail(url=thumbnail)
  e.set_author(name=author, url=authorurl, icon_url=authoricon)
  for field in fields:
    e.add_field(name=field[0], value=field[1])
  await client.send_message(message.channel, embed=e)

async def delmsg(messages):
  ### Single message
  if type(messages) == discord.Message:
    try: await client.delete_message(messages)
    except discord.errors.NotFound: pass
  ### 1 message
  elif len(messages) == 1:
    try: await client.delete_message(messages[0])
    except discord.errors.NotFound: pass
  ### 2+ message
  else:
    # Separate between (14 days) old and new
    dt_14d = now_datetime() - datetime.timedelta(days=14)
    oldList = []
    newList = []
    for msg in messages:
      if dt_14d < msg.timestamp: newList.append(msg)
      else: oldList.append(msg)
    # Individually delete old
    for msg in oldList:
      try: await client.delete_message(msg)
      except discord.errors.NotFound: pass
    # Bulk-delete new (max of 100 at a time)
    i = 0
    while i < len(newList):
      if len(newList[i:(i+99)]) == 1:
        try: await client.delete_message(newList[i])
        except discord.errors.NotFound: pass
      else:
        try: await client.delete_messages(newList[i:(i+99)])
        except discord.errors.NotFound: logging.warning("delmsg:discord.errors.NotFound")
      i += 100

async def delmsgs(channel,limit=1000,*,before=None,after=None,around=None,reverse=False,cond=None):
  delList = []
  messages = client.logs_from(channel, limit=limit,
                          before=before, after=after, around=around,
                          reverse=reverse)
  async for message in messages:
    if (not cond) or (cond and cond(message)): delList.append(message)
  await delmsg(delList)

def isMyMsg(message):
  return (message.author == client.user)

def isNotMyMsg(message):
  return not isMyMsg(message)

def isBpin(message):
  return isMyMsg(message) and (message.content.startswith(EMOJI_PIN))

def isAlert(message):
  return isMyMsg(message) and (message.content.startswith(EMOJI_BELL))

def isNotBpin(message):
  return not isBpin(message)

def isPvt(message):
  return type(message.channel) == discord.PrivateChannel

def isPub(message):
  return not isPvt(message)

async def numBpin(message):
  out = 0
  async for log in client.logs_from(message.channel, limit=1000):
    if isBpin(log): out += 1
  return out

def perm(channel, user, perm):
  permList = ["administrator", "create_instant_invite", "manage_server", "manage_channels", "kick_members", "ban_members", "read_messages", "read_message_history", "send_messages", "send_tts_messages", "mention_everyone", "add_reactions", "embed_links", "attach_files", "manage_messages", "connect", "speak", "mute_members", "deafen_members", "move_members", "use_voice_activation", "change_nickname", "manage_nicknames", "manage_roles", "manage_webhooks", "manage_emojis"]
  pic = user.permissions_in(channel)
  if perm == permList[0]: return pic.administrator
  elif perm == permList[1]: return pic.create_instant_invite
  elif perm == permList[2]: return pic.manage_server
  elif perm == permList[3]: return pic.manage_channels
  elif perm == permList[4]: return pic.kick_members
  elif perm == permList[5]: return pic.ban_members
  elif perm == permList[6]: return pic.read_messages
  elif perm == permList[7]: return pic.read_message_history
  elif perm == permList[8]: return pic.send_messages
  elif perm == permList[9]: return pic.send_tts_messages
  elif perm == permList[10]: return pic.mention_everyone
  elif perm == permList[11]: return pic.add_reactions
  elif perm == permList[12]: return pic.embed_links
  elif perm == permList[13]: return pic.attach_files
  elif perm == permList[14]: return pic.manage_messages
  elif perm == permList[15]: return pic.connect
  elif perm == permList[16]: return pic.speak
  elif perm == permList[17]: return pic.mute_members
  elif perm == permList[18]: return pic.deafen_members
  elif perm == permList[19]: return pic.move_members
  elif perm == permList[20]: return pic.use_voice_activation
  elif perm == permList[21]: return pic.change_nickname
  elif perm == permList[22]: return pic.manage_nicknames
  elif perm == permList[23]: return pic.manage_roles
  elif perm == permList[24]: return pic.manage_webhooks
  elif perm == permList[25]: return pic.manage_emojis

def perm_mngMsg(message): return perm(message.channel, message.author, "manage_messages")
def perm_mngRole(message): return perm(message.channel, message.author, "manage_roles")

def isDev(ID): return servData_isDev(ID)

async def msgExc():
  traceback.print_exc()
  await msgs(DATA_CHAN["exception"], traceback.format_exc().splitlines(), pre="An exception has occurred.", box=0)

########## onMsg (Discord) ##########

async def onMsg_help(message, param=None, kr=False):
  if param: await msgs(message.author, fileData_read("help_" + param + ("_kr" if kr else "")).split("<n>"))
  else: await msgs(message.author, fileData_read("help" + ("_kr" if kr else "")).split("<n>"))
  if isPub(message):
    text = ("개인 메세지함을 열어보세요." if kr else "check your direct message inbox.")
    await reply(message, text)

async def onMsg_feedback(message, text, kr=False):
  t = message.author.name + "#" + message.author.discriminator + " says:"
  await msgs(DATA_CHAN["feedback"], [t, text])
  text = ("피드백을 보냈습니다. 감사합니다." if kr else "your feedback has been sent. Thank you.")
  await reply(message, text)

async def onMsg_time(message):
  await msg(message, "Current Time: " + mono(now_ymdhms() + " UTC"))

async def onMsg_bpin(message, text):
  # Delete old bpin
  await delmsgs(message.channel, cond=isBpin)
  # Add bpin message
  await msg(message, EMOJI_PIN + " " + text)
  if isPub(message): await delmsg(message)

async def onMsg_bpin_move(message):
  async with lock_bpin:
    try:
      async for log in client.logs_from(message.channel, limit=1):
        if isBpin(log): return
      ### Repost bpin
      moved = False
      async for log in client.logs_from(message.channel, limit=1000):
        if isBpin(log):
          if not moved: await msg(message, log.content)
          await delmsg(log)
          moved = True
    except discord.errors.NotFound: pass

async def onMsg_bpin_clear(message):
  ### Clear BPin + command
  await delmsgs(message.channel, cond=isBpin)
  await delmsg(message)

########## onMsg (Delete) ##########

async def onMsg_delete(message, count):
  ### BPin count
  nBpin = await numBpin(message)
  ### Delete log + command
  await delmsgs(message.channel, limit=count+1+nBpin, cond=isNotBpin)

async def onMsg_delete_day(message, day):
  ### Time
  time = now_datetime() - datetime.timedelta(days=day)
  ### Delete log + command
  await delmsgs(message.channel, before=time, cond=isNotBpin)
  await delmsg(message)

async def onMsg_delete_auto(message, day, kr=False):
  await min_delete_set(message.channel.id, day, message.server.name + "\n" + message.channel.name)
  text = ("자동삭제 기능이 활성화 되었습니다. " + str(day) + "일 이상 지난 메세지는 자동으로 지워집니다." if kr else
          "Automatic deletion enabled. Messages older than " + str(day) + " days will be deleted automatically.")
  await msg(message, text)

async def onMsg_delete_auto_clear(message):
  await min_delete_clear(message.channel.id)
  text = ("자동삭제 기능이 비활성화 되었습니다." if kr else
          "Automatic deletion disabled.")
  await msg(message, text)

########## onMsg (Warframe) ##########

async def onMsg_drain(message, eff, dur, drain="-1"):
  ### Efficiency float
  effF = 0.0
  if eff[-1] == "%": effF = float(eff[:-1])/100
  elif float(eff) >= 10: effF = float(eff)/100
  else: effF = float(eff)
  ### Duration float
  durF = 0.0
  if dur[-1] == "%": durF = float(dur[:-1])/100
  elif float(dur) >= 10: durF = float(dur)/100
  else: durF = float(dur)
  ### Drain efficiency
  dEff = (2.0-effF)/durF
  dEffCap = dEff
  dEffStr = ""
  if dEff < 0.25:
    dEffCap = 0.25
    dEffStr = "(" + str(200-round(dEff*100, 2)) + "% before cap) "
  elif dEff > 1.75:
    dEffCap = 1.75
    dEffStr = "(" + str(200-round(dEff*100, 2)) + "% before cap) "
  drainF = float(drain)
  text = (str(round(effF*100, 2)) + " Efficiency | " + str(round(durF*100, 2)) + " Duration\n" +
          ARROW_RIGHT + " " + str(200-round(dEffCap*100, 2)) + "% Drain Efficiency " + dEffStr)
  if drainF > 0: text += ("\n" + str(round(drainF, 2)) + " Energy/Sec\n" +
                          ARROW_RIGHT + " " + str(round(drainF*dEffCap, 2)) + " Energy/Sec")
  await msg(message, box1(text))

def alert_block(alert, brief=False, kr=False):
  ### time
  timeLeft = int(alert["Expiry"]["$date"]["$numberLong"])//1000 - now_int()
  mInfo = alert["MissionInfo"]
  ID = alert["_id"]["$oid"]
  ### Type
  mType = convert("mission", mInfo["missionType"], kr=kr)
  ### Faction
  faction = convert("faction", mInfo["faction"], kr=kr)
  ### Level
  minLevel = str(mInfo["minEnemyLevel"])
  maxLevel = str(mInfo["maxEnemyLevel"])
  ### Node
  node = convert("node", mInfo["location"], ID, "alert", kr=kr)
  ### NM
  nm = ""
  try:
    if bool(mInfo["nightmare"]): nm = (" (나이트메어)" if kr else " (Nightmare)")
  except KeyError: pass
  ### Rewards
  reward = mInfo["missionReward"]
  item = ""
  cItem = ""
  credit = ""
  # Item
  try:
    for itemObj in reward["items"]:
      item += POINT + " " +  convert("item", itemObj, ID, "alert", kr=kr) + "\n"
  except KeyError: pass
  # Counted Item
  try:
    for cItemObj in reward["countedItems"]:
      c = cItemObj["ItemCount"]
      cItem += (POINT + " " + ("" if c == 1 else str(c) + " ") +
                convert("item", cItemObj["ItemType"], ID, "alert", kr=kr) + "\n")
  except KeyError: pass
  # Credit
  try:
    credit = POINT + " " + digitComma(reward["credits"]) + " cr\n"
  except KeyError: pass
  ### Credit only?
  itemExists = True
  if (not item) and (not cItem): itemExists = False
  ### Merge
  if brief:
    if kr:
      text = box1(mType + " " + wrapParen(faction) + ": " + dhms(timeLeft, kr=kr)+ "\n" +
                  item + cItem)
      return (text if itemExists else "")
    text = box1(mType + " " + wrapParen(faction) + " for " + dhms(timeLeft)+ "\n" +
                item + cItem)
    return (text if itemExists else "")
  if kr:
    return box1(mType + " " + wrapParen(faction) + ": " + node + "\n" +
               "레벨 " + minLevel + "-" + maxLevel + nm + "\n" +
               item + cItem + credit +
               "남은시간 " + dhms(timeLeft, kr=kr))
  return box1(mType + " " + wrapParen(faction) + " at " + node + "\n" +
             "Level " + minLevel + "-" + maxLevel + nm + "\n" +
             item + cItem + credit +
             "Alert ends in " + dhms(timeLeft))

def getStr_alert(brief=False, kr=False):
  text = ""
  count = 0
  for alert in wfAPI()["Alerts"]:
    block = alert_block(alert, brief, kr)
    if block:
      text += block
      count += 1
  if kr: return "**얼럿** (" + ("크레딧 얼럿 제외. " if brief else "") + str(count) + "개)\n" + text
  return "**Alert** (" + ("Excludes credit-only alerts. " if brief else "") + str(count) + " active)\n" + text

def invasion_p(invasion):
  return (invasion["Count"]+invasion["Goal"])/(invasion["Goal"]*2)

def invasion_block(invasion, brief=False, kr=False):
  p = invasion_p(invasion)
  info = ""
  ID = invasion["_id"]["$oid"]
  ### Node
  node = convert("node", invasion["Node"], ID, "invasion", kr=kr)
  aFaction = convert("faction", invasion["DefenderMissionInfo"]["faction"], kr=kr)
  dFaction = convert("faction", invasion["AttackerMissionInfo"]["faction"], kr=kr)
  if invasion["DefenderMissionInfo"]["faction"] == "FC_INFESTATION": p *= 2
  ### Attack
  # Item
  ais = [] # Attack Items
  try:
    if len(invasion["AttackerReward"]) > 0:
      for aItemObj in invasion["AttackerReward"]["items"]:
        ais.append(convert("item", aItemObj["ItemType"], ID, "invasion", aFaction, kr=kr))
  except KeyError: pass
  # Counted Item
  try:
    if len(invasion["AttackerReward"]) > 0:
      for acItemObj in invasion["AttackerReward"]["countedItems"]:
        c = acItemObj["ItemCount"]
        ais.append(("" if c == 1 else str(c) + " ") +
                   convert("item", acItemObj["ItemType"], ID, "invasion", aFaction, kr=kr))
  except KeyError: pass
  ### Defense
  # Item
  dis = [] # Defense Items
  try:
    for ditemObj in invasion["DefenderReward"]["items"]:
      dis.append(convert("item", dItemObj["ItemType"], ID, "invasion", dFaction, kr=kr))
  except KeyError: pass
  # Counted Item
  try:
    for dcItemObj in invasion["DefenderReward"]["countedItems"]:
      c = dcItemObj["ItemCount"]
      dis.append(("" if c == 1 else str(c) + " ") +
                 convert("item", dcItemObj["ItemType"], ID, "invasion", dFaction, kr=kr))
  except KeyError: pass
  ### Faction + progress
  # Progress
  perc = round((p*200-100),2)
  lArrow = ""
  rArrow = ""
  if perc > 0: rArrow = " " + ">"*int(perc*3/100+1)
  elif perc < 0: lArrow = "<"*int(abs(perc)*3/100+1) + " "
  percStr = str(abs(perc)) + "%"
  lPercStr = str(round(p*100,2)) + "%"
  rPercStr = str(round(100 - p*100,2)) + "%"
  # Node
  pp = node.split(", ")
  # Output
  if brief:
    infoList = [[] for i in range(2)]
    infoList[0].append(wrapParen(lPercStr) + " " + aFaction)
    infoList[1].append(dFaction + " " + wrapParen(rPercStr))
    ### Items
    while len(ais) + len(dis) > 0:
      if (len(ais) > 0) and (len(dis) > 0):
        infoList[0].append(ais[0] + " " + POINT)
        infoList[1].append(POINT + " " + dis[0])
        del ais[0]
        del dis[0]
      elif len(ais) > 0:
        infoList[0].append(ais[0] + " " + POINT)
        infoList[1].append("")
        del ais[0]
      else:
        infoList[0].append("")
        infoList[1].append(POINT + " " + dis[0])
        del dis[0]
    mSpace = maxGLen(infoList[0])
    info += " "*round(mSpace-glen(infoList[0][0])) + infoList[0][0] + " vs " + infoList[1][0] + "\n"
    for i in range(1, len(infoList[0])):
      info += " "*round(mSpace-glen(infoList[0][i])) + infoList[0][i] + " "*4 + infoList[1][i] + "\n"
  else:
    info += ((lmr(aFaction, node, dFaction) if len(pp) == 1 else lmmmr(aFaction, pp[0], ", ", pp[1], dFaction)) + "\n" +
             lmmmr(lPercStr, lArrow, percStr, rArrow, rPercStr) + "\n" +
             progBar(p) + "\n")
    ### Items
    while len(ais) + len(dis) > 0:
      if (len(ais) > 0) and (len(dis) > 0):
        info += lr(POINT + " " + ais[0], dis[0] + " " + POINT) + "\n"
        del ais[0]
        del dis[0]
      elif len(ais) > 0:
        info += lr(POINT + " " + ais[0], "") + "\n"
        del ais[0]
      else:
        info += lr("", dis[0] + " " + POINT) + "\n"
        del dis[0]
  ### Box
  return box1(info.rstrip())

def getStrList_invasion(brief=False, kr=False):
  textList = []
  count = 0
  ### All invasions (0 < p < 1)
  for invasion in wfAPI()["Invasions"]:
    p = invasion_p(invasion)
    if (0.0 <= p) and (p <= 1.0):
      count += 1
      textList.append(invasion_block(invasion, brief, kr=kr))
  ### Text
  text = ("**침공** (" + str(count) + "개)\n"
          if kr else
          "**Invasion** (" + str(count) + " active)\n")
  ### Return
  return [text] + textList

async def onMsg_invasion(message, brief=False, kr=False):
  textList = getStrList_invasion(brief=brief, kr=kr)
  await msgs(message, textList, sep="")

def getStr_sortie(brief=False, kr=False):
  text = ""
  for sortie in wfAPI()["Sorties"]:
    ### time
    timeLeft = int(sortie["Expiry"]["$date"]["$numberLong"])//1000 - now_int()
    ### Boss
    boss = convert("sortieBoss", str(sortie["Boss"]), kr=kr)
    subText = ""
    for mInfo in sortie["Variants"]:
      ### Node
      node = convert("node", mInfo["node"], kr=kr)
      ### Type
      mType = convert("mission", str(mInfo["missionType"]), kr=kr)
      ### Modifier
      modifier = convert("sortieMod", str(mInfo["modifierType"]), kr=kr)
      ### Merge
      subText += "\n" + POINT + " " + mType + " " + wrapParen(modifier) + ("" if brief else " at " + node)
    if kr:
      text = ("**출격**\n" +
              box1("# 보스: " + boss + subText + "\n" +
                   "남은시간 " + dhms(timeLeft, kr=kr)))
    else:
      text = ("**Sortie**\n" +
              box1("# Boss: " + boss + subText + "\n" +
                   "Sortie ends in " + dhms(timeLeft)))
  if not text: return ("현재 출격이 없습니다." if kr else "Sortie is not available right now.")
  return text

async def onMsg_voidTrader(message, kr=False):
  for trader in wfAPI()["VoidTraders"]:
    tStart = int(trader["Activation"]["$date"]["$numberLong"])//1000
    tEnd = int(trader["Expiry"]["$date"]["$numberLong"])//1000
    tCur = now_int()
    ### Arrived
    if (tStart < tCur) and (tCur < tEnd):
      pre = ("보이드 상인은 " + convert("node",trader["Node"], kr=kr)+"에 있습니다" if kr else
             "Void Trader at " + convert("node",trader["Node"], kr=kr))
      # item
      itemTypeList = []
      ducatList = []
      creditList = []
      for item in trader["Manifest"]:
        itemTypeList.append(convert("item", item["ItemType"], command="baro", kr=kr))
        ducatList.append(str(item["PrimePrice"]) + " du")
        credit = str(item["RegularPrice"]/1000)
        if credit.endswith(".0"): credit = credit[:-2]
        creditList.append(credit + "k cr")
      numItem = len(itemTypeList);
      pre += (": " + str(numItem) + "개 판매중." if kr else
              ": " + str(numItem) + " item" + ("" if numItem == 1 else "s") + " for sale.")
      # Paste items
      mlDucat = round(maxGLen(ducatList))
      mlCredit = round(maxGLen(creditList))
      texts = []
      for i in range(numItem):
        texts.append(ducatList[i].rjust(mlDucat) + " + " + creditList[i].rjust(mlCredit) + " - " + itemTypeList[i])
      post = ("보이드 상인은 " + dhms(tEnd - tCur, kr=kr) + "후 떠납니다." if kr else
              "Void Trader will be departing in " + dhms(tEnd - tCur))
      await msgs(message, texts, pre=pre, post=post, box=1)
    ### Did not arrive
    else:
      if kr: await msg(message, "보이드 상인은 " + dhms(tStart - tCur, kr=kr) + "후 " + convert("node",trader["Node"], kr=kr) + "(으)로 옵니다.")
      else: await msg(message, "Void Trader will be coming at " + convert("node",trader["Node"]) + " in " + dhms(tStart - tCur))

def fissure_block(fissure, kr=False):
  timeLeft = int(fissure["Expiry"]["$date"]["$numberLong"])//1000 - now_int()
  nodeData = fissure["Node"]
  node = convert("node", nodeData, kr=kr)
  level = convert("fissure", fissure["Modifier"], kr=kr)
  ### Get Mission Type
  mType = (g.nodeMTypeDict[fissure["Node"]] if nodeData in g.nodeMTypeDict else "???")
  if kr and (mType in g.enkrDict.keys()): mType = g.enkrDict[mType]
  if kr: return (level + " (" + mType + "): " + node + " - " + dhms(timeLeft, kr=kr) + " 남음")
  return (level + " (" + mType + ") at " + node + " for " + dhms(timeLeft))

def fissure_sortKey(s):
  if any([s.startswith(x) for x in ["Lith","리스"]]): return 1
  if any([s.startswith(x) for x in ["Meso","메소"]]): return 2
  if any([s.startswith(x) for x in ["Neo","네오"]]): return 3
  return 4

def getStr_fissure(kr=False):
  count = 0
  texts = []
  for fissure in wfAPI()["ActiveMissions"]:
    count += 1
    texts.append(fissure_block(fissure, kr=kr))
  text = "\n".join(sorted(texts, key=fissure_sortKey))
  if kr:return "**보이드 균열** (" + str(count) + "개)\n" + box1(text.strip())
  return "**Void Fissure** (" + str(count) + " active)\n" + box1(text.strip())

async def onMsg_cetus(message, kr=False):
  await msg(message, getStr_cetus(kr=kr))

def getStr_cetus(brief=False, kr=False):
  i = now_int()
  t = now_cetus(i)
  # It's high noon.
  if t == 6000: return "**" + ("세투스" if kr else "Cetus") + "**\n" + box_data(ART_DEADEYE)

  if isCetusNight(i):
    text = (("0 밤 0" if kr else "0 night time 0") + "\n")
  else:
    text = (("O 낮 O" if kr else "O day time O") + "\n")
  if not brief:
    text = " "*(17-round(glen(text.strip())/2)) + text
    text += (" "*(int(t/300) + (23 if isCetusNight(i) else (-9 if t < 6000 else -8))) + ARROW_DOWN + "\n" +
             "[OOOOOOOOOO OOOOOOOOOO|0000000000]" + "\n" +
             ("(각 원은 5분)" if kr else "(each circle represents 5 minutes.)") + "\n")

  if isCetusNight(i):
    text += (("지난 시간: " if kr else "Time Passed: ") + dhms(t, kr) + "\n" +
             ("낮까지 남은 시간: " if kr else "Time Until Day: ") + dhms(3000-t, kr))
  else:
    text += (("지난 시간: " if kr else "Time Passed: ") + dhms(t-3000, kr) + "\n" +
             ("밤까지 남은 시간: " if kr else "Time Until Night: ") + dhms(9000-t, kr))
  return "**" + ("세투스" if kr else "Cetus") + "**\n" + box3(text)

async def onMsg_active(message, kr=False):
  l = [getStr_alert(brief=True, kr=kr),
       "".join(getStrList_invasion(brief=True, kr=kr)),
       getStr_fissure(kr=kr),
       getStr_sortie(brief=True, kr=kr),
       getStr_cetus(brief=True, kr=kr)]
  await msgs(message, l, sep="")

def pc_block(data):
  text = data["Title"]
  item = data["Title"][:-6]
  # Supply/Demand
  if len(data["SupDem"]) == 2:
    supply = data["SupDem"][0]
    demand = data["SupDem"][1]
    text += " (Supply: " + str(supply) + "% | Demand: " + str(demand) + "%)"
  text += "\n"

  nameList = []
  valueList = []
  ducatList = []
  ### Var for Set/BP
  setValue = ""
  bpValue = ""
  ### Read thru components
  for comp in data["Components"]:
    name = comp["name"]
    value = -1
    if comp["comp_val_rt"]: value = round(float(comp["comp_val_rt"]), 2)
    # Set
    if name == "Set": setValue = value
    # BP
    elif name == "Blueprint": bpValue = value
    else:
      nameList.append(POINT + " " + name)
      valueList.append(value)
      ducatList.append(g.ducatDict[item][name] if name in g.ducatDict.get(item,{}).keys() else -1)
  ### Append Set/BP to the front
  if bpValue:
    nameList.insert(0, POINT + " BP")
    valueList.insert(0, bpValue)
    ducatList.insert(0, (g.ducatDict[item]["BP"] if "BP" in g.ducatDict.get(item,{}).keys() else -1))
  if setValue:
    nameList.insert(0, "# Set")
    valueList.insert(0, setValue)
    ducatList.insert(0, (sum(g.ducatDict[item].values()) if item in g.ducatDict.keys() else -1))
  ### Compute Ducat/Value
  vdStrList = []
  for i in range(len(ducatList)):
    vdStrList.append("" if ducatList[i] < 0 or valueList[i] <= 0 else "%.2f" % (ducatList[i] / valueList[i]))
  ### Paste
  mlName = round(maxGLen(nameList))
  valStrList = [("%.2f" % x) for x in valueList]
  mlValue = round(maxGLen(valStrList))
  mlDucat = round(maxGLen(ducatList))
  mlVD = round(maxGLen(vdStrList))
  if len(nameList) > 0:
    for i in range(len(nameList)):
      valStr = "N/A" if valueList[i] < 0 else valStrList[i].rjust(mlValue) + " pl"
      ducStr = "" if ducatList[i] < 0 else (" - " + str(ducatList[i]).rjust(mlDucat) + " du" +
                                            ("" if valueList[i] <= 0 else " (" + vdStrList[i].rjust(mlVD) + " du/pl)"))
      text += (nameList[i].ljust(mlName) + " - " + valStr + ducStr + "\n")
  else: text += "Not Available"
  return text.strip()

async def onMsg_pc(message, args):
  ### API
  try: pcSet = wfPC()
  except urllib.error.HTTPError as e:
    await msg_urllibError(message, e, url=URL_NEXUS_MAIN)
    return
  query = args.lower()
  simStr = getSimStr(query, [x["Title"].lower() for x in pcSet])
  text = ""
  for data in pcSet:
    if data["Title"].lower() == simStr:
      text = pc_block(data)
      break
  ### Send msg
  dne = ("" if query == simStr else
         "\n" + mono(args) + " does not exist in the database. Check the link above. Searching for the closest item name instead...")
  if not text: await msg(message, "No data for " + mono(args.title()))
  else: await msg(message, ("Data provided by NexusStats <https://nexus-stats.com/>" + dne + box1(text)))

#TODO: async def onMsg_stat(message, *, bHealth=None, bShield=None, bArmor=None, bDamage=None, bAffinity=None, bLevel=None, cLevel=None)
# Current Health = Base Health × ( 1 + ( Current Level − Base Level )^2 × 0.015 )
# Current Shield = Base Shield × ( 1 + ( Current Level − Base Level )^2 × 0.0075 )
# Current Armor = Base Armor × ( 1 + ( Current Level − Base Level )^1.75 × 0.005 )
# Current Damage = Base Damage × ( 1 + ( Current Level − Base Level )^1.55 × 0.015 )
# Current Affinity = floor ( Base Affinity × ( 1 + Current Level^0.5 × 0.1425 ) )
# Current Effective Hitpoints = Current Health × ( 1 + Current Armor ÷ 300 ) + Current Shield

async def onMsg_armor(message, armor):
  reduction = armor / (armor + 300.0) * 100
  text = str(reduction) + "% Reduction"
  await msg(message, box1(text))

async def onMsg_wikia(message, query):
  url = URL_WIKIA_PREFIX + query.replace(" ","%20") + URL_WIKIA_SUFFIX
  try:
    j = api_json(url)
    await msg(message, j["items"][0]["url"])
  except urllib.error.HTTPError as e: await msg_urllibError(message, e, query=query)

def dropStr_sortKey(s):
  return s.replace("Intact", "1").replace("Exceptional", "2").replace("Flawless", "3").replace("Radiant", "4")

def dropStr_rec(d, indent=0):
  if type(d) == set:
    return [" or ".join(d)]
  else:
    l = []
    for k in sorted(d.keys(), key=dropStr_sortKey):
      v = d[k]
      sub = dropStr_rec(v, indent + 2)
      if len(sub) == 1:
        l.append(" "*indent + k + " - " + sub[0].strip())
      else:
        l.append(" "*indent + k)
        l += sub
    return l

async def onMsg_drop(message, args):
  query = args.lower()
  key = getSimStr(query, g.dropDict.keys())
  l = []
  for col, data in g.dropDict[key]:
    l.append("# " + " - ".join(col))
    l += dropStr_rec(data)
  pre = ("Data provided by <http://drops.warframestat.us/>\n" +
         "Official drop table (forum thread): <https://forums.warframe.com/topic/809777-warframe-drop-rates-data/>")
  pre += ("" if query == key.lower() else
         "\n" + mono(args) + " does not exist in the database. Check the link above. Searching for the closest item name instead...")
  await msgs(message, [key] + l, pre=pre, box=1)

async def onMsg_raid(message, name, kr=False):
  ### JSON
  url = URL_TRIALS_PREFIX + name + URL_TRIALS_SUFFIX
  api = api_json(url)
  ### Stat
  if api:
    ### Evaluate
    s = {} # {type:[nTrial/nWon/Time/nKill/nDeath/nHost/nPlayer]}
    f = {} # {type:fastest}
    r = {} # {type:[data]}
    for rData in api:
      rType = rData["type"]
      ## init
      if rType not in r.keys():
        r[rType] = []
        s[rType] = [0] * 7
        f[rType] = -1
      ## Recent
      if len(r[rType]) < LIMIT_RAIDRECENT: r[rType].append(rData)
      ## Stat
      s[rType][0] += 1 # nTrial
      if rData["objective"] == "VICTORY":
        s[rType][1] += 1 # nWon
        timeArr = [int(x) for x in rData["time"].split(":")]
        timeInt = (timeArr[0] * 60 + timeArr[1]) * 60 + timeArr[2]
        s[rType][2] += timeInt # Time
        s[rType][3] += rData["kills"] # nKill
        s[rType][4] += rData["deaths"] # nDeath
        s[rType][5] += 1 if name.lower() == rData["host"].lower() else 0 # nKill
        s[rType][6] += (len(rData["players"]) + 1)
        ## Fastest
        f[rType] = timeInt if f[rType] < 0 else min(timeInt, f[rType]) # Fastest
    mss = []
    ### Message String
    ts = ("데이터 제공자: " if kr else "Data provided by ") + "<https://trials.wf>"
    for rType in r.keys():
      typeStr = ({"lor":"응보의 법칙", "lornm":"응보의 법칙: 나이트메어", "jv":"조르다스 평결"} if kr else
                 {"lor":"The Law of Retribution", "lornm":"The Law of Retribution: Nightmare", "jv":"Jordas Verdict"})
      ms = ("# " + (typeStr[rType] if rType in typeStr else rType) + "\n" +
            ("성공률" if kr else "Clear Rate") + ": " + str(int(s[rType][1]*100/s[rType][0]+0.5)) + "% (" + str(s[rType][1]) + "/" + str(s[rType][0]) + ")\n" +
            ("최단시간" if kr else "Best Time") + ": " + dhms(f[rType], kr=kr) + "\n" +
            ("평균시간" if kr else "Average Time") + ": " + dhms(int(s[rType][2]/s[rType][1]+0.5), kr=kr) + "\n" +
            ("평균 방 킬/데스" if kr else "Average Team Kills/Deaths") + ": " + str(int(s[rType][3]/s[rType][1]+0.5)) + " / " + str(int(s[rType][4]/s[rType][1]+0.5)) + "\n" +
            ("평균인원" if kr else "Average Number of Members") + ": " + str(round(s[rType][6]/s[rType][1], 1)) + "\n" +
            ("방장률" if kr else "Hosting Rate") + ": " + str(int(s[rType][5]*100/max(1, s[rType][1])+0.5)) + "% (" + str(s[rType][5]) + "/" + str(s[rType][1]) + ")")
      mss.append(box1(ms))
    ### Message
    await msgs(message, mss, sep="", pre=ts)
  elif kr:
    await msg(message, ("데이터 제공자: <https://trials.wf>\n" +
                        mono(name) + "에 대한 정보가 없습니다. (유저를 찾을 수 없거나 유저가 토벌전을 안했을 수도 있습니다.)"))
  else:
    await msg(message, ("Data provided by <https://trials.wf>\n" +
                        "No data for " + mono(name) + " (Either no such player exists or the player has not done the raid.)"))

########## onMsg (Notification) ##########

async def onMsg_sub_list(message):
  post = ("Any listed roles can be subscribed if the server provides them.\n" +
          "If you subscribe to a role, you are subscribed to all indented roles under the role.\n" +
          "e.g. If you subscribe to `Pomato`, you are subscribed to `Reactor`, `Catalyst`, and `Exilus`.")
  cetusRoleList = ["^ Cetus Day/Night time in Cetus",
                   "  > Day Day time in Cetus",
                   "  > Night Night time in Cetus"]
  await msgs(message.author, fileData_read("alert_list").splitlines() + cetusRoleList, post=post, box=2)
  if isPub(message): await reply(message, "check your direct message inbox.")

async def onMsg_sub(message, role):
  ### Remove prefix if role starts with it
  if role.startswith(PREFIX_ROLE): role = role[1:]
  ### Get simRole
  simRole = getSimStr(role, getRoles())
  if role.lower() == simRole[1:].lower():
    ### For each server role
    for sRole in message.server.roles:
      if sRole.name == simRole:
        # Nothing if owned
        if sRole in message.author.roles:
          await react(message, EMOJI_EXCLAMATION)
          await reply(message, "you already have " + mono(sRole.name[1:]) + " role. Nothing has changed.")
        # Subscribe if not owned
        else:
          await client.add_roles(message.author, sRole)
          await reply(message, mono(sRole.name[1:]) + " role is added.")
        return
    ### role not found in server
    await react(message, EMOJI_NEG)
    await msg(message, mono(role) + " role does not exist in this server. Ask admins if they can set up the subscription.")
  else:
    await react(message, EMOJI_QUESTION)
    await msg(message, mono(role) + " role does not exist. Did you mean " + mono(simRole[1:]) + "?")

async def onMsg_unsub(message, role=""):
  ### Unsub a role
  if role:
    ### Remove prefix if role starts with it
    if role.startswith(PREFIX_ROLE): role = role[1:]
    ### Get simRole
    simRole = getSimStr(role, getRoles())
    if role.lower() == simRole[1:].lower():
      ### For each server role
      for sRole in message.server.roles:
        if sRole.name == simRole:
          # Unsub if owned
          if sRole in message.author.roles:
            await client.remove_roles(message.author, sRole)
            await reply(message, mono(sRole.name[1:]) + " role is removed.")
          # Nothing if not owned
          else:
            await react(message, EMOJI_EXCLAMATION)
            await reply(message, "you do not have " + mono(sRole.name[1:]) + " role. Nothing has changed.")
          return
      ### role not found in server
      await react(message, EMOJI_EXCLAMATION)
      await msg(message, mono(role) + " role does not exist in this server. Nothing has changed.")
    else:
      await react(message, EMOJI_QUESTION)
      await msg(message, mono(role) + " role does not exist. Did you mean " + mono(simRole[1:]) + "?")
  ### Unsub all
  else:
    for sRole in message.server.roles:
      if sRole.name in getRoles():
        await client.remove_roles(message.author, sRole)
    await reply(message, "All notification roles are removed.")

def getRoles_alert():
  lines = fileData_read("alert_list").splitlines()
  out = []
  for line in lines:
    # Strip
    line = line.strip()
    # index
    first = line.find(" ") + 1
    second = line[first:].find(" ") + first
    # append
    out.append(PREFIX_ROLE + line[first:second])
  return out

def getRoles_cetus():
  return [PREFIX_ROLE + x for x in ["Cetus", "Day", "Night"]]

def getRoles():
  return getRoles_alert() + getRoles_cetus()

async def deleteRole(server, role=None):
  ### Single
  if type(role) == discord.Role:
    if role.name.startswith(PREFIX_ROLE): await client.delete_role(server, role)
  ### Multiple
  else:
    # Delete all if role is empty
    if not role: role = server.roles
    # Delete
    for sRole in role:
      if sRole.name.startswith(PREFIX_ROLE): await client.delete_role(server, sRole)

async def onMsg_sub_on(message, roleType, aRoleName="", kr=False):
  roleList = getRoles_alert() if any([roleType.startswith(x) for x in KEYWORD_ALERT]) else getRoles_cetus()
  ### Server
  s = message.server
  ### Create
  aRolePerm = discord.Permissions.none()
  aRoleColour = discord.Colour.default()
  ## Copy perm
  if aRoleName:
    # Find and copy perm
    for sRole in s.roles:
      if sRole.name == aRoleName:
        aRolePerm = sRole.permissions
        aRoleColour = sRole.colour
    # Specified role name does not exist
    if not aRolePerm:
      text = (mono(aRoleName) + "역할이 없습니다."
              if kr else
              mono(aRoleName) + " role does not exist.")
      await msg(message, text)
      return
  ### Delete unused
  delNum = 0
  for sRole in s.roles:
    if sRole.name.startswith(PREFIX_ROLE) and (sRole.name not in getRoles()):
      await deleteRole(s, sRole)
      delNum += 1
  ### Create/modify role
  modNum = 0
  addNum = 0
  for nRole in roleList:
    exists = False
    for sRole in s.roles:
      if (nRole == sRole.name) and ((aRolePerm != sRole.permissions) or (aRoleColour != sRole.colour)):
        await client.edit_role(s, sRole, permissions=aRolePerm, colour=aRoleColour, mentionable=True)
        exists = True
        modNum += 1
      elif (nRole == sRole.name): exists = True
    if not exists:
      await client.create_role(s, name=nRole, permissions=aRolePerm, colour=aRoleColour, mentionable=True)
      addNum += 1
  text = (("알림 역할이 생성되었습니다.\n(" +
           str(delNum) + "개의 쓰지 않는 역할 제거. " +
           str(modNum) + "개의 존재하는 역할 변경. " +
           str(addNum) + "개의 새 역할 생성.)")
          if kr else
          ("Notification roles generated. \n(" +
           str(delNum) + " unused role" + ("" if delNum==1 else "s") + " removed. " +
           str(modNum) + " existing role" + ("" if modNum==1 else "s") + " modified. " +
           str(addNum) + " role" + ("" if addNum==1 else "s") + " created.)"))
  await msg(message, text)

async def onMsg_sub_off(message, roleType, kr=False):
  roleList = getRoles_alert() if any([roleType.startswith(x) for x in KEYWORD_ALERT]) else getRoles_cetus()
  ### Server
  s = message.server
  ### Delete
  delNum = 0
  for sRole in s.roles:
    if sRole.name.startswith(PREFIX_ROLE) and (sRole.name in roleList):
      await deleteRole(s, sRole)
      delNum += 1
  text = ("알림 역할이 제거되었습니다. (" + str(delNum) + "개의 역할 제거.)" if kr else
          "Notification roles cleared. (" + str(delNum) + " role" + ("" if delNum == 1 else "s") + " removed.)")
  await msg(message, text)

########## onMsg (Alert/Cetus) ##########

async def onMsg_notice_start(message, noticeType, kr=False):
  await min_notice_set(noticeType, message.server.id, message.channel.id + "|" + (LANG_KR if kr else LANG_EN), message.server.name + "\n" + message.channel.name)
  isAlert = any([noticeType.startswith(x) for x in KEYWORD_ALERT])
  if kr:
    nType1 = "얼럿/침공" if isAlert else "세투스 낮/밤"
    nType2 = "얼럿" if isAlert else "세투스" #TODO: "얼럿"?
    await msg(message, (nType1 + " 알림이 켜졌습니다.\n" +
                        "서버 내 구독 기능을 추가하시려면 " + mono(PREFIX + "알림 " + nType2 + " 구독") + "을 고려해보세요."))
  else:
    nType = "Alert/Invasion" if isAlert else "Cetus day/night"
    await msg(message, (nType + " notification has started.\n" +
                        "Take a look at " + mono(PREFIX + "notice " + noticeType + " sub") + " if you want a subscription feature in this server."))

async def onMsg_notice_stop(message, noticeType, kr=False):
  await min_notice_clear(noticeType, message.server.id)
  isAlert = any([noticeType.startswith(x) for x in KEYWORD_ALERT])
  if kr:
    nType = "얼럿/침공" if isAlert else "세투스 낮/밤"
    await msg(message, nType + " 알림이 꺼졌습니다.")
  else:
    nType = "Alert/Invasion" if isAlert else "Cetus day/night"
    await msg(message, nType + " notification has stopped.")

########## onMsg (Event) ##########

async def onMsg_event_on(message, code, time, kr=False):
  ### Code lower
  code = code.lower()
  ### Code alphabet + digit + underscore
  if not re.compile("^[a-z0-9_]+$").match(code):
    await react(message, EMOJI_NEG)
    await msg(message, "Only alphabets(a-z), digits(0-9), and underscores(_) are allowed for event codes.")
    return
  ### Code exists
  k = message.server.id + "|" + code + "|"
  for key in g.eventDict:
    if key.startswith(k):
      await react(message, EMOJI_NEG)
      await msg(message, "There is already a event code " + mono(code) + " on this server.")
      return
  ### Time format
  try:
    time = datetime.datetime.strptime(time, DATETIME_YMDHM).strftime(DATETIME_YMDHM)
  except ValueError:
    await react(message, EMOJI_NEG)
    await msg(message, "Time format is incorrect. The format must be `YYYY-MM-DD hh:mm`.")
    return
  ### Save
  await min_event_set(message.server, code, message.author, time, kr)
  await msg(message, "An event has been registered. Other users can join with " + mono(PREFIX + "event join " + code))

async def onMsg_event_list(message):
  k = message.server.id + "|"
  l = []
  for key in g.eventDict:
    if key.startswith(k):
      kps = key.split("|")
      vps = g.eventDict[key][1:-1].split("|")
      vp = vps[0]
      vn = "unknown"
      for member in message.server.members:
        if vp == member.id:
          vn = member.display_name + " (" + member.name + "#" + member.discriminator + ")"
          if member.name == member.display_name:
            vn = member.name + "#" + member.discriminator
          break
      time = datetime.datetime.strptime(kps[2], DATETIME_YMDHM)
      ml = math.ceil((time - now_datetime()).total_seconds() / 60)
      hl = round(ml/60, 1)
      text = ("Code: " + kps[1] + "\n" +
              "Event Time: " + kps[2] + " UTC\n" +
              "Minutes Left: " + str(ml) + " minutes" + (" (" + str(hl) + " hours)" if hl > 1 else "") + "\n" +
              "Host: " + vn + "\n" +
              "Participants: " + str(len(vps)) + " member" + ("" if len(vps) == 1 else "s"))
      l.append(box1(text.strip()))
  pre = "Current Time: " + mono(now_ymdhms() + " UTC")
  if l:
    post = ("To join an event, try " + mono(PREFIX + "event join [CODE]") +
            "For the list of participants, try " + mono(PREFIX + "event list [CODE]"))
    await msgs(message, l, sep="", pre=pre, post=post)
  else:
    text = "No events are registered on this server."
    await msg(message, pre + "\n" + text)

async def onMsg_event_partList(message, code):
  ### Code lower
  code = code.lower()
  ### Keyword
  k = message.server.id + "|" + code + "|"
  found = False
  for key in g.eventDict:
    if key.startswith(k):
      ## If server+code found
      vps = g.eventDict[key][1:-1].split("|")
      vns = []
      for vp in vps:
        # If member found
        foundV = False
        for member in message.server.members:
          if vp == member.id:
            vn = member.display_name + " (" + member.name + "#" + member.discriminator + ")"
            if member.name == member.display_name:
              vn = member.name + "#" + member.discriminator
            vns.append(vn)
            foundV = True
            break
        # If member not found
        if not foundV:
          vns.append("unknown")
      found = True
      break
  if found:
    pre = str(len(vps)) + " participant" + ("" if len(vps) == 1 else "s") + " in " + mono(code)
    await msgs(message, vns, pre=pre, box=1)
  else:
    await react(message, EMOJI_NEG)
    await msg(message, "There is no such event code " + mono(code) + " on this server.")

async def onMsg_event_off(message, code):
  ### Code lower
  code = code.lower()
  ### Check if code exists
  k = message.server.id + "|" + code + "|"
  for key in g.eventDict:
    if key.startswith(k):
      ### Host cannot leave
      if g.eventDict[key].startswith(wrap("|", message.author.id)):
        ### Delete
        await min_event_clear(message.server, code)
        await msg(message, "The event has been removed.")
      else:
        await react(message, EMOJI_NEG)
        await msg(message, "Only the host can remove the event. If you wish to leave the event, try " + mono(PREFIX + "event leave " + code))
      return
  ### Code does not exist
  await react(message, EMOJI_NEG)
  await msg(message, "There is no such event code " + mono(code) + " on this server.")

async def onMsg_event_join(message, code):
  ### Code lower
  code = code.lower()
  ### Check if code exists
  k = message.server.id + "|" + code + "|"
  for key in g.eventDict:
    if key.startswith(k):
      ### Already joined
      if wrap("|", message.author.id) in g.eventDict[key]:
        await react(message, EMOJI_EXCLAMATION)
        await msg(message, "You already joined the event. Nothing has changed.")
      ### Join
      else:
        await min_event_join(message.server, code, message.author)
        await msg(message, "You have joined the event.")
      return
  ### Code does not exist
  await react(message, EMOJI_NEG)
  await msg(message, "There is no such event code " + mono(code) + " on this server.")

async def onMsg_event_leave(message, code):
  ### Code lower
  code = code.lower()
  ### Check if code exists
  k = message.server.id + "|" + code + "|"
  for key in g.eventDict:
    if key.startswith(k):
      ### Host cannot leave
      if g.eventDict[key].startswith(wrap("|", message.author.id)):
        await react(message, EMOJI_NEG)
        await msg(message, "The host cannot leave the event. If you wish to remove the event, try " + mono(PREFIX + "event off " + code))
      ### Leave
      elif wrap("|", message.author.id) in g.eventDict[key]:
        await min_event_leave(message.server, code, message.author)
        await msg(message, "You have left the event.")
        return
      ### Not joined
      else:
        await react(message, EMOJI_EXCLAMATION)
        await msg(message, "You are not participating in the event. Nothing has changed.")
      return
  ### Code does not exist
  await react(message, EMOJI_NEG)
  await msg(message, "There is no such event code " + mono(code) + " on this server.")

########## onMsg (Developer) ##########

async def onMsg_server(message, ID=None):
  s = message.server
  if ID: s = client.get_server(ID)
  if s and (not s.unavailable):
    # Image URL
    imgurl = s.icon_url
    # Role
    roleCount = 0
    roleList = []
    for role in s.role_hierarchy:
      if not role.is_everyone:
        roleCount += 1
        roleList.append(role.name)
    # Channel
    textChanCount = 0
    voiceChanCount = 0
    for chan in s.channels:
      if chan.type == discord.ChannelType.text: textChanCount += 1
      elif chan.type == discord.ChannelType.voice: voiceChanCount += 1
    # Member
    memOn = 0
    for member in s.members:
      if member.status != discord.Status.offline: memOn += 1
    # Verification Level
    vlDict = {"none":"None", "low":"Low", "medium":"Medium", "high":"(╯°□°)╯︵ ┻━┻", "4":"┻━┻ミヽ(ಠ益ಠ)ノ彡┻━┻"}
    vl = vlDict[str(s.verification_level)]
    # Fields
    fields = [("Region", s.region), ("Owner", s.owner), ("Verification Level", vl),
              ("Text/Voice Channel Count", str(textChanCount) + "/" + str(voiceChanCount)),
              ("Member Online/Total", str(memOn) + "/" + str(s.member_count)), ("Emoji Count", len(s.emojis)),
              ("Default Channel", s.default_channel)]

    # Send embedded message
    await embed(message, title=s.name, desc=("Created at " + s.created_at.strftime("%Y-%m-%d %I:%M:%S %p") + " UTC"),
                footer="ID: " + s.id, thumbnail=imgurl, fields=fields)
    rolePre = "Roles (" + str(roleCount) + ")"
    await msgs(message, roleList, sep=", ", pre=rolePre, box=1)
  elif s and s.unavailable: await msg(message, "Unavailable Server ID " + mono(ID))
  else: await msg(message, "Unknown Server ID " + mono(ID))

async def onMsg_server_channel(message, ID=None):
  s = message.server
  if ID: s = client.get_server(ID)
  if s:
    ### Channel
    # Separate text/voice
    textChanList = []
    voiceChanList = []
    for chan in s.channels:
      if chan.type == discord.ChannelType.text: textChanList.append(chan)
      elif chan.type == discord.ChannelType.voice: voiceChanList.append(chan)
    # Count
    textChanCount = len(textChanList)
    voiceChanCount = len(voiceChanList)
    # Sort
    textChanList = sorted(textChanList, key=lambda x: x.position)
    voiceChanList = sorted(voiceChanList, key=lambda x: x.position)
    # Convert to string
    textChanStrs = [(x.id + " " + x.name) for x in textChanList]
    voiceChanStrs = [(x.id + " " + x.name) for x in voiceChanList]
    ### Fields
    pre = [str(textChanCount) + " Text Channel(s)", str(voiceChanCount) + " Voice Channel(s)"]
    ### Send embedded message
    await msgs(message, textChanStrs, pre=pre[0], box=2)
    await msgs(message, voiceChanStrs, pre=pre[1], box=2)
  elif s and s.unavailable: await msg(message, "Unavailable Server ID " + mono(ID))
  else: await msg(message, "Unknown Server ID " + mono(ID))

async def onMsg_server_member(message, ID=None):
  s = message.server
  if ID: s = client.get_server(ID)
  if s:
    # Member
    memberList = []
    for member in s.members:
      text = " "*(18-len(member.id)) + member.id + " " + member.name + "#" + member.discriminator
      memberList.append(text.replace("[","［").replace("]","］"))
    # Send message
    pre = s.name + " Member List " + wrapParen(str(len(memberList)))
    texts = memberList
    await msgs(message, texts, pre=pre, box=2)
  elif s and s.unavailable: await msg(message, "Unavailable Server ID " + mono(ID))
  else: await msg(message, "Unknown Server ID " + mono(ID))

async def onMsg_server_emoji(message, ID=None):
  s = message.server
  if ID: s = client.get_server(ID)
  if s:
    # Emoji
    eList = [(" "*(18-len(x.id)) + x.id + " " + x.name) for x in s.emojis]
    # Send embedded message
    if eList:
      await msg(message, s.name + " Emoji List " + wrapParen(str(len(eList))) + "\n" + box2("\n".join(eList)))
    else: await msg(message, s.name + " Emoji(s)\nNot Available")
  elif s and s.unavailable: await msg(message, "Unavailable Server ID " + mono(ID))
  else: await msg(message, "Unknown Server ID " + mono(ID))

async def onMsg_channel(message, ID):
  c = client.get_channel(ID)
  if c:
    if not c.is_private:
      # Image URL
      imgurl = c.server.icon_url
      # Topic
      topic = "(No Topic)"
      if c.topic: topic = c.topic
      # Fields
      fields = [("Server", c.server.name), ("Server ID", c.server.id),
                ("Created At", c.created_at.strftime("%Y-%m-%d %I:%M:%S %p") + " UTC"), ("Default Channel", c.is_default),
                ("Channel Type", str(c.type).title()), ("Position", ordinal(c.position+1))]
      if c.type == discord.ChannelType.voice:
        fields.append(("Bitrate", str(c.bitrate//1000) + "kbps"))
        if c.user_limit == 0: fields.append(("User Limit", "Unlimited"))
        else: fields.append(("Limit", c.user_limit))
      # Send embedded message
      await embed(message, title=c.name, desc=topic, footer="ID: " + c.id, thumbnail=imgurl, fields=fields)
    else: await msg(message, "DM ID is " + mono(ID))
  else: await msg(message, "Unknown Channel ID " + mono(servID))

async def onMsg_user(message, ID="", servID=""):
  ### Get server
  s = None
  # Server ID exists
  if servID:
    s = client.get_server(servID)
    # Invalid servID: return
    if s and s.unavailable:
      await msg(message, "Unavailable Server ID " + mono(servID))
      return
    if not s:
      await msg(message, "Unknown Server ID " + mono(servID))
      return
  # No servID: Get msg server
  elif isPub(message): s = message.server
  ### Get member
  u = None
  # No ID: Get sender
  if not ID: u = message.author
  # Server exists
  elif s:
    # Get member (ID in current server)
    u = discord.utils.find(lambda m: m.id == ID, s.members)
    # Get member (nick in current server)
    if not u: u = discord.utils.find(lambda m: m.name.lower().startswith(ID.lower()), s.members)
  # Get member (ID / name and disc)
  if not u:
    for server in client.servers:
      if u: break
      s = server
      for member in server.members:
        if u: break
        # ID
        if ID == member.id: u = member
        # name/disc
        elif "#" in ID:
          nd = ID.split("#")
          if (member.name == nd[0]) and (member.discriminator == nd[1]): u = member
  ### Evaluate
  if u:
    # Title
    title=u.name + "#" + u.discriminator
    # Description
    desc = ""
    if u.bot: title += " " + mono(BOT)
    # Image URL
    imgurl = u.default_avatar_url
    if u.avatar_url: imgurl = u.avatar_url
    # Fields
    fields = [("Created At", u.created_at.strftime("%Y-%m-%d %I:%M:%S %p") + " UTC")]
    ## Server
    if s:
      desc = "Server " + mono(s.name)
      if u.display_name != u.name: desc += "\n" + mono("AKA ") + u.display_name
      # Top Role (Field)
      fields.append(("Highest Role", u.top_role.name))
      # Roles (Field)
      roleList = []
      for role in u.roles:
        if not role.is_everyone: roleList.append(role.name)
      fields.append(("Role(s)", ", ".join(roleList)))
    # Send embedded message
    await embed(message, title=title, desc=desc, footer="ID: " + u.id, thumbnail=imgurl, fields=fields)
  else: await msg(message, "Unknown User ID " + mono(ID))

async def onMsg_serverList(message):
  s = ""
  for server in client.servers:
    s += server.id + " " + server.name + "\n"
  # Fields
  fields = [("Server ID/Name", mono(s.strip()))]
  # Send embedded message
  desc = str(len(client.servers)) + " Server(s)"
  await embed(message, title="List of Servers", desc=desc, fields=fields)

########## Events ##########

def cmdCheck(args, wordList, length=0):
  length += len(wordList)
  if len(args) < length: return False
  for i in range(len(wordList)):
    word = wordList[i]
    if type(word) == set:
      if not any([args[i].startswith(w) for w in word]): return False
    else:
      if not args[i].startswith(word): return False
  return True

async def msg_UNP_PD(message, kr=False):
  if isPub(message):
    await react(message, EMOJI_NEG)
    await msg_UNoPerm(message, kr=kr)
  else:
    await react(message, EMOJI_NEG)
    await msg_PvtDisabled(message, kr=kr)

@client.event
async def on_message(message):
  try:
    if isNotMyMsg(message) and message.content.startswith(PREFIX):
      ##### log
      if isPvt(message):
        logging.info("on_message:[" + str(message.timestamp) + "][" +
                     message.author.name + "#" + message.author.discriminator + "]" + message.content)
      else:
        logging.info("on_message:[" + str(message.timestamp) + "][" +
                     message.server.name + "][" + message.channel.name + "][" +
                     message.author.name + "#" + message.author.discriminator + "]" + message.content)
      ##### start of command check
      args = message.content[len(PREFIX):].split(" ")
      args[0] = args[0].lower()
      ### No argument
      if not args[0]: pass
      ### Discord
      elif cmdCheck(args, ["ver"]):
        await react(message, EMOJI_POS)
        await msg(message, "Ver. " +  VERSION)
      ## Help
      elif cmdCheck(args, ["help", "admin"]):
        await react(message, EMOJI_POS)
        await onMsg_help(message, "admin")
      elif cmdCheck(args, ["help", "dev"]):
        if isDev(message.author.id):
          await react(message, EMOJI_POS)
          await onMsg_help(message, "dev")
        else:
          await react(message, EMOJI_NEG)
          await msg_UNoPerm(message)
      elif cmdCheck(args, ["help"]):
        await react(message, EMOJI_POS)
        await onMsg_help(message)
      ## Help KR
      elif cmdCheck(args, ["도", "관"]):
        await react(message, EMOJI_POS)
        await onMsg_help(message, "admin", kr=True)
      elif cmdCheck(args, ["도"]):
        await react(message, EMOJI_POS)
        await onMsg_help(message, kr=True)
      ## Feedback
      elif cmdCheck(args, [{"feedback","report"}], 1):
        await react(message, EMOJI_POS)
        await onMsg_feedback(message, " ".join(args[1:]))
      elif cmdCheck(args, [{"feedback","report"}]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["feedback"])
      ## Time
      elif cmdCheck(args, ["time"]):
        await react(message, EMOJI_POS)
        await onMsg_time(message)
      ## Ping
      elif cmdCheck(args, ["ping"]):
        await msg(message, EMOJI_PONG)
      ## Hug
      elif cmdCheck(args, ["hug"]):
        await msg(message, EMOJI_FU)
      ### Discord (admin)
      ## BPin
      elif cmdCheck(args, ["bpin","clear"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_bpin_clear(message)
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["bpin"], 1):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_bpin(message, " ".join(args[1:]))
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["bpin"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["bpin"])
      ## Delete
      # del auto
      elif cmdCheck(args, ["del", "auto", "clear"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_delete_auto_clear(message)
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["del", "auto"], 1) and args[2].isdigit():
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_delete_auto(message, int(args[2]))
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["del", "auto"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin", ["del auto"])
      # del day
      elif cmdCheck(args, ["del", "day"], 1) and args[2].isdigit():
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_delete_day(message, int(args[2]))
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["del", "day"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin", ["del day"])
      # del
      elif cmdCheck(args, ["del"], 1) and args[1].isdigit():
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_delete(message, int(args[1]))
        else: await msg_UNP_PD(message)
      elif cmdCheck(args, ["del"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin", ["del","del day","del auto"])
      ### Warframe
      ## Drain
      elif cmdCheck(args, ["drain"], 3):
        await react(message, EMOJI_POS)
        await onMsg_drain(message, args[1], args[2], args[3])
      elif cmdCheck(args, ["drain"], 2):
        await react(message, EMOJI_POS)
        await onMsg_drain(message, args[1], args[2])
      elif cmdCheck(args, ["drain"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["drain"])
      ## Alerts
      elif cmdCheck(args, ["alert"]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_alert())
      ## Alerts KR
      elif cmdCheck(args, ["얼"]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_alert(kr=True))
      ## Invasions
      elif cmdCheck(args, ["inv"]):
        await react(message, EMOJI_POS)
        await onMsg_invasion(message)
      ## Invasions KR
      elif cmdCheck(args, ["침"]):
        await react(message, EMOJI_POS)
        await onMsg_invasion(message, kr=True)
      ## Sorties
      elif cmdCheck(args, ["sortie"]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_sortie())
      ## Sorties KR
      elif cmdCheck(args, ["출"]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_sortie(kr=True))
      ## Void Trader
      elif cmdCheck(args, [{"baro","trade"}]):
        await react(message, EMOJI_POS)
        await onMsg_voidTrader(message)
      ## Void Trader KR
      elif cmdCheck(args, [{"바","상"}]):
        await react(message, EMOJI_POS)
        await onMsg_voidTrader(message, kr=True)
      ## Void Fissure
      elif cmdCheck(args, [{"void","fissure"}]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_fissure())
      ## Void Fissure KR
      elif cmdCheck(args, [{"보","균"}]):
        await react(message, EMOJI_POS)
        await msg(message, getStr_fissure(kr=True))
      ## Cetus
      elif cmdCheck(args, [{"cetus","eid","poe"}]):
        await react(message, EMOJI_POS)
        await onMsg_cetus(message)
      ## Cetus KR
      elif cmdCheck(args, [{"세","아","평"}]):
        await react(message, EMOJI_POS)
        await onMsg_cetus(message, kr=True)
      ## Earth
      #elif cmdCheck(args, ["earth"]):
        #await react(message, EMOJI_POS)
        #await onMsg_earth(message)
      ## Earth KR
      #elif cmdCheck(args, ["지"]):
        #await react(message, EMOJI_POS)
        #await onMsg_earth(message, kr=True) #TODO: earth
      ## WFNow
      elif cmdCheck(args, [{"active","now"}]):
        await react(message, EMOJI_POS)
        await onMsg_active(message)
      ## WFNow KR
      elif cmdCheck(args, ["현"]):
        await react(message, EMOJI_POS)
        await onMsg_active(message, kr=True)
      ## Price Check
      elif cmdCheck(args, [{"pc","price"}], 1):
        await react(message, EMOJI_POS)
        await onMsg_pc(message, " ".join(args[1:]).lower())
      elif cmdCheck(args, [{"pc","price"}]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["pc"])
      ## Armor
      elif cmdCheck(args, ["armo"], 1) and isFloat(args[1]):
        await react(message, EMOJI_POS)
        await onMsg_armor(message, float(args[1]))
      elif cmdCheck(args, ["armo"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["armo"])
      ## Wikia
      elif cmdCheck(args, [{"wiki","what"}], 1):
        await react(message, EMOJI_POS)
        await onMsg_wikia(message, " ".join(args[1:]))
      elif cmdCheck(args, [{"wiki","what"}]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["wiki"])
      ## Drop Table
      elif cmdCheck(args, ["drop"], 1):
        await react(message, EMOJI_POS)
        await onMsg_drop(message, " ".join(args[1:]))
      elif cmdCheck(args, ["drop"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["drop"])
      ## Raid
      elif cmdCheck(args, ["raid"], 1):
        await react(message, EMOJI_POS)
        await onMsg_raid(message, args[1])
      elif cmdCheck(args, ["raid"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["raid"])
      ## Raid KR
      elif cmdCheck(args, [{"토","레"}], 1):
        await react(message, EMOJI_POS)
        await onMsg_raid(message, args[1], kr=True)
      elif cmdCheck(args, [{"토","레"}]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_kr", ["토"])
      ### Notice
      # notice alert/cetus sub on
      elif cmdCheck(args, ["notice",{"alert","cetus"},"sub","on"], 1):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_on(message, args[1], args[4])
        else: msg_UNP_PD(message)
      elif cmdCheck(args, ["notice",{"alert","cetus"},"sub","on"]):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_on(message, args[1])
        else: msg_UNP_PD(message)
      elif cmdCheck(args, ["notice",{"alert","cetus"},"sub","off"]):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_off(message, args[1])
        else: msg_UNP_PD(message)
      elif cmdCheck(args, ["notice",{"alert","cetus"},"sub"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin", ["notice alert|cetus sub"])
      # notice alert on
      elif cmdCheck(args, ["notice",{"alert","cetus"},"on"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_notice_start(message, args[1])
        else: msg_UNP_PD(message)
      # notice alert off
      elif cmdCheck(args, ["notice",{"alert","cetus"},"off"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_notice_stop(message, args[1])
        else: msg_UNP_PD(message)
      elif cmdCheck(args, ["notice"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin", ["notice","notice alert|cetus sub"])
      ### Notice KR
      # notice alert/cetus sub on
      elif cmdCheck(args, ["알",{"얼","세"},"구","켬"], 1):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_on(message, args[1], args[4], kr=True)
        else: msg_UNP_PD(message, kr=True)
      elif cmdCheck(args, ["알",{"얼","세"},"구","켬"]):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_on(message, args[1], kr=True)
        else: msg_UNP_PD(message, kr=True)
      elif cmdCheck(args, ["알",{"얼","세"},"구","끔"]):
        if isPub(message) and perm_mngRole(message):
          await react(message, EMOJI_POS)
          await onMsg_sub_off(message, args[1], kr=True)
        else: msg_UNP_PD(message, kr=True)
      elif cmdCheck(args, ["알",{"얼","세"},"구"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin_kr", ["알림 얼럿|세투스 구독"])
      # notice alert on
      elif cmdCheck(args, ["알",{"얼","세"},"켬"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_notice_start(message, args[1], kr=True)
        else: msg_UNP_PD(message, kr=True)
      # notice alert off
      elif cmdCheck(args, ["알",{"얼","세"},"끔"]):
        if isPub(message) and perm_mngMsg(message):
          await react(message, EMOJI_POS)
          await onMsg_notice_stop(message, args[1], kr=True)
        else: msg_UNP_PD(message, kr=True)
      elif cmdCheck(args, ["알"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help_admin_kr", ["알림","알림 얼럿|세투스 구독"])
      ### Subscribe
      elif cmdCheck(args, ["sub","list"]):
        await react(message, EMOJI_POS)
        await onMsg_sub_list(message)
      elif cmdCheck(args, ["sub"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_sub(message, args[1])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["sub"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["sub","sub(scribe) [ROLE]","unsub"])
      ### Unsubscribe
      elif cmdCheck(args, ["unsub"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_unsub(message, args[1])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["unsub"]):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_unsub(message)
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      ### Event
      elif cmdCheck(args, ["event","on"], 3):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_on(message, args[2], " ".join(args[3:5]))
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event","on"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["event on"])
      elif cmdCheck(args, ["event","off"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_off(message, args[2])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event","off"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["event off"])
      elif cmdCheck(args, ["event","join"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_join(message, args[2])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event","join"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["event join"])
      elif cmdCheck(args, ["event","leave"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_leave(message, args[2])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event","leave"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["event leave"])
      elif cmdCheck(args, ["event","list"], 1):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_partList(message, args[2])
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event","list"]):
        if isPub(message):
          await react(message, EMOJI_POS)
          await onMsg_event_list(message)
        else:
          await react(message, EMOJI_NEG)
          await msg_PvtDisabled(message)
      elif cmdCheck(args, ["event"]):
        await react(message, EMOJI_QUESTION)
        await msg_help(message, "help", ["event on","event off","event join","event list"])
      ### Developer
      elif isDev(message.author.id):
        ## Test
        if cmdCheck(args, ["test"]):
          await test(message)
        ## Export Spy
        elif cmdCheck(args, ["exp"]):
          await export(message)
        elif cmdCheck(args, ["data","backup","save"]):
          await react(message, EMOJI_POS)
          await servData_backup(True)
        elif cmdCheck(args, ["data","backup","load"]):
          await react(message, EMOJI_POS)
          await servData_backup(False)
        elif cmdCheck(args, ["data","backup"]):
          await react(message, EMOJI_QUESTION)
          await msg_help(message, "help_dev", ["data b"])
        elif cmdCheck(args, ["data","clean"], 1):
          if args[2] in g.servData.keys():
            await react(message, EMOJI_POS)
            await servData_clean(args[2])
          else:
            await react(message, EMOJI_NEG)
            await msg(message, mono(args[2]) + " category does not exist.")
        elif cmdCheck(args, ["data","clean"]):
          await react(message, EMOJI_QUESTION)
          await msg_help(message, "help_dev", ["data c"])
        elif cmdCheck(args, ["data","del"], 2):
          if args[2] in g.servData.keys():
            await react(message, EMOJI_POS)
            deleted = await servData_delete(args[2], args[3])
            if deleted: await msg(message, mono(args[3]) + " deleted.")
            else:
              await react(message, EMOJI_NEG)
              await msg(message, mono(args[3]) + " not found.")
          else:
            await react(message, EMOJI_NEG)
            await msg(message, mono(args[2]) + " category does not exist.")
        elif cmdCheck(args, ["data","del"]):
          await react(message, EMOJI_QUESTION)
          await msg_help(message, "help_dev", ["data d"])
        elif cmdCheck(args, ["data","eval"], 1):
          if args[2] in g.servData.keys():
            await react(message, EMOJI_POS)
            s = args[2]
            g.servData[s].clear()
            g.servData[s] = await servData_eval(s, g.servData[s])
          else:
            await react(message, EMOJI_NEG)
            await msg(message, mono(args[2]) + " category does not exist.")
        elif cmdCheck(args, ["data","eval"]):
          await react(message, EMOJI_QUESTION)
          await msg_help(message, "help_dev", ["data e"])
        elif cmdCheck(args, ["data"]):
          await react(message, EMOJI_QUESTION)
          await msg_help(message, "help_dev", ["data b","data c","data d","data e"])
        ## serv --
        elif cmdCheck(args, ["serv","list"]):
          await react(message, EMOJI_POS)
          await onMsg_serverList(message)
        elif cmdCheck(args, ["serv","chan"]):
          await react(message, EMOJI_POS)
          await onMsg_server_channel(message)
        elif cmdCheck(args, ["serv",{"user","mem"}]):
          await react(message, EMOJI_POS)
          await onMsg_server_member(message)
        elif cmdCheck(args, ["serv","emo"]):
          await react(message, EMOJI_POS)
          await onMsg_server_emoji(message)
        ## serv id --
        elif cmdCheck(args, ["serv","","chan"]):
          await react(message, EMOJI_POS)
          await onMsg_server_channel(message, args[1])
        elif cmdCheck(args, ["serv","",{"user","mem"}]):
          await react(message, EMOJI_POS)
          await onMsg_server_member(message, args[1])
        elif cmdCheck(args, ["serv","","emo"]):
          await react(message, EMOJI_POS)
          await onMsg_server_emoji(message, args[1])
        elif cmdCheck(args, ["serv"], 1):
          await react(message, EMOJI_POS)
          await onMsg_server(message, args[1])
        elif cmdCheck(args, ["serv"]):
          if isPub(message):
            await react(message, EMOJI_POS)
            await onMsg_server(message)
          else:
            await react(message, EMOJI_NEG)
            await msg(message, "DM is not a server.")
        elif cmdCheck(args, ["chan"], 1):
          await react(message, EMOJI_POS)
          await onMsg_channel(message, args[1])
        elif cmdCheck(args, ["chan"]):
          await react(message, EMOJI_POS)
          await onMsg_channel(message, message.channel.id)
        elif cmdCheck(args, [{"user","mem"}, "serv"], 2):
          await react(message, EMOJI_POS)
          await onMsg_user(message, " ".join(args[3:]), args[2])
        elif cmdCheck(args, [{"user","mem"}], 1):
          await react(message, EMOJI_POS)
          await onMsg_user(message, " ".join(args[1:]))
        elif cmdCheck(args, [{"user","mem"}]):
          await react(message, EMOJI_POS)
          await onMsg_user(message)
      ##### end of command check
    if (not isBpin(message)):
      try: await onMsg_bpin_move(message)
      except discord.errors.HTTPException: pass
  ### Exceptions
  except discord.errors.Forbidden:
    await react(message, EMOJI_NEG)
    await msg_INoPerm(message)
  except urllib.error.HTTPError as e: await msg_urllibError(message, e, url=URL_WF_MAIN)
  except: await msgExc()

@client.event
async def on_ready():
  print("discord.py Version: " + discord.__version__)
  if DEBUG: print("Cephalon Echo Version: " + VERSION)
  else: print("Cephalon Schwa Version: " + VERSION)
  print("Name: " + client.user.name + "#" + client.user.discriminator)
  print("ID: " + client.user.id)
  print("--------------------READY--------------------")

########## Minute ##########

##### Item

async def min_item():
  while g.itemUploadSet:
    await servData_add("item", g.itemUploadSet.pop())

##### Delete

async def min_delete_set(ID, day, comment):
  async with lock_delete:
    g.deleteDict[ID] = str(day)
    await servData_add("delete", ID + "\n" + str(day) + "\n" + comment)

async def min_delete_clear(ID):
  async with lock_delete:
    del g.deleteDict[ID]
    await servData_delete("delete", ID)

async def min_delete():
  subClearList = []
  async with lock_delete:
    for k, v in g.deleteDict.items():
      channel = client.get_channel(k)
      if not channel: subClearList.append(k)
      elif channel:
        # Time
        time = now_datetime()-datetime.timedelta(days=int(v))
        # Delete old days
        try: await delmsgs(channel, before=time, cond=isNotBpin)
        except discord.errors.HTTPException as e:
          logging.warning("min_delete:discord.errors.HTTPException:code " + str(e.code))
  ### Delete unavailable channel ID
  for k in subClearList: await min_delete_clear(k)

##### Notice

async def min_notice_set(noticeType, servID, chanIDnLang, comment):
  if any([noticeType.startswith(x) for x in KEYWORD_ALERT]):
    async with lock_alert:
      g.alertDict[servID] = chanIDnLang
      await servData_add("alert", servID + "\n" + chanIDnLang + "\n" + comment)
  else:
    async with lock_cetus:
      g.cetusDict[servID] = chanIDnLang
      await servData_add("cetus", servID + "\n" + chanIDnLang + "\n" + comment)

async def min_notice_clear(noticeType, servID):
  if any([noticeType.startswith(x) for x in KEYWORD_ALERT]):
    async with lock_alert:
      del g.alertDict[servID]
      await servData_delete("alert", servID)
  else:
    async with lock_cetus:
      del g.cetusDict[servID]
      await servData_delete("cetus", servID)

def mentionRole(server, roleName):
  if not roleName.startswith(PREFIX_ROLE): roleName = PREFIX_ROLE + roleName
  for role in server.roles:
    if roleName == role.name: return role.mention
  return "@" + roleName

##### Notice Alert

async def min_alert_current():
  out = {}
  try:
    ### Alert
    for alert in wfAPI()["Alerts"]:
      ID = alert["_id"]["$oid"]
      reward = alert["MissionInfo"]["missionReward"]
      itemSet = set()
      itemExists = 2
      # Item
      try:
        for itemObj in reward["items"]:
          c = convert("alert", itemObj, ID, "alert")
          itemSet.update(c)
      except KeyError: itemExists -= 1
      # Counted Item
      try:
        for cItemObj in reward["countedItems"]:
          c = convert("alert", cItemObj["ItemType"], ID, "alert")
          itemSet.update(c)
      except KeyError: itemExists -= 1
      if itemExists > 0: out[ID] = itemSet
    ### Invasion
    for invasion in wfAPI()["Invasions"]:
      p = invasion_p(invasion)
      if (0.0 <= p) and (p <= 1.0):
        ID = invasion["_id"]["$oid"]
        aFaction = convert("faction", invasion["DefenderMissionInfo"]["faction"])
        dFaction = convert("faction", invasion["AttackerMissionInfo"]["faction"])
        itemSet = set()
        itemExists = 4
        # Attack Item
        try:
          if len(invasion["AttackerReward"]) > 0:
            for itemObj in invasion["AttackerReward"]["items"]:
              c = convert("alert", itemObj["ItemType"], ID, "invasion", aFaction)
              itemSet.update(c)
        except KeyError: itemExists -= 1
        # Attack Counted Item
        try:
          if len(invasion["AttackerReward"]) > 0:
            for itemObj in invasion["AttackerReward"]["countedItems"]:
              c = convert("alert", itemObj["ItemType"], ID, "invasion", aFaction)
              itemSet.update(c)
        except KeyError: itemExists -= 1
        # Defend Item
        try:
          for itemObj in invasion["DefenderReward"]["items"]:
            c = convert("alert", itemObj["ItemType"], ID, "invasion", dFaction)
            itemSet.update(c)
        except KeyError: itemExists -= 1
        # Defend Counted Item
        try:
          for itemObj in invasion["DefenderReward"]["countedItems"]:
            c = convert("alert", itemObj["ItemType"], ID, "invasion", dFaction)
            itemSet.update(c)
        except KeyError: itemExists -= 1
        if itemExists > 0: out[ID] = itemSet
    return out
  except urllib.error.HTTPError as e: return {}

async def min_alert():
  try:
    delServID = set()
    async with lock_alert:
      curAlertDict = await min_alert_current()
      ### for each alert
      for alertID in curAlertDict.keys():
        ### for each server
        for servID in g.alertDict.keys():
          value = g.alertDict[servID].split("|")
          channel = client.get_channel(value[0])
          lang = (value[1] == LANG_KR)
          ### Start notif
          if channel:
            ## Check if sent
            sent = False
            async for log in client.logs_from(channel, limit=1000):
              if alertID in log.content:
                sent = True
                break
            ## Send
            if not sent:
              # Get block
              block = ""
              isAlert = False
              try:
                for alert in wfAPI()["Alerts"]:
                  if block: break
                  if alertID == alert["_id"]["$oid"]:
                    block = alert_block(alert, kr=lang)
                    isAlert = True
                for invasion in wfAPI()["Invasions"]:
                  if block: break
                  if alertID == invasion["_id"]["$oid"]: block = invasion_block(invasion, kr=lang)
              except urllib.error.HTTPError as e: return
              # Form text
              text = ((EMOJI_DAGGER if isAlert else EMOJI_SWORD) + " " + mono(now_ymdhms()+" UTC") + " " +
                      " ".join([mentionRole(channel.server, x) for x in curAlertDict[alertID]]) +
                      block + mono(alertID))
              await msg(channel, text)
          ### Mark for delete
          else: delServID.add(servID)
    ### Delete unused channel
    for servID in delServID: await min_notice_clear("alert", servID)
  except Exception as e: logging.warning("min_alert:" + type(e).__name__)

##### Cetus

def now_cetus(i):
  return (i + 3000) % 9000

def isCetusNight(i):
  return (now_cetus(i) < 3000)

def now_cetusStart(i):
  return i - now_cetus(i) + (0 if isCetusNight(i) else 3000)

async def min_cetus():
  try:
    i = now_int()
    cetusID = hash96(str(now_cetusStart(i)))
    delServID = set()
    async with lock_cetus:
      ### for each server
      for servID in g.cetusDict.keys():
        value = g.cetusDict[servID].split("|")
        channel = client.get_channel(value[0])
        kr = (value[1] == LANG_KR)
        ### Start notif
        if channel:
          ## Check if sent
          sent = False
          async for log in client.logs_from(channel, limit=1000):
            if cetusID in log.content:
              sent = True
              break
          ## Send
          if not sent:
            if kr:
              text = ((EMOJI_MOON + " " + mono(now_ymdhms()+" UTC") + " " +
                       " ".join([mentionRole(channel.server, x) for x in ["Cetus", "Night"]]) + "\n" +
                       box1("세투스의 밤이 시작되었습니다.") + mono(cetusID))
                      if isCetusNight(i) else
                      (EMOJI_SUN + " " + mono(now_ymdhms()+" UTC") + " " +
                       " ".join([mentionRole(channel.server, x) for x in ["Cetus", "Day"]]) + "\n" +
                       box1("세투스의 낮이 시작되었습니다.") + mono(cetusID)))
              await msg(channel, text)
            else:
              text = ((EMOJI_MOON + " " + mono(now_ymdhms()+" UTC") + " " +
                       " ".join([mentionRole(channel.server, x) for x in ["Cetus", "Night"]]) + "\n" +
                       box1("Cetus night cycle has started.") + mono(cetusID))
                      if isCetusNight(i) else
                      (EMOJI_SUN + " " + mono(now_ymdhms()+" UTC") + " " +
                       " ".join([mentionRole(channel.server, x) for x in ["Cetus", "Day"]]) + "\n" +
                       box1("Cetus day cycle has started.") + mono(cetusID)))
              await msg(channel, text)
        ### Mark for delete
        else: delServID.add(servID)
    ### Delete unused channel
    for servID in delServID: await min_notice_clear("cetus", servID)
  except Exception as e: logging.warning("min_cetus:" + type(e).__name__)

##### Event

async def min_event_set(server, code, user, time, kr):
  async with lock_event:
    k = server.id + "|" + code + "|" + time + "|" + (LANG_KR if kr else LANG_EN)
    g.eventDict[k] = "|" + user.id + "|"
    await servData_add("event", k + "\n" + g.eventDict[k] + "\n" + server.name)

async def min_event_clear(server, code):
  async with lock_event:
    key = server.id + "|" + code + "|"
    for k in g.eventDict.keys():
      if k.startswith(key):
        del g.eventDict[k]
        await servData_delete("event", k)
        return

async def min_event_join(server, code, user):
  async with lock_event:
    key = server.id + "|" + code + "|"
    for k in g.eventDict.keys():
      if k.startswith(key):
        g.eventDict[k] += user.id + "|"
        await servData_add("event", k + "\n" + g.eventDict[k] + "\n" + server.name)
        return

async def min_event_leave(server, code, user):
  async with lock_event:
    key = server.id + "|" + code + "|"
    for k in g.eventDict.keys():
      if k.startswith(key):
        g.eventDict[k] = g.eventDict[k].replace(wrap("|", user.id), "|")
        await servData_add("event", k + "\n" + g.eventDict[k] + "\n" + server.name)
        return

async def min_event_alert(server, code, time, timeLeft, users, kr):
  for user in users:
    h = hash96(server.id + code + str(time) + str(timeLeft))
    ### Check if sent
    sent = False
    for pChan in client.private_channels:
      # Private channel found
      if user.id == pChan.user.id:
        async for log in client.logs_from(pChan, limit=1000):
          if h in log.content:
            sent = True
            break
    ### Send
    if not sent:
      text = (EMOJI_BELL + " About " + str(timeLeft) + " minutes left\n" +
              box1("Server: " + server.name + "\n" +
                   "Code: " + code + "\n" +
                   "Current Time: " + now_ymdhms() + " UTC\n" +
                   "Event Time: " + time.strftime(DATETIME_YMDHM) + " UTC") +
              mono(h))
      await msg(user, text)

async def min_event():
  exps = []
  async with lock_event:
    for k in g.eventDict.keys():
      ### Key: servID|code|time|kr
      kps = k.split("|")
      servID = kps[0]
      code = kps[1]
      time = datetime.datetime.strptime(kps[2], DATETIME_YMDHM)
      kr = (kps[3] == LANG_KR)
      ### Value: |userID|
      vps = g.eventDict[k][1:-1].split("|")
      if time < now_datetime():
        ### Mark for delete
        exps.append(k)
      else:
        ### Alert for 10, 30, 60 minutes
        for t in [10, 30, 60]:
          if (time - datetime.timedelta(minutes=t)) < now_datetime():
            server = client.get_server(servID)
            users = [server.get_member(x) for x in vps]
            await min_event_alert(server, code, time, t, users, kr)
            break
  ### Delete
  for exp in exps:
    kps = exp.split("|")
    servID = kps[0]
    server = client.get_server(servID)
    code = kps[1]
    await min_event_clear(server, code)

##### Void Trader

async def min_voidTrader():
  try:
    for trader in wfAPI()["VoidTraders"]:
      tStart = int(trader["Activation"]["$date"]["$numberLong"])//1000
      tEnd = int(trader["Expiry"]["$date"]["$numberLong"])//1000
      tCur = now_int()
      ### Arrived
      if (tStart < tCur) and (tCur < tEnd):
        h = hash96(str(tStart))
        channel = client.get_channel(DATA_CHAN["itemBaro"])
        itemTypeList = []
        for item in trader["Manifest"]:
          data = item["ItemType"]
          if data not in g.itemDict: itemTypeList.append(data)
        ## Check if sent
        sent = False
        async for log in client.logs_from(channel, limit=1000):
          if h in log.content:
            sent = True
            break
        ### Send if not sent and some item data not converted
        if (not sent) and (itemTypeList): await msgs(channel, itemTypeList, post=mono(h), box=0)
  except Exception as e:
    logging.warning("min_voidTrader:" + type(e).__name__)


########## Test ##########
async def test(message):
  l = ["markdown","Ruby","PHP","Perl","python",
     "profile","xml","css","json","javascript",
     "coffeescript","django","apache","sql","java",
     "delphi","applescript","cpp","objectivec","ini",
     "cs","vala","d","rsl","rib",
     "mel","smalltalk","lisp","clojure","nginx",
     "diff","dos","bash","cmake","axapta",
     "glsl","lc","avrasm","vhdl","parser3",
     "tex","brainfuck","haskell","erlang","erlang-repl",
     "rust","matlab","r"]
  t = ("^help : List commands. (This one!)\n" +
       ">help admin (OPTION) b (option) : List commands that require permission.\n" +
       "^feedback [TEXT] a [text] : Send a feedback to developers.")
  for s in l:
    await client.send_message(message.channel, (s+
      "```" + s + "\n" + t + "```"))

async def paste():
  data = ""
  CHAN_VAULT = "332552719871115264"
  c = client.get_channel(CHAN_VAULT)
  async for message in client.logs_from(c, limit=10000):
    data += message.content + "\n"
  arg = {"api_dev_key":PASTEBIN_DEV_KEY,"api_paste_code":data,"api_option":"paste",
         "api_user_key":"","api_paste_private":int(1),"api_paste_expire_date":"10M"}
  request = urllib.request.urlopen(PASTEBIN_API_URL, urllib.parse.urlencode(arg).encode(CHAR_UTF8))
  return request.read()

async def export(message):
  link = await paste()
  await msg(message, "<" + str(link.decode(CHAR_UTF8)) + ">")

def debug(text):
  if DEBUG:
    with open("debug.txt", "w", encoding=CHAR_UTF8) as file:
      file.write(str(text))

########## Initialization ##########

##### Starchart dictionary generation from GitHub
def init_node():
  data = eval(fileData_read("node"))
  for k in data.keys():
    g.nodeDict[k] = data[k][0]
    g.nodeMTypeDict[k] = convert("mission", data[k][1])

async def init_servData():
  for s, o in g.servData.items():
    # Clean up data
    # await servData_clean(s)
    # Update data from server
    o.clear()
    o = await servData_eval(s, o)

def init_enkr():
  data = fileData_code("enkr")
  for line in data:
    conv = line.split(":")
    g.enkrDict[conv[0]] = conv[1]

def init_ducat():
  data = fileData_code("ducat")
  for line in data:
    conv = line.split(":")
    if conv[0] not in g.ducatDict.keys(): g.ducatDict[conv[0]] = {}
    g.ducatDict[conv[0]][conv[1]] = int(conv[2])

##### Droptable

def dropDict_rec(d, l):
  if len(l) == 2:
    k = l[0]
    v = l[1]
    if k not in d.keys(): d[k] = set()
    d[k].add(v)
  elif len(l) > 2:
    k = l[0]
    v = l[1:]
    if k not in d.keys(): d[k] = {}
    dropDict_rec(d[k], v)

def dropDict_insert(q, d, col):
  query = q.strip()
  data = [x.strip() for x in d]
  if query not in g.dropDict.keys(): g.dropDict[query] = []
  if col not in [x[0] for x in g.dropDict[query]]: g.dropDict[query].append((col, {}))
  for l in g.dropDict[query]:
    if l[0] == col:
       dropDict_rec(l[1], data)
       return

def init_drop():
  api = api_json(URL_WFCD_DROPTABLE)
  # missionRewards
  a = api["missionRewards"]
  for planet in a.keys():
    for node in a[planet].keys():
      rewards = a[planet][node]["rewards"]
      if type(rewards) == list:
        for data in rewards:
          item = data["itemName"]
          chance = str(float(data["chance"])) + "%"
          dropDict_insert(node, [item, chance], ["Item","Chance"])
          dropDict_insert(item, [node + ", " + planet, chance], ["Source","Chance"])
      else:
        for rotation in rewards.keys():
          for data in rewards[rotation]:
            item = data["itemName"]
            chance = str(float(data["chance"])) + "%"
            dropDict_insert(node, ["Rotation " + rotation, item, chance], ["Source","Item","Chance"])
            dropDict_insert(item, [node + " (Rot." + rotation + "), " + planet, chance], ["Source","Chance"])
  # relics
  a = api["relics"]
  for relic in a:
    name = relic["tier"] + " " + relic["relicName"] + " Relic"
    state = relic["state"]
    for data in relic["rewards"]:
      item = data["itemName"]
      chance = str(float(data["chance"])) + "%"
      dropDict_insert(name, [state, item, chance], ["Refinement","Item","Chance"])
      dropDict_insert(item, [name + " " + state, chance], ["Relic","Chance"])
  # transientRewards
  a = api["transientRewards"]
  for obj in a:
    name = obj["objectiveName"]
    for data in obj["rewards"]:
      rotation = data["rotation"]
      item = data["itemName"]
      chance = str(float(data["chance"])) + "%"
      if rotation:
        dropDict_insert(item, [name + " (Rot." + rotation + ")", chance], ["Source","Chance"])
        dropDict_insert(name, ["Rotation " + rotation, item, chance], ["Source","Item","Chance"])
      else:
        dropDict_insert(item, [name, chance], ["Source","Chance"])
        dropDict_insert(name, [item, chance], ["Item","Chance"])
  # modLocations
  a = api["modLocations"]
  for mod in a:
    item = mod["modName"]
    for data in mod["enemies"]:
      name = data["enemyName"]
      dropChance = str(float(data["enemyModDropChance"])) + "%"
      chance = str(float(data["chance"])) + "%"
      dropDict_insert(item, [name, dropChance, chance], ["Enemy", "Mod Drop Chance","Chance"])
      dropDict_insert(name, [item, dropChance, chance], ["Item", "Mod Drop Chance","Chance"])
  # enemyModTables
  a = api["enemyModTables"]
  for enemy in a:
    name = enemy["enemyName"]
    dropChance = str(float(enemy["ememyModDropChance"])) + "%"
    for data in enemy["mods"]:
      item = data["modName"]
      chance = str(float(data["chance"])) + "%"
      dropDict_insert(item, [name, dropChance, chance], ["Enemy", "Mod Drop Chance","Chance"])
      dropDict_insert(name, [item, dropChance, chance], ["Item", "Mod Drop Chance","Chance"])
  # blueprintLocations
  a = api["blueprintLocations"]
  for mod in a:
    item = mod["blueprintName"]
    for data in mod["enemies"]:
      name = data["enemyName"]
      dropChance = str(float(data["enemyBlueprintDropChance"])) + "%"
      chance = str(float(data["chance"])) + "%"
      dropDict_insert(item, [name, dropChance, chance], ["Enemy", "BP Drop Chance","Chance"])
      dropDict_insert(name, [item, dropChance, chance], ["Item", "BP Drop Chance","Chance"])
  # enemyBlueprintTables
  a = api["enemyBlueprintTables"]
  for enemy in a:
    name = enemy["enemyName"]
    dropChance = str(float(enemy["blueprintDropChance"])) + "%"
    for data in enemy["mods"]:
      item = data["modName"]
      chance = str(float(data["chance"])) + "%"
      dropDict_insert(item, [name, dropChance, chance], ["Enemy", "BP Drop Chance","Chance"])
      dropDict_insert(name, [item, dropChance, chance], ["Item", "BP Drop Chance","Chance"])
  # sortieRewards
  a = api["sortieRewards"]
  for data in a:
    item = data["itemName"]
    chance = str(float(data["chance"])) + "%"
    dropDict_insert(item, ["Sortie", chance], ["Source","Chance"])
    dropDict_insert("Sortie", [item, chance], ["Item","Chance"])
  # keyRewards
  a = api["keyRewards"]
  for key in a:
    name = key["keyName"]
    for rotation in key["rewards"].keys():
      for data in key["rewards"][rotation]:
        item = data["itemName"]
        chance = str(float(data["chance"])) + "%"
        dropDict_insert(item, [name + " (Rot." + rotation + ")", chance], ["Source","Chance"])
        dropDict_insert(name, ["Rotation " + rotation, item, chance], ["Source","Item","Chance"])
  # cetusBountyRewards
  '''a = api["cetusBountyRewards"]
  for bounty in a:
    name = bounty["bountyLevel"]
    for rotation in bounty["rewards"].keys():
      for data in bounty["rewards"][rotation]:
        item = data["itemName"]
        chance = str(float(data["chance"])) + "%"
        dropDict_insert(item, [name + " (Rot." + rotation + ")", chance], ["Source","Chance"])
        dropDict_insert(name, ["Rotation " + rotation, item, chance], ["Source","Item","Chance"])'''

async def init():
  init_node()
  init_enkr()
  init_ducat()
  init_drop()
  await init_servData()
  await client.change_presence(game=discord.Game(name=str(PREFIX + "도움말 | " + PREFIX + "help")))

########## Loop ##########

async def loop_min():
  await client.wait_until_ready()
  await init()
  while not client.is_closed:
    try:
      await min_item() # Upload item data
      await min_delete() # Delete msgs
      await min_alert() # Notification
      await min_cetus() # Cetus day/night cycle
      await min_event() # Event alerts
      await min_voidTrader() # Save unconverted item data
    except Exception as e: logging.warning("loop_min:" + type(e).__name__)
    finally: await asyncio.sleep(10)

########## Run ##########

client.loop.create_task(loop_min())
if DEBUG: client.run(os.getenv("BOT_DEBUG_TOKEN", ""))
else: client.run(os.getenv("BOT_TOKEN", ""))
