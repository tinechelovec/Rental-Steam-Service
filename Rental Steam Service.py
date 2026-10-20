import os
import json
import re
import time
import math
import uuid
import shutil
import hashlib
import logging
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone, timedelta
from urllib.parse import quote

import requests
from bs4 import BeautifulSoup
from telebot.types import InlineKeyboardMarkup as K, InlineKeyboardButton as B
import tg_bot.CBT as CBT

NAME = 'Rental Steam Service'
VERSION = '1.0.0'
DESCRIPTION = 'Автоматическая аренда Steam-аккаунтов через подключаемых провайдеров для FunPay.'
CREDITS = '@tinechelovec'
UUID = 'c496f874-3f3c-4d08-a53a-ae8b94f8de73'
SETTINGS_PAGE = False

CREATOR_URL = 'https://t.me/tinechelovec'
INSTRUCTION_URL = 'https://teletype.in/@tinechelovec/Rental-Steam-Service'
INSTRUCTION_GITHUB_URL = 'https://github.com/tinechelovec/Rental-Steam-Service/blob/main/instructions.md'
REPOSITORY_URL = 'https://github.com/tinechelovec/Rental-Steam-Service'
GROUP_URL = 'https://t.me/dev_thc_chat'
CHANNEL_URL = 'https://t.me/by_thc'
STEAMSMM_DOCS_URL = 'https://steamsmm.ru/api/docs?lang=ru'
STEAMSMM_SERVICE_URL = 'https://steamsmm.ru/register?ref=lgtTgUBk'
KOSELL_SERVICE_URL = 'https://ru.kosell.store/rent'
MUVSELL_SERVICE_URL = 'https://muvsell.store/login?mode=register&ref=111'

STEAMSMM_BASE = os.getenv('AUTO_RENTAL_STEAMSMM_BASE', 'https://steamsmm.ru/api').strip().rstrip('/')
PLUGIN_FOLDER = 'storage/plugins/FPC-Auto-Rental'
SETTINGS_FILE = os.path.join(PLUGIN_FOLDER, 'settings.json')
SETTINGS_BAK = SETTINGS_FILE + '.bak'
RENTALS_FILE = os.path.join(PLUGIN_FOLDER, 'rentals.json')
RENTALS_BAK = RENTALS_FILE + '.bak'
EXTENSIONS_FILE = os.path.join(PLUGIN_FOLDER, 'extension_lots.json')
EXTENSIONS_BAK = EXTENSIONS_FILE + '.bak'
LOG_FILE = os.path.join(PLUGIN_FOLDER, 'log.txt')

HTTP_CONNECT_TIMEOUT = float(os.getenv('AUTO_RENTAL_CONNECT_TIMEOUT', '10'))
HTTP_READ_TIMEOUT = float(os.getenv('AUTO_RENTAL_READ_TIMEOUT', '35'))
DEFAULT_CHECK_INTERVAL = max(60, int(os.getenv('AUTO_RENTAL_CHECK_INTERVAL', '300')))
DEFAULT_EXTENSION_TTL = max(300, int(os.getenv('AUTO_RENTAL_EXTENSION_TTL', '1200')))
DEFAULT_GUARD_COOLDOWN = max(10, int(os.getenv('AUTO_RENTAL_GUARD_COOLDOWN', '25')))
LOT_SAVE_RETRIES = max(1, min(3, int(os.getenv('AUTO_RENTAL_LOT_SAVE_RETRIES', '3'))))
LOT_SAVE_VERIFY_DELAY = max(0.0, float(os.getenv('AUTO_RENTAL_LOT_SAVE_VERIFY_DELAY', '0.8')))
LOT_SAVE_LOCATION = os.getenv('AUTO_RENTAL_LOT_SAVE_LOCATION', 'trade').strip() or 'trade'
FALLBACK_UA = os.getenv(
    'AUTO_RENTAL_FALLBACK_UA',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36'
).strip()

logger = logging.getLogger('Rental-Steam-Service')
logger.setLevel(logging.INFO)
logger.propagate = False
os.makedirs(PLUGIN_FOLDER, exist_ok=True)

class _AnsiLogFormatter(logging.Formatter):
    RESET = '\x1b[0m'
    DIM = '\x1b[90m'
    BOLD = '\x1b[1m'
    TAG = '\x1b[95m'
    COLORS = {
        logging.DEBUG: '\x1b[90m',
        logging.INFO: '\x1b[96m',
        logging.WARNING: '\x1b[93m',
        logging.ERROR: '\x1b[91m',
        logging.CRITICAL: '\x1b[97;41m',
    }
    LETTERS = {
        logging.DEBUG: 'D', logging.INFO: 'I', logging.WARNING: 'W',
        logging.ERROR: 'E', logging.CRITICAL: 'C',
    }
    def format(self, record):
        ts = time.strftime('%d-%m-%Y %H:%M:%S', time.localtime(record.created))
        color = self.COLORS.get(record.levelno, '\x1b[96m')
        letter = self.LETTERS.get(record.levelno, 'I')
        msg = record.getMessage()


        msg = re.sub(r'^\s*\[Rental Steam Service\]\s*', '', str(msg), flags=re.I)
        return (
            f'{self.DIM}[{ts}]>{self.RESET} '
            f'{color}{self.BOLD}{letter}:{self.RESET} '
            f'{self.TAG}{self.BOLD}[Rental Steam Service]{self.RESET} '
            f'{color}{msg}{self.RESET}'
        )

for _handler in list(logger.handlers):
    try:
        logger.removeHandler(_handler)
    except Exception:
        pass
sh = logging.StreamHandler()
sh.setFormatter(_AnsiLogFormatter())
logger.addHandler(sh)
try:
    fh = logging.FileHandler(LOG_FILE, encoding='utf-8')
    fh.setFormatter(logging.Formatter('[%(asctime)s]> %(levelname).1s: [Rental Steam Service] %(message)s', '%d-%m-%Y %H:%M:%S'))
    logger.addHandler(fh)
except Exception:
    pass

_HTTP = requests.Session()
_SETTINGS_LOCK = threading.RLock()
_RENTALS_LOCK = threading.RLock()
_EXTENSIONS_LOCK = threading.RLock()
_FSM_LOCK = threading.RLock()
_JOBS_LOCK = threading.RLock()
_FSM = {}
_JOBS = {}
_CARDINAL_REF = None
_MAINT_THREAD_STARTED = False
_MAINT_STOP = threading.Event()
_LAST_GUARD = {}
_LAST_COMMAND_REPLY = {}
_LAST_AUTO_SYNC = 0
_LOT_LIST_PAGE = {}

CB = 'ar:' + UUID[:8]
CB_HOME = CB + ':home'
CB_SETTINGS = CB + ':settings'
CB_INFO = CB + ':info'
CB_UPDATE = CB + ':update'
CB_UPDATE_LOCAL = CB + ':update_local'
CB_UPDATE_ONLINE = CB + ':update_online'
CB_MINI_SETTINGS = CB + ':mini_settings'
CB_PLUGIN_STATUS = CB + ':plugin_status'
CB_STATS = CB + ':stats'
CB_STATS_REFRESH = CB + ':stats_refresh'
CB_SYNC_MENU = CB + ':sync_menu'
CB_AUTO_CHECK = CB + ':auto_check'
CB_DELETE_ASK = CB + ':delete_ask'
CB_DELETE_YES = CB + ':delete_yes'
CB_DELETE_NO = CB + ':delete_no'
CB_PLUGINS_LIST = f"{getattr(CBT, 'PLUGINS_LIST', '44')}:0"
CB_TOKEN = CB + ':token'
CB_LOTS = CB + ':lots'
CB_LOT_ADD = CB + ':la'
CB_LOT_REFRESH = CB + ':lr'
CB_LOTS_PAGE = CB + ':lpg:'
CB_LOTS_GENERAL = CB + ':lg'
CB_LOTS_ALL_ON = CB + ':lgaon'
CB_LOTS_ALL_OFF = CB + ':lgaoff'
CB_LOTS_GENERAL_MARKUP = CB + ':lgmk'
CB_LOTS_GENERAL_PRICE = CB + ':lgprice'
CB_LOTS_GENERAL_DEACT = CB + ':lgdeact'
CB_LOTS_GENERAL_RESERVE = CB + ':lgrsv'
CB_LOTS_GENERAL_INTERVAL = CB + ':lgint'
CB_LOTS_GENERAL_CHECK = CB + ':lgcheck'
CB_ADD_PRODUCT_PICK = CB + ':apick:'
CB_ADD_PRODUCT_PAGE = CB + ':apg:'
CB_LOT_OPEN = CB + ':lo:'
CB_LOT_TOGGLE = CB + ':lt:'
CB_LOT_AP = CB + ':lap:'
CB_LOT_AS = CB + ':las:'
CB_LOT_AB = CB + ':lab:'
CB_LOT_MARKUP = CB + ':lmk:'
CB_LOT_MARKUP_GLOBAL = CB + ':lmg:'
CB_LOT_MARKUP_CUSTOM = CB + ':lmc:'
CB_LOT_DEL = CB + ':ld:'
CB_PRODUCTS = CB + ':products'
CB_PRODUCTS_PAGE = CB + ':pp:'
CB_PRODUCT_HELP = CB + ':product_help'
CB_AUTO = CB + ':auto'
CB_AUTO_TOGGLE_PRICE = CB + ':atp'
CB_AUTO_TOGGLE_DEACT = CB + ':atd'
CB_AUTO_RESERVE = CB + ':arv'
CB_AUTO_INTERVAL = CB + ':aint'
CB_GLOBAL_MARKUP = CB + ':gmk'
CB_SYNC = CB + ':sync'
CB_RENTALS = CB + ':rentals'
CB_RENT_OPEN = CB + ':ro:'
CB_RENT_STATUS = CB + ':rs:'
CB_RENT_CREDS = CB + ':rc:'
CB_RENT_GUARD = CB + ':rg:'
CB_RENT_EXT1 = CB + ':re1:'
CB_RENT_EXT24 = CB + ':re24:'
CB_RENT_EXT168 = CB + ':re168:'
CB_EXT = CB + ':ext'
CB_EXT_TTL = CB + ':ettl'
CB_EXT_MARKUP = CB + ':emk'
CB_EXT_TOGGLE = CB + ':etg'
CB_COMMANDS = CB + ':cmd'
CB_CMD_GUARD = CB + ':cg'
CB_CMD_CREDS = CB + ':cc'
CB_CMD_STATUS = CB + ':cs'
CB_CMD_EXTEND = CB + ':ce'
CB_MESSAGES = CB + ':msg'
CB_NOTIFICATIONS = CB + ':notifications'
CB_NOTIFY_MASTER = CB + ':nm'
CB_NOTIFY_ORDER = CB + ':no'
CB_NOTIFY_RENT = CB + ':nr'
CB_NOTIFY_ERROR = CB + ':ne'
CB_NOTIFY_STOCK = CB + ':ns'
CB_NOTIFY_PRICE = CB + ':np'
CB_NOTIFY_LOT = CB + ':nl'
CB_NOTIFY_EXT = CB + ':nx'
CB_NOTIFY_API = CB + ':na'
CB_MSG_EDIT = CB + ':me:'
CB_CANCEL = CB + ':cancel'


def _h(value):
    import html
    return html.escape(str(value), quote=False)


def _now():
    return int(time.time())


def _compact_error(error, limit=260):
    text = str(error or '').strip()
    if not text:
        return 'неизвестная ошибка'
    m = re.search(r'Текст ответа:\s*(\{.*?\})(?:\s*$|\n)', text, re.S)
    if m:
        raw = m.group(1)
        try:
            data = json.loads(raw)
            parts = []
            for row in data.get('errors') or []:
                if isinstance(row, (list, tuple)) and len(row) >= 2 and row[1]:
                    parts.append(str(row[1]))
            general = str(data.get('error') or '').strip()
            if general and general not in parts:
                parts.append(general)
            text = 'FunPay: ' + ('; '.join(dict.fromkeys(parts)) if parts else raw)
        except Exception:
            text = 'FunPay: ' + raw
    text = re.sub(r'\s+', ' ', text).strip()
    return text if len(text) <= limit else text[:limit - 1] + '…'


def _remember_lot_funpay_price(lot_id, price):
    try:
        owner_key, cfg = _owner_entry()
        if owner_key is None:
            return
        rows = cfg.get('lots') or []
        for row in rows:
            if int(row.get('lot_id') or 0) == int(lot_id):
                row['last_funpay_price'] = round(float(price), 2)
                _set_cfg(owner_key, lots=rows)
                return
    except Exception:
        pass

def _as_int(value, default=0, minimum=None, maximum=None):
    try:
        if isinstance(value, bool):
            raise ValueError
        if isinstance(value, str):
            m = re.search(r'-?\d+', value.strip())
            if not m:
                raise ValueError
            n = int(m.group(0))
        else:
            n = int(float(value))
    except Exception:
        n = int(default)
    if minimum is not None:
        n = max(int(minimum), n)
    if maximum is not None:
        n = min(int(maximum), n)
    return n


def _normalize_rental_id(value):
    if value is None or isinstance(value, bool):
        return ''
    value = str(value).strip()
    if not value:
        return ''


    value = value.strip('/')
    if not value or len(value) > 256:
        return ''
    return value


def _rental_path_id(value):
    rid = _normalize_rental_id(value)
    if not rid:
        raise SteamSMMError('У аренды отсутствует rental_id.', code='BAD_RENTAL_ID')
    return quote(rid, safe='')


def _as_float(value, default=0.0, minimum=None):
    try:
        if value is None or isinstance(value, bool):
            raise ValueError
        if isinstance(value, str):
            s = value.strip().replace(',', '.')
            m = re.search(r'-?\d+(?:\.\d+)?', s)
            if not m:
                raise ValueError
            f = float(m.group(0))
        else:
            f = float(value)
    except Exception:
        f = float(default)
    if minimum is not None:
        f = max(float(minimum), f)
    return f


def _cfg_bool(cfg, key, default=False):
    value = cfg.get(key, default)
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {'1', 'true', 'yes', 'on', 'вкл'}
    return bool(default)


def _atomic_json(path, data, backup=None):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if backup and os.path.exists(path):
        try:
            shutil.copy2(path, backup)
        except Exception:
            pass
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def _load_json(path, default, backup=None):
    for candidate in (path, backup):
        if not candidate or not os.path.exists(candidate):
            continue
        try:
            with open(candidate, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, type(default)):
                return data
        except Exception as e:
            logger.warning('Не удалось прочитать %s: %s', candidate, e)
    return json.loads(json.dumps(default))


def _default_templates():
    return {
        'review_gift_offer': '🎁 Отзыв от {stars}★ — +{duration} к аренде бесплатно.',
        'review_gift_success': '🎁 Спасибо за отзыв! +{duration} к аренде.\nДо: {ends_at}',
        'rent_success': (
            '✅ Аренда активна\n'
            '🎮 {game} · {duration}\n'
            '⏰ До: {ends_at}\n\n'
            '🔐 Логин: {login}\n'
            'Пароль: {password}\n\n'
            '🛡 {guard_command}\n'
            '⏱ {status_command}\n'
            '➕ {extend_command}'
        ),
        'rent_failed': '⚠️ Не удалось выдать аккаунт автоматически. {reason}',
        'credentials': (
            '🔐 Логин: {login}\n'
            'Пароль: {password}\n\n'
            '🛡 {guard_command} · ⏱ {status_command} · ➕ {extend_command}'
        ),
        'credentials_pending': '⏳ Аренда активна, данные входа ещё готовятся. Пришлю их сюда автоматически.',
        'credentials_failed': '⚠️ Сейчас не удалось получить данные. {reason}',
        'guard': '🔐 Steam Guard: {code}',
        'guard_wait': '⏳ Новый код можно запросить через {seconds} сек.',
        'guard_failed': '⚠️ Не удалось получить Steam Guard. {reason}',
        'status': '⏱ Осталось: {remaining}\nДо: {ends_at}',
        'status_failed': '⚠️ Не удалось проверить срок. {reason}',
        'extend_choose': '➕ Выберите продление:\n{cmd1}\n{cmd24}\n{cmd168}',
        'extend_offer': '➕ +{duration} · {price} ₽\n{lot_time}\n{url}',
        'extend_success': '✅ Продлено на {duration}. До: {ends_at}',
        'extend_failed': '⚠️ Продление не выполнено. {reason}',
        'extension_disabled': 'Продление сейчас выключено.',
        'extend_usage': 'Напишите !продлить_ЗАКАЗ или !продлить_ЛОГИН.',
        'extension_existing': '🔗 Лот для продления уже создан:\n{url}',
        'extension_create_failed': '⚠️ Не удалось создать лот продления. {reason}',
        'extension_expired': '⌛ Временный лот истёк. Отправьте команду продления ещё раз.',
        'no_active_rental': 'Не нашёл активную аренду по этим данным.',
        'rental_expired': 'Срок этой аренды уже закончился.',
        'bad_guard_command': 'Формат: !код_ЛОГИН',
        'bad_status_command': 'Формат: !срок_ЗАКАЗ или !срок_ЛОГИН',
        'bad_credentials_command': 'Формат: !данные_ЗАКАЗ',
    }


_LEGACY_TEMPLATES_V5 = {'review_gift_offer': '🎁 За отзыв любой оценки по этому заказу — +{duration} к аренде бесплатно. Оставьте отзыв, пока аренда активна: подарок будет выдан автоматически после проверки.', 'review_gift_success': '🎁 Спасибо за отзыв! Аренда {game} продлена бесплатно на {duration}.\nНовый срок: {ends_at}', 'rent_success': '✅ Аренда успешно активирована!\n\n🎮 Игра: {game}\n⏱ Срок: {duration}\n📅 Аренда до: {ends_at}\n\n🔐 Данные для входа\nЛогин: {login}\nПароль: {password}\n\n📌 Команды для этой аренды\n🛡 Steam Guard: {guard_command}\n⏱ Проверить срок: {status_command}\n➕ Продлить: {extend_command}', 'rent_failed': '⚠️ Автовыдача аренды пока не выполнена.\nПричина: {reason}\nЗаказ сохранён. При временной ошибке возможен автоматический повтор; если результат списания неизвестен, потребуется проверка продавцом.', 'credentials': '🔐 Данные для входа\nЛогин: {login}\nПароль: {password}\n\n📌 Команды для этой аренды\n🛡 Steam Guard: {guard_command}\n⏱ Проверить срок: {status_command}\n➕ Продлить: {extend_command}', 'credentials_pending': '⏳ Аренда {game} уже активирована. Получаю данные аккаунта у провайдера.\nКак только логин и пароль будут готовы, я пришлю их автоматически.\nПовторно оплачивать заказ не нужно.', 'credentials_failed': '⚠️ Не удалось получить данные аккаунта: {reason}', 'guard': '🔐 Steam Guard код: {code}\n\nИспользуйте код сразу.', 'guard_wait': '⏳ Guard-код запрашивался недавно. Повторите через {seconds} сек.', 'guard_failed': '⚠️ Не удалось получить Steam Guard: {reason}', 'status': '🎮 {game}\nСтатус: {status}\nЗакончится: {ends_at}\nОсталось: {remaining}', 'status_failed': '⚠️ Не удалось проверить срок аренды: {reason}', 'extend_choose': '➕ Выберите срок продления для {game}:\n\n{cmd1}\n{cmd24}\n{cmd168}', 'extend_offer': '🕒 Продление для {game}\nСрок: +{duration}\nЦена: {price} ₽\n\nЛот действует {ttl_minutes} мин.:\n{url}', 'extend_success': '✅ Аренда {game} продлена на {duration}.\nНовый срок: {ends_at}', 'extend_failed': '⚠️ Продление пока не выполнено. Причина: {reason}', 'extension_disabled': 'Продление сейчас отключено продавцом.', 'extend_usage': 'Формат: !продлить_ЗАКАЗ или !продлить_ЛОГИН.', 'extension_existing': 'У вас уже есть активный лот продления:\n{url}', 'extension_create_failed': '⚠️ Не удалось создать лот продления: {reason}', 'extension_expired': '🗑 Лот продления истёк и удалён. Создайте новый командой !продлить_ЗАКАЗ.', 'no_active_rental': 'Не нашёл актуальную аренду для указанных данных.', 'rental_expired': 'Эта аренда уже закончилась. Доступ к аккаунту больше не относится к этому заказу.', 'bad_guard_command': 'Формат: !код_ЛОГИН', 'bad_status_command': 'Формат: !срок_ЗАКАЗ или !срок_ЛОГИН', 'bad_credentials_command': 'Формат: !данные_ЗАКАЗ'}

def _default_cfg():
    return {
        'plugin_enabled': True,
        'api_key': '',
        'providers': {},
        'balance': None,
        'regular_balance': None,
        'promo_balance': None,
        'currency': 'RUB',
        'last_api_ok': 0,
        'last_api_error': '',
        'lots': [],
        'global_markup_percent': 20.0,
        'auto_price_enabled': True,
        'auto_deactivate_enabled': True,
        'check_interval_sec': DEFAULT_CHECK_INTERVAL,
        'min_balance_rub': 0.0,
        'funpay_card_factor': 1.1915,
        'funpay_sbp_factor': 1.1405,
        'extension_enabled': True,
        'review_gift_enabled': False,
        'review_gift_hours': 1,
        'review_gift_min_stars': 5,
        'extension_temporary_enabled': True,
        'extension_ttl_sec': 1200,
        'guard_cooldown_sec': DEFAULT_GUARD_COOLDOWN,
        'guard_command': '!код',
        'credentials_command': '!данные',
        'status_command': '!срок',
        'extend_command': '!продлить',
        'templates': _default_templates(),
        'price_notifications': True,
        'stock_notifications': True,
        'notifications_enabled': True,
        'notify_orders': True,
        'notify_rentals': True,
        'notify_errors': True,
        'notify_stock': True,
        'notify_price': True,
        'notify_lot_state': True,
        'notify_extensions': True,
        'notify_api': True,
        'last_notified_balance_state': '',
        'api_was_down': False,
        'config_version': 6,
    }


def _sanitize_lot(item):
    if not isinstance(item, dict):
        return None
    lot_id = _as_int(item.get('lot_id'), 0, 1)
    product_id = _as_int(item.get('product_id'), 0, 1)
    hours = _as_int(item.get('duration_hours'), 0, 1)
    if not lot_id or not product_id or not hours:
        return None
    override = item.get('markup_override_percent', None)
    if override is None and 'markup_override_percent' not in item and 'markup_percent' in item:
        override = item.get('markup_percent')
    if override is not None:
        override = _as_float(override, 0.0)
    row = dict(item)
    row.update({
        'lot_id': lot_id,
        'provider': str(item.get('provider') or 'steamsmm'),
        'product_id': product_id,
        'duration_hours': hours,
        'product_name': str(item.get('product_name') or f'Product {product_id}')[:160],
        'markup_override_percent': override,
        'auto_price': _cfg_bool(item, 'auto_price', True),
        'auto_stock': _cfg_bool(item, 'auto_stock', True),
        'auto_balance': _cfg_bool(item, 'auto_balance', True),
        'manual_enabled': _cfg_bool(item, 'manual_enabled', True),
        'auto_disabled': _cfg_bool(item, 'auto_disabled', False),
        'auto_disabled_reason': str(item.get('auto_disabled_reason') or ''),
        'last_stock': _as_int(item.get('last_stock'), -1),
        'last_funpay_amount': _as_int(item.get('last_funpay_amount'), -1),
        'last_api_cost': _as_float(item.get('last_api_cost'), 0.0),
        'last_funpay_price': _as_float(item.get('last_funpay_price'), 0.0),
        'updated_ts': _as_int(item.get('updated_ts'), 0),
    })
    row.pop('markup_percent', None)
    return row

def _sanitize_cfg(raw):
    if isinstance(raw, dict) and 'min_balance_rub' not in raw and 'balance_reserve_rub' in raw:
        raw = dict(raw, min_balance_rub=raw['balance_reserve_rub'])
    cfg = _default_cfg()
    if isinstance(raw, dict):
        cfg.update(raw)
    cfg.pop('balance_reserve_rub', None)
    cfg['review_gift_enabled'] = _cfg_bool(cfg, 'review_gift_enabled', False)
    cfg['review_gift_hours'] = _as_int(cfg.get('review_gift_hours'), 1, 1, 720)
    cfg['review_gift_min_stars'] = _as_int(cfg.get('review_gift_min_stars'), 5, 1, 5)

    cfg['extension_temporary_enabled'] = True
    cfg['plugin_enabled'] = _cfg_bool(cfg, 'plugin_enabled', True)
    cfg['api_key'] = str(cfg.get('api_key') or '').strip()
    raw_providers = cfg.get('providers')
    cfg['providers'] = {k: dict(v, api_key=str(v.get('api_key') or '').strip()) for k, v in (raw_providers.items() if isinstance(raw_providers, dict) else []) if k in {'kosell', 'muvsell'} and isinstance(v, dict)}
    for key in ('balance', 'regular_balance', 'promo_balance'):
        value = cfg.get(key)
        cfg[key] = _as_float(value, 0.0) if value is not None else None
    cfg['auto_price_enabled'] = _cfg_bool(cfg, 'auto_price_enabled', True)
    cfg['auto_deactivate_enabled'] = _cfg_bool(cfg, 'auto_deactivate_enabled', True)
    cfg['extension_enabled'] = _cfg_bool(cfg, 'extension_enabled', True)
    cfg['global_markup_percent'] = _as_float(cfg.get('global_markup_percent'), 20.0)
    cfg['price_notifications'] = _cfg_bool(cfg, 'price_notifications', True)
    cfg['stock_notifications'] = _cfg_bool(cfg, 'stock_notifications', True)
    for _nk in ('notifications_enabled', 'notify_orders', 'notify_rentals', 'notify_errors',
                'notify_stock', 'notify_price', 'notify_lot_state', 'notify_extensions', 'notify_api'):
        cfg[_nk] = _cfg_bool(cfg, _nk, True)
    cfg['last_notified_balance_state'] = str(cfg.get('last_notified_balance_state') or '')
    cfg['api_was_down'] = _cfg_bool(cfg, 'api_was_down', False)
    cfg['check_interval_sec'] = _as_int(cfg.get('check_interval_sec'), DEFAULT_CHECK_INTERVAL, 60, 86400)
    cfg['min_balance_rub'] = _as_float(cfg.get('min_balance_rub'), 0.0, 0.0)
    cfg['funpay_card_factor'] = _as_float(cfg.get('funpay_card_factor'), 1.1915, 1.0)
    cfg['funpay_sbp_factor'] = _as_float(cfg.get('funpay_sbp_factor'), 1.1405, 1.0)

    cfg['extension_ttl_sec'] = 1200
    cfg['guard_cooldown_sec'] = _as_int(cfg.get('guard_cooldown_sec'), DEFAULT_GUARD_COOLDOWN, 10, 600)
    cfg['guard_command'] = '!код'
    cfg['credentials_command'] = '!данные'
    cfg['status_command'] = '!срок'
    cfg['extend_command'] = '!продлить'
    templates = _default_templates()
    legacy_template_defaults = {
        'rent_success': (
            '✅ Аренда успешно активирована!\n\n'
            '🎮 Игра: {game}\n'
            '⏱ Срок: {duration}\n'
            '📅 Аренда до: {ends_at}\n\n'
            '🔐 Логин: {login}\n'
            '🔑 Пароль: {password}\n\n'
            '🛡 Steam Guard: {guard_command}\n'
            '⏱ Проверить срок: {status_command}\n'
            '➕ Продлить: {extend_command}'
        ),
        'credentials': (
            '🔐 Логин: {login}\n'
            '🔑 Пароль: {password}\n\n'
            '🛡 Guard: {guard_command}\n'
            '⏱ Срок: {status_command}\n'
            '➕ Продлить: {extend_command}'
        ),
        'credentials_pending': (
            '✅ Аренда {game} активирована, но провайдер пока не отдал данные входа.\n'
            'Попробуйте чуть позже: {credentials_command}'
        ),
    }
    if isinstance(cfg.get('templates'), dict):
        for key, value in cfg['templates'].items():
            if key in templates and isinstance(value, str) and value.strip():
                if _as_int((raw or {}).get('config_version'), 0) < 6 and value == _LEGACY_TEMPLATES_V5.get(key):
                    continue

                if key in legacy_template_defaults and value == legacy_template_defaults[key]:
                    continue


                if key in {'rent_success', 'credentials'} and 'Повторно получить данные: {credentials_command}' in value:
                    continue
                if key == 'credentials_pending':
                    low = value.casefold()


                    if ('steam guard:' in low or '{guard_command}' in low or '{status_command}' in low) and ('пока не отдал' in low or 'данные входа' in low):
                        continue
                templates[key] = value
    cfg['templates'] = templates
    lots = []
    seen = set()
    for item in cfg.get('lots') or []:
        row = _sanitize_lot(item)
        if not row or row['lot_id'] in seen:
            continue
        seen.add(row['lot_id'])
        lots.append(row)
    cfg['lots'] = sorted(lots, key=lambda x: x['lot_id'])
    cfg['config_version'] = 6
    return cfg


def _load_settings():
    with _SETTINGS_LOCK:
        data = _load_json(SETTINGS_FILE, {}, SETTINGS_BAK)
        changed = False
        result = {}
        for key, value in data.items():
            if not isinstance(value, dict):
                continue
            cfg = _sanitize_cfg(value)
            result[str(key)] = cfg
            if cfg != value:
                changed = True
        if changed:
            _atomic_json(SETTINGS_FILE, result, SETTINGS_BAK)
        return result


def _save_settings(data):
    with _SETTINGS_LOCK:
        normalized = {str(k): _sanitize_cfg(v) for k, v in (data or {}).items() if isinstance(v, dict)}
        _atomic_json(SETTINGS_FILE, normalized, SETTINGS_BAK)
        return normalized


def _get_cfg(chat_id):
    data = _load_settings()
    key = str(chat_id)
    cfg = _sanitize_cfg(data.get(key) or {})
    if data.get(key) != cfg:
        data[key] = cfg
        _save_settings(data)
    return cfg


def _set_cfg(chat_id, **updates):
    with _SETTINGS_LOCK:
        data = _load_settings()
        key = str(chat_id)
        cfg = _sanitize_cfg(data.get(key) or {})
        cfg.update(updates)
        cfg = _sanitize_cfg(cfg)
        data[key] = cfg
        _save_settings(data)
        return cfg


def _owner_entry(chat_id=None):
    data = _load_settings()
    if chat_id is not None:
        cfg = data.get(str(chat_id))
        if isinstance(cfg, dict) and _has_provider_keys(cfg):
            return str(chat_id), _sanitize_cfg(cfg)
    for key, raw in data.items():
        if isinstance(raw, dict) and _has_provider_keys(raw):
            return str(key), _sanitize_cfg(raw)
    if chat_id is not None:
        return str(chat_id), _get_cfg(chat_id)
    return None, _sanitize_cfg({})


def _owner_cfg(chat_id=None):
    return _owner_entry(chat_id)[1]


def _api_key_fp(cfg):
    token = str((cfg or {}).get('api_key') or '').strip()
    if not token:
        return ''
    if _provider_id(cfg) != 'steamsmm':
        token = _provider_id(cfg) + ':' + token
    return hashlib.sha256(token.encode('utf-8')).hexdigest()[:16]


def _known_api_configs():
    rows, seen = [], set()
    for key, raw in _load_settings().items():
        for provider in PROVIDERS:
            cfg = _provider_cfg(raw, provider)
            fp = _api_key_fp(cfg)
            if fp and fp not in seen:
                seen.add(fp)
                rows.append((str(key), cfg, fp))
    return rows


def _owner_key_for_cfg(cfg):
    fp = _api_key_fp(cfg)
    if not fp:
        return None
    for key, _cfg, known_fp in _known_api_configs():
        if known_fp == fp:
            return key
    return None


def _cfg_candidates_for_record(record, preferred_cfg=None):
    record = record or {}
    provider = _provider_id(record)
    fp = str(record.get('api_key_fp') or '')
    owner = str(record.get('owner_key') or '')
    candidates = [r for r in _known_api_configs() if _provider_id(r[1]) == provider]
    if fp:
        candidates = [r for r in candidates if r[2] == fp]
    if owner:
        candidates = [r for r in candidates if r[0] == owner]
    return candidates


def _claim_rental_owner(record, owner_key, cfg):
    rec = dict(record or {})
    rec['provider'] = _provider_id(cfg)
    fp = _api_key_fp(cfg)
    if owner_key:
        rec['owner_key'] = str(owner_key)
    if fp:
        rec['api_key_fp'] = fp
    rec['owner_resolved_ts'] = _now()
    return _rental_save(rec) or rec


def _cfg_for_record(record, fallback_cfg=None):
    candidates = _cfg_candidates_for_record(record, fallback_cfg)
    if candidates:
        return candidates[0][1]

    cfg = _provider_cfg(fallback_cfg or {}, _provider_id(record))
    cfg['api_key'] = ''
    return cfg


def _set_owner_cfg(chat_id=None, **updates):
    key, _ = _owner_entry(chat_id)
    if key is None:
        key = str(chat_id or '__global__')
    return _set_cfg(key, **updates)


def _db_default():
    return {'schema': 1, 'updated_at': _now(), 'records': {}}


def _load_rentals():
    with _RENTALS_LOCK:
        data = _load_json(RENTALS_FILE, _db_default(), RENTALS_BAK)
        if not isinstance(data.get('records'), dict):
            data['records'] = {}
        return data


def _save_rentals(data):
    with _RENTALS_LOCK:
        data = dict(data or {})
        data['schema'] = 1
        data['updated_at'] = _now()
        data['records'] = data.get('records') if isinstance(data.get('records'), dict) else {}
        _atomic_json(RENTALS_FILE, data, RENTALS_BAK)
        return data


def _rental_get(order_id):
    return (_load_rentals().get('records') or {}).get(str(order_id))


def _rental_save(record):
    if not isinstance(record, dict) or not record.get('order_id'):
        return None
    with _RENTALS_LOCK:
        data = _load_rentals()
        records = data['records']
        oid = str(record['order_id'])
        old = records.get(oid) if isinstance(records.get(oid), dict) else {}
        row = {**old, **record, 'order_id': oid, 'updated_ts': _now()}
        records[oid] = row
        if len(records) > 1000:
            ordered = sorted(records.items(), key=lambda kv: _as_int((kv[1] or {}).get('updated_ts'), 0))
            data['records'] = dict(ordered[-1000:])
        _save_rentals(data)
        return row


def _rental_list(active_only=False):
    records = list((_load_rentals().get('records') or {}).values())
    if active_only:
        records = [r for r in records if str(r.get('status') or '').lower() in {'active', 'creating', 'retry'}]
    records.sort(key=lambda r: _as_int(r.get('updated_ts'), 0), reverse=True)
    return records


def _load_extensions():
    with _EXTENSIONS_LOCK:
        data = _load_json(EXTENSIONS_FILE, _db_default(), EXTENSIONS_BAK)
        if not isinstance(data.get('records'), dict):
            data['records'] = {}
        return data


def _save_extensions(data):
    with _EXTENSIONS_LOCK:
        data = dict(data or {})
        data['schema'] = 1
        data['updated_at'] = _now()
        data['records'] = data.get('records') if isinstance(data.get('records'), dict) else {}
        _atomic_json(EXTENSIONS_FILE, data, EXTENSIONS_BAK)
        return data


def _extension_save(record):
    if not isinstance(record, dict) or not record.get('lot_id'):
        return None
    with _EXTENSIONS_LOCK:
        data = _load_extensions()
        key = str(int(record['lot_id']))
        old = data['records'].get(key) if isinstance(data['records'].get(key), dict) else {}
        row = {**old, **record, 'lot_id': int(record['lot_id']), 'updated_ts': _now()}
        data['records'][key] = row
        _save_extensions(data)
        return row


def _extension_delete(lot_id):
    with _EXTENSIONS_LOCK:
        data = _load_extensions()
        data['records'].pop(str(int(lot_id)), None)
        _save_extensions(data)


def _extension_records():
    return dict((_load_extensions().get('records') or {}))


def _extension_purchase_routes():
    data = _load_extensions()
    routes = data.get('purchase_routes')
    return dict(routes) if isinstance(routes, dict) else {}


def _extension_purchase_get(order_id):
    oid = str(order_id or '').strip().lstrip('#')
    if not oid:
        return None
    row = _extension_purchase_routes().get(oid)
    return dict(row) if isinstance(row, dict) else None


def _extension_purchase_mark(order_id, ext=None, status='claimed', **extra):
    oid = str(order_id or '').strip().lstrip('#')
    if not oid:
        return None
    with _EXTENSIONS_LOCK:
        data = _load_extensions()
        routes = data.get('purchase_routes')
        if not isinstance(routes, dict):
            routes = {}
        old = routes.get(oid) if isinstance(routes.get(oid), dict) else {}
        row = dict(old)
        if isinstance(ext, dict):
            row.update({
                'purchase_order_id': oid,
                'extension_lot_id': _as_int(ext.get('lot_id'), 0, 1),
                'source_order_id': str(ext.get('order_id') or ''),
                'rental_id': _normalize_rental_id(ext.get('rental_id')),
                'chat_id': str(ext.get('chat_id') or ''),
                'owner_key': str(ext.get('owner_key') or ''),
                'marker': str(ext.get('marker') or ''),
                'duration_hours': _as_int(ext.get('duration_hours'), 0),
            })
        row.update(extra)
        row['purchase_order_id'] = oid
        row['route'] = 'extension'
        row['status'] = str(status or row.get('status') or 'claimed')
        row['updated_ts'] = _now()
        row.setdefault('created_ts', _now())
        routes[oid] = row
        if len(routes) > 2000:
            ordered = sorted(
                routes.items(),
                key=lambda kv: _as_int((kv[1] or {}).get('updated_ts'), 0)
            )
            routes = dict(ordered[-2000:])
        data['purchase_routes'] = routes
        _save_extensions(data)
        return dict(row)


class SteamSMMError(RuntimeError):
    def __init__(self, message, status=None, code=None, retryable=False, data=None):
        super().__init__(str(message))
        self.status = status
        self.code = str(code or '')
        self.retryable = bool(retryable)
        self.data = data


def _safe_api_error_message(error):
    if isinstance(error, SteamSMMError):
        code = error.code or (f'HTTP {error.status}' if error.status else '')
        text = str(error)
        return f'{code}: {text}'.strip(': ')
    return str(error)


def _buyer_error_message(error):
    code = str(getattr(error, 'code', '') or '').upper()
    friendly = {
        'NO_STOCK': 'Сейчас нет свободных аккаунтов.',
        'INSUFFICIENT_BALANCE': 'Аренда временно недоступна. Попробуйте позже.',
        'PRODUCT_NOT_FOUND': 'Товар временно недоступен.',
        'RENTAL_NOT_FOUND': 'Аренда не найдена или уже завершена.',
        'NETWORK_ERROR': 'Сервис временно не отвечает. Попробуйте позже.',
        'INVALID_RESPONSE': 'Сервис временно не отвечает. Попробуйте позже.',
        'NO_API_KEY': 'Автовыдача временно недоступна.',
        'PAYMENT_UNCERTAIN': 'Нужна проверка заказа продавцом.',
    }
    if code in friendly:
        return friendly[code]
    text = str(error or '').strip()
    text = re.sub(r'\b(?:SteamSMM|Kosell|Muvsell)\s*:\s*', '', text, flags=re.I)
    text = re.sub(r'^\s*[A-Z][A-Z0-9_ -]{2,40}:\s*', '', text)
    text = re.sub(r'HTTP\s+\d{3}[: ]*', '', text, flags=re.I)
    text = re.sub(r'\s+', ' ', text).strip(' .:')
    if not text:
        return 'Попробуйте позже или напишите продавцу.'
    return _compact_error(text, 150)


def _steamsmm_request(cfg, method, path, payload=None, retries=1):
    token = str((cfg or {}).get('api_key') or '').strip()
    if not token:
        raise SteamSMMError('API-ключ SteamSMM не настроен.', code='NO_API_KEY')
    headers = {
        'Authorization': f'Bearer {token}',
        'Accept': 'application/json',
        'User-Agent': f'{NAME}/{VERSION}',
    }
    if payload is not None:
        headers['Content-Type'] = 'application/json'
    url = STEAMSMM_BASE + '/' + str(path).lstrip('/')
    attempts = max(1, int(retries))
    last_error = None
    for attempt in range(1, attempts + 1):
        try:
            response = _HTTP.request(
                method.upper(), url, headers=headers,
                json=payload if payload is not None else None,
                timeout=(HTTP_CONNECT_TIMEOUT, HTTP_READ_TIMEOUT)
            )
        except requests.RequestException as e:
            last_error = SteamSMMError(str(e), retryable=True)
            if attempt < attempts:
                time.sleep(min(1.5 * attempt, 4.0))
                continue
            raise last_error
        try:
            body = response.json()
        except Exception:
            body = None
        if response.status_code in (200, 201) and isinstance(body, dict) and body.get('status') == 'success':
            return body
        code = body.get('code') if isinstance(body, dict) else None
        message = body.get('message') if isinstance(body, dict) else None
        if not message:
            message = (response.text or f'HTTP {response.status_code}')[:500]
        retryable = response.status_code in (500, 502, 503, 504) or str(code or '') in {
            'EXTENSION_IN_PROGRESS', 'EXTENSION_CONFLICT', 'EXTENSION_REJECTED'
        }
        last_error = SteamSMMError(message, response.status_code, code, retryable, body)
        if retryable and attempt < attempts:
            time.sleep(min(1.5 * attempt, 4.0))
            continue
        raise last_error
    raise last_error or SteamSMMError('Неизвестная ошибка SteamSMM.')


PROVIDERS = {'steamsmm': 'SteamSMM', 'kosell': 'Kosell', 'muvsell': 'Muvsell'}
PROVIDER_BASES = {'kosell': 'https://ru.kosell.store/api/v1', 'muvsell': 'https://muvsell.store/api/v1'}
_PROVIDER_UI = {}
_OPERATIONS_LOCK = threading.RLock()
OPERATIONS_FILE = os.path.join(PLUGIN_FOLDER, 'provider_operations.json')


def _provider_id(row):
    return str((row or {}).get('provider') or 'steamsmm')


def _provider_cfg(cfg, provider):
    if provider not in PROVIDERS:
        raise SteamSMMError('Неизвестный провайдер.', code='UNKNOWN_PROVIDER')
    result = dict(cfg)
    result['provider'] = provider
    if provider != 'steamsmm':
        entry = cfg.get('providers', {}).get(provider) or {}
        for key in ('balance', 'regular_balance', 'promo_balance', 'last_api_ok', 'last_api_error', 'api_was_down', 'last_notified_balance_state'):
            result[key] = entry.get(key)
        result['api_key'] = str(entry.get('api_key') or '')
    elif _provider_id(cfg) != 'steamsmm':
        result['api_key'] = str(cfg.get('_steamsmm_key') or '')
    result['_steamsmm_key'] = cfg.get('_steamsmm_key', cfg.get('api_key', ''))
    return result


def _has_provider_keys(cfg):
    return bool(cfg.get('api_key') or any((v or {}).get('api_key') for v in cfg.get('providers', {}).values() if isinstance(v, dict)))


def _wizard_cfg(chat_id):
    return _provider_cfg(_get_cfg(chat_id), _provider_id(_fsm_get(chat_id)))


def _provider_save(owner, provider, **updates):
    with _SETTINGS_LOCK:
        if provider == 'steamsmm':
            return _set_cfg(owner, **updates)
        cfg = _get_cfg(owner)
        providers = dict(cfg.get('providers') or {})
        entry = dict(providers.get(provider) or {})
        entry.update(updates)
        providers[provider] = entry
        return _set_cfg(owner, providers=providers)


def _provider_sync_save(owner, cfg, **updates):
    with _SETTINGS_LOCK:
        rows = updates.pop('lots', [])
        current = _get_cfg(owner)
        changes = {int(r['lot_id']): r for r in rows}
        merged = []
        for row in current.get('lots', []):
            updated = changes.get(int(row['lot_id']))

            if updated and (_provider_id(updated), updated['product_id']) == (_provider_id(row), row['product_id']):
                row = dict(row, **{k: v for k, v in updated.items() if k.startswith('last_') or k in {'auto_disabled', 'auto_disabled_reason', 'updated_ts', 'product_name'}})
            merged.append(row)
        _set_cfg(owner, lots=merged)
        _provider_save(owner, _provider_id(cfg), **updates)


def _external_request(cfg, method, path, payload=None, idem=None):
    provider = _provider_id(cfg)
    token = str(cfg.get('api_key') or '').strip()
    if not token:
        raise SteamSMMError(f'API-ключ {PROVIDERS[provider]} не настроен.', code='NO_API_KEY')
    headers = {'X-API-Key': token, 'Accept': 'application/json', 'User-Agent': f'{NAME}/{VERSION}'}
    if idem:
        headers['Idempotency-Key'] = str(idem)
    try:
        response = _HTTP.request(method, PROVIDER_BASES[provider] + path, headers=headers,
                                 json=payload, timeout=(HTTP_CONNECT_TIMEOUT, HTTP_READ_TIMEOUT))
    except requests.RequestException:
        raise SteamSMMError(f'{PROVIDERS[provider]}: нет ответа сервера.', code='NETWORK_ERROR', retryable=True)
    try:
        body = response.json()
    except Exception:
        raise SteamSMMError(f'{PROVIDERS[provider]}: некорректный ответ HTTP {response.status_code}.',
                            status=response.status_code, code='INVALID_RESPONSE', retryable=True)
    if 200 <= response.status_code < 300 and isinstance(body, (dict, list)):
        if not isinstance(body, dict) or (body.get('success') is not False and not body.get('error')):
            return body
    detail = body.get('detail') or body.get('message') or body.get('error') if isinstance(body, dict) else ''
    if isinstance(detail, dict):
        detail = detail.get('message') or detail.get('error') or str(detail)
    code = str(body.get('code') or body.get('error') or '') if isinstance(body, dict) else ''
    code = {'no_stock': 'NO_STOCK', 'insufficient_balance': 'INSUFFICIENT_BALANCE',
            'not_found': 'RENTAL_NOT_FOUND' if '/rental/' in path and path.endswith(('/credentials', '/code')) else 'PRODUCT_NOT_FOUND'}.get(code, code)

    message = str(detail or f'HTTP {response.status_code}').replace(token, '[скрыто]')[:300]
    raise SteamSMMError(f'{PROVIDERS[provider]}: {message}', response.status_code, code,
                        response.status_code >= 500 or response.status_code == 429)


def _external_rental(provider, data):
    raw = data.get('rental', data)
    result = dict(raw)
    if provider == 'kosell':
        result.update(rental_id=raw.get('rental_uid'), starts_at=raw.get('started_at'),
                      ends_at=raw.get('new_expires_at') or raw.get('expires_at'),
                      amount=raw.get('price_rub') if raw.get('price_rub') is not None else raw.get('price_paid'))
    else:
        result.update(rental_id=raw.get('id'), starts_at=raw.get('createdAt'),
                      ends_at=raw.get('endsAt') or data.get('endsAt'), amount=raw.get('totalRub', data.get('cost')))
        items = raw.get('items') or []
        accounts = items[0].get('accounts', []) if items else []
        if len(accounts) == 1:
            result.update(login=accounts[0].get('login'), password=accounts[0].get('password'))
    if result.get('status') == 'completed':
        result['status'] = 'ended'
    return result


def _muv_game(cfg, product_id):
    rows = _api_products(cfg).get('products', [])
    matches = [r for r in rows if int(r['product_id']) == int(product_id)]
    if len(matches) != 1:
        raise SteamSMMError('Игра Muvsell не найдена однозначно.', code='PRODUCT_NOT_FOUND')
    return matches[0]['game_id']


def _single_account(data, key):
    rows = data.get(key) or []
    if len(rows) != 1:
        raise SteamSMMError('Ожидался один аккаунт в аренде. Проверьте заказ у провайдера.', code='ACCOUNT_COUNT')
    return dict(rows[0])


def _once_operation(cfg, operation, idem, call, recover=None):
    key = hashlib.sha256(f'{_provider_id(cfg)}:{_api_key_fp(cfg)}:{operation}:{idem}'.encode()).hexdigest()
    with _OPERATIONS_LOCK:
        ledger = _load_json(OPERATIONS_FILE, {}, OPERATIONS_FILE + '.bak')
        old = ledger.get(key)
        if old and old.get('state') == 'done':
            return dict(old['result'])
        if old:
            result = recover() if recover else None
            if result is not None:
                ledger[key] = {'state': 'done', 'result': result, 'ts': _now()}
                _atomic_json(OPERATIONS_FILE, ledger, OPERATIONS_FILE + '.bak')
                return result
            raise SteamSMMError('Результат списания не подтверждён. Проверьте заказ в кабинете провайдера; '
                                'повторное списание заблокировано.', code='PAYMENT_UNCERTAIN')
        ledger[key] = {'state': 'pending', 'ts': _now()}
        _atomic_json(OPERATIONS_FILE, ledger, OPERATIONS_FILE + '.bak')
        try:
            result = call()
        except SteamSMMError as error:
            if error.status in (400, 401, 403, 404, 422, 429):
                ledger.pop(key, None)
                _atomic_json(OPERATIONS_FILE, ledger, OPERATIONS_FILE + '.bak')
                raise
            raise SteamSMMError('Ответ на списание потерян. Проверьте заказ у провайдера; '
                                'автоматическое повторное списание заблокировано.', code='PAYMENT_UNCERTAIN') from error
        ledger[key] = {'state': 'done', 'result': result, 'ts': _now()}
        _atomic_json(OPERATIONS_FILE, ledger, OPERATIONS_FILE + '.bak')
        return result


def _external_rent(cfg, product_id, hours, idem):
    provider = _provider_id(cfg)
    if provider == 'kosell':
        return _external_rental(provider, _external_request(cfg, 'POST', '/rental/rent',
            {'product_id': int(product_id), 'duration_hours': int(hours), 'currency': 'RUB', 'idempotency_key': str(idem)}, idem))
    game = _muv_game(cfg, product_id)
    marker = 'FPC:' + str(idem)
    def recover():
        rows = _external_request(cfg, 'GET', '/rental/orders').get('rentals', [])
        matches = [r for r in rows if r.get('comment') == marker]
        if len(matches) == 1:
            return {k: _external_rental(provider, matches[0]).get(k) for k in ('rental_id', 'status', 'starts_at', 'ends_at', 'amount')}
        return None
    def purchase():
        result = _external_rental(provider, _external_request(cfg, 'POST', '/rental/create',
            {'items': [{'gameId': game, 'durationKey': f'{int(hours)}h', 'qty': 1}], 'payWith': 'rub', 'comment': marker}))
        if not result.get('rental_id'):
            raise SteamSMMError('Нет ID аренды.', code='INVALID_RESPONSE')

        return {k: result.get(k) for k in ('rental_id', 'status', 'starts_at', 'ends_at', 'amount')}
    return _once_operation(cfg, 'rent', idem, purchase, recover)


def _external_extend(cfg, rental_id, hours, idem):
    provider = _provider_id(cfg)
    payload = {'hours': int(hours), 'currency': 'RUB'} if provider == 'kosell' else {'durationKey': f'{int(hours)}h', 'payWith': 'rub'}
    def extend():
        raw = _external_request(cfg, 'POST', f'/rental/{_rental_path_id(rental_id)}/extend', payload)
        result = _external_rental(provider, raw)
        if not result.get('ends_at'):
            raise SteamSMMError('Нет нового срока аренды.', code='INVALID_RESPONSE')
        return {k: result.get(k) for k in ('rental_id', 'ends_at', 'amount')}
    return _once_operation(cfg, 'extend:' + str(rental_id), idem, extend)


def _api_extension_price(cfg, record, hours):
    if _provider_id(cfg) == 'kosell':
        result = _external_request(cfg, 'POST', '/rental/calculate-extend-price',
                                   {'rental_uid': str(record['rental_id']), 'hours': int(hours)})
        return {'total_cost': result['total_rub']}
    return _api_calculate_price(cfg, record['product_id'], hours)


def _providers_text(chat_id):
    cfg = _get_cfg(chat_id)
    lines = ['🔌 <b>Провайдеры аренды</b>', '', 'Все провайдеры:', '']
    for pid, name in PROVIDERS.items():
        pcfg = _provider_cfg(cfg, pid)
        info = cfg if pid == 'steamsmm' else cfg.get('providers', {}).get(pid, {})
        balance = info.get('regular_balance')
        lines.append(f'{"✅" if pcfg.get("api_key") else "❌"} <b>{name}</b> · {balance if balance is not None else "—"} ₽')
    return '\n'.join(lines)


def _providers_kb():
    kb = K()
    for pid, name in PROVIDERS.items():
        kb.row(B(name, callback_data=CB + ':provider:' + pid))
    kb.row(
        B('SteamSMM', url=STEAMSMM_SERVICE_URL),
        B('Kosell', url=KOSELL_SERVICE_URL),
        B('Muvsell', url=MUVSELL_SERVICE_URL),
    )
    kb.add(B('◀️ Назад', callback_data=CB_SETTINGS))
    return kb


def _provider_panel(bot, chat_id, message_id, pid):
    _PROVIDER_UI[str(chat_id)] = pid
    cfg = _get_cfg(chat_id)
    pcfg = _provider_cfg(cfg, pid)
    info = cfg if pid == 'steamsmm' else cfg.get('providers', {}).get(pid, {})
    text = (f'🔑 <b>{PROVIDERS[pid]}</b>\n\nКлюч: <code>{_h(_masked_token(pcfg.get("api_key")))}</code>\n'
            f'Баланс: <b>{info.get("regular_balance") if info.get("regular_balance") is not None else "—"} ₽</b>')
    kb = K()
    kb.row(B('✏️ Установить ключ', callback_data=CB + ':pkey:' + pid), B('🔄 Баланс', callback_data=CB + ':pbal:' + pid))
    kb.add(B('◀️ Провайдеры', callback_data=CB_TOKEN))
    _safe_edit(bot, chat_id, message_id, text, kb)


def _choose_lot_provider(bot, chat_id, state):
    state['step'] = 'add_provider'
    _fsm_set(chat_id, state)
    kb = K()
    cfg = _get_cfg(chat_id)
    for pid, name in PROVIDERS.items():
        if _provider_cfg(cfg, pid).get('api_key'):
            kb.add(B(name, callback_data=CB + ':lotprovider:' + pid))
    kb.add(B('◀️ Назад', callback_data=CB_CANCEL))
    prompt = bot.send_message(chat_id, '🔌 Выберите провайдера для этого лота.\nЕсли список пуст, сначала подключите сервис в разделе «Провайдеры».', reply_markup=kb)
    state['prompt_msg_id'] = getattr(prompt, 'message_id', getattr(prompt, 'id', None))
    _fsm_set(chat_id, state)


def _register_provider_callbacks(cardinal):
    tg, bot = cardinal.telegram, cardinal.telegram.bot
    def provider(c):
        pid = c.data.split(':')[-1]
        if pid in PROVIDERS:
            _provider_panel(bot, c.message.chat.id, c.message.id, pid)
        bot.answer_callback_query(c.id)
    def key(c):
        pid = c.data.split(':')[-1]
        if pid not in PROVIDERS:
            return
        state = {'step': 'provider_key', 'provider': pid, 'menu_message_id': c.message.id, 'return_menu': 'token'}
        _fsm_prompt(bot, c.message.chat.id, state, f'🔑 Отправьте API-ключ <b>{PROVIDERS[pid]}</b>. Сначала проверю подключение.')
        bot.answer_callback_query(c.id)
    def balance(c):
        pid = c.data.split(':')[-1]
        try:
            data = _api_balance(_provider_cfg(_get_cfg(c.message.chat.id), pid))
            _provider_save(c.message.chat.id, pid, **data, last_api_ok=_now(), last_api_error='')
            _provider_panel(bot, c.message.chat.id, c.message.id, pid)
            bot.answer_callback_query(c.id, 'Баланс обновлён.')
        except Exception as e:
            bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
    def select(c):
        chat_id = c.message.chat.id
        state = _fsm_get(chat_id)
        pid = c.data.split(':')[-1]
        if not state or state.get('step') != 'add_provider' or pid not in PROVIDERS:
            return bot.answer_callback_query(c.id, 'Откройте настройку лота заново.')
        state['provider'] = pid
        try:
            _show_product_picker(bot, chat_id, state)
            bot.answer_callback_query(c.id)
        except Exception as e:
            bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
    def rebind(c):
        lid = _as_int(c.data.split(':')[-1], 0)
        cfg = _get_cfg(c.message.chat.id)
        row = next((r for r in cfg['lots'] if r['lot_id'] == lid), None)
        if row:
            _choose_lot_provider(bot, c.message.chat.id, {'lot_id': lid, 'menu_message_id': c.message.id, 'return_menu': 'lot', 'editing': True})
        bot.answer_callback_query(c.id)
    tg.cbq_handler(provider, func=lambda c: c.data.startswith(CB + ':provider:'))
    tg.cbq_handler(key, func=lambda c: c.data.startswith(CB + ':pkey:'))
    tg.cbq_handler(balance, func=lambda c: c.data.startswith(CB + ':pbal:'))
    tg.cbq_handler(select, func=lambda c: c.data.startswith(CB + ':lotprovider:'))
    tg.cbq_handler(rebind, func=lambda c: c.data.startswith(CB + ':rebind:'))


def _api_balance(cfg):
    if _provider_id(cfg) != 'steamsmm':
        raw = _external_request(cfg, 'GET', '/account/balance')
        amount = raw['balance_rub'] if _provider_id(cfg) == 'kosell' else raw['balanceRub']
        return {'balance': amount, 'regular_balance': amount, 'promo_balance': 0, 'currency': 'RUB'}
    return _steamsmm_request(cfg, 'GET', '/user/balance', retries=2).get('data') or {}


def _api_products(cfg):
    provider = _provider_id(cfg)
    if provider != 'steamsmm':
        raw = _external_request(cfg, 'GET', '/rental/products')
        rows = raw if isinstance(raw, list) else raw.get('products', [])
        products = []
        for row in rows:
            if provider == 'kosell':
                products.append(dict(row, product_id=row['id'], price_per_hour=row['price_per_hour_rub'], stock=row['available_accounts']))
            else:
                products.append(dict(row, product_id=row['lotId'], game_id=row['id'], price_per_hour=row.get('pricePerHourRub'), stock=row['inStock'] if row.get('available') else 0))
        return {'products': products}
    return _steamsmm_request(cfg, 'GET', '/rentals/products', retries=2).get('data') or {}


def _api_calculate_price(cfg, product_id, hours):
    provider = _provider_id(cfg)
    if provider == 'kosell':
        raw = _external_request(cfg, 'POST', '/rental/calculate-price', {'product_id': int(product_id), 'hours': int(hours)})
        return {'total_cost': raw['total_rub']}
    if provider == 'muvsell':
        raw = _external_request(cfg, 'POST', '/rental/quote', {'gameId': _muv_game(cfg, product_id), 'durationKey': f'{int(hours)}h', 'qty': 1})
        return {'total_cost': raw['totalRub']}
    body = _steamsmm_request(cfg, 'POST', '/rentals/calculate-price', {
        'product_id': int(product_id), 'duration_hours': int(hours)
    }, retries=2)
    return body.get('data') or {}


def _api_rent(cfg, product_id, hours, idempotency_key):
    if _provider_id(cfg) != 'steamsmm':
        return _external_rent(cfg, product_id, hours, idempotency_key)
    body = _steamsmm_request(cfg, 'POST', '/rentals/rent', {
        'product_id': int(product_id),
        'duration_hours': int(hours),
        'idempotency_key': str(idempotency_key),
    }, retries=3)
    data = body.get('data') or {}
    if isinstance(data, dict):
        data = dict(data)
        if body.get('idempotent_replay') is not None and data.get('idempotent_replay') is None:
            data['idempotent_replay'] = body.get('idempotent_replay')
    return data


def _api_extend(cfg, rental_id, hours, idempotency_key):
    if _provider_id(cfg) != 'steamsmm':
        return _external_extend(cfg, rental_id, hours, idempotency_key)
    rid = _rental_path_id(rental_id)
    body = _steamsmm_request(cfg, 'POST', f'/rentals/{rid}/extend', {
        'duration_hours': int(hours),
        'idempotency_key': str(idempotency_key),
    }, retries=3)
    return body.get('data') or {}


def _api_status(cfg, rental_id):
    provider = _provider_id(cfg)
    if provider == 'kosell':
        rows = _external_request(cfg, 'GET', '/rental/active')
        for row in rows:
            if str(row.get('rental_uid')) == str(rental_id):
                return _external_rental(provider, row)
        return {'status': 'ended'}
    if provider == 'muvsell':
        return _external_rental(provider, _external_request(cfg, 'GET', f'/rental/{_rental_path_id(rental_id)}'))
    rid = _rental_path_id(rental_id)
    return (_steamsmm_request(cfg, 'GET', f'/rentals/{rid}/status', retries=2).get('data') or {})


def _api_credentials(cfg, rental_id):
    provider = _provider_id(cfg)
    if provider != 'steamsmm':
        raw = _external_request(cfg, 'GET', f'/rental/{_rental_path_id(rental_id)}/credentials')
        return _single_account(raw, 'accounts') if provider == 'muvsell' else raw
    rid = _rental_path_id(rental_id)
    return (_steamsmm_request(cfg, 'GET', f'/rentals/{rid}/credentials', retries=2).get('data') or {})


def _api_guard(cfg, rental_id):
    provider = _provider_id(cfg)
    if provider != 'steamsmm':
        raw = _external_request(cfg, 'GET', f'/rental/{_rental_path_id(rental_id)}/code')
        result = _single_account(raw, 'codes') if provider == 'muvsell' else raw
        if not result.get('code'):
            raise SteamSMMError('Steam Guard пока не доступен.', code='GUARD_UNAVAILABLE')
        return result
    rid = _rental_path_id(rental_id)
    return (_steamsmm_request(cfg, 'GET', f'/rentals/{rid}/guard-code', retries=1).get('data') or {})


def _stock_scalar(value):
    if value is None:
        return None
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, (int, float)):
        try:
            return max(0, int(value))
        except Exception:
            return None
    if isinstance(value, str):
        text = value.strip()
        if not text:
            return None
        m = re.search(r'\d+', text)
        if m:
            return max(0, int(m.group(0)))
        return None
    if isinstance(value, (list, tuple, set)):
        return len(value)
    return None


def _stock_key_norm(key):
    return re.sub(r'[^a-z0-9]+', '', str(key or '').lower())


def _extract_product_stock(raw):
    if not isinstance(raw, dict):
        return None, 'missing'

    exact_keys = (
        'stock',
        'available_count', 'available_accounts_count', 'available_accounts',
        'accounts_available', 'accounts_available_count',
        'free_count', 'free_accounts_count', 'free_accounts',
        'available_slots', 'free_slots', 'slots_available',
        'available_quantity', 'quantity_available', 'count_available',
        'remaining', 'remaining_count', 'in_stock',

        'availableCount', 'availableAccountsCount', 'availableAccounts',
        'accountsAvailable', 'freeCount', 'freeAccountsCount', 'freeAccounts',
        'availableSlots', 'freeSlots', 'availableQuantity', 'remainingCount',
    )

    for key in exact_keys:
        if key not in raw or raw.get(key) is None:
            continue
        value = raw.get(key)
        scalar = _stock_scalar(value)
        if scalar is not None:
            return scalar, key
        if isinstance(value, dict):
            nested, source = _extract_product_stock(value)
            if nested is not None:
                return nested, f'{key}.{source}'

    nested_keys = (
        'availability', 'inventory', 'stock_info', 'stockInfo',
        'accounts', 'pool', 'availability_info', 'availabilityInfo',
    )
    for key in nested_keys:
        value = raw.get(key)
        if isinstance(value, dict):
            nested, source = _extract_product_stock(value)
            if nested is not None:
                return nested, f'{key}.{source}'
        elif value is not None:
            scalar = _stock_scalar(value)
            if scalar is not None:
                return scalar, key


    for key, value in raw.items():
        norm = _stock_key_norm(key)
        availability_like = (
            norm == 'stock'
            or 'available' in norm
            or norm.startswith('free')
            or 'freeaccounts' in norm
            or 'freeslots' in norm
            or norm.startswith('remaining')
            or norm == 'instock'
        )
        if not availability_like:
            continue
        scalar = _stock_scalar(value)
        if scalar is not None:
            return scalar, str(key)
        if isinstance(value, dict):
            nested, source = _extract_product_stock(value)
            if nested is not None:
                return nested, f'{key}.{source}'

    return None, 'unknown'


def _normalize_products(data):
    products = data.get('products') if isinstance(data, dict) else None
    if isinstance(products, dict):
        products = list(products.values())
    if not isinstance(products, list):
        products = []
    out = []
    for raw in products:
        if not isinstance(raw, dict):
            continue
        pid = _as_int(raw.get('product_id') or raw.get('id'), 0, 1)
        if not pid:
            continue
        title = str(raw.get('title') or raw.get('name') or raw.get('game') or f'Product {pid}')
        stock, stock_source = _extract_product_stock(raw)
        stock_known = stock is not None
        if stock is None:
            stock = -1
        hourly = None
        for key in ('price_per_hour', 'hourly_price', 'price_hour', 'price'):
            if raw.get(key) is not None:
                hourly = _as_float(raw.get(key), 0.0, 0.0)
                break
        out.append({
            'product_id': pid,
            'title': title,
            'stock': stock,
            'stock_known': stock_known,
            'stock_source': stock_source,
            'hourly_price': hourly,
            'raw': raw,
        })
    return out


def _find_product(data, product_id):
    pid = int(product_id)
    for row in _normalize_products(data):
        if row['product_id'] == pid:
            return row
    return None


def _price_total(data):
    if not isinstance(data, dict):
        return None
    for key in ('total_cost', 'total_price', 'amount', 'total', 'price', 'cost'):
        if data.get(key) is not None:
            value = _as_float(data.get(key), -1.0)
            if value >= 0:
                return value
    nested = data.get('price')
    if isinstance(nested, dict):
        return _price_total(nested)
    return None


def _credentials_values(data):
    login_keys = {'login', 'username', 'account_login', 'steam_login', 'steam_username'}
    pass_keys = {'password', 'pass', 'account_password', 'steam_password', 'pwd'}
    container_keys = {'credentials', 'account', 'account_data', 'access', 'auth', 'steam', 'rental'}
    seen = set()

    def walk(value, depth=0, parent_key=''):
        if depth > 5 or id(value) in seen:
            return '', ''
        if isinstance(value, (dict, list)):
            seen.add(id(value))
        if isinstance(value, dict):
            login = ''
            password = ''
            for k, v in value.items():
                kl = str(k).lower()
                if kl in login_keys and not isinstance(v, (dict, list)):
                    login = str(v or '').strip()
                elif kl in pass_keys and not isinstance(v, (dict, list)):
                    password = str(v or '').strip()
            if login and password:
                return login, password

            ordered = []
            for k, v in value.items():
                if str(k).lower() in container_keys:
                    ordered.append((k, v))
            for k, v in value.items():
                if isinstance(v, (dict, list)) and (k, v) not in ordered:
                    ordered.append((k, v))
            for k, v in ordered:
                a, b = walk(v, depth + 1, str(k).lower())
                if a or b:
                    return a, b

            for k, v in value.items():
                kl = str(k).lower()
                if kl in container_keys and isinstance(v, str) and ':' in v:
                    left, right = v.split(':', 1)
                    if left.strip() and right.strip():
                        return left.strip(), right.strip()
        elif isinstance(value, list):
            for item in value:
                a, b = walk(item, depth + 1, parent_key)
                if a or b:
                    return a, b
        return '', ''

    return walk(data)


def _rent_response_meta(data):
    if not isinstance(data, dict):
        return {'type': type(data).__name__}
    keys = ('rental_id', 'product_id', 'hours', 'duration_hours', 'amount', 'currency',
            'status', 'starts_at', 'ends_at', 'idempotent_replay')
    meta = {k: data.get(k) for k in keys if data.get(k) is not None}
    meta['fields'] = sorted(str(k) for k in data.keys())
    return meta


def _rent_api_id(data):
    if not isinstance(data, dict):
        return ''
    sources = [data]
    nested = data.get('rental')
    if isinstance(nested, dict):
        sources.append(nested)
    for source in sources:
        rid = _normalize_rental_id(source.get('rental_id'))
        if rid:
            return rid
    return ''


def _recover_rental_identity(cfg, record, reason='', return_replay=False):
    if not isinstance(record, dict):
        raise SteamSMMError('Некорректная запись аренды.', code='BAD_RENTAL_RECORD')
    product_id = _as_int(record.get('product_id'), 0, 1)
    hours = _as_int(record.get('duration_hours'), 0, 1)
    idem = str(record.get('idempotency_key') or '').strip()
    if not product_id or not hours or not idem:
        raise SteamSMMError('Недостаточно данных для восстановления аренды.', code='BAD_RENTAL_RECORD')


    fp = str(record.get('api_key_fp') or '').strip()
    known = [r for r in _known_api_configs() if _provider_id(r[1]) == _provider_id(record)]
    cfg_fp = _api_key_fp(cfg)
    if fp and cfg_fp != fp:
        raise SteamSMMError('Исходный API-ключ аренды не совпадает с текущим.', code='RENTAL_OWNER_MISMATCH')
    if not fp:
        unique_fps = {x[2] for x in known}
        if len(unique_fps) != 1:
            raise SteamSMMError(
                'Нельзя безопасно повторить аренду: для старого заказа не определён исходный API-ключ.',
                code='RENTAL_OWNER_UNKNOWN'
            )

        cfg = known[0][1]
        cfg_fp = known[0][2]

    now = _now()
    last_replay = _as_int(record.get('last_identity_replay_ts'), 0)
    if last_replay and now - last_replay < 120:
        raise SteamSMMError(
            'SteamSMM уже проверялся недавно; ждём перед следующим безопасным replay.',
            code='RENTAL_REPLAY_COOLDOWN', retryable=True
        )

    replay = _api_rent(cfg, product_id, hours, idem)
    recovered_id = _rent_api_id(replay)
    if not recovered_id:
        safe_fields = ', '.join(sorted(str(k) for k in replay.keys())) if isinstance(replay, dict) else type(replay).__name__
        logger.error('Заказ #%s · SteamSMM rent/replay не вернул rental_id · поля: %s',
                     record.get('order_id'), safe_fields or '—')
        raise SteamSMMError(
            'Провайдер не вернул data.rental_id при idempotent replay.',
            code='NO_RENTAL_ID', retryable=True, data={'fields': safe_fields}
        )

    old_id = _normalize_rental_id(record.get('rental_id'))
    rec = dict(record)
    rec['last_identity_replay_ts'] = now
    rec['rent_response_meta'] = _rent_response_meta(replay)
    if old_id and old_id != recovered_id:
        rec['previous_invalid_rental_id'] = old_id
    rec['rental_id'] = recovered_id
    owner = _owner_key_for_cfg(cfg)
    rec = _claim_rental_owner(rec, owner, cfg)


    rlogin, rpassword = _credentials_values(replay)
    if rlogin and rpassword:
        rec['rental_id_verified'] = True
        rec['rental_id_verified_by'] = 'rent_response_credentials'
        rec['api_inconsistent'] = False
        rec = _rental_save(rec) or rec
        return (rec, replay) if return_replay else rec

    try:
        st = _api_status(cfg, recovered_id)
        rec['rental_id_verified'] = True
        rec['rental_id_verified_by'] = 'status'
        rec['api_inconsistent'] = False
        if isinstance(st, dict):
            rec['status'] = str(st.get('status') or replay.get('status') or rec.get('status') or 'active')
            rec['starts_at'] = st.get('starts_at') or replay.get('starts_at') or rec.get('starts_at')
            rec['ends_at'] = st.get('ends_at') or replay.get('ends_at') or rec.get('ends_at')
        rec = _rental_save(rec) or rec
    except SteamSMMError as e:
        if e.code != 'RENTAL_NOT_FOUND':
            raise
        rec['rental_id_verified'] = False
        rec['rental_id_verified_by'] = ''
        rec['api_inconsistent'] = True
        rec['api_inconsistent_code'] = 'RENTAL_NOT_FOUND'
        rec['credentials_next_retry_ts'] = _now() + 120
        rec = _rental_save(rec) or rec
        meta = _rent_response_meta(replay)
        logger.warning(
            'Заказ #%s · SteamSMM API несогласован: POST /rent вернул rental_id=%s, '
            'но GET /rentals/%s/status отвечает RENTAL_NOT_FOUND · meta=%s',
            rec.get('order_id'), recovered_id, recovered_id, meta
        )
        raise SteamSMMError(
            f'POST /rent вернул rental_id={recovered_id}, но status/credentials не видят эту аренду.',
            code='RENTAL_API_INCONSISTENT', retryable=True, data=meta
        )

    if old_id and old_id != recovered_id:
        logger.warning('Заказ #%s · исправлен Rental ID: %s → %s (%s)',
                       rec.get('order_id'), old_id, recovered_id, reason or 'recovery')
    else:
        logger.info('Заказ #%s · Rental ID проверен через /status: %s (%s)',
                    rec.get('order_id'), recovered_id, reason or 'recovery')
    return (rec, replay) if return_replay else rec


def _credentials_for_record(cfg, record):
    rec = dict(record or {})
    rental_id = _normalize_rental_id(rec.get('rental_id'))
    if not rental_id:
        safe_cfg = _cfg_for_record(rec, cfg)
        rec, replay = _recover_rental_identity(safe_cfg, rec, reason='missing_rental_id', return_replay=True)
        login, password = _credentials_values(replay)
        if login and password:
            return rec, replay
        rental_id = _normalize_rental_id(rec.get('rental_id'))

    not_found = []
    candidates = _cfg_candidates_for_record(rec, cfg)
    for owner_key, candidate_cfg, fp in candidates:
        try:
            data = _api_credentials(candidate_cfg, rental_id)
            rec = _claim_rental_owner(rec, owner_key, candidate_cfg)
            rec['rental_id_verified'] = True
            rec['rental_id_verified_by'] = 'credentials'
            rec['api_inconsistent'] = False
            rec = _rental_save(rec) or rec
            return rec, data
        except SteamSMMError as e:
            if e.code == 'RENTAL_NOT_FOUND':
                not_found.append(fp)
                continue

            rec = _claim_rental_owner(rec, owner_key, candidate_cfg)
            rec['rental_id_verified'] = True
            rec['rental_id_verified_by'] = f'credentials_error:{e.code or "api"}'
            rec = _rental_save(rec) or rec
            raise


    owner_cfg = _cfg_for_record(rec, cfg)
    try:
        rec, replay = _recover_rental_identity(owner_cfg, rec, reason='credentials_RENTAL_NOT_FOUND', return_replay=True)
        login, password = _credentials_values(replay)
        if login and password:
            return rec, replay


        owner_cfg = _cfg_for_record(rec, owner_cfg)
        return rec, _api_credentials(owner_cfg, rec['rental_id'])
    except SteamSMMError as e:
        if e.code in {'RENTAL_API_INCONSISTENT', 'RENTAL_OWNER_UNKNOWN', 'RENTAL_REPLAY_COOLDOWN'}:
            raise
        raise SteamSMMError(
            'Аренда не найдена ни одним из настроенных API-ключей SteamSMM.',
            code='RENTAL_NOT_FOUND_ALL_KEYS', retryable=True,
            data={'checked_keys': len(not_found), 'rental_id': rental_id}
        ) from e


def _migrate_opaque_rental_ids():
    fixed = 0
    data = _load_rentals()
    records = data.get('records') or {}
    for oid, rec in list(records.items()):
        if not isinstance(rec, dict):
            continue
        current = _normalize_rental_id(rec.get('rental_id'))
        meta = rec.get('rent_response_meta') if isinstance(rec.get('rent_response_meta'), dict) else {}
        raw = _normalize_rental_id(meta.get('rental_id'))
        if raw and raw != current:

            rec['previous_invalid_rental_id'] = current
            rec['rental_id'] = raw
            rec['rental_id_verified'] = False
            rec['rental_id_verified_by'] = ''
            rec['api_inconsistent'] = False
            rec['api_inconsistent_code'] = ''
            rec['api_inconsistent_notified'] = False
            rec['credentials_next_retry_ts'] = 0
            rec['updated_ts'] = _now()
            records[str(oid)] = rec
            fixed += 1
    if fixed:
        data['records'] = records
        _save_rentals(data)


    ext_fixed = 0
    try:
        ext_data = _load_extensions()
        ext_records = ext_data.get('records') or {}
        for key, ext in list(ext_records.items()):
            if not isinstance(ext, dict):
                continue
            oid = str(ext.get('order_id') or '').strip()
            parent = records.get(oid) if oid else None
            if isinstance(parent, dict):
                parent_rid = _normalize_rental_id(parent.get('rental_id'))
                if parent_rid and _normalize_rental_id(ext.get('rental_id')) != parent_rid:
                    ext['rental_id'] = parent_rid
                    ext['updated_ts'] = _now()
                    ext_records[key] = ext
                    ext_fixed += 1
        if ext_fixed:
            ext_data['records'] = ext_records
            _save_extensions(ext_data)
    except Exception:
        pass

    if fixed or ext_fixed:
        logger.warning('Исправлены opaque Rental ID: аренды=%s, продления=%s.', fixed, ext_fixed)
    return fixed + ext_fixed


def _format_duration(hours):
    hours = int(hours)
    if hours % 168 == 0:
        weeks = hours // 168
        return f'{weeks} нед.'
    if hours % 24 == 0:
        days = hours // 24
        return f'{days} дн.'
    return f'{hours} ч.'


STEAMSMM_TZ = timezone(timedelta(hours=3))

def _api_datetime(value):
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(str(value).replace('Z', '+00:00'))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=STEAMSMM_TZ)
        return dt
    except Exception:
        return None


def _fmt_dt(value):
    if not value:
        return '—'
    dt = _api_datetime(value)
    if dt is None:
        return str(value)

    return dt.astimezone(STEAMSMM_TZ).strftime('%d.%m.%Y %H:%M')


def _remaining(value):
    ts = _parse_iso_ts(value)
    if ts is None:
        return '—'
    seconds = int(ts - time.time())
    if seconds <= 0:
        return 'завершена'
    days, rem = divmod(seconds, 86400)
    hours, rem = divmod(rem, 3600)
    minutes = rem // 60
    if days:
        return f'{days} д. {hours} ч.'
    return f'{hours} ч. {minutes} мин.'


def _tpl(cfg, key, **values):
    templates = (cfg or {}).get('templates') if isinstance(cfg, dict) else None
    raw = (templates or {}).get(key) or _default_templates().get(key, '')
    try:
        return raw.format(**values)
    except Exception:
        return raw


def _masked_token(token):
    token = str(token or '')
    if not token:
        return 'не задан'
    if len(token) <= 8:
        return '••••' + token[-2:]
    return token[:3] + '••••••••' + token[-4:]


def _safe_send(cardinal, chat_id, text, **kwargs):
    if chat_id is None:
        return None
    try:
        return cardinal.send_message(chat_id, str(text))
    except Exception:
        try:
            return cardinal.account.send_message(chat_id, str(text))
        except Exception as e:
            logger.warning('Не удалось отправить сообщение в FunPay chat=%s: %s', chat_id, e)
            return None


def _safe_tg(bot, chat_id, text, kb=None):
    try:
        return bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
    except Exception:
        try:
            return bot.send_message(chat_id, re.sub(r'<[^>]+>', '', text), reply_markup=kb, disable_web_page_preview=True)
        except Exception:
            return None


def _safe_edit(bot, chat_id, message_id, text, kb=None):
    try:
        return bot.edit_message_text(text, chat_id, message_id, parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
    except Exception:
        return _safe_tg(bot, chat_id, text, kb)


def _tg_delete(bot, chat_id, message_id):
    if not message_id:
        return False
    try:
        bot.delete_message(chat_id, message_id)
        return True
    except Exception:
        return False


def _fsm_attach_prompt(chat_id, state, prompt_message):
    state = dict(state or {})
    state['prompt_msg_id'] = getattr(prompt_message, 'message_id', getattr(prompt_message, 'id', None))
    _fsm_set(chat_id, state)
    return state


def _fsm_back_kb():
    kb = K()
    kb.add(B('◀️ Назад', callback_data=CB_CANCEL))
    return kb


def _fsm_prompt(bot, chat_id, state, text, *, parse_mode='HTML'):
    prompt = bot.send_message(
        chat_id,
        text,
        parse_mode=parse_mode,
        reply_markup=_fsm_back_kb(),
        disable_web_page_preview=True,
    )
    return _fsm_attach_prompt(chat_id, state, prompt)


def _fsm_prompt_edit(bot, chat_id, state, text, *, parse_mode='HTML'):
    message_id = (state or {}).get('prompt_msg_id')
    if message_id:
        try:
            return bot.edit_message_text(
                text,
                chat_id,
                message_id,
                parse_mode=parse_mode,
                reply_markup=_fsm_back_kb(),
                disable_web_page_preview=True,
            )
        except Exception:
            pass
    return _fsm_prompt(bot, chat_id, state, text, parse_mode=parse_mode)


def _fsm_restore_menu(bot, chat_id, state):
    menu_id = (state or {}).get('menu_message_id')
    if not menu_id:
        return
    target = (state or {}).get('return_menu')
    try:
        if target == 'config':
            _safe_edit(bot, chat_id, menu_id, _config_text(), _config_kb())
        elif target == 'gift':
            _safe_edit(bot, chat_id, menu_id, _gift_text(chat_id), _gift_kb(chat_id))
        elif target == 'lot':
            _safe_edit(bot, chat_id, menu_id, _lot_detail_text(chat_id, state.get('lot_id')), _lot_detail_kb(chat_id, state.get('lot_id')))
        elif target == 'lot_markup':
            _safe_edit(bot, chat_id, menu_id, _lot_markup_text(chat_id, state.get('lot_id')), _lot_markup_kb(chat_id, state.get('lot_id')))
        elif target == 'lots':
            _safe_edit(bot, chat_id, menu_id, _lots_text(chat_id), _lots_kb(chat_id))
        elif target == 'lots_general':
            _safe_edit(bot, chat_id, menu_id, _lots_general_text(chat_id), _lots_general_kb(chat_id))
        elif target == 'auto':
            _safe_edit(bot, chat_id, menu_id, _auto_text(chat_id), _auto_kb(chat_id))
        elif target == 'ext':
            _safe_edit(bot, chat_id, menu_id, _extensions_text(chat_id), _extensions_kb(chat_id))
        elif target == 'token':
            _safe_edit(bot, chat_id, menu_id, _token_text(chat_id), _token_kb())
        elif target == 'messages':
            _safe_edit(bot, chat_id, menu_id, _messages_text(chat_id), _messages_kb(chat_id))
        elif target == 'update':
            _safe_edit(bot, chat_id, menu_id, _update_text(), _update_kb())
    except Exception:
        pass


def _fsm_cleanup_input(bot, chat_id, state, user_message=None):
    _tg_delete(bot, chat_id, (state or {}).get('prompt_msg_id'))
    _tg_delete(bot, chat_id, getattr(user_message, 'message_id', getattr(user_message, 'id', None)))


def _fsm_edit_origin(bot, chat_id, state, text, kb=None):
    message_id = (state or {}).get('menu_message_id')
    if message_id:
        return _safe_edit(bot, chat_id, message_id, text, kb)
    return _safe_tg(bot, chat_id, text, kb)


def _notification_allowed(cfg, kind='general'):
    cfg = _sanitize_cfg(cfg or {})
    if not cfg.get('notifications_enabled', True):
        return False
    mapping = {
        'order': 'notify_orders',
        'rental': 'notify_rentals',
        'error': 'notify_errors',
        'stock': 'notify_stock',
        'price': 'notify_price',
        'lot': 'notify_lot_state',
        'extension': 'notify_extensions',
        'api': 'notify_api',
    }
    key = mapping.get(str(kind or 'general'))
    return True if not key else bool(cfg.get(key, True))


def _notify_admin(text, cfg=None, kind='general', owner_key=None):
    cardinal = _CARDINAL_REF
    if cardinal is None:
        return
    bot = getattr(getattr(cardinal, 'telegram', None), 'bot', None)
    if bot is None:
        return
    settings = _load_settings()
    targets = []
    if owner_key is not None and str(owner_key) in settings:
        targets.append((str(owner_key), _sanitize_cfg(settings[str(owner_key)])))
    else:
        for key, raw in settings.items():
            if isinstance(raw, dict) and _has_provider_keys(raw):
                targets.append((str(key), _sanitize_cfg(raw)))
    sent = set()
    for key, target_cfg in targets:
        active_cfg = _sanitize_cfg(cfg) if isinstance(cfg, dict) and _has_provider_keys(cfg) else target_cfg
        if not _notification_allowed(active_cfg, kind):
            continue
        try:
            cid = int(key)
        except Exception:
            continue
        if cid in sent:
            continue
        sent.add(cid)
        try:
            bot.send_message(cid, text, parse_mode='HTML', disable_web_page_preview=True)
        except Exception:
            pass


def _schedule(key, fn, *args, **kwargs):
    with _JOBS_LOCK:
        current = _JOBS.get(str(key))
        if current is not None and not current.done():
            return False
        executor = getattr(_schedule, '_executor', None)
        if executor is None:
            executor = ThreadPoolExecutor(max_workers=5, thread_name_prefix='AUTO-RENTAL')
            _schedule._executor = executor
        future = executor.submit(fn, *args, **kwargs)
        _JOBS[str(key)] = future
        def cleanup(done):
            with _JOBS_LOCK:
                if _JOBS.get(str(key)) is done:
                    _JOBS.pop(str(key), None)
        future.add_done_callback(cleanup)
        return True


def _order_field(obj, name, default=None):
    if obj is None:
        return default
    if isinstance(obj, dict):
        return obj.get(name, default)
    try:
        return getattr(obj, name, default)
    except Exception:
        return default


def _event_chat_id(event):
    message = _order_field(event, 'message')
    chat = _order_field(event, 'chat')
    msg_chat = _order_field(message, 'chat')
    return (
        _order_field(message, 'chat_id')
        or _order_field(msg_chat, 'id')
        or _order_field(event, 'chat_id')
        or _order_field(chat, 'id')
        or _order_field(_order_field(event, 'order'), 'chat_id')
    )


def _order_id(event):
    order = _order_field(event, 'order')
    return str(
        _order_field(order, 'id')
        or _order_field(order, 'order_id')
        or _order_field(event, 'order_id')
        or ''
    )


def _walk_event_objects(order, event):
    objects = [x for x in (order, event) if x is not None]
    index = 0
    while index < len(objects) and len(objects) < 30:
        parent = objects[index]
        index += 1
        for name in ('order', 'lot', 'offer', 'lot_shortcut', 'offer_shortcut', 'node', 'fields', 'data', 'item'):
            child = _order_field(parent, name)
            if child is not None and all(child is not obj for obj in objects):
                objects.append(child)
    return objects


def _order_lot_ids(order, event=None):
    ids = set()

    def add(value):
        try:
            if value is not None:
                value = int(value)
                if value > 0:
                    ids.add(value)
        except Exception:
            pass

    def read_lot_container(container):
        if container is None:
            return
        add(_order_field(container, 'lot_id'))
        add(_order_field(container, 'offer_id'))
        add(_order_field(container, 'id'))

    for obj in (order, event):
        if obj is None:
            continue
        add(_order_field(obj, 'lot_id'))
        add(_order_field(obj, 'offer_id'))
        for name in ('lot', 'offer', 'lot_shortcut', 'offer_shortcut'):
            read_lot_container(_order_field(obj, name))
        for name in ('data', 'fields', 'item'):
            nested = _order_field(obj, name)
            if nested is None:
                continue
            add(_order_field(nested, 'lot_id'))
            add(_order_field(nested, 'offer_id'))
            for child_name in ('lot', 'offer', 'lot_shortcut', 'offer_shortcut'):
                read_lot_container(_order_field(nested, child_name))
    return ids


def _event_text(event):
    message = _order_field(event, 'message')
    chat = _order_field(event, 'chat')
    text = (
        _order_field(message, 'text')
        or _order_field(message, 'content')
        or _order_field(chat, 'last_message_text')
        or _order_field(event, 'text')
        or _order_field(event, 'last_message_text')
        or _order_field(event, 'content')
        or ''
    )
    return str(text or '').strip()


def _event_author(event):
    message = _order_field(event, 'message')
    chat = _order_field(event, 'chat')
    author = _order_field(message, 'author')
    if isinstance(author, str):
        return author
    return str(
        _order_field(author, 'username')
        or _order_field(author, 'name')
        or _order_field(message, 'chat_name')
        or _order_field(event, 'chat_name')
        or _order_field(chat, 'name')
        or ''
    )


def _is_buyer_message(cardinal, event):
    message = _order_field(event, 'message')
    author_id = _order_field(message, 'author_id')
    account_id = _order_field(getattr(cardinal, 'account', None), 'id')
    author = _event_author(event).strip().lower().lstrip('@')
    my_name = str(_order_field(getattr(cardinal, 'account', None), 'username') or '').strip().lower().lstrip('@')
    if author in {'funpay', 'system', 'система'}:
        return False
    if author and my_name and author == my_name:
        return False
    if author_id is not None and account_id is not None and str(author_id) == str(account_id):
        return False
    return True


def _lot_raw_fields(fields):
    if fields is None:
        return None
    try:
        raw = getattr(fields, 'fields', None)
        if callable(raw):
            raw = raw()
        return raw if isinstance(raw, dict) else None
    except Exception:
        return None


def _ensure_account_ua(account):
    try:
        if not getattr(account, 'user_agent', None):
            account.user_agent = FALLBACK_UA
    except Exception:
        pass


def _funpay_save_error(response):
    if response is None:
        return None
    data = response if isinstance(response, dict) else None
    if data is None:
        try:
            data = response.json()
        except Exception:
            data = None
    if isinstance(data, dict):
        if data.get('error') or data.get('errors'):
            return str(data.get('error') or data.get('errors'))[:500]
        if data.get('success') is False or data.get('ok') is False or data.get('saved') is False:
            return str(data)[:500]
        redirect = str(data.get('url') or data.get('redirect') or '')
        if '/premium/limit' in redirect.lower():
            return 'Достигнут лимит активных лотов FunPay.'
    return None


def _lot_subcategory_id(fields):
    try:
        sub = getattr(fields, 'subcategory', None) or getattr(fields, 'subcat', None)
        if sub is not None:
            for attr in ('id', 'subcategory_id', 'category_id'):
                value = getattr(sub, attr, None)
                if value is not None:
                    return int(value)
        for attr in ('subcategory_id', 'category_id'):
            value = getattr(fields, attr, None)
            if value is not None:
                return int(value)
        raw = _lot_raw_fields(fields) or {}
        value = raw.get('node_id') or raw.get('subcategory_id')
        return int(value) if value is not None else None
    except Exception:
        return None


def _parse_offer_edit_form(html_text):
    soup = BeautifulSoup(str(html_text or ''), 'html.parser')
    form = soup.find('form', {'class': 'form-offer-editor'})
    if form is None:
        form = soup.find('form', action=re.compile(r'offerSave', re.I))
    if form is None:
        raise RuntimeError('FunPay не вернул полную форму редактирования LOT.')
    payload = {}
    for field in form.find_all('input'):
        name = field.get('name')
        if not name:
            continue
        field_type = str(field.get('type') or 'text').lower()
        if field_type in {'checkbox', 'radio'}:
            if field.has_attr('checked'):
                payload[name] = field.get('value') or 'on'
            elif name not in payload:
                payload[name] = ''
        else:
            payload[name] = field.get('value') or ''
    for field in form.find_all('textarea'):
        name = field.get('name')
        if name:
            payload[name] = field.text or ''
    for field in form.find_all('select'):
        name = field.get('name')
        if not name:
            continue
        option = field.find('option', selected=True) or field.find('option')
        payload[name] = option.get('value', '') if option is not None else ''
    return payload


def _fetch_offer_edit_payload(account, lot_id):
    lot_id = int(lot_id)
    headers = {
        'accept': '*/*',
        'x-requested-with': 'XMLHttpRequest',
        'referer': f'https://funpay.com/lots/offerEdit?offer={lot_id}',
    }
    method = getattr(account, 'method', None)
    if not callable(method):
        raise RuntimeError('FunPayAPI Account.method недоступен.')
    response = method('get', f'lots/offerEdit?offer={lot_id}', headers, {}, raise_not_200=True)
    html_text = getattr(response, 'text', '') or ''
    try:
        data = response.json()
        if isinstance(data, dict):
            html_text = data.get('html') or data.get('content') or html_text
    except Exception:
        pass
    payload = _parse_offer_edit_form(html_text)
    payload['offer_id'] = str(lot_id)
    if getattr(account, 'csrf_token', None):
        payload['csrf_token'] = account.csrf_token
    return payload


def _full_lot_payload(account, lot_id, *, enabled=None, price=None):
    payload = _fetch_offer_edit_payload(account, lot_id)
    if not payload.get('node_id'):
        fields = _get_lot_fields_ready(account, lot_id)
        node_id = _lot_subcategory_id(fields)
        if node_id:
            payload['node_id'] = str(node_id)
    if enabled is not None:
        if bool(enabled):
            payload['active'] = 'on'
        else:
            payload.pop('active', None)
    if price is not None:
        payload['price'] = str(round(float(price), 2))
    payload.setdefault('deleted', '')
    return payload


def _lot_payload(fields, account=None, target=None):
    if fields is None:
        raise RuntimeError('Лот не найден.')
    try:
        if target is not None:
            fields.active = bool(target)
    except Exception:
        pass
    try:
        if account is not None and hasattr(fields, 'csrf_token') and getattr(account, 'csrf_token', None):
            fields.csrf_token = account.csrf_token
    except Exception:
        pass
    renew = getattr(fields, 'renew_fields', None)
    if callable(renew):
        renewed = renew()
        if renewed is not None:
            fields = renewed
    raw = _lot_raw_fields(fields)
    if not isinstance(raw, dict):
        raise RuntimeError('FunPayAPI не вернул поля лота.')
    payload = dict(raw)
    payload['offer_id'] = str(getattr(fields, 'lot_id', payload.get('offer_id') or 0))
    payload['location'] = LOT_SAVE_LOCATION
    if target is not None:
        if target:
            payload['active'] = 'on'
        else:
            payload.pop('active', None)
    if account is not None and getattr(account, 'csrf_token', None):
        payload['csrf_token'] = account.csrf_token
    return fields, payload


def _post_lot_payload(account, payload, referer_lot_id=0):
    node_id = _as_int(payload.get('node_id'), 0, 1)
    if not node_id:
        raise RuntimeError('Не удалось определить категорию FunPay лота.')
    referer = (
        f'https://funpay.com/lots/offerEdit?offer={int(referer_lot_id)}'
        if int(referer_lot_id or 0) > 0
        else f'https://funpay.com/lots/offerEdit?node={node_id}'
    )
    headers = {
        'accept': '*/*',
        'content-type': 'application/x-www-form-urlencoded; charset=UTF-8',
        'x-requested-with': 'XMLHttpRequest',
        'origin': 'https://funpay.com',
        'referer': referer,
    }
    method = getattr(account, 'method', None)
    if not callable(method):
        raise RuntimeError('FunPayAPI Account.method недоступен.')
    response = method('post', 'lots/offerSave', headers, payload, raise_not_200=True)
    error = _funpay_save_error(response)
    if error:
        raise RuntimeError(f'FunPay отклонил сохранение лота: {error}')
    return response


def _ensure_funpay_account_loaded(account, force=False):
    if account is None:
        return False


    if not force:
        if getattr(account, 'id', None) not in (None, 0, '') or getattr(account, 'username', None):
            return True
    getter = getattr(account, 'get', None)
    if not callable(getter):
        return False
    getter()
    return True


def _get_lot_fields_ready(account, lot_id):
    try:
        return account.get_lot_fields(int(lot_id))
    except Exception as e:
        msg = str(e).lower()
        if 'account.get' not in msg and 'данные об аккаунте' not in msg:
            raise
        _ensure_funpay_account_loaded(account, force=True)
        return account.get_lot_fields(int(lot_id))


def _configured_lot_ids():
    ids = set()
    for raw in _load_settings().values():
        if not isinstance(raw, dict):
            continue
        cfg = _sanitize_cfg(raw)
        for row in cfg.get('lots') or []:
            lot_id = _as_int(row.get('lot_id'), 0, 1)
            if lot_id:
                ids.add(lot_id)
    return ids


def _extension_record_for_lot(lot_id):
    lot_id = _as_int(lot_id, 0, 1)
    if not lot_id:
        return None
    row = _extension_records().get(str(lot_id))
    return dict(row) if isinstance(row, dict) else None


def _extension_lot_verified(cardinal, lot_id, record=None):
    lot_id = _as_int(lot_id, 0, 1)
    if not lot_id:
        return False
    rec = dict(record) if isinstance(record, dict) else _extension_record_for_lot(lot_id)
    marker = str((rec or {}).get('marker') or '').strip()
    if not marker:
        return False
    target = cardinal or _CARDINAL_REF
    if target is None:
        return False
    return _lot_contains_marker(target, lot_id, marker)


def _lot_write_allowed(cardinal, lot_id):
    lot_id = _as_int(lot_id, 0, 1)
    if not lot_id:
        return False
    if lot_id in _configured_lot_ids():
        return True
    return _extension_lot_verified(cardinal, lot_id)


def _set_lot_active(cardinal, lot_id, enabled):
    account = getattr(cardinal, 'account', None) if cardinal is not None else None
    if account is None and _CARDINAL_REF is not None:
        account = getattr(_CARDINAL_REF, 'account', None)
    if account is None:
        logger.error('LOT %s · аккаунт FunPay недоступен', lot_id)
        return False

    lot_id = int(lot_id)
    if not _lot_write_allowed(cardinal, lot_id):
        logger.error('LOT %s · изменение заблокировано: LOT не принадлежит Rental Steam Service', lot_id)
        return False
    target = bool(enabled)
    action = 'ВКЛ' if target else 'ВЫКЛ'
    last_error = None
    for attempt in range(1, LOT_SAVE_RETRIES + 1):
        try:
            lf = _get_lot_fields_ready(account, lot_id)
            if not lf:
                raise RuntimeError('лот не найден')
            current = getattr(lf, 'active', None)
            if current is not None and bool(current) == target:
                logger.info('LOT %s · уже %s', lot_id, action)
                return True

            lf.active = target
            current_price = _as_float(getattr(lf, 'price', None), 0.0)
            if 0 < current_price < 1.0:
                logger.warning('LOT %s · цена %.2f ₽ не принимается FunPay → 1.00 ₽', lot_id, current_price)
                lf.price = 1.0
                _remember_lot_funpay_price(lot_id, 1.0)

            renew = getattr(lf, 'renew_fields', None)
            if callable(renew):
                renewed = renew()
                if renewed is not None:
                    lf = renewed
            save_lot = getattr(account, 'save_lot', None)
            if not callable(save_lot):
                raise RuntimeError('Account.save_lot недоступен')
            save_lot(lf)

            if LOT_SAVE_VERIFY_DELAY:
                time.sleep(LOT_SAVE_VERIFY_DELAY)
            check = _get_lot_fields_ready(account, lot_id)
            actual = getattr(check, 'active', None) if check is not None else None
            if actual is None or bool(actual) == target:
                logger.info('LOT %s · %s', lot_id, action)
                return True
            last_error = f'после сохранения active={actual}'
        except Exception as e:
            last_error = _compact_error(e)
            logger.warning('LOT %s · %s · %s/%s · %s', lot_id, action, attempt, LOT_SAVE_RETRIES, last_error)
            if attempt < LOT_SAVE_RETRIES:
                time.sleep(min(0.6 * attempt, 1.2))
    logger.error('LOT %s · %s не выполнено · %s', lot_id, action, last_error or 'неизвестная ошибка')
    return False

def _set_lot_price(cardinal, lot_id, price):
    account = getattr(cardinal, 'account', None) if cardinal is not None else None
    if account is None and _CARDINAL_REF is not None:
        account = getattr(_CARDINAL_REF, 'account', None)
    if account is None:
        raise RuntimeError('Аккаунт FunPay недоступен')

    lot_id = int(lot_id)
    if not _lot_write_allowed(cardinal, lot_id):
        raise RuntimeError(f'LOT {lot_id} не принадлежит Rental Steam Service')
    calculated = round(float(price), 2)
    actual_price = max(1.0, calculated)
    last_error = None
    for attempt in range(1, LOT_SAVE_RETRIES + 1):
        try:
            lf = _get_lot_fields_ready(account, lot_id)
            if not lf:
                raise RuntimeError('лот не найден')
            lf.price = actual_price
            renew = getattr(lf, 'renew_fields', None)
            if callable(renew):
                renewed = renew()
                if renewed is not None:
                    lf = renewed
            save_lot = getattr(account, 'save_lot', None)
            if not callable(save_lot):
                raise RuntimeError('Account.save_lot недоступен')
            save_lot(lf)
            _remember_lot_funpay_price(lot_id, actual_price)
            if calculated < 1.0:
                logger.info('LOT %s · расчёт %.2f ₽ · FunPay 1.00 ₽', lot_id, calculated)
            else:
                logger.info('LOT %s · цена %.2f ₽', lot_id, actual_price)
            return True
        except Exception as e:
            last_error = _compact_error(e)
            logger.warning('LOT %s · цена %.2f ₽ · %s/%s · %s', lot_id, actual_price, attempt, LOT_SAVE_RETRIES, last_error)
            if attempt < LOT_SAVE_RETRIES:
                time.sleep(min(0.5 * attempt, 1.0))
    raise RuntimeError(last_error or 'FunPay не сохранил цену LOT')

def _get_lot_price(cardinal, lot_id):
    try:
        fields = _get_lot_fields_ready(cardinal.account, lot_id)
        for attr in ('price', 'cost', 'price_rub'):
            if hasattr(fields, attr):
                try:
                    return float(getattr(fields, attr))
                except Exception:
                    pass
        raw = _lot_raw_fields(fields) or {}
        return _as_float(raw.get('price'), 0.0)
    except Exception:
        return None


def _get_lot_amount(cardinal, lot_id):
    account = getattr(cardinal, 'account', None) if cardinal is not None else None
    if account is None and _CARDINAL_REF is not None:
        account = getattr(_CARDINAL_REF, 'account', None)
    if account is None:
        return None
    try:
        fields = _get_lot_fields_ready(account, lot_id)
        value = getattr(fields, 'amount', None)
        if value not in (None, ''):
            return _as_int(value, 0, 0)
        raw = _lot_raw_fields(fields) or {}
        value = raw.get('amount')
        if value not in (None, ''):
            return _as_int(value, 0, 0)
    except Exception:
        pass
    return None


def _set_lot_amount(cardinal, lot_id, amount):
    account = getattr(cardinal, 'account', None) if cardinal is not None else None
    if account is None and _CARDINAL_REF is not None:
        account = getattr(_CARDINAL_REF, 'account', None)
    if account is None:
        raise RuntimeError('Аккаунт FunPay недоступен')
    lot_id = int(lot_id)
    if not _lot_write_allowed(cardinal, lot_id):
        raise RuntimeError(f'LOT {lot_id} не принадлежит Rental Steam Service')
    target = max(1, int(amount))
    last_error = None
    for attempt in range(1, LOT_SAVE_RETRIES + 1):
        try:
            lf = _get_lot_fields_ready(account, lot_id)
            if not lf:
                raise RuntimeError('лот не найден')
            current = getattr(lf, 'amount', None)
            if current in (None, ''):
                current = (_lot_raw_fields(lf) or {}).get('amount')
            current_i = _as_int(current, -1)
            if current_i == target:
                return True
            lf.amount = target


            current_price = _as_float(getattr(lf, 'price', None), 0.0)
            if 0 < current_price < 1.0:
                lf.price = 1.0
                _remember_lot_funpay_price(lot_id, 1.0)
            renew = getattr(lf, 'renew_fields', None)
            if callable(renew):
                renewed = renew()
                if renewed is not None:
                    lf = renewed
            save_lot = getattr(account, 'save_lot', None)
            if not callable(save_lot):
                raise RuntimeError('Account.save_lot недоступен')
            save_lot(lf)
            check = _get_lot_fields_ready(account, lot_id)
            actual = getattr(check, 'amount', None) if check is not None else None
            if actual in (None, ''):
                actual = (_lot_raw_fields(check) or {}).get('amount') if check is not None else None
            actual_i = _as_int(actual, target)
            if actual_i != target:
                raise RuntimeError(f'после сохранения amount={actual_i}, ожидалось {target}')
            logger.info('LOT %s · количество %s → %s', lot_id, current_i if current_i >= 0 else '—', target)
            return True
        except Exception as e:
            last_error = _compact_error(e)
            logger.warning('LOT %s · количество %s · %s/%s · %s', lot_id, target, attempt, LOT_SAVE_RETRIES, last_error)
            if attempt < LOT_SAVE_RETRIES:
                time.sleep(min(0.5 * attempt, 1.0))
    raise RuntimeError(last_error or 'FunPay не сохранил количество LOT')


def _subcategory_lot_ids(cardinal, node_id):
    ids = set()
    fn = getattr(cardinal.account, 'get_my_subcategory_lots', None)
    if callable(fn):
        try:
            for lot in fn(int(node_id)) or []:
                value = getattr(lot, 'id', getattr(lot, 'lot_id', None))
                if value is not None:
                    ids.add(int(value))
        except Exception as e:
            logger.debug('get_my_subcategory_lots failed: %s', e)
    return ids


def _parse_offer_form(html_text):
    soup = BeautifulSoup(str(html_text or ''), 'html.parser')
    form = soup.find('form', {'class': 'form-offer-editor'}) or soup.find('form', action=re.compile(r'offerSave', re.I))
    if form is None:
        raise RuntimeError('FunPay не вернул форму предложения.')
    payload = {}
    for field in form.find_all('input'):
        name = field.get('name')
        if not name:
            continue
        typ = str(field.get('type') or 'text').lower()
        if typ in {'checkbox', 'radio'}:
            payload[name] = (field.get('value') or 'on') if field.has_attr('checked') else ''
        else:
            payload[name] = field.get('value') or ''
    for field in form.find_all('textarea'):
        if field.get('name'):
            payload[field.get('name')] = field.text or ''
    for field in form.find_all('select'):
        name = field.get('name')
        if not name:
            continue
        option = field.find('option', selected=True) or field.find('option')
        payload[name] = option.get('value', '') if option else ''
    return payload


def _response_new_lot_id(response, excluded):
    excluded = {int(x) for x in excluded}
    candidates = []
    try:
        body = response.json()
    except Exception:
        body = None

    def add(value):
        try:
            n = int(str(value).strip())
        except Exception:
            return
        if n > 0 and n not in excluded and n not in candidates:
            candidates.append(n)

    def walk(obj):
        if isinstance(obj, dict):
            for key, value in obj.items():
                key_l = str(key).lower()
                if key_l in {'offer_id', 'lot_id', 'offerid', 'lotid'}:
                    add(value)

                if isinstance(value, str) and key_l in {'url', 'redirect', 'location', 'href'}:
                    for pattern in (
                        r'[?&]offer=(\d+)',
                        r'[?&]id=(\d+)',
                        r'/lots/offer/(\d+)',
                    ):
                        m = re.search(pattern, value, re.I)
                        if m:
                            add(m.group(1))
                walk(value)
        elif isinstance(obj, (list, tuple)):
            for item in obj:
                walk(item)
        elif isinstance(obj, str):

            for pattern in (
                r'(?:offer_id|lot_id)[^0-9]{0,12}(\d{3,})',
                r'[?&]offer=(\d+)',
            ):
                for m in re.findall(pattern, obj, re.I):
                    add(m)

    walk(body)
    try:
        walk(getattr(response, 'text', '') or '')
    except Exception:
        pass
    return candidates[0] if candidates else None


def _canonical_funpay_offer_url(lot_id):
    try:
        lot_id = int(str(lot_id).strip())
    except Exception:
        return ''
    return f'https://funpay.com/lots/offer?id={lot_id}' if lot_id > 0 else ''


def _lot_contains_marker(cardinal, lot_id, marker):
    marker = str(marker or '').strip().casefold()
    if not marker:
        return False
    try:
        texts = _funpay_lot_text(cardinal, int(lot_id))
    except Exception:
        texts = []
    return any(marker in str(text).casefold() for text in texts)


def _find_extension_lot_by_marker(cardinal, record):
    marker = str((record or {}).get('marker') or '').strip()
    if not marker or cardinal is None or getattr(cardinal, 'account', None) is None:
        return None

    source_lot_id = _as_int((record or {}).get('source_lot_id'), 0, 1)
    node_id = 0
    if source_lot_id:
        try:
            source_fields = _get_lot_fields_ready(cardinal.account, source_lot_id)
            node_id = _lot_subcategory_id(source_fields) or 0
        except Exception:
            node_id = 0
    if not node_id:
        node_id = _as_int((record or {}).get('node_id'), 0, 1)
    if not node_id:
        return None

    for lot_id in sorted(_subcategory_lot_ids(cardinal, node_id), reverse=True):
        if _lot_contains_marker(cardinal, lot_id, marker):
            return int(lot_id)
    return None


def _repair_extension_record(cardinal, record):
    if not isinstance(record, dict):
        return record
    row = dict(record)
    old_id = _as_int(row.get('lot_id'), 0, 1)
    marker = str(row.get('marker') or '').strip()
    if not marker:
        return row

    verified_id = old_id if old_id and _lot_contains_marker(cardinal, old_id, marker) else None
    if not verified_id:
        verified_id = _find_extension_lot_by_marker(cardinal, row)

    if not verified_id:
        old_url = str(row.get('url') or '')
        for pattern in (r'[?&]offer=(\d+)', r'[?&]id=(\d+)'):
            m = re.search(pattern, old_url, re.I)
            if not m:
                continue
            candidate = _as_int(m.group(1), 0, 1)
            if candidate and _lot_contains_marker(cardinal, candidate, marker):
                verified_id = candidate
                break

    if not verified_id:
        return row

    changed = old_id != int(verified_id) or row.get('url') != _canonical_funpay_offer_url(verified_id)
    row['lot_id'] = int(verified_id)
    row['url'] = _canonical_funpay_offer_url(verified_id)
    if changed:
        if old_id and old_id != int(verified_id):
            _extension_delete(old_id)
        _extension_save(row)
        logger.info('Лот продления исправлен · LOT %s → %s', old_id or '—', verified_id)
    return row


def _create_extension_lot(cardinal, rental_record, hours, requested_by='buyer'):
    cfg = _cfg_for_record(
        rental_record,
        _owner_cfg(rental_record.get('owner_key') or rental_record.get('chat_id'))
    )
    if not cfg.get('extension_enabled', True):
        raise RuntimeError('Продления отключены продавцом.')
    rental_id = _normalize_rental_id(rental_record.get('rental_id'))
    if not rental_id:
        raise RuntimeError('У аренды отсутствует rental_id.')
    source_lot_id = _as_int(rental_record.get('lot_id'), 0, 1)
    if not source_lot_id:
        raise RuntimeError('Не найден исходный FunPay LOT.')
    price_data = _api_extension_price(cfg, rental_record, hours)
    api_cost = _price_total(price_data)
    if api_cost is None:
        raise RuntimeError('Провайдер не вернул стоимость продления.')
    markup = _effective_markup(cfg, source_lot_id)
    seller_price = _seller_price(api_cost, markup)

    account = cardinal.account
    _ensure_account_ua(account)
    source_fields = _get_lot_fields_ready(account, source_lot_id)
    if not source_fields:
        raise RuntimeError(f'Исходный LOT {source_lot_id} не найден.')
    node_id = _lot_subcategory_id(source_fields)
    if not node_id:
        raise RuntimeError('Не удалось определить категорию исходного лота.')
    before_ids = _subcategory_lot_ids(cardinal, node_id)
    _, payload = _lot_payload(source_fields, account, target=True)
    marker = 'AREXT-' + hashlib.sha1(f'{rental_record.get("order_id")}:{hours}:{time.time_ns()}'.encode()).hexdigest()[:8].upper()
    payload['offer_id'] = '0'
    payload['node_id'] = str(node_id)
    payload['location'] = ''
    payload['deleted'] = ''
    payload['active'] = 'on'
    payload['deactivate_after_sale'] = 'on'
    payload['price'] = str(seller_price)
    payload['amount'] = '1'
    ext_title_ru = f'Продление аренды {rental_record.get("product_name") or "Steam"} +{_format_duration(hours)} [{marker}]'
    ext_title_en = f'Rental extension {rental_record.get("product_name") or "Steam"} +{_format_duration(hours)} [{marker}]'
    payload['fields[summary][ru]'] = ext_title_ru
    if 'fields[summary][en]' in payload:
        payload['fields[summary][en]'] = ext_title_en
    payload['fields[payment_msg][ru]'] = ''
    if 'fields[payment_msg][en]' in payload:
        payload['fields[payment_msg][en]'] = ''
    payload['fields[desc][ru]'] = (
        f'Персональное продление аренды на {_format_duration(hours)}. ' +
        (f'Временный лот, действует не более 20 минут. Код: {marker}.'
         if cfg.get('extension_temporary_enabled', True)
         else f'Персональный лот продления. Код: {marker}.')
    )
    if 'fields[desc][en]' in payload:
        payload['fields[desc][en]'] = (
            f'Personal rental extension for {_format_duration(hours)}. '
            f'One-time offer. Reference: {marker}.'
        )
    response = _post_lot_payload(account, payload, referer_lot_id=0)
    response_candidate = _response_new_lot_id(response, before_ids)
    new_lot_id = None


    for _ in range(12):
        time.sleep(0.75)
        after_ids = _subcategory_lot_ids(cardinal, node_id)
        new_ids = sorted(after_ids - before_ids)


        if response_candidate and response_candidate in new_ids and _lot_contains_marker(cardinal, response_candidate, marker):
            new_lot_id = int(response_candidate)
            break


        for candidate in new_ids:
            if _lot_contains_marker(cardinal, candidate, marker):
                new_lot_id = int(candidate)
                break
        if new_lot_id:
            break


    if not new_lot_id:
        raise RuntimeError(f'FunPay создал лот, но его реальный offer ID не найден. Маркер: {marker}')
    now = _now()
    record = {
        'lot_id': int(new_lot_id),
        'provider': _provider_id(rental_record),
        'source_lot_id': source_lot_id,
        'node_id': int(node_id),
        'order_id': str(rental_record.get('order_id') or ''),
        'rental_id': rental_id,
        'product_id': int(rental_record['product_id']),
        'product_name': str(rental_record.get('product_name') or ''),
        'duration_hours': int(hours),
        'api_cost': float(api_cost),
        'price': float(seller_price),
        'chat_id': str(rental_record.get('delivery_chat_id') or rental_record.get('chat_id') or ''),
        'owner_key': str(rental_record.get('owner_key') or _owner_key_for_cfg(cfg) or ''),
        'api_key_fp': str(rental_record.get('api_key_fp') or _api_key_fp(cfg)),
        'marker': marker,
        'status': 'active',
        'requested_by': str(requested_by),
        'created_ts': now,
        'expires_ts': now + 1200 if cfg.get('extension_temporary_enabled', True) else 0,
        'url': _canonical_funpay_offer_url(new_lot_id),
    }
    _extension_save(record)
    _notify_admin(
        f'➕ <b>Создан лот продления</b>\n'
        f'Заказ: <code>{_h(record.get("order_id"))}</code>\n'
        f'Игра: <b>{_h(record.get("product_name"))}</b>\n'
        f'Срок: <b>+{_format_duration(record.get("duration_hours") or 0)}</b>\n'
        f'Цена: <code>{record.get("price", 0):.2f} ₽</code>',
        cfg=cfg, kind='extension'
    )
    return record


def _delete_funpay_lot(cardinal, lot_id):
    account = cardinal.account
    lot_id = int(lot_id)
    if not _extension_lot_verified(cardinal, lot_id):
        logger.error('LOT %s · удаление заблокировано: временный LOT Rental Steam Service не подтверждён', lot_id)
        return False
    for name in ('delete_lot', 'remove_lot'):
        fn = getattr(account, name, None)
        if callable(fn):
            try:
                if fn(lot_id) is not False:
                    return True
            except Exception:
                pass
    try:
        fields = _get_lot_fields_ready(account, lot_id)
        if not fields:
            return True
        _, payload = _lot_payload(fields, account, target=False)
        payload.pop('active', None)
        payload['deleted'] = '1'
        _post_lot_payload(account, payload, referer_lot_id=lot_id)
        return True
    except Exception as e:
        logger.warning('Не удалось удалить временный LOT %s: %s', lot_id, e)
        return False


def _cleanup_extension(cardinal, record, notify=False):
    record = _repair_extension_record(cardinal, record)
    lot_id = _as_int(record.get('lot_id'), 0, 1)
    if not lot_id:
        return
    if not _extension_lot_verified(cardinal, lot_id, record):
        record['status'] = 'cleanup_blocked'
        record['last_error'] = 'LOT не подтверждён маркером Rental Steam Service'
        _extension_save(record)
        logger.error('LOT %s · очистка заблокирована: маркер Rental Steam Service не найден', lot_id)
        return
    try:
        _set_lot_active(cardinal, lot_id, False)
    except Exception:
        pass
    deleted = _delete_funpay_lot(cardinal, lot_id)
    if deleted:
        _extension_delete(lot_id)
    else:
        record['status'] = 'cleanup_pending'
        record['next_cleanup_ts'] = _now() + 300
        _extension_save(record)
    if notify and record.get('chat_id'):
        cfg = _owner_cfg(record.get('chat_id'))
        _safe_send(cardinal, record.get('chat_id'), _tpl(cfg, 'extension_expired', extend_command=cfg['extend_command']))
        _notify_admin(
            f'🗑 <b>Лот продления истёк</b>\n'
            f'Заказ: <code>{_h(record.get("order_id"))}</code>\n'
            f'LOT: <code>{record.get("lot_id")}</code>',
            cfg=cfg, kind='extension'
        )


def _extension_by_event(order, event, extra_text=''):
    records = _extension_records()
    repaired_records = {}
    for rec in records.values():
        if not isinstance(rec, dict):
            continue
        try:
            rec = _repair_extension_record(_CARDINAL_REF, rec) if _CARDINAL_REF else dict(rec)
        except Exception:
            rec = dict(rec)
        repaired_records[str(rec.get('lot_id'))] = rec
    records = repaired_records or records
    lot_ids = set(_order_lot_ids(order, event)) | _candidate_ids_from_html(order, event)
    for lot_id in lot_ids:
        rec = records.get(str(lot_id))
        if isinstance(rec, dict) and rec.get('status') in {'active', 'processing', 'retry'}:
            return dict(rec)


    blob = ' | '.join(_order_text_candidates(order, event, extra_text)).casefold()
    for rec in records.values():
        if rec.get('status') not in {'active', 'processing', 'retry'}:
            continue
        marker = str(rec.get('marker') or '').strip()
        if marker and marker.casefold() in blob:
            return dict(rec)
    return None


def _normalize_order_text(value):
    text = str(value or '').casefold()
    text = text.replace('ё', 'е')
    text = re.sub(r'[^a-zа-я0-9]+', ' ', text, flags=re.I)
    return re.sub(r'\s+', ' ', text).strip()


def _order_text_candidates(order, event=None, extra_text=''):
    values = []
    for obj in (order, event):
        if obj is None:
            continue
        for name in ('short_description', 'description', 'title', 'full_description', 'name', 'subcategory_name', 'html'):
            v = _order_field(obj, name)
            if v:
                values.append(str(v))
    if extra_text:
        values.append(str(extra_text))
    result = []
    for value in values:
        if value and value not in result:
            result.append(value)
    return result


def _funpay_lot_text(cardinal, lot_id):
    texts = []
    try:
        fields = _get_lot_fields_ready(cardinal.account, lot_id)
    except Exception:
        fields = None
    if fields is not None:
        for attr in ('title', 'description', 'summary', 'name'):
            value = getattr(fields, attr, None)
            if value:
                texts.append(str(value))
        raw = _lot_raw_fields(fields) or {}
        for key, value in raw.items():
            lk = str(key).lower()
            if not value:
                continue
            if any(token in lk for token in ('summary', 'desc', 'title', 'type', 'game', 'platform', 'edition', 'region')):
                texts.append(str(value))
            elif isinstance(value, str) and len(value) <= 120 and not any(token in lk for token in ('csrf', 'token', 'password', 'payment_msg')):


                texts.append(value)
    result = []
    for value in texts:
        value = str(value).strip()
        if value and value not in result:
            result.append(value)
    return result


def _lot_match_score(cardinal, item, normalized_blob):
    if not normalized_blob:
        return 0
    product = _normalize_order_text(item.get('product_name'))
    score = 0
    if product and len(product) >= 3 and product in normalized_blob:
        score += 60 + min(20, len(product.split()) * 4)
    seen = set()
    for text in _funpay_lot_text(cardinal, item['lot_id']):
        norm = _normalize_order_text(text)
        if not norm or norm in seen or len(norm) < 3:
            continue
        seen.add(norm)
        if norm == product:
            continue
        if norm in normalized_blob:
            score += 35 + min(25, len(norm.split()) * 5)
            continue
        tokens = [x for x in norm.split() if len(x) >= 3]
        if tokens:
            overlap = sum(1 for x in set(tokens) if x in normalized_blob.split())
            if overlap >= 2:
                score += min(30, overlap * 6)
    return score


def _unmanaged_lot_match_score(cardinal, item, normalized_blob):
    try:
        fields = _get_lot_fields_ready(cardinal.account, item['lot_id'])
        node_id = _lot_subcategory_id(fields)
    except Exception:
        return 0
    if not node_id:
        return 0
    managed = _configured_lot_ids()
    for key in _extension_records().keys():
        lot_id = _as_int(key, 0, 1)
        if lot_id:
            managed.add(lot_id)
    best = 0
    for lot_id in _subcategory_lot_ids(cardinal, node_id):
        if lot_id in managed:
            continue


        fake = {'lot_id': lot_id, 'product_name': ''}
        best = max(best, _lot_match_score(cardinal, fake, normalized_blob))
    return best


def _candidate_ids_from_html(order, event=None):
    result = set()
    for obj in (order, event):
        html_value = _order_field(obj, 'html')
        if not isinstance(html_value, str):
            continue
        for m in re.finditer(r'(?:offer\?id=|data-offer=["\']|data-lot-id=["\'])(\d+)', html_value, re.I):
            try:
                result.add(int(m.group(1)))
            except Exception:
                pass
    return result


def _has_unmanaged_product_collision(cardinal, item, product_norm):
    if cardinal is None or not product_norm:
        return False
    try:
        fields = _get_lot_fields_ready(cardinal.account, item['lot_id'])
        node_id = _lot_subcategory_id(fields)
    except Exception:
        return False
    if not node_id:
        return False
    managed = _configured_lot_ids()
    for key in _extension_records().keys():
        lot_id = _as_int(key, 0, 1)
        if lot_id:
            managed.add(lot_id)
    for lot_id in _subcategory_lot_ids(cardinal, node_id):
        if lot_id in managed:
            continue
        for text in _funpay_lot_text(cardinal, lot_id):
            if product_norm in _normalize_order_text(text):
                return True
    return False


def _get_lot_active(cardinal, lot_id):
    account = getattr(cardinal, 'account', None) if cardinal is not None else None
    if account is None and _CARDINAL_REF is not None:
        account = getattr(_CARDINAL_REF, 'account', None)
    if account is None:
        return None
    try:
        fields = _get_lot_fields_ready(account, int(lot_id))
        if fields is None:
            return None
        value = getattr(fields, 'active', None)
        return bool(value) if value is not None else None
    except Exception:
        return None


def _order_price_candidates(order, event=None):
    values = []
    seen = set()
    roots = []
    nested_order = _order_field(event, 'order') if event is not None else None
    for obj in (nested_order, order, event):
        if obj is not None and all(obj is not x for x in roots):
            roots.append(obj)
    for root in roots:
        for obj in _walk_event_objects(root, None):
            if obj is None:
                continue
            for name in ('price', 'sum', 'sum_', 'total', 'total_price', 'order_sum'):
                raw = _order_field(obj, name)
                if raw in (None, '') or isinstance(raw, bool):
                    continue
                try:
                    value = round(float(str(raw).replace(' ', '').replace(',', '.')), 2)
                except Exception:
                    continue
                if value > 0 and value not in seen:
                    seen.add(value)
                    values.append(value)
    return values


def _flatten_match_values(value):
    result = []
    if value is None or isinstance(value, bool):
        return result
    if isinstance(value, dict):
        for key, val in value.items():
            result.extend(_flatten_match_values(key))
            result.extend(_flatten_match_values(val))
        return result
    if isinstance(value, (list, tuple, set)):
        for item in value:
            result.extend(_flatten_match_values(item))
        return result
    norm = _normalize_order_text(value)
    if norm:
        result.append(norm)
    return result


def _order_structured_values(order, event=None):
    result = set()
    for obj in _walk_event_objects(order, event):
        if obj is None:
            continue
        fields = _order_field(obj, 'fields')
        if isinstance(fields, dict):
            for key, field in fields.items():
                result.update(_flatten_match_values(key))
                for attr in ('id', 'name', 'field_type_id', 'value'):
                    result.update(_flatten_match_values(_order_field(field, attr)))
                if isinstance(field, dict):
                    result.update(_flatten_match_values(field))
        for name in ('server', 'side'):
            child = _order_field(obj, name)
            if child is not None:
                result.update(_flatten_match_values(_order_field(child, 'name')))
                result.update(_flatten_match_values(_order_field(child, 'id')))
    return {x for x in result if x and len(x) >= 1}


def _lot_structured_values(cardinal, lot_id):
    result = set()
    try:
        fields = _get_lot_fields_ready(cardinal.account, int(lot_id))
    except Exception:
        fields = None
    if fields is None:
        return result
    raw = _lot_raw_fields(fields) or {}
    ignored = ('csrf', 'token', 'payment_msg', 'desc', 'summary', 'images', 'secrets', 'active', 'deleted', 'price', 'amount', 'offer_id')
    for key, value in raw.items():
        low = str(key).lower()
        if any(part in low for part in ignored):
            continue
        result.update(_flatten_match_values(key))
        result.update(_flatten_match_values(value))
    for attr in ('server', 'side'):
        obj = getattr(fields, attr, None)
        if obj is not None:
            result.update(_flatten_match_values(getattr(obj, 'name', None)))
            result.update(_flatten_match_values(getattr(obj, 'id', None)))
    return {x for x in result if x and len(x) >= 1}


def _unique_configured_lot_by_order_details(cardinal, order, event, candidates):
    candidates = list(candidates or [])
    if len(candidates) <= 1:
        return candidates[0] if candidates else None


    prices = _order_price_candidates(order, event)
    price_diag = []
    live_prices = {}
    for item in candidates:
        expected = 0.0
        if cardinal is not None:
            expected = _as_float(_get_lot_price(cardinal, item['lot_id']), 0.0)
        if expected <= 0:
            expected = _as_float(item.get('last_funpay_price'), 0.0)
        expected = round(expected, 2) if expected > 0 else 0.0
        live_prices[int(item['lot_id'])] = expected
        price_diag.append((int(item['lot_id']), expected))


    for order_price in prices:
        price_matches = [
            item for item in candidates
            if live_prices.get(int(item['lot_id']), 0.0) > 0
            and abs(live_prices[int(item['lot_id'])] - order_price) <= 0.02
        ]
        if len(price_matches) == 1:
            chosen = price_matches[0]
            logger.info(
                'LOT %s сопоставлен среди дублей по цене заказа · order=%.2f · lot=%.2f',
                chosen['lot_id'], order_price, live_prices[int(chosen['lot_id'])]
            )
            return chosen
        if len(price_matches) > 1:
            candidates = price_matches
            break


    order_values = _order_structured_values(order, event)
    fields_diag = []
    if cardinal is not None and order_values and len(candidates) > 1:
        scored = []
        for item in candidates:
            lot_values = _lot_structured_values(cardinal, item['lot_id'])
            common = order_values & lot_values
            score = sum(1 + min(8, len(v)) for v in common if len(v) >= 2)
            scored.append((score, int(item['lot_id']), item, sorted(common)[:8]))
        scored.sort(key=lambda row: (row[0], row[1]), reverse=True)
        if scored and scored[0][0] > 0 and (len(scored) == 1 or scored[0][0] > scored[1][0]):
            chosen = scored[0][2]
            logger.info('LOT %s сопоставлен среди дублей по полям оплаченного LOT · score=%s',
                        chosen['lot_id'], scored[0][0])
            return chosen
        fields_diag = [(x[1], x[0], x[3]) for x in scored]


    logger.warning(
        'Дубли Rental LOT не удалось безопасно различить · order_prices=%s · lot_prices=%s · fields=%s',
        prices, price_diag, fields_diag
    )
    return None


def _paid_order_product_hint(values):
    for value in values or []:
        text = re.sub(r'<[^>]+>', ' ', str(value or ''))
        text = re.sub(r'\s+', ' ', text).strip()
        if not text:
            continue
        match = re.search(
            r'(?:оплатил|оплатила)\s+заказ\s*#[A-Za-z0-9_-]+\.\s*([^,.;\n]{2,160})',
            text, re.I
        )
        if match:
            return match.group(1).strip()
    return ''


def _lot_by_event(cfg, order, event, cardinal=None, extra_text=''):
    configured = cfg.get('lots') or []
    if not configured:
        return None
    lot_ids = set(_order_lot_ids(order, event)) | _candidate_ids_from_html(order, event)
    for item in configured:
        if int(item['lot_id']) in lot_ids:
            return item
    if lot_ids:
        return None

    texts = _order_text_candidates(order, event, extra_text)
    normalized_blob = ' | '.join(_normalize_order_text(x) for x in texts if x)
    if not normalized_blob:
        return None


    paid_hint = _normalize_order_text(_paid_order_product_hint(texts))
    if paid_hint:
        hint_matches = []
        for item in configured:
            product = _normalize_order_text(item.get('product_name'))
            if product and len(product) >= 3 and (product in paid_hint or paid_hint in product):
                hint_matches.append(item)
        if len(hint_matches) == 1:
            candidate = hint_matches[0]
            logger.info('LOT %s сопоставлен по системному сообщению FunPay · hint=%s',
                        candidate['lot_id'], paid_hint)
            return candidate
        if len(hint_matches) > 1:
            resolved = _unique_configured_lot_by_order_details(cardinal, order, event, hint_matches)
            if resolved is not None:
                return resolved
            logger.warning('Системное сообщение FunPay совпало с несколькими настроенными LOT · hint=%s · lots=%s',
                           paid_hint, [int(x.get('lot_id') or 0) for x in hint_matches])


    product_matches = []
    for item in configured:
        product = _normalize_order_text(item.get('product_name'))
        if product and len(product) >= 3 and product in normalized_blob:
            product_matches.append(item)
    if len(product_matches) == 1:
        candidate = product_matches[0]
        logger.info('LOT %s сопоставлен по названию настроенного товара · product=%s',
                    candidate['lot_id'], candidate.get('product_name') or '')
        return candidate


    candidates = product_matches if product_matches else configured
    if len(candidates) > 1:
        resolved = _unique_configured_lot_by_order_details(cardinal, order, event, candidates)
        if resolved is not None:
            return resolved
        if product_matches:
            logger.warning(
                'Rental LOT не выбран: одинаковый товар настроен в нескольких LOT и точного признака заказа недостаточно · lots=%s',
                [(int(x.get('lot_id') or 0), _provider_id(x), _as_float(x.get('last_funpay_price'), 0.0)) for x in candidates]
            )
            logger.info(
                'Rental LOT match debug · configured=%s · product_matches=%s · order_prices=%s · text=%s',
                [(int(x.get('lot_id') or 0), str(x.get('product_name') or '')) for x in configured],
                [int(x.get('lot_id') or 0) for x in product_matches],
                _order_price_candidates(order, event),
                _compact_error(normalized_blob, 220)
            )
            return None
    if cardinal is not None:
        scored = []
        for item in candidates:
            score = _lot_match_score(cardinal, item, normalized_blob)
            if score > 0:
                scored.append((score, int(item['lot_id']), item))
        scored.sort(key=lambda row: (row[0], row[1]), reverse=True)
        if scored:
            best_score, _lid, candidate = scored[0]
            second_score = scored[1][0] if len(scored) > 1 else 0
            if best_score >= 60 and best_score > second_score:
                logger.info('LOT %s сопоставлен по полям настроенного LOT · score=%s',
                            candidate['lot_id'], best_score)
                return candidate
            logger.warning(
                'Rental LOT не выбран: неоднозначность между настроенными LOT · scores=%s',
                [(row[1], row[0]) for row in scored[:5]]
            )

    logger.info(
        'Rental LOT match debug · configured=%s · product_matches=%s · text=%s',
        [(int(x.get('lot_id') or 0), str(x.get('product_name') or '')) for x in configured],
        [int(x.get('lot_id') or 0) for x in product_matches],
        _compact_error(normalized_blob, 220)
    )
    return None


def _resolve_full_order(cardinal, order_id, fallback=None):
    if not order_id or not getattr(cardinal, 'account', None):
        return fallback
    getter = getattr(cardinal.account, 'get_order', None)
    if not callable(getter):
        return fallback
    try:
        return getter(str(order_id).lstrip('#')) or fallback
    except Exception as e:
        logger.debug('get_order(%s) fallback: %s', order_id, _compact_error(e))
        return fallback


def _resolve_order_chat_id(cardinal, event, order, order_id=''):
    chat_id = _event_chat_id(event) or _order_field(order, 'chat_id')
    if chat_id:
        return chat_id
    full = _resolve_full_order(cardinal, order_id, order)
    chat_id = _order_field(full, 'chat_id')
    if chat_id:
        return chat_id
    buyer = str(_order_field(full, 'buyer_username') or _order_field(order, 'buyer_username') or '').strip()
    if buyer and getattr(cardinal, 'account', None):
        getter = getattr(cardinal.account, 'get_chat_by_name', None)
        if callable(getter):
            try:
                chat = getter(buyer, True)
                if chat and getattr(chat, 'id', None):
                    return chat.id
            except Exception:
                pass
    return None


def _idem(prefix, value):
    base = re.sub(r'[^A-Za-z0-9._:-]+', '-', str(value))[:80]
    return f'fpc-{prefix}-{base}'[:120]


def _lot_cfg_by_id(cfg, lot_id):
    try:
        lid = int(lot_id)
    except Exception:
        return None
    return next((x for x in (cfg.get('lots') or []) if int(x.get('lot_id') or 0) == lid), None)


def _effective_markup(cfg, lot_or_id=None):
    row = lot_or_id if isinstance(lot_or_id, dict) else _lot_cfg_by_id(cfg, lot_or_id)
    if isinstance(row, dict) and row.get('markup_override_percent') is not None:
        return _as_float(row.get('markup_override_percent'), 0.0)
    return _as_float(cfg.get('global_markup_percent'), 20.0)


def _seller_price(api_cost, markup_percent):


    calculated = round(float(api_cost or 0.0) * (1.0 + float(markup_percent or 0.0) / 100.0), 2)
    return max(1.0, calculated)

def _buyer_price_estimate(cfg, seller_price):
    seller_price = max(0.01, float(seller_price or 0))
    return {
        'card': round(seller_price * float(cfg.get('funpay_card_factor') or 1.1915), 2),
        'sbp': round(seller_price * float(cfg.get('funpay_sbp_factor') or 1.1405), 2),
    }


def _rent_success_message(cfg, record, credentials):
    login, password = _credentials_values(credentials)
    order_id = str(record.get('order_id') or '')
    login_id = login or str(record.get('account_login') or '')
    result = _tpl(
        cfg, 'rent_success',
        game=record.get('product_name') or f"Product {record.get('product_id')}",
        duration=_format_duration(record.get('duration_hours') or 0),
        ends_at=_fmt_dt(record.get('ends_at')),
        login=login or '—', password=password or '—',
        guard_command=(f'!код_{login_id}' if login_id else 'после получения логина'),
        credentials_command=f'!данные_{order_id}',
        status_command=f'!срок_{order_id}',
        extend_command=f'!продлить_{order_id}',
        order_id=order_id, rental_id=record.get('rental_id')
    )

    if record.get("review_gift_eligible") and cfg.get("review_gift_enabled"):
        result += "\n\n" + _tpl(
            cfg, "review_gift_offer",
            duration=_format_duration(record.get("review_gift_hours") or 1),
            stars=int(record.get("review_gift_min_stars") or cfg.get("review_gift_min_stars") or 5),
            order_id=record.get("order_id"), rental_id=record.get("rental_id")
        )
    return result


def _norm_username(value):
    return str(value or '').strip().lower().lstrip('@')


def _record_chat_aliases(record):
    aliases = set()
    if record.get('chat_id') not in (None, ''):
        aliases.add(str(record.get('chat_id')))
    raw = record.get('chat_aliases') or []
    if isinstance(raw, (list, tuple, set)):
        for value in raw:
            if value not in (None, ''):
                aliases.add(str(value))
    return aliases


def _remember_rental_contact(order_id, chat_id=None, buyer_username=''):
    rec = _rental_get(order_id)
    if not rec:
        return None
    aliases = _record_chat_aliases(rec)
    if chat_id not in (None, ''):
        aliases.add(str(chat_id))
    if buyer_username:
        rec['buyer_username'] = str(buyer_username).strip()
    rec['chat_aliases'] = sorted(aliases)

    if chat_id not in (None, ''):
        rec['delivery_chat_id'] = str(chat_id)
    return _rental_save(rec)


def _record_belongs_to_buyer(record, chat_id=None, author=''):
    if not record:
        return False
    if chat_id not in (None, '') and str(chat_id) in _record_chat_aliases(record):
        return True
    buyer = _norm_username(record.get('buyer_username'))
    who = _norm_username(author)
    if buyer and who and buyer == who:
        _remember_rental_contact(record.get('order_id'), chat_id, author)
        return True
    return False


def _repair_rental_contact(cardinal, record, preferred_chat_id=None):
    if not record or not record.get('order_id'):
        return record
    full = _resolve_full_order(cardinal, record.get('order_id'), None)
    buyer = str(_order_field(full, 'buyer_username') or record.get('buyer_username') or '').strip()
    aliases = _record_chat_aliases(record)
    full_chat = _order_field(full, 'chat_id')
    if full_chat not in (None, ''):
        aliases.add(str(full_chat))
    if preferred_chat_id not in (None, ''):
        aliases.add(str(preferred_chat_id))
    if buyer and getattr(cardinal, 'account', None):
        getter = getattr(cardinal.account, 'get_chat_by_name', None)
        if callable(getter):
            try:
                chat = getter(buyer, True)
                if chat and getattr(chat, 'id', None) is not None:
                    aliases.add(str(chat.id))
                    preferred_chat_id = chat.id
            except Exception:
                pass
    record['buyer_username'] = buyer
    record['chat_aliases'] = sorted(aliases)
    if preferred_chat_id not in (None, ''):
        record['delivery_chat_id'] = str(preferred_chat_id)
    return _rental_save(record)


def _credentials_delivery_worker(cardinal, order_id, max_wait_sec=600):
    started = time.time()
    last_error = ''
    while time.time() - started < max_wait_sec:
        rec = _rental_get(order_id)
        if not rec or not rec.get('rental_id'):
            return False
        if rec.get('credentials_delivered'):
            return True
        if _as_int(rec.get('credentials_next_retry_ts'), 0) > _now():
            return False
        rec = _repair_rental_contact(cardinal, rec) or rec
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id')))
        rec_cfg = _cfg_for_record(rec, cfg)
        try:
            rec, data = _credentials_for_record(rec_cfg, rec)
            login, password = _credentials_values(data)
            if login and password:
                if login:
                    rec['account_login'] = login
                rec['credentials_pending'] = False
                rec['credentials_delivered'] = True
                rec['credentials_delivered_ts'] = _now()
                rec['credentials_error'] = ''
                _rental_save(rec)
                target_chat = rec.get('delivery_chat_id') or rec.get('chat_id')
                _safe_send(cardinal, target_chat, _rent_success_message(cfg, rec, data))
                _notify_admin(
                    f'🔐 <b>Данные аренды выданы</b>\nЗаказ: <code>{_h(order_id)}</code>\n'
                    f'Игра: <b>{_h(rec.get("product_name"))}</b>',
                    cfg=cfg, kind='rental'
                )
                return True
            last_error = 'Провайдер пока не вернул логин/пароль.'
        except SteamSMMError as e:
            last_error = _safe_api_error_message(e)
            if e.code in {'RENTAL_API_INCONSISTENT', 'RENTAL_NOT_FOUND_ALL_KEYS', 'RENTAL_OWNER_UNKNOWN'}:
                rec = _rental_get(order_id) or rec
                rec['credentials_pending'] = True
                rec['credentials_error'] = last_error
                rec['credentials_next_retry_ts'] = _now() + 120
                first_notice = not rec.get('api_inconsistent_notified')
                rec['api_inconsistent_notified'] = True
                _rental_save(rec)
                if first_notice:
                    meta = rec.get('rent_response_meta') or {}
                    _notify_admin(
                        f'⚠️ <b>Несогласованный ответ SteamSMM API</b>\n'
                        f'Заказ: <code>{_h(order_id)}</code>\n'
                        f'Rental ID: <code>{_h(rec.get("rental_id"))}</code>\n'
                        f'POST /rent: <code>success</code>\n'
                        f'GET status/credentials: <code>{_h(e.code)}</code>\n'
                        f'Поля rent: <code>{_h(", ".join(meta.get("fields") or []))}</code>\n\n'
                        'Новая покупка автоматически НЕ создаётся.',
                        cfg=cfg, kind='error', owner_key=rec.get('owner_key')
                    )
                return False

        except Exception as e:
            last_error = _compact_error(e)
        rec = _rental_get(order_id) or rec
        rec['credentials_pending'] = True
        rec['credentials_error'] = last_error
        _rental_save(rec)
        elapsed = time.time() - started
        time.sleep(3 if elapsed < 30 else 10)

    rec = _rental_get(order_id)
    if rec and not rec.get('credentials_delivered'):
        rec['credentials_pending'] = True
        rec['credentials_wait_timeout'] = True
        rec['credentials_error'] = last_error or 'Данные аккаунта долго не появляются.'
        _rental_save(rec)
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id')))
        _notify_admin(
            f'⚠️ <b>Провайдер долго не отдаёт данные входа</b>\nЗаказ: <code>{_h(order_id)}</code>\n'
            f'Rental ID: <code>{_h(rec.get("rental_id"))}</code>\n'
            f'Ошибка: <code>{_h(rec.get("credentials_error"))}</code>',
            cfg=cfg, kind='error'
        )
    return False


def _process_rental_order(cardinal, event, lot, cfg, order_id, chat_id, buyer_username=''):
    existing = _rental_get(order_id)
    cfg = _cfg_for_record(existing, cfg) if existing else _provider_cfg(cfg, _provider_id(lot))
    if existing and existing.get('rental_id') and str(existing.get('status')) in {'active', 'completed', 'ended'}:
        existing = _remember_rental_contact(order_id, chat_id, buyer_username) or existing
        if str(existing.get('status')) in {'active', 'completed'} and not existing.get('credentials_delivered'):
            _schedule(f'credentials:{order_id}', _credentials_delivery_worker, cardinal, order_id)
        return existing
    aliases = []
    if chat_id not in (None, ''):
        aliases.append(str(chat_id))
    record = existing or {
        'order_id': str(order_id),
        'provider': _provider_id(cfg),
        'review_gift_eligible': bool(cfg.get('review_gift_enabled')),
        'review_gift_hours': int(cfg.get('review_gift_hours') or 1),
        'review_gift_min_stars': int(cfg.get('review_gift_min_stars') or 5),
        'chat_id': str(chat_id or ''),
        'delivery_chat_id': str(chat_id or ''),
        'chat_aliases': aliases,
        'buyer_username': str(buyer_username or '').strip(),
        'lot_id': int(lot['lot_id']),
        'product_id': int(lot['product_id']),
        'product_name': str(lot.get('product_name') or ''),
        'duration_hours': int(lot['duration_hours']),
        'idempotency_key': _idem('rent', order_id),
        'owner_key': str(_owner_key_for_cfg(cfg) or ''),
        'api_key_fp': _api_key_fp(cfg),
        'status': 'creating',
        'created_ts': _now(),
        'attempts': 0,
    }
    if chat_id not in (None, ''):
        record['delivery_chat_id'] = str(chat_id)
        record['chat_aliases'] = sorted(_record_chat_aliases(record) | {str(chat_id)})
    if buyer_username:
        record['buyer_username'] = str(buyer_username).strip()
    record['attempts'] = _as_int(record.get('attempts'), 0) + 1
    record['status'] = 'creating'
    _rental_save(record)
    try:
        result = _api_rent(cfg, record['product_id'], record['duration_hours'], record['idempotency_key'])
        rental_id = _rent_api_id(result)
        if not rental_id:
            safe_fields = ', '.join(sorted(str(k) for k in result.keys())) if isinstance(result, dict) else type(result).__name__
            logger.error('[%s] Заказ #%s · аренда оплачена/ответ получен, но data.rental_id отсутствует · поля: %s',
                         NAME, order_id, safe_fields or '—')
            raise SteamSMMError(
                'Провайдер не вернул data.rental_id. Повтор будет выполнен с тем же idempotency_key без повторного списания.',
                code='NO_RENTAL_ID', retryable=True, data={'fields': safe_fields}
            )
        record.update({
            'rental_id': rental_id,

            'rental_id_verified': False,
            'owner_key': str(_owner_key_for_cfg(cfg) or record.get('owner_key') or ''),
            'api_key_fp': _api_key_fp(cfg),
            'rent_response_meta': _rent_response_meta(result),
            'status': str(result.get('status') or 'active'),
            'api_cost': _as_float(result.get('amount') or result.get('total_cost') or result.get('cost'), 0.0),
            'starts_at': result.get('starts_at'),
            'ends_at': result.get('ends_at'),
            'last_error': '',
            'fulfilled_ts': _now(),
        })
        if record['status'] not in {'active', 'completed'}:
            record['status'] = 'active'
        _rental_save(record)


        credentials = result if all(_credentials_values(result)) else {}
        credentials_error = ''
        if not all(_credentials_values(credentials)):
            try:
                record, credentials = _credentials_for_record(cfg, record)
                rental_id = _normalize_rental_id(record.get('rental_id')) or rental_id
            except Exception as e:
                credentials_error = _safe_api_error_message(e)
        login, password = _credentials_values(credentials)
        if login:
            record['account_login'] = login
        if login and password:
            record['credentials_pending'] = False
            record['credentials_delivered'] = True
            record['credentials_delivered_ts'] = _now()
            record['credentials_error'] = ''
            _rental_save(record)
            _safe_send(cardinal, record.get('delivery_chat_id') or chat_id, _rent_success_message(cfg, record, credentials))
        else:
            record['credentials_pending'] = True
            record['credentials_error'] = credentials_error or 'Провайдер пока не вернул логин/пароль.'
            _rental_save(record)
            if not record.get('credentials_pending_notified'):
                _safe_send(cardinal, record.get('delivery_chat_id') or chat_id, _tpl(
                    cfg, 'credentials_pending',
                    game=record.get('product_name') or f"Product {record.get('product_id')}",
                    credentials_command=f'!данные_{record.get("order_id")}',
                    guard_command='!код_ЛОГИН', status_command=f'!срок_{record.get("order_id")}',
                    extend_command=f'!продлить_{record.get("order_id")}',
                    order_id=record.get('order_id'), rental_id=rental_id
                ))
                record['credentials_pending_notified'] = True
                _rental_save(record)

            _schedule(f'credentials:{order_id}', _credentials_delivery_worker, cardinal, order_id)
        _notify_admin(
            f'✅ <b>Аренда создана</b>\nЗаказ: <code>{_h(order_id)}</code>\n'
            f'Игра: <b>{_h(record.get("product_name"))}</b>\nRental ID: <code>{rental_id}</code>'
            + (f'\n⚠️ Credentials: <code>{_h(credentials_error)}</code>' if credentials_error and not (login or password) else ''),
            cfg=cfg, kind='rental'
        )

        _schedule(f'post-rent-sync:{order_id}', _sync_all, cardinal, True)
        return record
    except SteamSMMError as e:
        code = e.code
        record['last_error'] = _safe_api_error_message(e)
        record['last_error_code'] = code
        will_retry = bool(e.retryable or code in {'NO_STOCK', 'INSUFFICIENT_BALANCE'})
        record['status'] = 'retry' if will_retry else 'failed'
        record['next_retry_ts'] = _now() + min(300, 30 * record['attempts']) if will_retry else 0
        _rental_save(record)
        first_failure_notice = not bool(record.get('failure_notified'))
        if code in {'NO_STOCK', 'INSUFFICIENT_BALANCE', 'PRODUCT_NOT_FOUND'} and cfg.get('auto_deactivate_enabled', True):
            try:
                if _set_lot_active(cardinal, lot['lot_id'], False):
                    lots = cfg.get('lots') or []
                    for row in lots:
                        if int(row['lot_id']) == int(lot['lot_id']):
                            row['auto_disabled'] = True
                            row['auto_disabled_reason'] = code.lower()
                    _set_owner_cfg(chat_id, lots=lots)
            except Exception:
                pass
        if first_failure_notice:
            _safe_send(cardinal, chat_id, _tpl(cfg, 'rent_failed', reason=_buyer_error_message(e)))
            record['failure_notified'] = True
            _rental_save(record)
        _notify_admin(
            f'⚠️ <b>Ошибка аренды</b>\nЗаказ: <code>{_h(order_id)}</code>\n'
            f'LOT: <code>{lot["lot_id"]}</code>\nПричина: <code>{_h(record["last_error"])}</code>',
            cfg=cfg, kind='error'
        )
        return record
    except Exception as e:
        record['last_error'] = str(e)
        record['status'] = 'retry'
        record['next_retry_ts'] = _now() + 60
        _rental_save(record)
        logger.exception('Rental processing failed: %s', e)
        _notify_admin(
            f'❌ <b>Внутренняя ошибка Rental Steam Service</b>\nЗаказ: <code>{_h(order_id)}</code>\n'
            f'LOT: <code>{lot.get("lot_id")}</code>\nПричина: <code>{_h(_compact_error(e))}</code>',
            cfg=cfg, kind='error'
        )
        return record


def _process_extension_order(cardinal, event, ext, order_id, chat_id):


    route = _extension_purchase_get(order_id)
    if route and route.get('status') == 'completed':
        logger.info('Заказ #%s · продление уже обработано, повторное событие пропущено.', order_id)
        return
    cfg = _cfg_for_record(ext, _owner_cfg(ext.get('owner_key') or ext.get('chat_id') or chat_id))
    ext = dict(ext)
    _extension_purchase_mark(order_id, ext, status='processing')
    ext.update({
        'status': 'processing',
        'purchase_order_id': str(order_id),
        'purchase_ts': _now(),
        'idempotency_key': ext.get('idempotency_key') or _idem('extend', order_id),
        'attempts': _as_int(ext.get('attempts'), 0) + 1,
    })
    _extension_save(ext)
    try:
        _set_lot_active(cardinal, ext['lot_id'], False)
    except Exception:
        pass
    try:
        result = _api_extend(cfg, ext['rental_id'], ext['duration_hours'], ext['idempotency_key'])
        ends_at = result.get('ends_at') or result.get('new_ends_at')
        original = _rental_get(ext['order_id'])
        if original:
            original['ends_at'] = ends_at or original.get('ends_at')
            original['status'] = 'active'
            original['last_extension_ts'] = _now()
            _rental_save(original)
        ext['status'] = 'completed'
        ext['ends_at'] = ends_at
        ext['last_error'] = ''
        _extension_save(ext)
        _extension_purchase_mark(
            order_id, ext, status='completed',
            ends_at=ends_at or '', completed_ts=_now()
        )
        _safe_send(cardinal, chat_id, _tpl(
            cfg, 'extend_success', game=ext.get('product_name') or 'Steam',
            duration=_format_duration(ext['duration_hours']), ends_at=_fmt_dt(ends_at),
            order_id=ext.get('order_id'), rental_id=ext.get('rental_id')
        ))
        _notify_admin(
            f'✅ <b>Аренда продлена</b>\nRental ID: <code>{ext["rental_id"]}</code>\n'
            f'Срок: <b>+{_format_duration(ext["duration_hours"])}</b>',
            cfg=cfg, kind='extension'
        )
        _cleanup_extension(cardinal, ext, notify=False)
        return
    except SteamSMMError as e:
        ext['last_error'] = _safe_api_error_message(e)
        if e.retryable:
            ext['status'] = 'retry'
            ext['next_retry_ts'] = _now() + min(300, 30 * ext['attempts'])
        else:
            ext['status'] = 'failed'
        _extension_purchase_mark(
            order_id, ext, status=ext['status'],
            last_error=ext['last_error'], next_retry_ts=ext.get('next_retry_ts') or 0
        )
        _delete_funpay_lot(cardinal, ext['lot_id'])
        first_failure_notice = not bool(ext.get('failure_notified'))
        if first_failure_notice:
            _safe_send(cardinal, chat_id, _tpl(cfg, 'extend_failed', reason=_buyer_error_message(e)))
            ext['failure_notified'] = True
            _extension_save(ext)
        _notify_admin(f'⚠️ Продление Rental <code>{ext["rental_id"]}</code>: <code>{_h(ext["last_error"])}</code>', cfg=cfg, kind='error')
    except Exception as e:
        ext['last_error'] = str(e)
        ext['status'] = 'retry'
        ext['next_retry_ts'] = _now() + 60
        _extension_save(ext)
        _extension_purchase_mark(
            order_id, ext, status='retry',
            last_error=ext['last_error'], next_retry_ts=ext['next_retry_ts']
        )
        _delete_funpay_lot(cardinal, ext['lot_id'])
        if not ext.get('failure_notified'):
            _safe_send(cardinal, chat_id, _tpl(cfg, 'extend_failed', reason=_buyer_error_message(e)))
            ext['failure_notified'] = True
            _extension_save(ext)
        logger.exception('Extension processing failed: %s', e)


def _parse_iso_ts(value):
    dt = _api_datetime(value)
    return dt.timestamp() if dt is not None else None


def _record_locally_current(rec):
    status = str(rec.get('status') or '').strip().lower()
    if status not in {'active', 'completed', 'creating', 'retry', 'running', 'rented'}:
        return False
    ends_ts = _parse_iso_ts(rec.get('ends_at'))
    if ends_ts is not None and ends_ts <= time.time():
        return False
    return bool(rec.get('rental_id'))


def _active_rentals_for_chat(chat_id):
    rows = []
    for rec in _rental_list(active_only=False):
        if str(rec.get('chat_id')) != str(chat_id):
            continue
        if not _record_locally_current(rec):
            if str(rec.get('status') or '').lower() in {'active', 'completed', 'running', 'rented'}:
                ends_ts = _parse_iso_ts(rec.get('ends_at'))
                if ends_ts is not None and ends_ts <= time.time():
                    rec['status'] = 'ended'
                    _rental_save(rec)
            continue
        rows.append(rec)
    return rows


def _refresh_rental_current(cfg, rec):
    if not rec:
        return None
    if not rec.get('rental_id'):
        return rec if _record_locally_current(rec) else None
    rid = rec.get('rental_id')
    last_not_found = None
    for owner_key, candidate_cfg, fp in _cfg_candidates_for_record(rec, cfg):
        try:
            data = _api_status(candidate_cfg, rid)
            rec = _claim_rental_owner(rec, owner_key, candidate_cfg)
            if isinstance(data, dict):
                api_status = str(data.get('status') or rec.get('status') or 'active').strip().lower()
                rec['status'] = api_status
                rec['starts_at'] = data.get('starts_at') or rec.get('starts_at')
                rec['ends_at'] = data.get('ends_at') or rec.get('ends_at')
                rec['rental_id_verified'] = True
                rec['rental_id_verified_by'] = 'status'
                rec['api_inconsistent'] = False
                _rental_save(rec)


                if api_status in {'active', 'running', 'rented', 'creating'}:
                    return rec
                if api_status in {'ended', 'expired', 'cancelled', 'canceled', 'rejected'}:
                    return None
            return rec if _record_locally_current(rec) else None
        except SteamSMMError as e:
            if e.code == 'RENTAL_NOT_FOUND':
                last_not_found = e
                continue

            return rec if _record_locally_current(rec) else None
        except Exception:
            return rec if _record_locally_current(rec) else None
    if last_not_found is not None:
        rec['rental_id_verified'] = False
        rec['api_inconsistent'] = True
        _rental_save(rec)
    return rec if _record_locally_current(rec) else None


def _ensure_record_login(cfg, rec):
    login = str(rec.get('account_login') or '').strip()
    if login:
        return login
    if not rec.get('rental_id'):
        return ''
    try:
        rec, data = _credentials_for_record(cfg, rec)
        login, _password = _credentials_values(data)
        if login:
            rec['account_login'] = login
            _rental_save(rec)
        return login
    except Exception:
        return ''


def _select_rental_by_order(chat_id, order_hint, author='', cardinal=None):
    clean = str(order_hint or '').strip().lstrip('#').rstrip('.,;:!?')
    if not clean:
        return None
    rec = _rental_get(clean)
    if not rec:
        return None

    cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id') or chat_id))
    rec = _refresh_rental_current(cfg, rec)
    if not rec:
        return None
    if not _record_belongs_to_buyer(rec, chat_id, author):
        if cardinal is not None:
            full = _resolve_full_order(cardinal, clean, None)
            buyer = _norm_username(_order_field(full, 'buyer_username'))
            if buyer and buyer == _norm_username(author):
                rec = _repair_rental_contact(cardinal, rec, preferred_chat_id=chat_id) or rec
        if not _record_belongs_to_buyer(rec, chat_id, author):
            return None
    _remember_rental_contact(rec.get('order_id'), chat_id, author)
    return rec


def _select_rental_by_login(chat_id, login_hint, author='', cardinal=None):
    clean = str(login_hint or '').strip().rstrip('.,;:!?')
    if not clean:
        return None
    for rec in _rental_list(active_only=False):
        if not rec.get('rental_id'):
            continue
        saved_login = str(rec.get('account_login') or '').strip()
        if saved_login and saved_login.lower() != clean.lower():
            continue
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id') or chat_id))


        rec_cfg = _cfg_for_record(rec, cfg)
        rec = _refresh_rental_current(rec_cfg, rec)
        if not rec:
            continue
        login = saved_login or _ensure_record_login(cfg, rec)
        if not login or login.lower() != clean.lower():
            continue
        if not _record_belongs_to_buyer(rec, chat_id, author):
            if cardinal is not None:
                full = _resolve_full_order(cardinal, rec.get('order_id'), None)
                buyer = _norm_username(_order_field(full, 'buyer_username'))
                if buyer and buyer == _norm_username(author):
                    rec = _repair_rental_contact(cardinal, rec, preferred_chat_id=chat_id) or rec
            if not _record_belongs_to_buyer(rec, chat_id, author):
                continue
        _remember_rental_contact(rec.get('order_id'), chat_id, author)
        return rec
    return None


def _select_rental_order_or_login(chat_id, hint, author='', cardinal=None):
    return _select_rental_by_order(chat_id, hint, author, cardinal) or _select_rental_by_login(chat_id, hint, author, cardinal)


def _parse_command_target(text, base):
    text = str(text or '').strip()
    base = str(base or '').strip()
    if not text.lower().startswith(base.lower()):
        return None
    tail = text[len(base):]
    if not tail:
        return ''
    if tail[0] in {'_', '*'}:
        return tail[1:].strip()
    if tail[0].isspace():
        return tail.strip()
    return None


def _split_extend_target_and_duration(arg):
    raw = str(arg or '').strip()
    if not raw:
        return '', None
    duration_aliases = [
        ('1неделя', 168), ('1_неделя', 168), ('7дней', 168), ('168ч', 168),
        ('1день', 24), ('1_день', 24), ('24ч', 24),
        ('1час', 1), ('1_час', 1), ('1h', 1),
    ]
    low = raw.lower().replace('ё', 'е')
    for token, hours in duration_aliases:
        for sep in ('_', '*', ' '):
            suffix = sep + token
            if low.endswith(suffix):
                target = raw[:-len(suffix)].strip('_* ')
                return target, hours
    return raw, None

def _duration_from_text(text):
    s = str(text or '').strip().lower().replace('ё', 'е')
    aliases = {
        '1час': 1, '1 час': 1, 'час': 1, '1h': 1,
        '1день': 24, '1 день': 24, 'день': 24, '24ч': 24, '24 часа': 24,
        '1неделя': 168, '1 неделя': 168, 'неделя': 168, '7дней': 168, '7 дней': 168, '168ч': 168,
    }
    if s in aliases:
        return aliases[s]
    m = re.fullmatch(r'(\d{1,4})\s*(?:ч|час|часа|часов|h)', s)
    if m:
        return max(1, min(8760, int(m.group(1))))
    m = re.fullmatch(r'(\d{1,3})\s*(?:д|день|дня|дней)', s)
    if m:
        return max(1, min(365, int(m.group(1)))) * 24
    return None


def _message_id_from_obj(obj):
    for name in ('id', 'message_id', 'msg_id'):
        value = _order_field(obj, name)
        if value is not None:
            return value
    return None


def _try_delete_funpay_message(cardinal, chat_id, message_obj_or_id):
    msg_id = message_obj_or_id
    if not isinstance(message_obj_or_id, (str, int)):
        msg_id = _message_id_from_obj(message_obj_or_id)
    if msg_id is None:
        return False
    for owner in (cardinal, getattr(cardinal, 'account', None)):
        if owner is None:
            continue
        for method_name in ('delete_message', 'delete_chat_message', 'remove_message'):
            fn = getattr(owner, method_name, None)
            if not callable(fn):
                continue
            for args in ((chat_id, msg_id), (msg_id,)):
                try:
                    result = fn(*args)
                    if result is not False:
                        return True
                except Exception:
                    continue
    return False


def _command_reply(cardinal, event, text):
    chat_id = _event_chat_id(event)
    previous = _LAST_COMMAND_REPLY.get(str(chat_id))
    if previous is not None:
        _try_delete_funpay_message(cardinal, chat_id, previous)
    sent = _safe_send(cardinal, chat_id, text)
    if sent is not None:
        _LAST_COMMAND_REPLY[str(chat_id)] = sent
    incoming = _order_field(event, 'message')
    _try_delete_funpay_message(cardinal, chat_id, incoming)
    return sent


def _buyer_command_handler(cardinal, event):
    if not _is_buyer_message(cardinal, event):
        return False
    chat_id = _event_chat_id(event)
    if chat_id is None:
        return False
    text = _event_text(event)
    if not text:
        return False
    cfg = _owner_cfg(chat_id)
    buyer_author = _event_author(event)


    target = _parse_command_target(text, '!код')
    if target is not None:
        if not target:
            _command_reply(cardinal, event, _tpl(cfg, 'bad_guard_command'))
            return True
        rec = _select_rental_by_login(chat_id, target, buyer_author, cardinal)
        if not rec:
            _command_reply(cardinal, event, _tpl(cfg, 'no_active_rental'))
            return True
        rec_cfg = _cfg_for_record(rec, cfg)
        guard_key = f'{chat_id}:{rec["rental_id"]}'
        last = _LAST_GUARD.get(guard_key, 0)
        wait = int(rec_cfg['guard_cooldown_sec'] - (time.time() - last))
        if wait > 0:
            _command_reply(cardinal, event, _tpl(cfg, 'guard_wait', seconds=wait))
            return True
        _LAST_GUARD[guard_key] = time.time()
        try:
            data = _api_guard(rec_cfg, rec['rental_id'])
            code = str(data.get('code') or data.get('guard_code') or '').strip()
            if not code:
                raise RuntimeError('Провайдер не вернул Guard-код.')
            _command_reply(cardinal, event, _tpl(rec_cfg, 'guard', code=code, game=rec.get('product_name'), order_id=rec.get('order_id')))
        except Exception as e:
            _command_reply(cardinal, event, _tpl(rec_cfg, 'guard_failed', reason=_buyer_error_message(e)))
        return True


    target = _parse_command_target(text, '!данные')
    if target is not None:
        if not target:
            _command_reply(cardinal, event, _tpl(cfg, 'bad_credentials_command'))
            return True
        rec = _select_rental_by_order(chat_id, target, buyer_author, cardinal)
        if not rec:
            _command_reply(cardinal, event, _tpl(cfg, 'no_active_rental'))
            return True
        rec_cfg = _cfg_for_record(rec, cfg)
        try:
            rec, data = _credentials_for_record(rec_cfg, rec)
            login, password = _credentials_values(data)
            if login:
                rec['account_login'] = login
                _rental_save(rec)
            if not login and not password:
                raise RuntimeError('Провайдер пока не вернул данные аккаунта.')
            login_id = login or str(rec.get('account_login') or '')
            _command_reply(cardinal, event, _tpl(
                rec_cfg, 'credentials',
                login=login or '—', password=password or '—', game=rec.get('product_name'),
                guard_command=(f'!код_{login_id}' if login_id else '!код_ЛОГИН'),
                status_command=f'!срок_{rec.get("order_id")}',
                credentials_command=f'!данные_{rec.get("order_id")}',
                extend_command=f'!продлить_{rec.get("order_id")}',
                order_id=rec.get('order_id')
            ))
        except Exception as e:
            _command_reply(cardinal, event, _tpl(rec_cfg, 'credentials_failed', reason=_buyer_error_message(e)))
        return True


    target = _parse_command_target(text, '!срок')
    if target is not None:
        if not target:
            _command_reply(cardinal, event, _tpl(cfg, 'bad_status_command'))
            return True
        rec = _select_rental_order_or_login(chat_id, target, buyer_author, cardinal)
        if not rec:
            _command_reply(cardinal, event, _tpl(cfg, 'no_active_rental'))
            return True
        rec_cfg = _cfg_for_record(rec, cfg)
        try:
            data = _api_status(rec_cfg, rec['rental_id'])
            rec['status'] = str(data.get('status') or rec.get('status') or 'active')
            rec['starts_at'] = data.get('starts_at') or rec.get('starts_at')
            rec['ends_at'] = data.get('ends_at') or rec.get('ends_at')
            _rental_save(rec)
            if not _record_locally_current(rec):
                _command_reply(cardinal, event, _tpl(rec_cfg, 'rental_expired'))
                return True
            _command_reply(cardinal, event, _tpl(
                rec_cfg, 'status', game=rec.get('product_name') or 'Steam', status=rec['status'],
                ends_at=_fmt_dt(rec.get('ends_at')), remaining=_remaining(rec.get('ends_at')),
                order_id=rec.get('order_id'), rental_id=rec.get('rental_id')
            ))
        except Exception as e:
            _command_reply(cardinal, event, _tpl(rec_cfg, 'status_failed', reason=_buyer_error_message(e)))
        return True


    target = _parse_command_target(text, '!продлить')
    if target is not None:
        if not cfg.get('extension_enabled', True):
            _command_reply(cardinal, event, _tpl(cfg, 'extension_disabled'))
            return True
        if not target:
            _command_reply(cardinal, event, _tpl(cfg, 'extend_usage'))
            return True
        identity, hours = _split_extend_target_and_duration(target)
        rec = _select_rental_order_or_login(chat_id, identity, buyer_author, cardinal)
        if not rec:
            _command_reply(cardinal, event, _tpl(cfg, 'no_active_rental'))
            return True
        rec_cfg = _cfg_for_record(rec, cfg)
        rec = _refresh_rental_current(rec_cfg, rec)
        if not rec:
            _command_reply(cardinal, event, _tpl(rec_cfg, 'rental_expired'))
            return True

        base = f'!продлить_{identity}'
        if not hours:
            _command_reply(cardinal, event, _tpl(
                rec_cfg, 'extend_choose',
                game=rec.get('product_name') or 'Steam',
                cmd1=base + '_1час',
                cmd24=base + '_1день',
                cmd168=base + '_1неделя',
            ))
            return True

        for ext in _extension_records().values():
            if (
                str(ext.get('chat_id')) == str(chat_id)
                and str(ext.get('order_id')) == str(rec.get('order_id'))
                and str(ext.get('status')) == 'active'
                and (int(ext.get('expires_ts') or 0) <= 0 or int(ext.get('expires_ts') or 0) > _now())
            ):
                ext = _repair_extension_record(cardinal, ext)
                url = _canonical_funpay_offer_url(ext.get('lot_id')) or str(ext.get('url') or '')
                _command_reply(cardinal, event, _tpl(rec_cfg, 'extension_existing', url=url))
                return True
        try:
            ext = _create_extension_lot(cardinal, rec, hours, requested_by='buyer')
            _command_reply(cardinal, event, _tpl(
                rec_cfg, 'extend_offer', game=rec.get('product_name') or 'Steam',
                duration=_format_duration(hours), price=f'{ext["price"]:.2f}',
                lot_time=('⏳ Оплатите в течение 20 минут.' if rec_cfg.get('extension_temporary_enabled', True) else 'Лот активен до оплаты.'), ttl_minutes=20, url=ext['url'],
                order_id=rec.get('order_id'), rental_id=rec.get('rental_id')
            ))
        except Exception as e:
            _command_reply(cardinal, event, _tpl(rec_cfg, 'extension_create_failed', reason=_buyer_error_message(e)))
        return True

    return False

def _sync_balance(cfg, owner_key):
    data = _api_balance(cfg)
    updates = {
        'balance': _as_float(data.get('balance'), 0.0),
        'regular_balance': _as_float(data.get('regular_balance'), 0.0),
        'promo_balance': _as_float(data.get('promo_balance'), 0.0),
        'currency': str(data.get('currency') or 'RUB'),
        'last_api_ok': _now(),
        'last_api_error': '',
    }
    cfg.update(updates)
    _set_cfg(owner_key, **updates)
    return data


def _apply_lot_sync(cardinal, owner_key, cfg, products_data=None, balance_data=None, notify=True):
    if not cfg.get('api_key'):
        return {'changed': 0, 'errors': ['API key не задан']}
    products_data = products_data or _api_products(cfg)
    balance_data = balance_data or _api_balance(cfg)
    regular_balance = _as_float(balance_data.get('regular_balance'), 0.0)
    min_balance = _as_float(cfg.get('min_balance_rub'), 0.0, 0.0)
    lots = cfg.get('lots') or []
    changed = 0
    notes = []
    stock_notes = []
    price_notes = []
    lot_notes = []
    balance_blocked = False
    for row in lots:
        lot_id = int(row['lot_id'])
        prev_stock = row.get('last_stock')
        prev_api_cost = _as_float(row.get('last_api_cost'), 0.0)
        prev_funpay = _as_float(row.get('last_funpay_price'), 0.0)
        prev_auto_disabled = bool(row.get('auto_disabled'))
        prev_reason = str(row.get('auto_disabled_reason') or '')
        prev_stock_i = _as_int(prev_stock, -1)
        try:
            product = _find_product(products_data, row['product_id'])
            if not product:
                raise SteamSMMError('Игра отсутствует в каталоге.', code='PRODUCT_NOT_FOUND')
            row['product_name'] = product['title']
            new_stock = int(product['stock']) if product.get('stock_known', True) else -1
            row['last_stock'] = new_stock
            if isinstance(prev_stock, int) and prev_stock >= 0 and new_stock >= 0 and prev_stock != new_stock:
                stock_notes.append(f'{row["product_name"]}: в наличии {prev_stock} → {new_stock}')


            if row.get('auto_stock', True) and product.get('stock_known', True) and new_stock > 0:
                current_amount = _get_lot_amount(cardinal, lot_id)
                row['last_funpay_amount'] = current_amount if current_amount is not None else row.get('last_funpay_amount', -1)
                if current_amount is None or int(current_amount) != int(new_stock):
                    try:
                        _set_lot_amount(cardinal, lot_id, new_stock)
                        row['last_funpay_amount'] = int(new_stock)
                        changed += 1
                        notes.append(f'LOT {lot_id}: количество {current_amount if current_amount is not None else "—"} → {new_stock}')
                        stock_notes.append(f'LOT {lot_id}: FunPay количество → {new_stock}')
                    except Exception as amount_error:
                        notes.append(f'LOT {lot_id}: количество не обновлено · {_compact_error(amount_error)}')

            price_data = _api_calculate_price(_provider_cfg(cfg, _provider_id(row)), row['product_id'], row['duration_hours'])
            api_cost = _price_total(price_data)
            if api_cost is None:
                raise RuntimeError('Не удалось получить цену провайдера.')
            row['last_api_cost'] = float(api_cost)
            target_price = _seller_price(api_cost, _effective_markup(cfg, row))
            row['last_funpay_price'] = target_price
            if prev_api_cost > 0 and abs(prev_api_cost - float(api_cost)) >= 0.001:
                price_notes.append(f'{row["product_name"]}: SteamSMM {prev_api_cost:.2f} → {float(api_cost):.2f} ₽')
            if cfg.get('auto_price_enabled', True) and row.get('auto_price', True):
                current = _get_lot_price(cardinal, lot_id)
                if current is None or abs(float(current) - target_price) >= 0.01:
                    _set_lot_price(cardinal, lot_id, target_price)
                    changed += 1
                    notes.append(f'LOT {lot_id}: цена {current} → {target_price:.2f} ₽')
                    if prev_funpay > 0 and abs(prev_funpay - target_price) >= 0.01:
                        price_notes.append(f'LOT {lot_id}: FunPay {prev_funpay:.2f} → {target_price:.2f} ₽')
            reason = ''
            if cfg.get('auto_deactivate_enabled', True):
                if row.get('auto_stock', True) and product.get('stock_known', True) and product['stock'] <= 0:
                    reason = 'stock'
                elif row.get('auto_balance', True) and regular_balance < max(float(api_cost), min_balance):
                    reason = 'balance'
                    balance_blocked = True
            should_enable = bool(row.get('manual_enabled', True)) and not reason
            stock_returned = (
                row.get('auto_stock', True)
                and product.get('stock_known', True)
                and prev_stock_i == 0
                and new_stock > 0
            )
            if reason:
                need_mark = (not row.get('auto_disabled') or row.get('auto_disabled_reason') != reason)
                if need_mark:
                    if _set_lot_active(cardinal, lot_id, False):
                        row['auto_disabled'] = True
                        row['auto_disabled_reason'] = reason
                        changed += 1
                        human = 'нет аккаунтов в наличии' if reason == 'stock' else 'недостаточно баланса'
                        lot_notes.append(f'LOT {lot_id} выключен: {human}')
                        notes.append(f'LOT {lot_id}: выключен ({reason})')
            elif should_enable:


                actual_active = _get_lot_active(cardinal, lot_id)
                must_enable = bool(row.get('auto_disabled') or stock_returned or actual_active is False)
                if must_enable and _set_lot_active(cardinal, lot_id, True):
                    was_auto_disabled = bool(row.get('auto_disabled'))
                    row['auto_disabled'] = False
                    row['auto_disabled_reason'] = ''
                    changed += 1
                    if stock_returned or prev_stock_i == 0 or was_auto_disabled:
                        lot_notes.append(f'LOT {lot_id} снова включён: товар появился')
                        notes.append(f'LOT {lot_id}: снова включён после появления товара')
                    else:
                        lot_notes.append(f'LOT {lot_id} снова включён: товар доступен')
                        notes.append(f'LOT {lot_id}: восстановлено состояние ВКЛ')

            if prev_auto_disabled and not row.get('auto_disabled') and not any(f'LOT {lot_id} снова включён' == x for x in lot_notes):
                lot_notes.append(f'LOT {lot_id} снова доступен')
            elif (not prev_auto_disabled) and row.get('auto_disabled') and prev_reason != row.get('auto_disabled_reason'):
                pass
            row['updated_ts'] = _now()
        except SteamSMMError as e:
            if e.status in (500, 502, 503, 504) or e.retryable:
                notes.append(f'LOT {lot_id}: API временно недоступен, состояние не менялось')
            elif e.code == 'PRODUCT_NOT_FOUND' and cfg.get('auto_deactivate_enabled', True):
                if _set_lot_active(cardinal, lot_id, False):
                    row['auto_disabled'] = True
                    row['auto_disabled_reason'] = 'product_not_found'
                    lot_notes.append(f'LOT {lot_id} выключен: товар исчез у провайдера')
            else:
                notes.append(f'LOT {lot_id}: {_safe_api_error_message(e)}')
        except Exception as e:
            notes.append(f'LOT {lot_id}: {_compact_error(e)}')

    previous_balance_state = str(cfg.get('last_notified_balance_state') or '')
    balance_state = 'low' if balance_blocked else 'ok'
    _provider_sync_save(owner_key, cfg, lots=lots, regular_balance=regular_balance,
             balance=_as_float(balance_data.get('balance'), regular_balance),
             promo_balance=_as_float(balance_data.get('promo_balance'), 0.0),
             last_api_ok=_now(), last_api_error='', api_was_down=False,
             last_notified_balance_state=balance_state)

    if notify:
        if stock_notes:
            _notify_admin('<b>📦 Остатки провайдера изменились</b>\n' + '\n'.join(f'• {_h(x)}' for x in stock_notes[:20]), cfg=cfg, kind='stock', owner_key=owner_key)
        if price_notes:
            _notify_admin('<b>💰 Цены провайдера / FunPay изменились</b>\n' + '\n'.join(f'• {_h(x)}' for x in price_notes[:20]), cfg=cfg, kind='price', owner_key=owner_key)
        if lot_notes:
            _notify_admin('<b>🎮 Состояние Rental LOT изменилось</b>\n' + '\n'.join(f'• {_h(x)}' for x in lot_notes[:20]), cfg=cfg, kind='lot', owner_key=owner_key)
        if previous_balance_state and previous_balance_state != balance_state:
            if balance_state == 'low':
                _notify_admin(f'<b>💳 Недостаточно баланса провайдера</b>\nОбычный баланс: <code>{regular_balance:.2f} ₽</code>\nЧасть LOT временно выключена.', cfg=cfg, kind='lot', owner_key=owner_key)
            else:
                _notify_admin(f'<b>💳 Баланс провайдера снова достаточен</b>\nОбычный баланс: <code>{regular_balance:.2f} ₽</code>\nДоступные LOT будут включены автоматически.', cfg=cfg, kind='lot', owner_key=owner_key)
    return {'changed': changed, 'notes': notes, 'stock_notes': stock_notes, 'price_notes': price_notes, 'lot_notes': lot_notes}


def _sync_all(cardinal, notify=False):
    owner, root = _owner_entry()
    result = {'changed': 0, 'notes': []}
    if not owner:
        return result
    for provider, name in PROVIDERS.items():
        cfg = _provider_cfg(root, provider)
        cfg['lots'] = [r for r in root.get('lots', []) if _provider_id(r) == provider]
        if not cfg.get('api_key'):
            continue
        try:
            data = _apply_lot_sync(cardinal, owner, cfg, notify=notify)
            result['changed'] += data.get('changed', 0)
            result['notes'].extend(f'{name}: {x}' for x in data.get('notes', []))
        except Exception as e:
            error = _safe_api_error_message(e)
            _provider_save(owner, provider, last_api_error=error, api_was_down=True)
            result['notes'].append(f'{name}: {error}')
            if notify:
                _notify_admin(f'⚠️ <b>{name}</b>: {_h(error)}', cfg=cfg, kind='api', owner_key=owner)
            if isinstance(e, SteamSMMError) and e.status == 401:
                for row in cfg['lots']:
                    if cfg.get('auto_deactivate_enabled', True) and _set_lot_active(cardinal, row['lot_id'], False):
                        row.update(auto_disabled=True, auto_disabled_reason='api_unauthorized')
                _provider_sync_save(owner, cfg, lots=cfg['lots'])
    return result


def _retry_pending(cardinal):
    now = _now()
    cfg = _owner_cfg()
    for rec in _rental_list(active_only=False):
        if rec.get('status') != 'retry' or int(rec.get('next_retry_ts') or 0) > now:
            continue
        lot = None
        for row in cfg.get('lots') or []:
            if int(row['lot_id']) == int(rec.get('lot_id') or 0):
                lot = row
                break
        if not lot:
            continue
        fake_event = None
        _schedule(f'retry-rent:{rec["order_id"]}', _process_rental_order, cardinal, fake_event, lot, cfg, rec['order_id'], rec.get('chat_id'))
    for ext in _extension_records().values():
        if ext.get('status') == 'retry' and int(ext.get('next_retry_ts') or 0) <= now and ext.get('purchase_order_id'):
            _schedule(
                f'retry-ext:{ext["lot_id"]}', _process_extension_order,
                cardinal, None, ext, ext['purchase_order_id'], ext.get('chat_id')
            )


def _retry_pending_credentials(cardinal):
    now = _now()
    for rec in _rental_list(active_only=False):
        if not rec.get('rental_id') or rec.get('credentials_delivered'):
            continue
        if str(rec.get('status') or '').lower() not in {'active', 'completed', 'creating'}:
            continue
        if _as_int(rec.get('credentials_next_retry_ts'), 0) > now:
            continue

        _schedule(f'credentials:{rec.get("order_id")}', _credentials_delivery_worker, cardinal, rec.get('order_id'))


def _cleanup_extensions(cardinal):
    now = _now()
    for ext in list(_extension_records().values()):
        status = str(ext.get('status') or '')
        expires_ts = int(ext.get('expires_ts') or 0)
        if status == 'active' and expires_ts > 0 and expires_ts <= now:
            _schedule(f'cleanup-ext:{ext["lot_id"]}', _cleanup_extension, cardinal, ext, True)
        elif status == 'cleanup_pending' and int(ext.get('next_cleanup_ts') or 0) <= now:
            _schedule(f'cleanup-ext:{ext["lot_id"]}', _cleanup_extension, cardinal, ext, False)


def _restore_rentals_after_restart(cardinal):
    total = 0
    active = 0
    contacts = 0
    logins = 0
    ended = 0
    recovered = 0
    for original in _rental_list(active_only=False):
        total += 1
        rec = dict(original or {})
        if not rec.get('order_id') or not rec.get('rental_id'):
            continue
        old_status = str(rec.get('status') or '').lower()
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id')))
        refreshed = _refresh_rental_current(cfg, rec)
        if not refreshed:
            current = _rental_get(rec.get('order_id')) or rec

            if str(current.get('status') or '').lower() in {'ended', 'expired', 'cancelled', 'canceled', 'rejected'}:
                ended += 1
            elif _record_locally_current(current):
                refreshed = current
            else:
                ended += 1
        if not refreshed:
            continue
        rec = refreshed
        active += 1
        if old_status in {'ended', 'expired', 'cancelled', 'canceled'} and str(rec.get('status') or '').lower() in {'active', 'running', 'rented', 'creating'}:
            recovered += 1
            logger.info('Заказ #%s · аренда восстановлена как АКТИВНАЯ по SteamSMM status', rec.get('order_id'))
        before_aliases = _record_chat_aliases(rec)
        before_buyer = str(rec.get('buyer_username') or '')
        rec = _repair_rental_contact(cardinal, rec) or rec
        if before_aliases != _record_chat_aliases(rec) or before_buyer != str(rec.get('buyer_username') or ''):
            contacts += 1
        cfg = _cfg_for_record(rec, cfg)
        if not str(rec.get('account_login') or '').strip():
            login = _ensure_record_login(cfg, rec)
            if login:
                logins += 1
        if not rec.get('credentials_delivered'):
            _schedule(f'credentials:{rec.get("order_id")}', _credentials_delivery_worker, cardinal, rec.get('order_id'))
    logger.info(
        'Аренды после перезапуска восстановлены · всего=%s · активных=%s · контактов=%s · логинов=%s · восстановлено=%s · завершено=%s',
        total, active, contacts, logins, recovered, ended
    )
    return {'total': total, 'active': active, 'contacts': contacts, 'logins': logins, 'recovered': recovered, 'ended': ended}


def _maintenance_worker(cardinal):
    global _LAST_AUTO_SYNC
    while not _MAINT_STOP.is_set():
        try:
            owner_key, cfg = _owner_entry()
            if owner_key and cfg.get('plugin_enabled', True) and _has_provider_keys(cfg):
                interval = int(cfg.get('check_interval_sec') or DEFAULT_CHECK_INTERVAL)
                if time.time() - _LAST_AUTO_SYNC >= interval:
                    try:
                        _sync_all(cardinal, notify=True)
                        _LAST_AUTO_SYNC = time.time()
                    except Exception as e:
                        logger.warning('Автосинхронизация: %s', e)
                _retry_pending(cardinal)
                _retry_pending_credentials(cardinal)
                _cleanup_extensions(cardinal)
                _scan_review_gifts(cardinal)
        except Exception as e:
            logger.exception('Maintenance error: %s', e)
        _MAINT_STOP.wait(20)


def _start_maintenance(cardinal):
    global _MAINT_THREAD_STARTED
    if _MAINT_THREAD_STARTED:
        return
    _MAINT_THREAD_STARTED = True
    threading.Thread(target=_maintenance_worker, args=(cardinal,), daemon=True, name='AUTO-RENTAL-MAINT').start()


def _home_text(chat_id):
    return (
        f'🧩 <b>Плагин:</b> {NAME}\n'
        f'📦 <b>Версия:</b> {VERSION}\n'
        f'👤 <b>Автор:</b> <a href="{CREATOR_URL}">{CREDITS}</a>\n\n'
        'Выберите раздел ниже.'
    )

def _home_kb(chat_id):
    kb = K()
    kb.row(B('⚙️ Настройки', callback_data=CB_SETTINGS), B('ℹ️ Информация', callback_data=CB_INFO))
    kb.row(B('⬆️ Обновить плагин', callback_data=CB_UPDATE), B('🗑 Удалить', callback_data=CB_DELETE_ASK))
    kb.add(B('🔙 К списку плагинов', callback_data=CB_PLUGINS_LIST))
    return kb

def _settings_text(chat_id):
    cfg = _get_cfg(chat_id)
    lots = cfg.get('lots') or []
    enabled_lots = sum(1 for row in lots if row.get('manual_enabled', True) and not row.get('auto_disabled'))
    api_state = ', '.join(name for pid, name in PROVIDERS.items() if _provider_cfg(cfg, pid).get('api_key')) or 'не настроены'
    balance = cfg.get('regular_balance')
    return (
        f'⚙️ <b>{NAME} · Панель настроек</b>\n\n'
        f'🧩 Плагин: <b>{"🟢 ВКЛ" if cfg.get("plugin_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'🔌 Провайдеры: <b>{api_state}</b>\n'
        f'{_balance_lines(cfg)}\n'
        f'🎮 Лоты: <b>{enabled_lots} активных / {len(lots)} всего</b>\n\n'
        '<i>Выберите раздел:</i>'
    )


def _settings_kb(chat_id):
    cfg = _get_cfg(chat_id)
    lot_count = len(cfg.get('lots') or [])
    token_mark = '✅' if cfg.get('api_key') else '❌'
    kb = K()
    kb.row(B('🔌 Провайдеры аренды', callback_data=CB_TOKEN))
    kb.row(B('⚙️ Настройки плагина', callback_data=CB_MINI_SETTINGS))
    kb.row(B(f'🎮 Настройка лотов · {lot_count}', callback_data=CB_LOTS))
    kb.row(B('📊 Статистика', callback_data=CB_STATS))
    kb.add(B('◀️ Назад', callback_data=CB_HOME))
    return kb


def _mini_settings_text(chat_id):
    cfg = _get_cfg(chat_id)
    active_rentals = sum(1 for row in _rental_list(True) if row.get('rental_id'))
    active_ext = sum(1 for row in _extension_records().values() if row.get('status') == 'active')
    return (
        f'⚙️ <b>{NAME} · Настройки плагина</b>\n\n'
        f'🧩 Состояние: <b>{"🟢 ВКЛ" if cfg.get("plugin_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'💹 Автоцена: <b>{"🟢 ВКЛ" if cfg.get("auto_price_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'📦 Автодеактивация: <b>{"🟢 ВКЛ" if cfg.get("auto_deactivate_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'🕒 Активные аренды: <b>{active_rentals}</b>\n'
        f'➕ Лоты продления: <b>{active_ext}</b>\n\n'
        '<i>Выберите категорию:</i>'
    )


def _mini_settings_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.row(B('🧩 Плагин: ' + ('🟢 ВКЛ' if cfg.get('plugin_enabled', True) else '🔴 ВЫКЛ'), callback_data=CB + ':toggle'))
    kb.row(B('💰 Автоматика', callback_data=CB_AUTO))
    kb.row(B('📦 Заказы', callback_data=CB_ORDERS))
    kb.row(B('🔔 Уведомления', callback_data=CB_NOTIFICATIONS))
    kb.row(B('🛠 Обслуживание', callback_data=CB_SERVICE))
    kb.add(B('◀️ Назад', callback_data=CB_SETTINGS))
    return kb


def _notifications_text(chat_id):
    cfg = _get_cfg(chat_id)
    return (
        f'<b>🔔 Уведомления {NAME}</b>\n\n'
        f'Общие: <b>{"🟢 ВКЛ" if cfg.get("notifications_enabled", True) else "🔴 ВЫКЛ"}</b>\n\n'
        '🛒 <b>Новые заказы</b> — сообщает о новом заказе FunPay.\n'
        '✅ <b>Аренда успешно</b> — аренда создана и аккаунт выдан покупателю.\n'
        '⚠️ <b>Ошибки аренды</b> — выдача или создание аренды завершились ошибкой.\n'
        '📦 <b>Остатки аккаунтов</b> — изменилось количество доступных аккаунтов.\n'
        '💰 <b>Изменение цен</b> — изменилась рассчитанная цена LOT.\n'
        '🔁 <b>Вкл/выкл LOT и баланс</b> — LOT автоматически включён/выключен или не хватает баланса.\n'
        '➕ <b>Продления</b> — создание, оплата или ошибка продления аренды.\n'
        '🔌 <b>API провайдеров</b> — провайдер недоступен, восстановился или вернул ошибку.'
    )


def _notifications_kb(chat_id):
    cfg = _get_cfg(chat_id)
    def st(key):
        return '🟢' if cfg.get(key, True) else '🔴'
    kb = K()
    kb.row(B(f'{st("notifications_enabled")} Все уведомления', callback_data=CB_NOTIFY_MASTER))
    kb.row(B(f'{st("notify_orders")} Новые заказы', callback_data=CB_NOTIFY_ORDER))
    kb.row(B(f'{st("notify_rentals")} Аренда успешно', callback_data=CB_NOTIFY_RENT))
    kb.row(B(f'{st("notify_errors")} Ошибки аренды', callback_data=CB_NOTIFY_ERROR))
    kb.row(B(f'{st("notify_stock")} Остатки аккаунтов', callback_data=CB_NOTIFY_STOCK))
    kb.row(B(f'{st("notify_price")} Изменение цен', callback_data=CB_NOTIFY_PRICE))
    kb.row(B(f'{st("notify_lot_state")} Вкл/выкл LOT и баланс', callback_data=CB_NOTIFY_LOT))
    kb.row(B(f'{st("notify_extensions")} Продления', callback_data=CB_NOTIFY_EXT))
    kb.row(B(f'{st("notify_api")} API провайдеров', callback_data=CB_NOTIFY_API))
    kb.add(B('◀️ Назад', callback_data=CB_MINI_SETTINGS))
    return kb


def _plugin_status_text(chat_id):
    cfg = _get_cfg(chat_id)
    lots = cfg.get('lots') or []
    auto_disabled = sum(1 for row in lots if row.get('auto_disabled'))
    return (
        '<b>🧩 Состояние Rental Steam Service</b>\n\n'
        f'🔌 Плагин: <b>{"🟢 ВКЛ" if cfg.get("plugin_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'🎮 Настроено лотов: <b>{len(lots)}</b>\n'
        f'🟠 Автоотключено: <b>{auto_disabled}</b>\n'
        f'🔌 Провайдеры: <b>{"✅ настроены" if _has_provider_keys(cfg) else "❌ не настроены"}</b>\n\n'
        '<i>При выключении новые заказы и фоновые действия Rental Steam Service не обрабатываются.</i>'
    )


def _plugin_status_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.row(B('🔌 Плагин: ' + ('ВКЛ' if cfg.get('plugin_enabled', True) else 'ВЫКЛ'), callback_data=CB + ':toggle'))
    kb.add(B('◀️ Назад', callback_data=CB_MINI_SETTINGS))
    return kb


def _stats_text(chat_id):
    cfg = _get_cfg(chat_id)
    rentals = _rental_list(False)
    active = [row for row in rentals if row.get('rental_id') and str(row.get('status') or '').lower() in {'active', 'created', 'pending_credentials'}]
    finished = [row for row in rentals if str(row.get('status') or '').lower() in {'ended', 'completed', 'finished', 'expired'}]
    pending = [row for row in rentals if str(row.get('status') or '').lower() in {'pending', 'retry', 'processing'}]
    ext_records = list(_extension_records().values())
    active_ext = sum(1 for row in ext_records if row.get('status') == 'active')
    purchased_ext = sum(1 for row in ext_records if row.get('status') in {'purchased', 'extended', 'completed'})
    balance = cfg.get('regular_balance')
    if balance is None:
        balance = cfg.get('balance')
    return (
        '<b>📊 Статистика Rental Steam Service</b>\n\n'
        f'• Лотов: <b>{len(cfg.get("lots") or [])}</b>\n'
        f'• Всего записей аренд: <b>{len(rentals)}</b>\n'
        f'• Активных аренд: <b>{len(active)}</b>\n'
        f'• Завершённых: <b>{len(finished)}</b>\n'
        f'• В ожидании / retry: <b>{len(pending)}</b>\n'
        f'• Активных лотов продления: <b>{active_ext}</b>\n'
        f'• Оплаченных продлений: <b>{purchased_ext}</b>\n\n'
        f'{_balance_lines(cfg)}'
    )

def _stats_kb():
    kb = K()
    kb.row(B('🔄 Обновить данные', callback_data=CB_STATS_REFRESH))
    kb.add(B('◀️ Назад', callback_data=CB_SETTINGS))
    return kb


def _sync_text(chat_id):
    return _service_text()


def _sync_kb():
    return _service_kb()


def _open_settings(bot, call):
    chat_id = call.message.chat.id
    _safe_edit(bot, chat_id, call.message.id, _settings_text(chat_id), _settings_kb(chat_id))
    try:
        bot.answer_callback_query(call.id)
    except Exception:
        pass


def _info_text():
    return (
        '<b>ℹ️ Информация</b>\n\n'
        f'<b>{NAME}</b>\n\n'
        'Инструкции, обновления и ссылки проекта находятся ниже.'
    )


def _info_kb():
    kb = K()
    kb.row(B('📖 Инструкция', url=INSTRUCTION_URL), B('📘 Инструкция GitHub', url=INSTRUCTION_GITHUB_URL))
    kb.row(B('⬇️ GitHub / обновления', url=REPOSITORY_URL))
    kb.row(B('💬 Чат', url=GROUP_URL), B('📢 Канал', url=CHANNEL_URL))
    kb.row(B('👤 Автор', url=CREATOR_URL))
    kb.add(B('◀️ Назад', callback_data=CB_HOME))
    return kb


def _update_text():
    return (
        f'⬆️ <b>Обновление {NAME}</b>\n\n'
        f'Текущая версия: <code>{VERSION}</code>\n\n'
        '• <b>Локальное обновление</b> — отправить новый <code>.py</code>-файл прямо в Telegram.\n'
        '• <b>GitHub / обновления</b> — официальный репозиторий со свежими версиями.\n\n'
        'Перед локальным обновлением текущий файл сохраняется в резервную копию. Настройки не удаляются.'
    )


def _update_kb():
    kb = K()
    kb.row(B('📥 Локальное обновление', callback_data=CB_UPDATE_LOCAL))
    kb.row(B('🌐 GitHub / обновления', url=REPOSITORY_URL))
    kb.row(B('📖 Инструкция', url=INSTRUCTION_URL))
    kb.add(B('◀️ Назад', callback_data=CB_HOME))
    return kb


def _plugin_version_from_source(source):
    match = re.search(r'(?m)^\s*VERSION\s*=\s*["\']([^"\']+)["\']', source or '')
    return match.group(1).strip() if match else None


def _validate_update_payload(payload):
    if not isinstance(payload, (bytes, bytearray)) or len(payload) < 5000:
        raise RuntimeError('файл обновления слишком маленький или не прочитан')
    if len(payload) > 5 * 1024 * 1024:
        raise RuntimeError('файл обновления слишком большой (>5 MB)')
    try:
        source = bytes(payload).decode('utf-8-sig')
    except UnicodeDecodeError as error:
        raise RuntimeError(f'файл должен быть в UTF-8: {error}') from error
    low = source[:500].lower()
    if '<html' in low or '<!doctype' in low:
        raise RuntimeError('получена HTML-страница вместо Python-файла')
    required = ('Rental Steam Service', 'def init_cardinal', 'BIND_TO_PRE_INIT', 'BIND_TO_NEW_ORDER')
    missing = [item for item in required if item not in source]
    if missing:
        raise RuntimeError('это не файл Rental Steam Service: нет ' + ', '.join(missing))
    if UUID not in source:
        raise RuntimeError('UUID загруженного плагина не совпадает')
    version = _plugin_version_from_source(source)
    if not version:
        raise RuntimeError('в файле не найдена VERSION')
    compile(source, os.path.abspath(__file__), 'exec')
    return source, version


def _install_local_update(payload, original_name='Rental_Steam_Service.py'):
    plugin_file = os.path.abspath(__file__)
    source, version = _validate_update_payload(payload)
    current = b''
    try:
        with open(plugin_file, 'rb') as file:
            current = file.read()
    except Exception:
        pass
    if current == bytes(payload):
        return {'ok': True, 'changed': False, 'version': version, 'backup': None}
    stamp = time.strftime('%Y%m%d-%H%M%S')
    backup = plugin_file + f'.pre-update.{stamp}.bak'
    temp = plugin_file + '.update.tmp'
    if os.path.isfile(SETTINGS_FILE):
        try:
            shutil.copy2(SETTINGS_FILE, SETTINGS_BAK)
        except Exception:
            pass
    with open(temp, 'wb') as file:
        file.write(bytes(payload))
        file.flush()
        os.fsync(file.fileno())
    try:
        os.chmod(temp, os.stat(plugin_file).st_mode)
    except Exception:
        pass
    shutil.copy2(plugin_file, backup)
    os.replace(temp, plugin_file)
    return {'ok': True, 'changed': True, 'version': version, 'backup': backup, 'source': original_name}


def _delete_confirm_text():
    return (
        f'⚠️ <b>Удаление плагина</b>\n\n'
        f'Вы точно хотите удалить <b>{NAME}</b>?\n\n'
        'Будут удалены:\n'
        '• файл плагина\n'
        '• настройки, база аренд, временные лоты и логи\n\n'
        '<b>Перед удалением плагин попытается выключить все настроенные FunPay-лоты.</b>\n'
        'После удаления потребуется <code>/restart</code>.'
    )


def _delete_confirm_kb():
    kb = K()
    kb.row(B('✅ Да, удалить', callback_data=CB_DELETE_YES), B('❌ Нет', callback_data=CB_DELETE_NO))
    return kb


def _self_delete_from_disk(cardinal, chat_id):
    errors = []
    try:
        cfg = _get_cfg(chat_id)
        for row in cfg.get('lots') or []:
            try:
                _set_lot_active(cardinal, int(row.get('lot_id') or 0), False)
            except Exception as error:
                errors.append(f'LOT {row.get("lot_id")}: {error}')
    except Exception as error:
        errors.append(f'Не удалось выключить лоты: {error}')
    try:
        shutil.rmtree(PLUGIN_FOLDER, ignore_errors=True)
    except Exception as error:
        errors.append(f'Не удалось удалить папку данных: {error}')
    plugin_file = os.path.abspath(__file__)
    try:
        pycache = os.path.join(os.path.dirname(plugin_file), '__pycache__')
        if os.path.isdir(pycache):
            base = os.path.splitext(os.path.basename(plugin_file))[0]
            for filename in os.listdir(pycache):
                if filename.startswith(base) and filename.endswith('.pyc'):
                    try:
                        os.remove(os.path.join(pycache, filename))
                    except Exception:
                        pass
        os.remove(plugin_file)
    except Exception as error:
        errors.append(f'Не удалось удалить файл плагина: {error}')
    return not errors, errors

def _open_home(bot, call):
    chat_id = call.message.chat.id
    _safe_edit(bot, chat_id, call.message.id, _home_text(chat_id), _home_kb(chat_id))
    try:
        bot.answer_callback_query(call.id)
    except Exception:
        pass


def _token_text(chat_id):
    return _providers_text(chat_id)

def _token_kb():
    return _providers_kb()


def _lots_page(chat_id, rows):
    per_page = 8
    pages = max(1, math.ceil(len(rows) / per_page))
    page = max(0, min(_as_int(_LOT_LIST_PAGE.get(str(chat_id)), 0, 0), pages - 1))
    _LOT_LIST_PAGE[str(chat_id)] = page
    return page, pages, per_page


def _lots_text(chat_id):
    cfg = _get_cfg(chat_id)
    rows = cfg.get('lots') or []
    active = sum(1 for row in rows if row.get('manual_enabled', True) and not row.get('auto_disabled'))
    off = len(rows) - active
    page, pages, _ = _lots_page(chat_id, rows)
    return (
        f'⭐ <b>Настройка лотов {NAME}</b>\n\n'
        f'• Всего лотов: <b>{len(rows)} шт.</b>\n'
        f'• Активных: 🟢 <b>{active}</b> | Выключенных: 🔴 <b>{off}</b>\n'
        f'• Общая наценка: <b>{_as_float(cfg.get("global_markup_percent"), 20.0):g}%</b>\n'
        f'• Страница: <b>{page + 1}/{pages}</b>'
    )


def _lots_kb(chat_id):
    cfg = _get_cfg(chat_id)
    rows = cfg.get('lots') or []
    page, pages, per_page = _lots_page(chat_id, rows)
    kb = K()
    kb.row(B('🔄 Проверить все', callback_data=CB_LOT_REFRESH), B('➕ Добавить вручную', callback_data=CB_LOT_ADD))
    kb.row(B('⚙️ Общее', callback_data=CB_LOTS_GENERAL))
    for row in rows[page * per_page:(page + 1) * per_page]:
        if not row.get('manual_enabled', True):
            icon = '🔴'
        elif row.get('auto_disabled'):
            icon = '🟠'
        else:
            icon = '🟢'
        title = str(row.get('product_name') or f'Product {row.get("product_id")}')
        duration = _format_duration(row.get('duration_hours') or 0)
        stock = row.get('last_stock')
        stock_text = str(stock) if isinstance(stock, int) and stock >= 0 else '—'
        label = f'{icon} {PROVIDERS.get(_provider_id(row), _provider_id(row))} #{row["lot_id"]} · {title[:20]} · в наличии {stock_text}'
        kb.row(B(label, callback_data=CB_LOT_OPEN + str(row['lot_id'])))
    if pages > 1:
        nav = []
        if page > 0:
            nav.append(B('◀️ Пред.', callback_data=CB_LOTS_PAGE + str(page - 1)))
        nav.append(B(f'Стр {page + 1}/{pages}', callback_data=CB_LOTS_PAGE + str(page)))
        if page + 1 < pages:
            nav.append(B('След. ▶️', callback_data=CB_LOTS_PAGE + str(page + 1)))
        kb.row(*nav)
    kb.add(B('◀️ Назад', callback_data=CB_SETTINGS))
    return kb


def _lots_general_text(chat_id):
    cfg = _get_cfg(chat_id)
    rows = cfg.get('lots') or []
    enabled = sum(1 for row in rows if row.get('manual_enabled', True) and not row.get('auto_disabled'))
    return (
        '<b>⚙️ Общее · Лоты</b>\n\n'
        f'🎮 Лоты: <b>{enabled}/{len(rows)} включено</b>\n'
        f'💹 Общая наценка: <b>{_as_float(cfg.get("global_markup_percent"), 20.0):g}%</b>\n'
        f'💰 Автоцена: <b>{"🟢 ВКЛ" if cfg.get("auto_price_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'📦 Автодеактивация: <b>{"🟢 ВКЛ" if cfg.get("auto_deactivate_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'💳 Мин. баланс: <code>{cfg.get("min_balance_rub", 0)} ₽</code>\n'
        f'⏱ Проверка: <code>каждые {math.ceil(cfg.get("check_interval_sec", 300) / 60)} мин.</code>'
    )


def _lots_general_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.row(B('🟢 Включить все', callback_data=CB_LOTS_ALL_ON), B('🔴 Выключить все', callback_data=CB_LOTS_ALL_OFF))
    kb.row(B(f'💹 Общая наценка · {_as_float(cfg.get("global_markup_percent"), 20.0):g}%', callback_data=CB_LOTS_GENERAL_MARKUP))
    kb.row(B('💰 Автоцена: ' + ('🟢 ВКЛ' if cfg.get('auto_price_enabled', True) else '🔴 ВЫКЛ'), callback_data=CB_LOTS_GENERAL_PRICE))
    kb.row(B('📦 Автодеактивация: ' + ('🟢 ВКЛ' if cfg.get('auto_deactivate_enabled', True) else '🔴 ВЫКЛ'), callback_data=CB_LOTS_GENERAL_DEACT))
    kb.row(B('💳 Мин. баланс', callback_data=CB_LOTS_GENERAL_RESERVE), B('⏱ Интервал', callback_data=CB_LOTS_GENERAL_INTERVAL))
    kb.row(B('🔄 Проверить сейчас', callback_data=CB_LOTS_GENERAL_CHECK))
    kb.add(B('◀️ Назад', callback_data=CB_LOTS))
    return kb


def _product_picker_rows(chat_id):
    cfg = _wizard_cfg(chat_id)
    products = sorted(_normalize_products(_api_products(cfg)), key=lambda x: (str(x.get('title') or '').lower(), int(x.get('product_id') or 0)))
    return [row for row in products if bool(row.get('stock_known', True)) and int(row.get('stock') or 0) > 0]


def _product_picker_text(chat_id, page=0):
    try:
        rows = _product_picker_rows(chat_id)
    except Exception as error:
        return f'🎮 <b>Выбор товара провайдера</b>\n\n❌ {_h(_safe_api_error_message(error))}'
    per_page = 7
    pages = max(1, math.ceil(len(rows) / per_page))
    page = max(0, min(int(page or 0), pages - 1))
    chunk = rows[page * per_page:(page + 1) * per_page]
    lines = ['🎮 <b>Выберите товар провайдера</b>', '', 'Показываются только товары, у которых сейчас есть свободные аккаунты.', '']
    for row in chunk:
        price = row.get('hourly_price')
        price_text = f'{price:g} ₽/ч' if isinstance(price, (int, float)) else '— ₽/ч'
        lines.append(f'<code>{row["product_id"]}</code> · <b>{_h(row.get("title"))}</b> · {row.get("stock")} шт. · {price_text}')
    lines += ['', f'Страница <b>{page + 1}/{pages}</b>']
    return '\n'.join(lines)


def _product_picker_kb(chat_id, page=0):
    rows = _product_picker_rows(chat_id)
    per_page = 7
    pages = max(1, math.ceil(len(rows) / per_page))
    page = max(0, min(int(page or 0), pages - 1))
    kb = K()
    for row in rows[page * per_page:(page + 1) * per_page]:
        label = f'🟢 {row["product_id"]} · {str(row.get("title") or "")[:25]} · {row.get("stock")} шт.'
        kb.row(B(label, callback_data=CB_ADD_PRODUCT_PICK + str(row['product_id'])))
    if pages > 1:
        nav=[]
        if page > 0:
            nav.append(B('◀️', callback_data=CB_ADD_PRODUCT_PAGE + str(page - 1)))
        if page + 1 < pages:
            nav.append(B('▶️', callback_data=CB_ADD_PRODUCT_PAGE + str(page + 1)))
        if nav:
            kb.row(*nav)
    kb.add(B('◀️ Назад', callback_data=CB_CANCEL))
    return kb


def _show_product_picker(bot, chat_id, state, page=0):
    state = dict(state or {})
    state['step'] = 'add_product_id'
    state['product_page'] = int(page or 0)
    _fsm_set(chat_id, state)
    message_id = state.get('prompt_msg_id')
    text = _product_picker_text(chat_id, page)
    kb = _product_picker_kb(chat_id, page)
    if message_id:
        try:
            bot.edit_message_text(text, chat_id, message_id, parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
            return
        except Exception:
            pass
    prompt = bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
    state['prompt_msg_id'] = getattr(prompt, 'message_id', getattr(prompt, 'id', None))
    _fsm_set(chat_id, state)


def _products_text(chat_id, page=0):
    cfg = _get_cfg(chat_id)
    if not cfg.get('api_key'):
        return '<b>📋 ID товаров SteamSMM</b>\n\nСначала подключите API-ключ SteamSMM.'
    try:
        rows = sorted(_normalize_products(_api_products(cfg)), key=lambda x: (str(x.get('title') or '').lower(), int(x.get('product_id') or 0)))
    except Exception as error:
        return f'<b>📋 ID товаров SteamSMM</b>\n\n❌ {_h(_safe_api_error_message(error))}'
    per_page = 12
    pages = max(1, math.ceil(len(rows) / per_page))
    page = max(0, min(int(page or 0), pages - 1))
    chunk = rows[page * per_page:(page + 1) * per_page]
    lines = [
        '<b>📋 ID товаров SteamSMM</b>', '',
        'Это актуальный каталог из <code>GET /api/rentals/products</code>.',
        'Для добавления LOT нужен <b>Product ID</b>. Товары с 0 свободных аккаунтов добавить нельзя.', ''
    ]
    for row in chunk:
        stock = int(row.get('stock', -1))
        known = bool(row.get('stock_known', stock >= 0))
        icon = '🟢' if stock > 0 else ('⏳' if known else '❔')
        price = row.get('hourly_price')
        price_text = f'{price:g} ₽/ч' if isinstance(price, (int, float)) else 'цена —'
        lines.append(
            f'{icon} <code>{row["product_id"]}</code> — <b>{_h(row.get("title"))}</b>\n'
            f'   свободно: <code>{stock if known else "?"}</code> · {price_text}'
        )
    lines += ['', f'Страница <b>{page + 1}/{pages}</b> · товаров: <b>{len(rows)}</b>']
    return '\n'.join(lines)


def _products_kb(page=0, pages=1):
    kb = K()
    nav = []
    if page > 0:
        nav.append(B('◀️', callback_data=CB_PRODUCTS_PAGE + str(page - 1)))
    if page + 1 < pages:
        nav.append(B('▶️', callback_data=CB_PRODUCTS_PAGE + str(page + 1)))
    if nav:
        kb.row(*nav)
    kb.add(B('ℹ️ Как узнать ID', callback_data=CB_PRODUCT_HELP))
    kb.add(B('◀️ Назад', callback_data=CB_LOTS))
    return kb


def _products_pages(chat_id):
    cfg = _get_cfg(chat_id)
    try:
        total = len(_normalize_products(_api_products(cfg))) if cfg.get('api_key') else 0
    except Exception:
        total = 0
    return max(1, math.ceil(total / 12))


def _product_help_text():
    return (
        '<b>ℹ️ Как узнать Product ID</b>\n\n'
        'На странице <code>steamsmm.ru/steam-rentals</code> карточка показывает название, цену и наличие, '
        'но Product ID в обычном интерфейсе не подписан.\n\n'
        '<b>Проще всего:</b> нажмите «📋 ID товаров» в этом плагине — он получает официальный каталог SteamSMM '
        'и показывает ID рядом с каждой игрой.\n\n'
        '<b>Через браузер:</b> откройте страницу аренды → <code>F12</code> → <b>Network</b> → обновите страницу → '
        'найдите запрос каталога аренды (обычно с <code>rentals/products</code>) → в Response найдите название игры и поле '
        '<code>product_id</code>/<code>id</code>.\n\n'
        'Официальная API-документация определяет <code>product_id</code> как ID игры из каталога аренды.'
    )


def _product_help_kb():
    kb = K()
    kb.row(B('🌐 SteamSMM аренда', url='https://steamsmm.ru/steam-rentals'))
    kb.row(B('📚 API документация', url=STEAMSMM_DOCS_URL))
    kb.add(B('◀️ Назад', callback_data=CB_LOTS))
    return kb


def _lot_finance_snapshot(cfg, row):
    api_cost = _as_float(row.get('last_api_cost'), 0.0)
    seller = _as_float(row.get('last_funpay_price'), 0.0)
    buyer = _buyer_price_estimate(cfg, seller or 0.01)
    profit = round(float(seller or 0.0) - float(api_cost or 0.0), 2)
    return {
        'api_cost': api_cost,
        'seller': seller,
        'buyer_card': buyer['card'],
        'buyer_sbp': buyer['sbp'],
        'profit': profit,
    }


def _lot_detail_text(chat_id, lot_id):
    cfg = _get_cfg(chat_id)
    row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == int(lot_id)), None)
    if not row:
        return '<b>Лот не найден.</b>'
    money = _lot_finance_snapshot(cfg, row)
    override = row.get('markup_override_percent')
    markup = _effective_markup(cfg, row)
    markup_text = f'своя {markup:g}%' if override is not None else f'общая {markup:g}%'
    if not row.get('manual_enabled', True):
        state = '🔴 ВЫКЛ'
    elif row.get('auto_disabled'):
        state = '🟠 АВТО-ВЫКЛ'
    else:
        state = '🟢 ВКЛ'
    stock = row.get('last_stock')
    reason = row.get('auto_disabled_reason') or ''
    reason_line = f'\n⚠️ {_h(reason)}' if reason else ''
    profit_sign = '+' if money['profit'] >= 0 else ''
    return (
        f'🎮 <b>{_h(row.get("product_name"))}</b> · LOT <code>{row["lot_id"]}</code>\n\n'
        f'{state} · ⏱ {_format_duration(row["duration_hours"])}\n'
        f'📦 В наличии: <b>{stock if isinstance(stock, int) and stock >= 0 else "—"}</b> · обновление каждые {math.ceil(cfg.get("check_interval_sec", DEFAULT_CHECK_INTERVAL) / 60)} мин.\n'
        f'💹 {markup_text}\n\n'
        f'💰 {_h(PROVIDERS.get(_provider_id(row), _provider_id(row)))} <code>{money["api_cost"]:.2f} ₽</code> → FunPay <code>{money["seller"]:.2f} ₽</code>\n'
        f'🛒 Покупателю ≈ <code>{money["buyer_card"]:.2f} ₽ карта / {money["buyer_sbp"]:.2f} ₽ СБП</code>\n'
        f'📈 Прибыль: <b>{profit_sign}{money["profit"]:.2f} ₽</b>'
        f'{reason_line}'
    )


def _lot_detail_kb(chat_id, lot_id):
    cfg = _get_cfg(chat_id)
    row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == int(lot_id)), None) or {}
    lid = str(lot_id)
    markup = _effective_markup(cfg, row) if row else 0
    own = row.get('markup_override_percent') is not None
    lot_state = '🟢 ВКЛ' if row.get('manual_enabled', True) else '🔴 ВЫКЛ'
    kb = K()
    kb.row(B('🔌 Провайдер: ' + PROVIDERS.get(_provider_id(row), _provider_id(row)), callback_data=CB + ':rebind:' + lid))
    kb.row(B(f'🎮 Лот: {lot_state}', callback_data=CB_LOT_TOGGLE + lid))
    kb.row(B(f'💹 Наценка: {"своя" if own else "общая"} · {markup:g}%', callback_data=CB_LOT_MARKUP + lid))
    kb.row(B('💰 Автоцена: ' + ('🟢 ВКЛ' if row.get('auto_price', True) else '🔴 ВЫКЛ'), callback_data=CB_LOT_AP + lid))
    kb.row(B('📦 По остатку: ' + ('🟢 ВКЛ' if row.get('auto_stock', True) else '🔴 ВЫКЛ'), callback_data=CB_LOT_AS + lid))
    kb.row(B('💳 По балансу: ' + ('🟢 ВКЛ' if row.get('auto_balance', True) else '🔴 ВЫКЛ'), callback_data=CB_LOT_AB + lid))
    kb.row(B('🗑 Удалить из плагина', callback_data=CB_LOT_DEL + lid))
    kb.add(B('◀️ Назад', callback_data=CB_LOTS))
    return kb


def _lot_markup_text(chat_id, lot_id, notice=''):
    cfg = _get_cfg(chat_id)
    row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == int(lot_id)), None)
    if not row:
        return '<b>Лот не найден.</b>'
    global_markup = _as_float(cfg.get('global_markup_percent'), 20.0)
    override = row.get('markup_override_percent')
    effective = _effective_markup(cfg, row)
    api_cost = _as_float(row.get('last_api_cost'), 0.0)
    target_seller = _seller_price(api_cost, effective)
    buyer = _buyer_price_estimate(cfg, target_seller)
    profit = round(target_seller - api_cost, 2)
    profit_sign = '+' if profit >= 0 else ''
    mode = 'Своя' if override is not None else 'Общая'
    own_text = f'{float(override):g}%' if override is not None else 'не задана'
    notice_text = f'{notice}\n\n' if notice else ''
    return (
        f'💹 <b>Наценка · LOT {lot_id}</b>\n\n'
        f'{notice_text}'
        f'• Режим: <b>{mode}</b>\n'
        f'• Общая наценка: <code>{global_markup:g}%</code>\n'
        f'• Своя наценка: <code>{own_text}</code>\n'
        f'• Сейчас применяется: <b>{effective:g}%</b>\n\n'
        f'<b>💰 Расчёт по выбранной наценке</b>\n'
        f'• {_h(PROVIDERS.get(_provider_id(row), _provider_id(row)))}: <code>{api_cost:.2f} ₽</code>\n'
        f'• Цена продавца: <code>{target_seller:.2f} ₽</code>\n'
        f'• Покупателю: <code>≈{buyer["card"]:.2f} ₽ карта / {buyer["sbp"]:.2f} ₽ СБП</code>\n'
        f'• Прибыль: <b>{profit_sign}{profit:.2f} ₽</b>\n\n'
        '<i>Выберите общую наценку или установите свою только для этого LOT.</i>'
    )


def _lot_markup_kb(chat_id, lot_id):
    cfg = _get_cfg(chat_id)
    row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == int(lot_id)), None) or {}
    global_markup = _as_float(cfg.get('global_markup_percent'), 20.0)
    override = row.get('markup_override_percent')
    lid = str(lot_id)
    kb = K()
    kb.row(B(f'🌐 Использовать общую · {global_markup:g}%', callback_data=CB_LOT_MARKUP_GLOBAL + lid))
    if override is None:
        kb.row(B('✏️ Задать свою наценку', callback_data=CB_LOT_MARKUP_CUSTOM + lid))
    else:
        kb.row(B(f'✏️ Своя наценка · {float(override):g}%', callback_data=CB_LOT_MARKUP_CUSTOM + lid))
    kb.add(B('◀️ Назад', callback_data=CB_LOT_OPEN + lid))
    return kb


def _auto_text(chat_id):
    cfg = _get_cfg(chat_id)
    return (
        '<b>💰 Автоматика</b>\n\n'
        f'💹 Общая наценка: <b>{_as_float(cfg.get("global_markup_percent"), 20.0):g}%</b>\n'
        f'💰 Автоцена: <b>{"🟢 ВКЛ" if cfg.get("auto_price_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'📦 Автодеактивация: <b>{"🟢 ВКЛ" if cfg.get("auto_deactivate_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'💳 Мин. баланс: <code>{cfg.get("min_balance_rub", 0)} ₽</code>\n'
        f'⏱ Проверка: <code>каждые {math.ceil(cfg.get("check_interval_sec", 300)/60)} мин.</code>'
    )


def _auto_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.row(B(f'💹 Общая наценка · {_as_float(cfg.get("global_markup_percent"), 20.0):g}%', callback_data=CB_GLOBAL_MARKUP))
    kb.row(B('💰 Автоцена: ' + ('🟢 ВКЛ' if cfg.get('auto_price_enabled', True) else '🔴 ВЫКЛ'), callback_data=CB_AUTO_TOGGLE_PRICE))
    kb.row(B('📦 Автодеактивация: ' + ('🟢 ВКЛ' if cfg.get('auto_deactivate_enabled', True) else '🔴 ВЫКЛ'), callback_data=CB_AUTO_TOGGLE_DEACT))
    kb.row(B('💳 Мин. баланс', callback_data=CB_AUTO_RESERVE), B('⏱ Интервал', callback_data=CB_AUTO_INTERVAL))
    kb.row(B('🔄 Проверить сейчас', callback_data=CB_AUTO_CHECK))
    kb.add(B('◀️ Назад', callback_data=CB_MINI_SETTINGS))
    return kb

def _rentals_text():
    rows = [r for r in _rental_list(False) if _record_locally_current(r)]
    lines = ['<b>🕒 Активные аренды</b>', '']
    if not rows:
        lines.append('Активных аренд пока нет.')
    for rec in rows[:30]:
        lines.append(
            f"• <code>#{_h(rec.get('order_id'))}</code> — <b>{_h(rec.get('product_name') or rec.get('product_id'))}</b>\n"
            f"  Rental: <code>{rec.get('rental_id')}</code>; до: <code>{_h(_fmt_dt(rec.get('ends_at')))}</code>"
        )
    return '\n'.join(lines)


def _rentals_kb():
    kb = K()
    for rec in [r for r in _rental_list(False) if _record_locally_current(r)][:30]:
        kb.add(B(f"#{str(rec.get('order_id'))[:10]} · {str(rec.get('product_name') or '')[:22]}", callback_data=CB_RENT_OPEN + str(rec['order_id'])[:30]))
    kb.add(B('◀️ Назад', callback_data=CB_ORDERS))
    return kb


def _rental_detail_text(order_id):
    rec = _rental_get(order_id)
    if not rec:
        return '<b>Аренда не найдена.</b>'
    return (
        f'🎮 <b>{_h(rec.get("product_name") or rec.get("product_id"))}</b>\n\n'
        f'🧾 FunPay: <code>#{_h(rec.get("order_id"))}</code>\n'
        f'🎫 LOT: <code>{rec.get("lot_id")}</code>\n'
        f'🔗 Rental ID: <code>{rec.get("rental_id")}</code>\n'
        f'📌 Статус: <b>{_h(rec.get("status"))}</b>\n\n'
        f'⏱ Срок: <b>{_format_duration(rec.get("duration_hours") or 0)}</b>\n'
        f'▶️ Начало: <code>{_h(_fmt_dt(rec.get("starts_at")))}</code>\n'
        f'⏹ Окончание: <code>{_h(_fmt_dt(rec.get("ends_at")))}</code>\n'
        f'⌛ Осталось: <b>{_h(_remaining(rec.get("ends_at")))}</b>'
    )


def _rental_detail_kb(order_id):
    oid = str(order_id)[:30]
    kb = K()
    kb.row(B('🔄 Статус', callback_data=CB_RENT_STATUS + oid), B('🔑 Данные', callback_data=CB_RENT_CREDS + oid))
    kb.row(B('🛡 Guard', callback_data=CB_RENT_GUARD + oid))
    kb.row(B('+1 час', callback_data=CB_RENT_EXT1 + oid), B('+1 день', callback_data=CB_RENT_EXT24 + oid), B('+1 неделя', callback_data=CB_RENT_EXT168 + oid))
    kb.add(B('◀️ Назад', callback_data=CB_RENTALS))
    return kb


def _extensions_text(chat_id):
    cfg = _get_cfg(chat_id)
    active = sum(1 for x in _extension_records().values() if x.get('status') == 'active')
    return (
        '<b>➕ Продление</b>\n\n'
        f'Статус: <b>{"🟢 ВКЛ" if cfg.get("extension_enabled", True) else "🔴 ВЫКЛ"}</b>\n'
        f'🧾 Активных лотов: <b>{active}</b>\n\n'
        'Персональный лот создаётся максимум на <b>20 минут</b>.'
    )


def _extensions_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.row(B('➕ Продление: ' + ('ВКЛ' if cfg.get('extension_enabled', True) else 'ВЫКЛ'), callback_data=CB_EXT_TOGGLE))
    kb.add(B('◀️ Назад', callback_data=CB_ORDERS))
    return kb


def _commands_text(chat_id):
    return (
        '<b>⌨️ Команды покупателя</b>\n\n'
        '🛡 Steam Guard\n'
        '<code>!код_ЛОГИН</code>\n\n'
        '⏱ Проверить срок\n'
        '<code>!срок_ЛОГИН</code>\n\n'
        '➕ Продлить аренду\n'
        '<code>!продлить_ЗАКАЗ</code> или <code>!продлить_ЛОГИН</code>\n\n'
        '<i>Команды работают только для актуальной аренды конкретного покупателя.</i>'
    )


def _commands_kb():
    return _orders_kb()

def _messages_text(chat_id):
    return ('💬 <b>Сообщения покупателю</b>\n\n'
            'Выберите сообщение, которое хотите поменять:')


def _messages_kb(chat_id):
    kb = K()
    for key in _get_cfg(chat_id)['templates']:
        label = MESSAGE_INFO.get(key, (key, ''))[0]
        kb.add(B(label, callback_data=CB_MSG_EDIT + key))
    kb.add(B('◀️ Назад', callback_data=CB_ORDERS))
    return kb


CB_ORDERS = CB + ':orders'
CB_SERVICE = CB + ':service'
CB_LOG_DOWNLOAD = CB + ':logs_download'
CB_CONFIG = CB + ':config'
CB_CONFIG_DOWNLOAD = CB + ':config_download'
CB_CONFIG_UPLOAD = CB + ':config_upload'
CB_GIFT = CB + ':review_gift'
CB_GIFT_TOGGLE = CB + ':gift_toggle'
CB_GIFT_HOURS = CB + ':gift_hours'
CB_GIFT_STARS = CB + ':gift_stars'
_GIFT_LOCK = threading.RLock()
_GIFT_SCAN_TS = 0
GIFTS_FILE = os.path.join(PLUGIN_FOLDER, 'review_gifts.json')

MESSAGE_INFO = {
    'rent_success': ('✅ После выдачи аккаунта', 'Отправляется после успешной аренды и получения логина с паролем.'),
    'rent_failed': ('⚠️ Не удалось выдать аренду', 'Когда покупка аренды у провайдера завершилась ошибкой.'),
    'credentials': ('🔑 Повторная выдача данных', 'Ответ на команду !данные_ЗАКАЗ.'),
    'credentials_pending': ('⏳ Данные аккаунта ещё готовятся', 'Аренда создана, но данные входа ещё не готовы.'),
    'credentials_failed': ('⚠️ Не удалось получить данные', 'Ошибка при повторном запросе логина и пароля.'),
    'guard': ('🛡 Получен код Steam Guard', 'Ответ с кодом на команду !код_ЛОГИН.'),
    'guard_wait': ('⏳ Steam Guard: слишком частый запрос', 'Покупатель повторно запросил код до окончания паузы.'),
    'guard_failed': ('⚠️ Steam Guard: код не получен', 'Код временно не удалось получить.'),
    'status': ('⏱ Показать оставшийся срок', 'Успешный ответ на команду !срок_ЗАКАЗ или !срок_ЛОГИН.'),
    'status_failed': ('⚠️ Не удалось проверить срок', 'Срок временно не удалось проверить.'),
    'extend_choose': ('➕ Выбор срока продления', 'Покупатель отправил !продлить без указания числа часов.'),
    'extend_offer': ('💳 Ссылка на оплату продления', 'После создания персонального лота на продление.'),
    'extend_success': ('✅ Продление выполнено', 'Покупатель оплатил продление, провайдер увеличил срок.'),
    'extend_failed': ('⚠️ Оплаченное продление не выполнено', 'Ошибка при обработке оплаченного лота продления.'),
    'extension_disabled': ('⛔ Продления выключены', 'Покупатель запросил продление, но продавец отключил его.'),
    'extend_usage': ('✍️ Как написать команду продления', 'Команда !продлить отправлена без логина или номера заказа.'),
    'extension_existing': ('🔗 Ссылка на уже созданное продление', 'Для этой аренды уже есть действующий лот продления.'),
    'extension_create_failed': ('⚠️ Не удалось создать лот продления', 'Ошибка создания ссылки на оплату продления.'),
    'extension_expired': ('⌛ Ссылка на продление истекла', 'Время оплаты персонального лота закончилось, лот удалён.'),
    'no_active_rental': ('🔍 Аренда покупателя не найдена', 'У этого покупателя нет подходящей актуальной аренды.'),
    'rental_expired': ('⌛ Срок аренды закончился', 'Покупатель обращается к завершённой аренде.'),
    'bad_guard_command': ('✍️ Подсказка для !код', 'Команда получения Steam Guard написана без логина.'),
    'bad_status_command': ('✍️ Подсказка для !срок', 'Команда проверки срока написана без номера заказа или логина.'),
    'bad_credentials_command': ('✍️ Подсказка для !данные', 'Команда получения данных написана без номера заказа.'),
    'review_gift_offer': ('🎁 Подарок за отзыв', 'Добавляется к первой выдаче, если функция включена.'),
    'review_gift_success': ('🎁 Подарок за отзыв выдан', 'После подтверждения отзыва и бесплатного продления аренды.'),
}


def _balance_lines(cfg):
    lines = []
    for pid, name in PROVIDERS.items():
        entry = cfg if pid == 'steamsmm' else cfg.get('providers', {}).get(pid, {})
        if not _provider_cfg(cfg, pid).get('api_key'):
            value = 'не подключён'
        else:
            amount = entry.get('regular_balance')
            if amount is None:
                amount = entry.get('balance')
            value = f'{float(amount):.2f} ₽' if amount is not None else 'ещё не проверен'
            if entry.get('last_api_error'):
                value += ' · ошибка обновления'
        lines.append(f'💳 <b>{name}:</b> {_h(value)}')
    return '\n'.join(lines)


def _orders_text(chat_id):
    return ('📦 <b>Заказы</b>\n\n'
            '🕒 <b>Аренды</b> — аккаунты, сроки, Steam Guard и данные выданных заказов.\n'
            '➕ <b>Продление</b> — включение платного продления аренды.\n'
            '💬 <b>Сообщения</b> — тексты для покупателя с описанием каждого случая.\n'
            '🎁 <b>Подарок за отзыв</b> — бесплатные часы к действующей аренде.')


def _orders_kb():
    kb = K()
    for label, cb in [('🕒 Аренды', CB_RENTALS), ('➕ Продление', CB_EXT),
                      ('💬 Сообщения', CB_MESSAGES), ('🎁 Подарок за отзыв', CB_GIFT)]:
        kb.add(B(label, callback_data=cb))
    kb.add(B('◀️ Назад', callback_data=CB_MINI_SETTINGS))
    return kb


def _service_text():
    return ('🛠 <b>Обслуживание</b>\n\n'
            '📄 <b>Скачать логи</b> — журнал работы плагина для диагностики.\n'
            '⚙️ <b>Конфигурация</b> — скачать настройки или загрузить JSON-файл.')


def _service_kb():
    kb = K()
    kb.add(B('📄 Скачать логи', callback_data=CB_LOG_DOWNLOAD))
    kb.add(B('⚙️ Конфигурация', callback_data=CB_CONFIG))
    kb.add(B('◀️ Назад', callback_data=CB_MINI_SETTINGS))
    return kb


def _config_text():
    return ('⚙️ <b>Конфигурация</b>\n\n'
            'Файл содержит настройки, лоты, шаблоны сообщений и API-ключи провайдеров. '
            'Храните его у себя.\n\nПри загрузке заменяются настройки этого профиля. '
            'История аренд и выданных подарков сохраняется. Перед заменой создаётся резервная копия.')


def _config_kb():
    kb = K()
    kb.row(B('📥 Скачать конфиг', callback_data=CB_CONFIG_DOWNLOAD))
    kb.row(B('📤 Загрузить конфиг', callback_data=CB_CONFIG_UPLOAD))
    kb.add(B('◀️ Назад', callback_data=CB_SERVICE))
    return kb


def _gift_text(chat_id):
    cfg = _get_cfg(chat_id)
    stars = int(cfg.get('review_gift_min_stars') or 5)
    return ('🎁 <b>Подарок за отзыв</b>\n\n'
            f'Состояние: <b>{"🟢 ВКЛ" if cfg.get("review_gift_enabled") else "🔴 ВЫКЛ"}</b>\n'
            f'Условие: <b>от {stars}★</b>\n'
            f'Подарок: <b>+{_format_duration(cfg.get("review_gift_hours", 1))}</b>\n\n'
            'Подарок выдаётся один раз, только пока аренда ещё активна.')


def _gift_kb(chat_id):
    cfg = _get_cfg(chat_id)
    kb = K()
    kb.add(B('🎁 Подарок: ' + ('🟢 ВКЛ' if cfg.get('review_gift_enabled') else '🔴 ВЫКЛ'), callback_data=CB_GIFT_TOGGLE))
    kb.add(B('⭐ Минимум: ' + str(cfg.get('review_gift_min_stars', 5)) + '★', callback_data=CB_GIFT_STARS))
    kb.add(B('⏱ Подарок: +' + str(cfg.get('review_gift_hours', 1)) + ' ч.', callback_data=CB_GIFT_HOURS))
    kb.add(B('💬 Сообщения покупателю', callback_data=CB_MESSAGES))
    kb.add(B('◀️ Назад', callback_data=CB_ORDERS))
    return kb


def _template_fields(key):
    import string
    fields = {field for _, field, _, _ in string.Formatter().parse(_default_templates()[key]) if field}
    if key == 'extend_offer':
        fields.add('ttl_minutes')
    return fields


def _validate_template(key, text):
    import string
    if not isinstance(text, str) or not text.strip() or len(text) > 3500:
        raise ValueError('Текст должен содержать от 1 до 3500 символов.')
    allowed = _template_fields(key) | {'order_id', 'rental_id'}
    for _, field, spec, conversion in string.Formatter().parse(text):
        if field is not None and (field not in allowed or spec or conversion):
            raise ValueError('Недопустимая переменная. Используйте переменные, перечисленные под шаблоном.')
    return text


def _message_edit_prompt(cfg, key):
    title, case = MESSAGE_INFO.get(key, (key, 'Сообщение покупателю.'))
    fields = ', '.join('{' + f + '}' for f in sorted(_template_fields(key))) or 'нет'
    return (f'💬 <b>{_h(title)}</b>\n\n<b>Когда отправляется:</b> {_h(case)}\n\n'
            f'<b>Текущий текст:</b>\n<pre>{_h(cfg["templates"][key])}</pre>\n\n'
            f'<b>Переменные:</b> <code>{_h(fields)}</code>\n\nОтправьте новый текст.')


def _export_config(cfg):
    return {'format': 'rental_smm_config', 'version': 1,
            'config': {k: v for k, v in cfg.items() if k in _default_cfg()}}


def _validate_config_payload(payload):
    if len(payload) > 2 * 1024 * 1024:
        raise ValueError('Конфиг должен быть не больше 2 МБ.')
    def no_constant(value):
        raise ValueError('NaN и Infinity в конфиге запрещены.')
    raw = json.loads(payload.decode('utf-8-sig'), parse_constant=no_constant)
    if not isinstance(raw, dict):
        raise ValueError('Ожидается JSON-объект с настройками.')
    if 'format' in raw:
        if raw.get('format') != 'rental_smm_config' or raw.get('version') != 1:
            raise ValueError('Неизвестный формат или версия конфига.')
        raw = raw.get('config')
    if not isinstance(raw, dict) or not {'lots', 'templates'}.issubset(raw):
        raise ValueError('В конфиге должны быть разделы lots и templates. Загрузите файл, скачанный из этого плагина.')
    allowed = set(_default_cfg()) | {'balance_reserve_rub'}
    if set(raw) - allowed:
        raise ValueError('В конфиге есть неизвестные поля: ' + ', '.join(sorted(set(raw) - allowed)))
    for key, value in raw.items():
        default = _default_cfg().get(key)
        if isinstance(default, bool) and not isinstance(value, bool):
            raise ValueError(f'{key}: ожидается true или false.')
        if isinstance(default, (int, float)) and not isinstance(default, bool):
            if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
                raise ValueError(f'{key}: ожидается конечное неотрицательное число.')
        if isinstance(default, str) and not isinstance(value, str):
            raise ValueError(f'{key}: ожидается строка.')
    providers = raw.get('providers', {})
    if not isinstance(providers, dict) or set(providers) - {'kosell', 'muvsell'}:
        raise ValueError('Некорректный раздел провайдеров.')
    for entry in providers.values():
        if not isinstance(entry, dict) or not isinstance(entry.get('api_key', ''), str):
            raise ValueError('Некорректный API-ключ провайдера.')
        for k in ('balance', 'regular_balance', 'promo_balance'):
            if entry.get(k) is not None and (isinstance(entry[k], bool) or not isinstance(entry[k], (int, float)) or not math.isfinite(entry[k])):
                raise ValueError('Некорректный баланс провайдера.')
    rows = raw['lots']
    if not isinstance(rows, list) or len(rows) > 5000:
        raise ValueError('lots должен быть списком, максимум 5000 лотов.')
    seen = set()
    for row in rows:
        if not isinstance(row, dict) or _provider_id(row) not in PROVIDERS:
            raise ValueError('У лота указан неизвестный провайдер.')
        for key in ('lot_id', 'product_id', 'duration_hours'):
            if type(row.get(key)) is not int or row[key] < 1:
                raise ValueError(f'{key} лота должен быть положительным целым числом.')
        if row['duration_hours'] > (720 if _provider_id(row) == 'muvsell' else 8760):
            raise ValueError('Срок аренды превышает лимит провайдера.')
        if row['lot_id'] in seen:
            raise ValueError('В конфиге повторяется LOT ID.')
        seen.add(row['lot_id'])
        if row.get('markup_override_percent') is not None:
            n = row['markup_override_percent']
            if isinstance(n, bool) or not isinstance(n, (int, float)) or not math.isfinite(n) or n < 0:
                raise ValueError('Некорректная наценка лота.')
    templates = raw['templates']
    if not isinstance(templates, dict) or set(templates) - set(_default_templates()):
        raise ValueError('Некорректный раздел шаблонов.')
    for key, value in templates.items():
        _validate_template(key, value)
    return _sanitize_cfg(raw)


def _import_config(chat_id, payload):
    cfg = _validate_config_payload(payload)
    with _SETTINGS_LOCK:
        data = _load_settings()
        backup = os.path.join(PLUGIN_FOLDER, 'config_before_import_' + hashlib.sha256(str(chat_id).encode()).hexdigest()[:16] + '.json')
        _atomic_json(backup, _export_config(data.get(str(chat_id)) or _default_cfg()))
        data[str(chat_id)] = cfg
        _save_settings(data)
    return cfg


def _redacted_logs():
    try:
        with open(LOG_FILE, 'rb') as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - 8 * 1024 * 1024))
            text = stream.read().decode('utf-8', errors='replace')
    except FileNotFoundError:
        text = 'Журнал пока пуст.'
    for _, cfg, _ in _known_api_configs():
        token = str(cfg.get('api_key') or '')
        if token:
            text = text.replace(token, '[API KEY скрыт]')
    text = re.sub(r'(?i)(Bearer\s+)\S+', r'\1[скрыто]', text)
    text = re.sub(r'''(?i)((?:api[_-]?key|steam_password|password|пароль|steam_login|login|логин)["']?\s*[:=]\s*["']?)[^\s,"'<>]+''', r'\1[скрыто]', text)
    return text


def _send_document_bytes(bot, chat_id, name, content, caption):
    import io
    stream = io.BytesIO(content)
    stream.name = name
    return bot.send_document(chat_id, stream, caption=caption)


def _register_order_service_callbacks(cardinal):
    tg, bot = cardinal.telegram, cardinal.telegram.bot
    def menu(c, text, kb):
        _safe_edit(bot, c.message.chat.id, c.message.id, text, kb)
        bot.answer_callback_query(c.id)
    tg.cbq_handler(lambda c: menu(c, _orders_text(c.message.chat.id), _orders_kb()), func=lambda c: c.data == CB_ORDERS)
    tg.cbq_handler(lambda c: menu(c, _service_text(), _service_kb()), func=lambda c: c.data == CB_SERVICE)
    tg.cbq_handler(lambda c: menu(c, _config_text(), _config_kb()), func=lambda c: c.data == CB_CONFIG)
    tg.cbq_handler(lambda c: menu(c, _gift_text(c.message.chat.id), _gift_kb(c.message.chat.id)), func=lambda c: c.data == CB_GIFT)
    def download(c):
        try:
            bot.answer_callback_query(c.id)
            if c.data == CB_LOG_DOWNLOAD:
                _send_document_bytes(bot, c.message.chat.id, 'Rental_Steam_Service_logs.txt', _redacted_logs().encode(), 'Журнал Rental Steam Service. Ключи и распознанные данные входа скрыты.')
            else:
                data = json.dumps(_export_config(_get_cfg(c.message.chat.id)), ensure_ascii=False, indent=2).encode()
                _send_document_bytes(bot, c.message.chat.id, 'Rental_Steam_Service_config.json', data, 'Конфигурация Rental Steam Service. Файл содержит API-ключи — храните его у себя.')
        except Exception:
            _safe_tg(bot, c.message.chat.id, 'Не удалось скачать файл. Попробуйте ещё раз.')
    tg.cbq_handler(download, func=lambda c: c.data in {CB_LOG_DOWNLOAD, CB_CONFIG_DOWNLOAD})
    def upload(c):
        state = {'step': 'config_upload', 'menu_message_id': c.message.id, 'return_menu': 'config'}
        _fsm_prompt(bot, c.message.chat.id, state, '📤 Пришлите конфигурацию Rental Steam Service файлом <b>.json</b> до 2 МБ. После проверки она заменит настройки этого профиля. История аренд и подарков сохраняется.')
        bot.answer_callback_query(c.id)
    tg.cbq_handler(upload, func=lambda c: c.data == CB_CONFIG_UPLOAD)
    def toggle(c):
        cfg = _get_cfg(c.message.chat.id)
        enabled = not cfg.get('review_gift_enabled', False)
        _set_cfg(c.message.chat.id, review_gift_enabled=enabled)
        menu(c, _gift_text(c.message.chat.id), _gift_kb(c.message.chat.id))
    tg.cbq_handler(toggle, func=lambda c: c.data == CB_GIFT_TOGGLE)
    def hours(c):
        state = {'step': 'gift_hours', 'menu_message_id': c.message.id, 'return_menu': 'gift'}
        _fsm_prompt(bot, c.message.chat.id, state, '🎁 Введите число часов в подарок: целое число от 1 до 720. Изменение действует для новых заказов.')
        bot.answer_callback_query(c.id)
    tg.cbq_handler(hours, func=lambda c: c.data == CB_GIFT_HOURS)
    def stars(c):
        state = {'step': 'gift_stars', 'menu_message_id': c.message.id, 'return_menu': 'gift'}
        _fsm_prompt(bot, c.message.chat.id, state, '⭐ Введите минимальную оценку для подарка: от 1 до 5 звёзд.')
        bot.answer_callback_query(c.id)
    tg.cbq_handler(stars, func=lambda c: c.data == CB_GIFT_STARS)


def _gift_save(order_id, **updates):
    with _GIFT_LOCK:
        data = _load_json(GIFTS_FILE, {}, GIFTS_FILE + '.bak')
        record = dict(data.get(str(order_id)) or {})
        record.update(updates, updated_ts=_now())
        data[str(order_id)] = record
        _atomic_json(GIFTS_FILE, data, GIFTS_FILE + '.bak')
        return record


def _review_gift_worker(cardinal, order_id):
    with _GIFT_LOCK:
        rec = _rental_get(order_id)
        if not rec or not rec.get('rental_id') or not rec.get('review_gift_eligible'):
            return
        rec['review_checked_ts'] = _now()
        _rental_save(rec)
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key')))
        if not cfg.get('plugin_enabled', True) or not cfg.get('review_gift_enabled') or not cfg.get('api_key'):
            return
        ledger = _load_json(GIFTS_FILE, {}, GIFTS_FILE + '.bak')
        gift = ledger.get(str(order_id)) or {}
        if gift.get('state') in {'done', 'manual_review', 'failed'}:
            return
        if gift.get('next_retry_ts', 0) > _now():
            return

        order = _resolve_full_order(cardinal, order_id, None)
        if not order or str(_order_field(order, 'id', '')) != str(order_id):
            return
        seller_id = _order_field(order, 'seller_id')
        account_id = getattr(cardinal.account, 'id', None)
        if not seller_id or not account_id or str(seller_id) != str(account_id):
            return
        status = _order_field(order, 'status')
        status_name = str(getattr(status, 'name', status)).upper().split('.')[-1]
        if status_name != 'CLOSED':
            return
        review = _order_field(order, 'review')
        review_stars = _as_int(_order_field(review, 'stars'), 0)
        min_stars = _as_int(rec.get('review_gift_min_stars'), cfg.get('review_gift_min_stars', 5), 1, 5)
        if not review or review_stars < min_stars:
            return

        stored_buyer = _norm_username(rec.get('buyer_username'))
        actual_buyer = _norm_username(_order_field(order, 'buyer_username'))
        if stored_buyer and stored_buyer != actual_buyer:
            return
        hours = int(gift.get('hours') or rec.get('review_gift_hours') or 1)
        try:
            if gift.get('state') != 'processing':
                current = _api_status(cfg, rec['rental_id'])
                if str(current.get('status') or '').lower() not in {'active', 'running', 'rented'}:
                    return
                quote = _api_extension_price(cfg, rec, hours)
                cost = _price_total(quote)
                if cost is None:
                    raise SteamSMMError('Не удалось определить цену подарка.', code='NO_PRICE')
                balance = _api_balance(cfg)
                if float(balance.get('regular_balance') or 0) < max(cost, float(cfg.get('min_balance_rub') or 0)):
                    raise SteamSMMError('Недостаточно баланса для подарка.', code='INSUFFICIENT_BALANCE', retryable=True)
            _gift_save(order_id, state='processing', hours=hours, provider=_provider_id(rec), rental_id=rec['rental_id'])
            result = _api_extend(cfg, rec['rental_id'], hours, _idem('review-gift', order_id))
            ends_at = result.get('ends_at') or result.get('new_ends_at')
            if not ends_at:
                raise SteamSMMError('Провайдер не подтвердил срок подарка.', code='PAYMENT_UNCERTAIN')
            _gift_save(order_id, state='done', hours=hours, ends_at=ends_at, next_retry_ts=0)
            rec.update(ends_at=ends_at, review_gift_given=True, review_gift_given_ts=_now())
            _rental_save(rec)
            _safe_send(cardinal, rec.get('delivery_chat_id') or rec.get('chat_id'), _tpl(cfg, 'review_gift_success',
                game=rec.get('product_name') or 'Steam', duration=_format_duration(hours), ends_at=_fmt_dt(ends_at),
                stars=review_stars, order_id=order_id, rental_id=rec['rental_id']))
            _notify_admin(f'🎁 Подарок за отзыв: заказ <code>{_h(order_id)}</code>, +{hours} ч., {_h(PROVIDERS[_provider_id(rec)])}.', cfg=cfg, kind='extension')
        except SteamSMMError as error:
            uncertain = error.code == 'PAYMENT_UNCERTAIN'
            retry = error.retryable and not uncertain
            state = 'manual_review' if uncertain else ('retry' if retry else 'failed')
            _gift_save(order_id, state=state, hours=hours, last_error=_safe_api_error_message(error), next_retry_ts=_now() + 300 if retry else 0)
            if gift.get('last_error') != _safe_api_error_message(error):
                _notify_admin(f'⚠️ Подарок за отзыв не выдан: <code>{_h(order_id)}</code>\n{_h(_safe_api_error_message(error))}', cfg=cfg, kind='error')
        except Exception:

            _gift_save(order_id, state='manual_review', hours=hours, last_error='Требуется проверка результата подарка.')
            _notify_admin(f'⚠️ Проверьте результат подарка за отзыв по заказу <code>{_h(order_id)}</code>. Автоповтор остановлен.', cfg=cfg, kind='error')


def _scan_review_gifts(cardinal):
    global _GIFT_SCAN_TS
    if _now() - _GIFT_SCAN_TS < 60:
        return
    _GIFT_SCAN_TS = _now()
    ledger = _load_json(GIFTS_FILE, {}, GIFTS_FILE + '.bak')
    rows = [r for r in _rental_list(False) if r.get('review_gift_eligible') and r.get('rental_id')
            and (_record_locally_current(r) or (ledger.get(str(r.get('order_id'))) or {}).get('state') == 'processing')
            and (ledger.get(str(r.get('order_id'))) or {}).get('state') not in {'done', 'failed', 'manual_review'}]
    rows.sort(key=lambda r: r.get('review_checked_ts', 0))
    for rec in rows[:5]:
        _schedule('review-gift:' + str(rec['order_id']), _review_gift_worker, cardinal, str(rec['order_id']))


def _review_message_handler(cardinal, event):
    message = getattr(event, 'message', None)
    if message is None or getattr(message, 'author_id', None) != 0:
        return
    kind = str(getattr(getattr(message, 'type', None), 'name', ''))
    if kind not in {'NEW_FEEDBACK', 'FEEDBACK_CHANGED'}:
        return
    match = re.search(r'#([A-Za-z0-9]{6,16})\b', _event_text(event))
    if match and _rental_get(match.group(1)):
        _schedule('review-gift:' + match.group(1), _review_gift_worker, cardinal, match.group(1))


def _fsm_set(chat_id, state):
    with _FSM_LOCK:
        _FSM[str(chat_id)] = dict(state or {})


def _fsm_get(chat_id):
    with _FSM_LOCK:
        return _FSM.get(str(chat_id))


def _fsm_clear(chat_id):
    with _FSM_LOCK:
        _FSM.pop(str(chat_id), None)


def _handle_fsm(message, cardinal):
    chat_id = message.chat.id
    state = _fsm_get(chat_id)
    if not state:
        return
    text = str(getattr(message, 'text', '') or '').strip()
    if text.lower() in {'/cancel', 'отмена', 'cancel'}:


        bot = cardinal.telegram.bot
        _fsm_cleanup_input(bot, chat_id, state, message)
        _fsm_clear(chat_id)
        _fsm_restore_menu(bot, chat_id, state)
        return
    bot = cardinal.telegram.bot
    step = state.get('step')
    try:
        if step == 'config_upload':
            doc = getattr(message, 'document', None)
            if doc is None or not str(getattr(doc, 'file_name', '')).lower().endswith('.json'):
                raise ValueError('Пришлите JSON-файл конфигурации как документ.')
            if int(getattr(doc, 'file_size', 0) or 0) > 2 * 1024 * 1024:
                raise ValueError('Размер файла не должен превышать 2 МБ.')
            file_info = bot.get_file(doc.file_id)
            payload = bot.download_file(file_info.file_path)
            cfg = _import_config(chat_id, payload)
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, '✅ Конфиг загружен. Настройки применены.\n\n' + _config_text(), _config_kb())
            return
        if step == 'gift_hours':
            if not re.fullmatch(r'[0-9]{1,3}', text) or not 1 <= int(text) <= 720:
                raise ValueError('Введите целое число часов от 1 до 720.')
            _set_cfg(chat_id, review_gift_hours=int(text))
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, _gift_text(chat_id), _gift_kb(chat_id))
            return
        if step == 'gift_stars':
            if not re.fullmatch(r'[1-5]', text):
                raise ValueError('Введите число от 1 до 5.')
            _set_cfg(chat_id, review_gift_min_stars=int(text))
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, _gift_text(chat_id), _gift_kb(chat_id))
            return
        if step == 'provider_key':
            pid = state['provider']
            cfg = _provider_cfg(_get_cfg(chat_id), pid)
            cfg['api_key'] = text
            data = _api_balance(cfg)
            _provider_save(chat_id, pid, api_key=text, **data, last_api_ok=_now(), last_api_error='')
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _provider_panel(bot, chat_id, state['menu_message_id'], pid)
            return
        if step == 'local_update':
            document = getattr(message, 'document', None)
            if document is None:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '⚠️ <b>Нужен файл Rental Steam Service</b>\n\nПришлите файл с расширением <code>.py</code>.')
            file_name = str(getattr(document, 'file_name', '') or 'Rental_Steam_Service.py')
            if not file_name.lower().endswith('.py'):
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '⚠️ <b>Неверный файл</b>\n\nНужен именно Python-файл с расширением <code>.py</code>.')
            file_info = bot.get_file(document.file_id)
            payload = bot.download_file(file_info.file_path)
            result = _install_local_update(payload, file_name)
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            suffix = (
                f'\n\n✅ Установлена версия <code>{_h(result.get("version"))}</code>. Перезапустите Cardinal командой <code>/restart</code>.'
                if result.get('changed')
                else f'\n\nℹ️ Эта версия уже установлена: <code>{_h(result.get("version"))}</code>.'
            )
            _fsm_edit_origin(bot, chat_id, state, _update_text() + suffix, _update_kb())
            return
        if step == 'set_token':
            cfg = _get_cfg(chat_id)
            cfg['api_key'] = text
            data = _api_balance(cfg)
            _set_cfg(chat_id, api_key=text, balance=_as_float(data.get('balance'), 0), regular_balance=_as_float(data.get('regular_balance'), 0), promo_balance=_as_float(data.get('promo_balance'), 0), last_api_ok=_now(), last_api_error='')
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, _token_text(chat_id), _token_kb())
            return
        if step == 'add_lot_id':
            lot_id = _as_int(text, 0, 1)
            if not lot_id:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '⚠️ <b>LOT ID должен быть числом.</b>\n\nВведите ID вашего лота FunPay.')
            fields = _get_lot_fields_ready(cardinal.account, lot_id)
            if not fields:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '❌ <b>LOT не найден.</b>\n\nПроверьте ID и отправьте его ещё раз.')
            _fsm_cleanup_input(bot, chat_id, state, message)
            state.update(lot_id=lot_id)
            _choose_lot_provider(bot, chat_id, state)
            return
        if step == 'add_product_id':
            product_id = _as_int(text, 0, 1)
            if not product_id:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '⚠️ <b>Product ID должен быть числом.</b>\n\nВведите ID игры провайдера.')
            cfg = _get_cfg(chat_id)
            products = _api_products(_provider_cfg(cfg, _provider_id(state)))
            product = _find_product(products, product_id)
            if not product:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '❌ <b>Такого Product ID нет в каталоге аренды провайдера.</b>\n\nПроверьте ID и попробуйте снова.')
            if int(product.get('stock') or 0) <= 0:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(
                    bot, chat_id, state,
                    f'⏳ <b>{_h(product["title"])}</b> сейчас недоступна.\n\n'
                    'Свободных аккаунтов: <b>0</b>. Такой лот сейчас добавить нельзя. '
                    'Когда аккаунт освободится и появится в наличии, добавьте товар повторно.'
                )
            _fsm_cleanup_input(bot, chat_id, state, message)
            state.update(step='add_hours', product_id=product_id, product_name=product['title'], stock=product['stock'])
            _fsm_prompt(
                bot, chat_id, state,
                f'✅ <b>{_h(product["title"])}</b>\n'
                f'Свободных аккаунтов: <b>{product["stock"]}</b>\n\n'
                '⏱ Введите срок аренды в часах.\nНапример: <code>1</code>, <code>24</code> или <code>168</code>.'
            )
            return
        if step == 'add_hours':
            hours = _as_int(text, 0, 1, 8760)
            if not hours:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '⚠️ <b>Введите срок аренды числом.</b>\n\nНапример: <code>1</code>, <code>24</code> или <code>168</code> часов.')
            cfg = _get_cfg(chat_id)
            price_data = _api_calculate_price(_provider_cfg(cfg, _provider_id(state)), state['product_id'], hours)
            api_cost = _price_total(price_data)
            if api_cost is None:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '❌ <b>Провайдер не вернул стоимость.</b>\n\nПопробуйте отправить срок ещё раз.')
            markup = _as_float(cfg.get('global_markup_percent'), 20.0)
            final_price = _seller_price(api_cost, markup)
            row = _sanitize_lot({
                'lot_id': state['lot_id'], 'product_id': state['product_id'],
                'provider': _provider_id(state),
                'product_name': state['product_name'], 'duration_hours': hours,
                'markup_override_percent': None,
                'auto_price': True, 'auto_stock': True, 'auto_balance': True,
                'manual_enabled': True, 'last_stock': state.get('stock', -1),
                'last_api_cost': api_cost, 'last_funpay_price': final_price,
            })
            previous = next((x for x in cfg.get('lots', []) if int(x['lot_id']) == int(row['lot_id'])), None)
            if previous:
                for key in ('markup_override_percent', 'auto_price', 'auto_stock', 'auto_balance', 'manual_enabled'):
                    row[key] = previous[key]
                final_price = _seller_price(api_cost, _effective_markup(cfg, row))
                row['last_funpay_price'] = final_price
            lots = [x for x in cfg.get('lots') or [] if int(x['lot_id']) != int(row['lot_id'])]
            lots.append(row)
            _set_cfg(chat_id, lots=lots)
            try:
                _set_lot_price(cardinal, row['lot_id'], final_price)
            except Exception as e:
                logger.warning('Первичная установка цены LOT %s: %s', row['lot_id'], e)
            buyer = _buyer_price_estimate(cfg, final_price)
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, _lots_text(chat_id), _lots_kb(chat_id))
            return
        if step == 'lot_markup':
            cfg = _get_cfg(chat_id)
            lot_id = int(state['lot_id'])
            lots = cfg.get('lots') or []
            row = next((x for x in lots if int(x['lot_id']) == lot_id), None)
            if not row:
                _fsm_clear(chat_id)
                return
            raw_value = str(text or '').strip().replace(',', '.')
            match = re.fullmatch(r'\s*(\d+(?:\.\d+)?)\s*%?\s*', raw_value)
            if not match:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(
                    bot, chat_id, state,
                    '⚠️ <b>Введите наценку числом.</b>\n\nНапример: <code>20</code>, <code>35</code> или <code>50</code>.'
                )
            value = float(match.group(1))
            row['markup_override_percent'] = value
            price_data = _api_calculate_price(_provider_cfg(cfg, _provider_id(row)), row['product_id'], row['duration_hours'])
            api_cost = _price_total(price_data)
            if api_cost is None:
                _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
                return _fsm_prompt_edit(bot, chat_id, state, '❌ <b>Провайдер не вернул стоимость.</b>\n\nПопробуйте ещё раз.')
            final_price = _seller_price(api_cost, value)
            row['last_api_cost'] = api_cost
            row['last_funpay_price'] = final_price
            _set_cfg(chat_id, lots=lots)
            if row.get('auto_price', True) and cfg.get('auto_price_enabled', True):
                _set_lot_price(cardinal, lot_id, final_price)
            buyer = _buyer_price_estimate(cfg, final_price)
            profit = round(final_price - api_cost, 2)
            sign = '+' if profit >= 0 else ''
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            notice = (
                f'✅ <b>Своя наценка сохранена: {value:g}%</b>\n'
                f'Покупателю: <code>≈{buyer["card"]:.2f} ₽ карта / {buyer["sbp"]:.2f} ₽ СБП</code>\n'
                f'Прибыль: <b>{sign}{profit:.2f} ₽</b>'
            )
            _fsm_edit_origin(bot, chat_id, state, _lot_markup_text(chat_id, lot_id, notice), _lot_markup_kb(chat_id, lot_id))
            return
        if step in {'reserve', 'interval', 'global_markup'}:

            if step == 'reserve':
                if not re.fullmatch(r'[0-9]+(?:[.,][0-9]{1,2})?', text):
                    raise ValueError('Введите неотрицательную сумму в рублях, например 100 или 100,50.')
                value = float(text.replace(',', '.'))
                if not math.isfinite(value):
                    raise ValueError('Некорректная сумма.')
                _set_cfg(chat_id, min_balance_rub=value)
            elif step == 'interval':
                minutes = _as_int(text, 0, 1, 1440)
                _set_cfg(chat_id, check_interval_sec=minutes * 60)
            elif step == 'global_markup':
                value = _as_float(text, 0.0)
                _set_cfg(chat_id, global_markup_percent=value)
                try:
                    _sync_all(cardinal, notify=False)
                except Exception as e:
                    logger.warning('Не удалось сразу применить общую наценку ко всем LOT: %s', e)
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            if state.get('return_menu') == 'lots_general':
                _fsm_edit_origin(bot, chat_id, state, _lots_general_text(chat_id), _lots_general_kb(chat_id))
            else:
                _fsm_edit_origin(bot, chat_id, state, _auto_text(chat_id), _auto_kb(chat_id))
            return
        if step == 'message_edit':
            cfg = _get_cfg(chat_id)
            templates = dict(cfg['templates'])
            templates[state['key']] = _validate_template(state['key'], text)
            _set_cfg(chat_id, templates=templates)
            _fsm_cleanup_input(bot, chat_id, state, message)
            _fsm_clear(chat_id)
            _fsm_edit_origin(bot, chat_id, state, _messages_text(chat_id), _messages_kb(chat_id))
            return
    except Exception as e:
        logger.exception('FSM error: %s', e)
        _tg_delete(bot, chat_id, getattr(message, 'message_id', getattr(message, 'id', None)))
        return _fsm_prompt_edit(bot, chat_id, state, f'❌ <b>Ошибка</b>\n\n{_h(_safe_api_error_message(e))}')

def _toggle_lot_flag(chat_id, lot_id, key):
    cfg = _get_cfg(chat_id)
    lots = cfg.get('lots') or []
    for row in lots:
        if int(row['lot_id']) == int(lot_id):
            row[key] = not bool(row.get(key, True))
            if key == 'manual_enabled':
                row['auto_disabled'] = False
                row['auto_disabled_reason'] = ''
            break
    _set_cfg(chat_id, lots=lots)
    return cfg

def _register_callbacks(cardinal):
    tg = cardinal.telegram
    bot = tg.bot
    _register_provider_callbacks(cardinal)
    _register_order_service_callbacks(cardinal)

    def home_message(m):
        _safe_tg(bot, m.chat.id, _home_text(m.chat.id), _home_kb(m.chat.id))

    tg.msg_handler(home_message, commands=['rental', 'rentalsmm'])
    tg.msg_handler(lambda m: _handle_fsm(m, cardinal), func=lambda m: _fsm_get(m.chat.id) is not None, content_types=['text', 'document'])

    tg.cbq_handler(lambda c: _open_home(bot, c), func=lambda c: c.data in {CB_HOME, f'{UUID}:0'} or c.data.startswith(f'{getattr(CBT, "EDIT_PLUGIN", "edit_plugin")}:{UUID}') or c.data.startswith(f'{getattr(CBT, "PLUGIN_SETTINGS", "plugin_settings")}:{UUID}'))

    tg.cbq_handler(lambda c: _open_settings(bot, c), func=lambda c: c.data == CB_SETTINGS)

    def mini_settings(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _mini_settings_text(c.message.chat.id), _mini_settings_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(mini_settings, func=lambda c: c.data == CB_MINI_SETTINGS)

    def plugin_status(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _plugin_status_text(c.message.chat.id), _plugin_status_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(plugin_status, func=lambda c: c.data == CB_PLUGIN_STATUS)

    def stats(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _stats_text(c.message.chat.id), _stats_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(stats, func=lambda c: c.data == CB_STATS)

    def sync_menu(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _sync_text(c.message.chat.id), _sync_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(sync_menu, func=lambda c: c.data == CB_SYNC_MENU)

    def notifications(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _notifications_text(c.message.chat.id), _notifications_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(notifications, func=lambda c: c.data == CB_NOTIFICATIONS)

    def toggle_notification(c, key):
        cfg = _get_cfg(c.message.chat.id)
        _set_cfg(c.message.chat.id, **{key: not bool(cfg.get(key, True))})
        _safe_edit(bot, c.message.chat.id, c.message.id, _notifications_text(c.message.chat.id), _notifications_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    for _cb_data, _cfg_key in (
        (CB_NOTIFY_MASTER, 'notifications_enabled'), (CB_NOTIFY_ORDER, 'notify_orders'),
        (CB_NOTIFY_RENT, 'notify_rentals'), (CB_NOTIFY_ERROR, 'notify_errors'),
        (CB_NOTIFY_STOCK, 'notify_stock'), (CB_NOTIFY_PRICE, 'notify_price'),
        (CB_NOTIFY_LOT, 'notify_lot_state'), (CB_NOTIFY_EXT, 'notify_extensions'),
        (CB_NOTIFY_API, 'notify_api'),
    ):
        tg.cbq_handler(lambda c, key=_cfg_key: toggle_notification(c, key), func=lambda c, data=_cb_data: c.data == data)

    def info(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _info_text(), _info_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(info, func=lambda c: c.data == CB_INFO)

    def update_menu(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _update_text(), _update_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(update_menu, func=lambda c: c.data == CB_UPDATE)

    def update_local(c):
        state = {'step': 'local_update', 'menu_message_id': c.message.id, 'return_menu': 'update'}
        try: bot.answer_callback_query(c.id, 'Пришлите новый .py файл')
        except Exception: pass
        _fsm_prompt(
            bot, c.message.chat.id, state,
            '📥 <b>Локальное обновление</b>\n\nПришлите новый файл Rental Steam Service с расширением <code>.py</code>.'
        )
    tg.cbq_handler(update_local, func=lambda c: c.data == CB_UPDATE_LOCAL)

    def update_online(c):
        try:
            bot.answer_callback_query(
                c.id,
                '🌐 Обновления находятся в официальном GitHub-репозитории.',
                show_alert=True,
            )
        except Exception:
            pass
    tg.cbq_handler(update_online, func=lambda c: c.data == CB_UPDATE_ONLINE)

    def delete_ask(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _delete_confirm_text(), _delete_confirm_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(delete_ask, func=lambda c: c.data == CB_DELETE_ASK)

    def delete_yes(c):
        try: bot.answer_callback_query(c.id, 'Удаляю…')
        except Exception: pass
        ok, errors = _self_delete_from_disk(cardinal, c.message.chat.id)
        kb = K()
        kb.add(B('🔙 К списку плагинов', callback_data=CB_PLUGINS_LIST))
        if ok:
            text = '✅ <b>Rental Steam Service удалён.</b>\n\nЧтобы применить изменения, выполните <code>/restart</code>.'
        else:
            text = '⚠️ <b>Удаление выполнено частично.</b>\n\n' + '\n'.join(f'• {_h(x)}' for x in errors[:10]) + '\n\nВыполните <code>/restart</code> после ручной проверки.'
        _safe_edit(bot, c.message.chat.id, c.message.id, text, kb)
    tg.cbq_handler(delete_yes, func=lambda c: c.data == CB_DELETE_YES)
    tg.cbq_handler(lambda c: _open_home(bot, c), func=lambda c: c.data == CB_DELETE_NO)

    def token(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _token_text(c.message.chat.id), _token_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(token, func=lambda c: c.data == CB_TOKEN)

    def lots(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _lots_text(c.message.chat.id), _lots_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lots, func=lambda c: c.data == CB_LOTS)

    def lots_page(c):
        chat_id = c.message.chat.id
        page = _as_int(c.data[len(CB_LOTS_PAGE):], 0, 0)
        _LOT_LIST_PAGE[str(chat_id)] = page
        _safe_edit(bot, chat_id, c.message.id, _lots_text(chat_id), _lots_kb(chat_id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lots_page, func=lambda c: c.data.startswith(CB_LOTS_PAGE))

    def lots_general(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _lots_general_text(c.message.chat.id), _lots_general_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lots_general, func=lambda c: c.data == CB_LOTS_GENERAL)

    def lots_all_state(c, enabled):
        chat_id = c.message.chat.id
        cfg = _get_cfg(chat_id)
        rows = cfg.get('lots') or []
        ok_count = 0
        failed = []
        for row in rows:
            lid = int(row.get('lot_id') or 0)
            if not lid:
                continue
            try:
                ok = _set_lot_active(cardinal, lid, bool(enabled))
            except Exception:
                ok = False
            if ok:
                row['manual_enabled'] = bool(enabled)
                row['auto_disabled'] = False
                row['auto_disabled_reason'] = ''
                ok_count += 1
            else:
                failed.append(lid)
        _set_cfg(chat_id, lots=rows)
        _safe_edit(bot, chat_id, c.message.id, _lots_general_text(chat_id), _lots_general_kb(chat_id))
        text = f'{"Включено" if enabled else "Выключено"}: {ok_count}/{len(rows)}'
        if failed:
            text += ' · ошибки: ' + ', '.join(map(str, failed[:5]))
        try: bot.answer_callback_query(c.id, text[:180], show_alert=bool(failed))
        except Exception: pass
    tg.cbq_handler(lambda c: lots_all_state(c, True), func=lambda c: c.data == CB_LOTS_ALL_ON)
    tg.cbq_handler(lambda c: lots_all_state(c, False), func=lambda c: c.data == CB_LOTS_ALL_OFF)

    def lots_general_toggle(c, key):
        chat_id = c.message.chat.id
        cfg = _get_cfg(chat_id)
        _set_cfg(chat_id, **{key: not bool(cfg.get(key, True))})
        _safe_edit(bot, chat_id, c.message.id, _lots_general_text(chat_id), _lots_general_kb(chat_id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lambda c: lots_general_toggle(c, 'auto_price_enabled'), func=lambda c: c.data == CB_LOTS_GENERAL_PRICE)
    tg.cbq_handler(lambda c: lots_general_toggle(c, 'auto_deactivate_enabled'), func=lambda c: c.data == CB_LOTS_GENERAL_DEACT)

    def lots_general_ask(c, step, text):
        state = {'step': step, 'menu_message_id': c.message.id, 'return_menu': 'lots_general'}
        try: bot.answer_callback_query(c.id)
        except Exception: pass
        _fsm_prompt(bot, c.message.chat.id, state, f'⚙️ <b>Общее · Лоты</b>\n\n{text}')
    tg.cbq_handler(lambda c: lots_general_ask(c, 'global_markup', 'Введите общую наценку для всех LOT без индивидуальной наценки, в %.'), func=lambda c: c.data == CB_LOTS_GENERAL_MARKUP)
    tg.cbq_handler(lambda c: lots_general_ask(c, 'reserve', 'Введите минимальный баланс в ₽.'), func=lambda c: c.data == CB_LOTS_GENERAL_RESERVE)
    tg.cbq_handler(lambda c: lots_general_ask(c, 'interval', 'Введите интервал проверки в минутах.'), func=lambda c: c.data == CB_LOTS_GENERAL_INTERVAL)

    def add_product_page(c):
        chat_id = c.message.chat.id
        state = _fsm_get(chat_id)
        if not state or state.get('step') != 'add_product_id':
            try: bot.answer_callback_query(c.id, 'Добавление LOT уже завершено.', show_alert=True)
            except Exception: pass
            return
        page = _as_int(c.data[len(CB_ADD_PRODUCT_PAGE):], 0, 0)
        _show_product_picker(bot, chat_id, state, page)
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(add_product_page, func=lambda c: c.data.startswith(CB_ADD_PRODUCT_PAGE))

    def add_product_pick(c):
        chat_id = c.message.chat.id
        state = _fsm_get(chat_id)
        if not state or state.get('step') != 'add_product_id':
            try: bot.answer_callback_query(c.id, 'Добавление LOT уже завершено.', show_alert=True)
            except Exception: pass
            return
        product_id = _as_int(c.data[len(CB_ADD_PRODUCT_PICK):], 0, 1)
        try:
            product = _find_product(_api_products(_wizard_cfg(chat_id)), product_id)
            if not product or int(product.get('stock') or 0) <= 0:
                return bot.answer_callback_query(c.id, 'Этот товар сейчас недоступен.', show_alert=True)
            _tg_delete(bot, chat_id, state.get('prompt_msg_id'))
            state.update(step='add_hours', product_id=product_id, product_name=product['title'], stock=product['stock'])
            _fsm_prompt(
                bot, chat_id, state,
                f'✅ <b>{_h(product["title"])}</b> · ID <code>{product_id}</code>\n'
                f'В наличии: <b>{product["stock"]}</b>\n\n'
                '⏱ Введите срок аренды в часах.\nНапример: <code>1</code>, <code>24</code> или <code>168</code>.'
            )
            try: bot.answer_callback_query(c.id, 'Товар выбран.')
            except Exception: pass
        except Exception as e:
            try: bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
            except Exception: pass
    tg.cbq_handler(add_product_pick, func=lambda c: c.data.startswith(CB_ADD_PRODUCT_PICK))

    def fsm_cancel(c):
        chat_id = c.message.chat.id
        state = _fsm_get(chat_id)
        try:
            bot.answer_callback_query(c.id)
        except Exception:
            pass
        if not state:
            try:
                _tg_delete(bot, chat_id, c.message.id)
            except Exception:
                pass
            return
        _tg_delete(bot, chat_id, state.get('prompt_msg_id') or c.message.id)
        _fsm_clear(chat_id)
        _fsm_restore_menu(bot, chat_id, state)
    tg.cbq_handler(fsm_cancel, func=lambda c: c.data == CB_CANCEL)

    def products(c):

        _safe_edit(bot, c.message.chat.id, c.message.id, _lots_text(c.message.chat.id), _lots_kb(c.message.chat.id))
        try:
            bot.answer_callback_query(c.id, 'ID товаров теперь выбираются только при добавлении LOT.')
        except Exception:
            pass
    tg.cbq_handler(products, func=lambda c: c.data == CB_PRODUCTS or c.data.startswith(CB_PRODUCTS_PAGE))

    def product_help(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _lots_text(c.message.chat.id), _lots_kb(c.message.chat.id))
        try:
            bot.answer_callback_query(c.id, 'Список товаров открывается на шаге добавления LOT.')
        except Exception:
            pass
    tg.cbq_handler(product_help, func=lambda c: c.data == CB_PRODUCT_HELP)

    def auto(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _auto_text(c.message.chat.id), _auto_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(auto, func=lambda c: c.data == CB_AUTO)

    def rentals(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _rentals_text(), _rentals_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(rentals, func=lambda c: c.data == CB_RENTALS)

    def ext(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _extensions_text(c.message.chat.id), _extensions_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(ext, func=lambda c: c.data == CB_EXT)

    def commands(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _commands_text(c.message.chat.id), _commands_kb())
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(commands, func=lambda c: c.data == CB_COMMANDS)

    def messages(c):
        _safe_edit(bot, c.message.chat.id, c.message.id, _messages_text(c.message.chat.id), _messages_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(messages, func=lambda c: c.data == CB_MESSAGES)

    def toggle_plugin(c):
        chat_id = c.message.chat.id
        cfg = _get_cfg(chat_id)
        new_state = not cfg.get('plugin_enabled', True)
        _set_cfg(chat_id, plugin_enabled=new_state)
        _safe_edit(bot, chat_id, c.message.id, _mini_settings_text(chat_id), _mini_settings_kb(chat_id))
        try:
            bot.answer_callback_query(c.id, 'Плагин включён.' if new_state else 'Плагин выключен.')
        except Exception:
            pass
        logger.info('🧩 Плагин %s', 'включён' if new_state else 'выключен')
    tg.cbq_handler(toggle_plugin, func=lambda c: c.data == CB + ':toggle')

    def set_token(c):
        state = {'step': 'set_token', 'menu_message_id': c.message.id, 'return_menu': 'token'}
        bot.answer_callback_query(c.id)
        _fsm_prompt(
            bot, c.message.chat.id, state,
            '🔑 <b>API-ключ SteamSMM</b>\n\nОтправьте API-ключ сервиса. После ввода плагин сразу проверит баланс и подключение.'
        )
    tg.cbq_handler(set_token, func=lambda c: c.data == CB + ':settoken')

    def del_token(c):
        _set_cfg(c.message.chat.id, api_key='', balance=None, regular_balance=None, promo_balance=None, last_api_error='')
        token(c)
    tg.cbq_handler(del_token, func=lambda c: c.data == CB + ':deltoken')

    def balance(c):
        chat_id = c.message.chat.id
        try:
            cfg = _get_cfg(chat_id)
            data = _api_balance(cfg)
            _set_cfg(chat_id, balance=_as_float(data.get('balance'), 0), regular_balance=_as_float(data.get('regular_balance'), 0), promo_balance=_as_float(data.get('promo_balance'), 0), last_api_ok=_now(), last_api_error='')
            bot.answer_callback_query(c.id, 'Баланс обновлён.')
        except Exception as e:
            bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
        token(c)
    tg.cbq_handler(balance, func=lambda c: c.data == CB + ':bal')

    def add_lot(c):
        state = {'step': 'add_lot_id', 'menu_message_id': c.message.id, 'return_menu': 'lots'}
        bot.answer_callback_query(c.id)
        _fsm_prompt(
            bot, c.message.chat.id, state,
            '➕ <b>Добавление лота</b>\n\nШаг 1/3 — отправьте <b>LOT ID FunPay</b>.'
        )
    tg.cbq_handler(add_lot, func=lambda c: c.data == CB_LOT_ADD)

    def lot_open(c):
        lid = _as_int(c.data[len(CB_LOT_OPEN):], 0, 1)
        _safe_edit(bot, c.message.chat.id, c.message.id, _lot_detail_text(c.message.chat.id, lid), _lot_detail_kb(c.message.chat.id, lid))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lot_open, func=lambda c: c.data.startswith(CB_LOT_OPEN))

    def lot_flag(c, prefix, key):
        lid = _as_int(c.data[len(prefix):], 0, 1)
        cfg = _get_cfg(c.message.chat.id)
        lots_cfg = cfg.get('lots') or []
        target = next((x for x in lots_cfg if int(x['lot_id']) == lid), None)
        if not target:
            return bot.answer_callback_query(c.id, 'Лот не найден.', show_alert=True)
        if key == 'manual_enabled':
            new_value = not bool(target.get(key, True))
            if _set_lot_active(cardinal, lid, new_value):
                target[key] = new_value
                target['auto_disabled'] = False
                target['auto_disabled_reason'] = ''
                _set_cfg(c.message.chat.id, lots=lots_cfg)
            else:
                return bot.answer_callback_query(c.id, 'FunPay не сохранил состояние.', show_alert=True)
        else:
            target[key] = not bool(target.get(key, True))
            _set_cfg(c.message.chat.id, lots=lots_cfg)
        _safe_edit(bot, c.message.chat.id, c.message.id, _lot_detail_text(c.message.chat.id, lid), _lot_detail_kb(c.message.chat.id, lid))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lambda c: lot_flag(c, CB_LOT_TOGGLE, 'manual_enabled'), func=lambda c: c.data.startswith(CB_LOT_TOGGLE))
    tg.cbq_handler(lambda c: lot_flag(c, CB_LOT_AP, 'auto_price'), func=lambda c: c.data.startswith(CB_LOT_AP))
    tg.cbq_handler(lambda c: lot_flag(c, CB_LOT_AS, 'auto_stock'), func=lambda c: c.data.startswith(CB_LOT_AS))
    tg.cbq_handler(lambda c: lot_flag(c, CB_LOT_AB, 'auto_balance'), func=lambda c: c.data.startswith(CB_LOT_AB))

    def lot_markup(c):
        lid = _as_int(c.data[len(CB_LOT_MARKUP):], 0, 1)
        cfg = _get_cfg(c.message.chat.id)
        row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == lid), None)
        if not row:
            return bot.answer_callback_query(c.id, 'Лот не найден.', show_alert=True)
        _safe_edit(bot, c.message.chat.id, c.message.id, _lot_markup_text(c.message.chat.id, lid), _lot_markup_kb(c.message.chat.id, lid))
        try:
            bot.answer_callback_query(c.id)
        except Exception:
            pass
    tg.cbq_handler(lot_markup, func=lambda c: c.data.startswith(CB_LOT_MARKUP))

    def lot_markup_global(c):
        lid = _as_int(c.data[len(CB_LOT_MARKUP_GLOBAL):], 0, 1)
        chat_id = c.message.chat.id
        cfg = _get_cfg(chat_id)
        lots_cfg = cfg.get('lots') or []
        row = next((x for x in lots_cfg if int(x['lot_id']) == lid), None)
        if not row:
            return bot.answer_callback_query(c.id, 'Лот не найден.', show_alert=True)
        row['markup_override_percent'] = None
        try:
            price_data = _api_calculate_price(_provider_cfg(cfg, _provider_id(row)), row['product_id'], row['duration_hours'])
            api_cost = _price_total(price_data)
            if api_cost is None:
                raise RuntimeError('Провайдер не вернул стоимость.')
            markup = _effective_markup(cfg, row)
            final_price = _seller_price(api_cost, markup)
            row['last_api_cost'] = api_cost
            row['last_funpay_price'] = final_price
            _set_cfg(chat_id, lots=lots_cfg)
            if row.get('auto_price', True) and cfg.get('auto_price_enabled', True):
                _set_lot_price(cardinal, lid, final_price)
            buyer = _buyer_price_estimate(cfg, final_price)
            profit = round(final_price - api_cost, 2)
            sign = '+' if profit >= 0 else ''
            notice = (
                f'✅ <b>Используется общая наценка: {markup:g}%</b>\n'
                f'Покупателю: <code>≈{buyer["card"]:.2f} ₽ карта / {buyer["sbp"]:.2f} ₽ СБП</code>\n'
                f'Прибыль: <b>{sign}{profit:.2f} ₽</b>'
            )
            _safe_edit(bot, chat_id, c.message.id, _lot_markup_text(chat_id, lid, notice), _lot_markup_kb(chat_id, lid))
            bot.answer_callback_query(c.id, 'Общая наценка применена.')
        except Exception as e:
            bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
    tg.cbq_handler(lot_markup_global, func=lambda c: c.data.startswith(CB_LOT_MARKUP_GLOBAL))

    def lot_markup_custom(c):
        lid = _as_int(c.data[len(CB_LOT_MARKUP_CUSTOM):], 0, 1)
        cfg = _get_cfg(c.message.chat.id)
        row = next((x for x in cfg.get('lots') or [] if int(x['lot_id']) == lid), None)
        if not row:
            return bot.answer_callback_query(c.id, 'Лот не найден.', show_alert=True)
        current = row.get('markup_override_percent')
        state = {'step': 'lot_markup', 'lot_id': lid, 'menu_message_id': c.message.id, 'return_menu': 'lot_markup'}
        try:
            bot.answer_callback_query(c.id)
        except Exception:
            pass
        current_text = f'{float(current):g}%' if current is not None else 'не задана'
        _fsm_prompt(
            bot, c.message.chat.id, state,
            f'✏️ <b>Своя наценка · LOT {lid}</b>\n\n'
            f'Сейчас: <b>{current_text}</b>\n'
            f'Общая: <b>{_as_float(cfg.get("global_markup_percent"), 20.0):g}%</b>\n\n'
            'Введите свою наценку в процентах.\n'
            'Например: <code>20</code>, <code>35</code> или <code>50</code>.'
        )
    tg.cbq_handler(lot_markup_custom, func=lambda c: c.data.startswith(CB_LOT_MARKUP_CUSTOM))

    def lot_del(c):
        lid = _as_int(c.data[len(CB_LOT_DEL):], 0, 1)
        cfg = _get_cfg(c.message.chat.id)
        _set_cfg(c.message.chat.id, lots=[x for x in cfg.get('lots') or [] if int(x['lot_id']) != lid])
        lots(c)
    tg.cbq_handler(lot_del, func=lambda c: c.data.startswith(CB_LOT_DEL))

    def sync(c):
        try:
            bot.answer_callback_query(c.id, 'Проверяю провайдеров и лоты…')
        except Exception:
            pass
        sync_notice = ''
        try:
            report = _sync_all(cardinal, notify=False)
            sync_notice = f'✅ Синхронизация завершена · изменений: {report.get("changed", 0)}'
            try:
                bot.answer_callback_query(c.id, sync_notice[:180])
            except Exception:
                pass
        except Exception as e:
            sync_notice = f'❌ {_safe_api_error_message(e)}'
            try:
                bot.answer_callback_query(c.id, sync_notice[:180], show_alert=True)
            except Exception:
                pass
        if c.data == CB_LOT_REFRESH:
            _safe_edit(bot, c.message.chat.id, c.message.id, _lots_text(c.message.chat.id), _lots_kb(c.message.chat.id))
        elif c.data == CB_LOTS_GENERAL_CHECK:
            _safe_edit(bot, c.message.chat.id, c.message.id, _lots_general_text(c.message.chat.id), _lots_general_kb(c.message.chat.id))
        elif c.data == CB_STATS_REFRESH:
            _safe_edit(bot, c.message.chat.id, c.message.id, _stats_text(c.message.chat.id), _stats_kb())
        elif c.data == CB_AUTO_CHECK:
            _safe_edit(bot, c.message.chat.id, c.message.id, _auto_text(c.message.chat.id), _auto_kb(c.message.chat.id))
        else:
            _safe_edit(bot, c.message.chat.id, c.message.id, _sync_text(c.message.chat.id), _sync_kb())
    tg.cbq_handler(sync, func=lambda c: c.data in {CB_SYNC, CB_LOT_REFRESH, CB_LOTS_GENERAL_CHECK, CB_STATS_REFRESH, CB_AUTO_CHECK})

    def toggle_auto(c, key):
        cfg = _get_cfg(c.message.chat.id)
        _set_cfg(c.message.chat.id, **{key: not bool(cfg.get(key, True))})
        _safe_edit(bot, c.message.chat.id, c.message.id, _auto_text(c.message.chat.id), _auto_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(lambda c: toggle_auto(c, 'auto_price_enabled'), func=lambda c: c.data == CB_AUTO_TOGGLE_PRICE)
    tg.cbq_handler(lambda c: toggle_auto(c, 'auto_deactivate_enabled'), func=lambda c: c.data == CB_AUTO_TOGGLE_DEACT)

    def ask_simple(c, step, text):
        return_menu = 'auto'
        state = {'step': step, 'menu_message_id': c.message.id, 'return_menu': return_menu}
        bot.answer_callback_query(c.id)
        _fsm_prompt(bot, c.message.chat.id, state, f'⚙️ <b>Изменение настройки</b>\n\n{text}')
    tg.cbq_handler(lambda c: ask_simple(c, 'reserve', 'Введите минимальный баланс в ₽. Лоты провайдера выключаются, если его баланс ниже этого порога или не хватает на аренду.'), func=lambda c: c.data == CB_AUTO_RESERVE)
    tg.cbq_handler(lambda c: ask_simple(c, 'interval', 'Введите интервал проверки в минутах.'), func=lambda c: c.data == CB_AUTO_INTERVAL)
    tg.cbq_handler(lambda c: ask_simple(c, 'global_markup', 'Введите общую наценку для всех LOT без индивидуальной наценки, в %.'), func=lambda c: c.data == CB_GLOBAL_MARKUP)
    def temporary_lot_toggle(c):


        _set_cfg(c.message.chat.id, extension_temporary_enabled=True, extension_ttl_sec=1200)
        _safe_edit(bot, c.message.chat.id, c.message.id, _extensions_text(c.message.chat.id), _extensions_kb(c.message.chat.id))
        try: bot.answer_callback_query(c.id, 'Временный LOT всегда ограничен 20 минутами.')
        except Exception: pass
    tg.cbq_handler(temporary_lot_toggle, func=lambda c: c.data == CB_EXT_TTL)

    def ext_toggle(c):
        cfg = _get_cfg(c.message.chat.id)
        _set_cfg(c.message.chat.id, extension_enabled=not cfg.get('extension_enabled', True))
        ext(c)
    tg.cbq_handler(ext_toggle, func=lambda c: c.data == CB_EXT_TOGGLE)

    def msg_edit(c):
        key = c.data[len(CB_MSG_EDIT):]
        cfg = _get_cfg(c.message.chat.id)
        if key not in cfg['templates']:
            return bot.answer_callback_query(c.id, 'Шаблон не найден.', show_alert=True)
        state = {'step': 'message_edit', 'key': key, 'menu_message_id': c.message.id, 'return_menu': 'messages'}
        bot.answer_callback_query(c.id)
        _fsm_prompt(
            bot, c.message.chat.id, state,
            _message_edit_prompt(cfg, key)
        )
    tg.cbq_handler(msg_edit, func=lambda c: c.data.startswith(CB_MSG_EDIT))

    def rental_open(c):
        oid = c.data[len(CB_RENT_OPEN):]
        _safe_edit(bot, c.message.chat.id, c.message.id, _rental_detail_text(oid), _rental_detail_kb(oid))
        try: bot.answer_callback_query(c.id)
        except Exception: pass
    tg.cbq_handler(rental_open, func=lambda c: c.data.startswith(CB_RENT_OPEN))

    def rental_action(c, prefix, action):
        oid = c.data[len(prefix):]
        rec = _rental_get(oid)
        if not rec:
            return bot.answer_callback_query(c.id, 'Аренда не найдена.', show_alert=True)
        cfg = _cfg_for_record(rec, _owner_cfg(rec.get('owner_key') or rec.get('chat_id')))
        try:
            if action == 'status':
                data = _api_status(cfg, rec['rental_id'])
                rec['status'] = str(data.get('status') or rec.get('status'))
                rec['starts_at'] = data.get('starts_at') or rec.get('starts_at')
                rec['ends_at'] = data.get('ends_at') or rec.get('ends_at')
                _rental_save(rec)
                bot.answer_callback_query(c.id, 'Статус обновлён.')
            elif action == 'creds':
                rec, data = _credentials_for_record(cfg, rec)
                login, password = _credentials_values(data)
                bot.send_message(c.message.chat.id, f'🔐 Логин: <code>{_h(login)}</code>\n🔑 Пароль: <code>{_h(password)}</code>', parse_mode='HTML')
                bot.answer_callback_query(c.id)
            elif action == 'guard':
                data = _api_guard(cfg, rec['rental_id'])
                bot.send_message(c.message.chat.id, f'🛡 Guard: <code>{_h(data.get("code") or data.get("guard_code") or "—")}</code>', parse_mode='HTML')
                bot.answer_callback_query(c.id)
            else:
                rec = _refresh_rental_current(cfg, rec)
                if not rec:
                    raise RuntimeError('Аренда уже завершена и больше не может быть продлена.')
                hours = int(action)
                ext_rec = _create_extension_lot(cardinal, rec, hours, requested_by='seller')
                _safe_send(cardinal, rec.get('chat_id'), _tpl(
                    cfg, 'extend_offer', game=rec.get('product_name') or 'Steam', duration=_format_duration(hours),
                    price=f'{ext_rec["price"]:.2f}', lot_time=('⏳ Оплатите в течение 20 минут.' if cfg.get('extension_temporary_enabled', True) else 'Лот активен до оплаты.'), ttl_minutes=20, url=ext_rec['url'],
                    order_id=rec.get('order_id'), rental_id=rec.get('rental_id')
                ))
                bot.send_message(c.message.chat.id, f'✅ Лот продления создан и отправлен покупателю:\n{ext_rec["url"]}')
                bot.answer_callback_query(c.id)
        except Exception as e:
            bot.answer_callback_query(c.id, _safe_api_error_message(e)[:180], show_alert=True)
        _safe_edit(bot, c.message.chat.id, c.message.id, _rental_detail_text(oid), _rental_detail_kb(oid))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_STATUS, 'status'), func=lambda c: c.data.startswith(CB_RENT_STATUS))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_CREDS, 'creds'), func=lambda c: c.data.startswith(CB_RENT_CREDS))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_GUARD, 'guard'), func=lambda c: c.data.startswith(CB_RENT_GUARD))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_EXT1, '1'), func=lambda c: c.data.startswith(CB_RENT_EXT1))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_EXT24, '24'), func=lambda c: c.data.startswith(CB_RENT_EXT24))
    tg.cbq_handler(lambda c: rental_action(c, CB_RENT_EXT168, '168'), func=lambda c: c.data.startswith(CB_RENT_EXT168))

def init_cardinal(cardinal):
    global _CARDINAL_REF
    _CARDINAL_REF = cardinal
    os.makedirs(PLUGIN_FOLDER, exist_ok=True)
    if not os.path.exists(SETTINGS_FILE):
        _atomic_json(SETTINGS_FILE, {})
    if not os.path.exists(RENTALS_FILE):
        _atomic_json(RENTALS_FILE, _db_default())
    if not os.path.exists(EXTENSIONS_FILE):
        _atomic_json(EXTENSIONS_FILE, _db_default())
    try:
        _migrate_opaque_rental_ids()
    except Exception as e:
        logger.warning('Миграция Rental ID: %s', _compact_error(e))
    _register_callbacks(cardinal)
    _start_maintenance(cardinal)
    _schedule('restore-rentals-on-start', _restore_rentals_after_restart, cardinal)
    try:
        cardinal.add_telegram_commands(UUID, [
            ('rental', 'Открыть Rental Steam Service', True),
            ('rentalsmm', 'Открыть Rental Steam Service', True),
            ('rentalsteamservice', 'Открыть Rental Steam Service', True),
        ])
    except Exception:
        pass
    logger.info('Rental Steam Service v%s запущен.', VERSION)
_PAID_ORDER_RE = re.compile(r'(?:оплатил|оплатила)\s+заказ\s*#([A-Za-z0-9]+)', re.I)

def _dispatch_paid_order(cardinal, event, order, oid, chat_id=None, source='event', extra_text=''):
    cfg = _owner_cfg(chat_id)
    if not cfg.get('plugin_enabled', True) or not _has_provider_keys(cfg):
        return False

    route = _extension_purchase_get(oid)
    if route and route.get('route') == 'extension':
        status = str(route.get('status') or '')
        logger.info(
            'Заказ #%s · уже закреплён за продлением · status=%s · source=%s',
            oid, status or 'claimed', source
        )
        if status in {'claimed', 'processing', 'retry'}:
            ext_rec = _extension_records().get(str(route.get('extension_lot_id') or ''))
            if isinstance(ext_rec, dict):
                target_chat = chat_id or ext_rec.get('chat_id') or route.get('chat_id')
                _schedule(
                    f'extension-order:{oid}', _process_extension_order,
                    cardinal, event, ext_rec, oid, target_chat
                )
        return True

    full_order = _resolve_full_order(cardinal, oid, order)
    ext = _extension_by_event(full_order, event, extra_text=extra_text)
    if ext:
        target_chat = chat_id or _resolve_order_chat_id(cardinal, event, full_order, oid) or ext.get('chat_id')

        _extension_purchase_mark(
            oid, ext, status='claimed',
            detected_source=source, detected_chat_id=str(target_chat or '')
        )
        logger.info('Заказ #%s · LOT продления %s сопоставлен · rental=%s', oid, ext.get('lot_id'), ext.get('rental_id'))
        _notify_admin(
            f'🧾 <b>Оплачен лот продления</b>\nЗаказ: <code>{_h(oid)}</code>\nRental ID: <code>{_h(ext.get("rental_id"))}</code>',
            cfg=cfg, kind='order'
        )
        _schedule(f'extension-order:{oid}', _process_extension_order, cardinal, event, ext, oid, target_chat)
        return True

    lot = _lot_by_event(cfg, full_order, event, cardinal=cardinal, extra_text=extra_text)
    if not lot and full_order is not order:
        lot = _lot_by_event(cfg, order, event, cardinal=cardinal, extra_text=extra_text)
    if not lot:

        lot = _lot_by_event(cfg, {'description': extra_text, 'title': extra_text}, event, cardinal=cardinal, extra_text=extra_text)
    if not lot:
        logger.info('Заказ #%s · Rental LOT не сопоставлен · source=%s · ids=%s · text=%s', oid, source, sorted(_order_lot_ids(full_order, event)), _compact_error(extra_text, 180))
        return False

    target_chat = chat_id or _resolve_order_chat_id(cardinal, event, full_order, oid)
    if not target_chat:
        logger.warning('Заказ #%s · LOT %s найден, но chat_id определить не удалось.', oid, lot['lot_id'])
        _notify_admin(
            f'⚠️ <b>Rental-заказ найден, но нет chat_id</b>\nЗаказ: <code>{_h(oid)}</code>\nLOT: <code>{lot["lot_id"]}</code>',
            cfg=cfg, kind='error'
        )
        return False

    buyer_username = str(
        _order_field(full_order, 'buyer_username')
        or _order_field(order, 'buyer_username')
        or _order_field(_order_field(event, 'chat'), 'name')
        or ''
    ).strip()

    existing = _rental_get(oid)
    if existing and existing.get('rental_id') and existing.get('status') in {'active', 'completed', 'ended'}:
        _remember_rental_contact(oid, target_chat, buyer_username)
        if existing.get('status') in {'active', 'completed'} and not existing.get('credentials_delivered'):
            _schedule(f'credentials:{oid}', _credentials_delivery_worker, cardinal, oid)
        return True

    stock = lot.get('last_stock')
    _notify_admin(
        f'🛒 <b>Новый Rental-заказ</b>\n'
        f'Заказ: <code>{_h(oid)}</code>\n'
        f'LOT: <code>{lot["lot_id"]}</code>\n'
        f'Игра: <b>{_h(lot.get("product_name"))}</b>\n'
        f'Срок: <b>{_format_duration(lot.get("duration_hours") or 0)}</b>\n'
        f'В наличии: <b>{stock if isinstance(stock, int) and stock >= 0 else "—"}</b>',
        cfg=cfg, kind='order'
    )
    logger.info('Заказ #%s · LOT %s сопоставлен · %s · chat=%s', oid, lot['lot_id'], source, target_chat)
    _schedule(f'rent-order:{oid}', _process_rental_order, cardinal, event, lot, cfg, oid, target_chat, buyer_username)
    return True

def new_order_handler(cardinal, event):
    try:
        order = _order_field(event, 'order')
        oid = _order_id(event)
        if not oid:
            logger.warning('Новый заказ без order_id пропущен.')
            return
        chat_id = _event_chat_id(event)
        extra = ' '.join(_order_text_candidates(order, event))
        if _dispatch_paid_order(cardinal, event, order, oid, chat_id=chat_id, source='new_order', extra_text=extra):
            return
        logger.info('Заказ #%s · жду системное сообщение FunPay для дополнительного сопоставления LOT.', oid)
    except Exception as e:
        logger.exception('new_order_handler error: %s', e)

def new_message_handler(cardinal, event):
    try:
        text = _event_text(event)
        match = _PAID_ORDER_RE.search(text)
        if match:
            oid = match.group(1).strip()
            chat_id = _event_chat_id(event)
            full_order = _resolve_full_order(cardinal, oid, None)
            fallback_order = full_order or {
                'id': oid,
                'chat_id': chat_id,
                'description': text,
                'title': text,
                'buyer_username': _event_author(event),
            }
            _dispatch_paid_order(cardinal, event, fallback_order, oid, chat_id=chat_id, source='paid_message', extra_text=text)
            return
        cfg = _owner_cfg(_event_chat_id(event))
        if not cfg.get('plugin_enabled', True) or not _has_provider_keys(cfg):
            return
        _review_message_handler(cardinal, event)
        _buyer_command_handler(cardinal, event)
    except Exception as e:
        logger.exception('new_message_handler error: %s', e)

BIND_TO_PRE_INIT = [init_cardinal]
BIND_TO_NEW_ORDER = [new_order_handler]
BIND_TO_NEW_MESSAGE = [new_message_handler]
BIND_TO_DELETE = None
