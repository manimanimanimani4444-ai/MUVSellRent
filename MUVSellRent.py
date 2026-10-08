"""
MUVSell Rent — плагин FunPay Cardinal: перепродажа аренды Steam-аккаунтов с muvsell.store на FunPay.

Покупатель оплачивает ваш лот на FunPay → плагин арендует аккаунт на MUVSell через API (списывает ваш
баланс MUVSell по цене сайта) и сразу присылает логин и пароль в чат. Повторная покупка той же игры
продлевает тот же аккаунт, код Steam Guard — по команде !код. Разница цен — ваш заработок.

Установка: положите файл в папку plugins/ FunPay Cardinal и перезапустите его. Настройки — в Telegram-боте
вашего FunPay Cardinal: Плагины → MUVSell Rent → Настройки (бот MUVSell для этого не нужен — он только для
привязки Telegram к аккаунту на сайте). API-ключ: muvsell.store → Профиль → API.
"""
from __future__ import annotations

import html
import json
import logging
import math
import os
import random
import re
import shutil
import threading
import time
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from typing import TYPE_CHECKING
from urllib.parse import urljoin

import requests
from telebot.types import InlineKeyboardButton as B, InlineKeyboardMarkup as K

from FunPayAPI.common.enums import MessageTypes, SubCategoryTypes
from FunPayAPI.types import LotFields
from tg_bot import CBT

if TYPE_CHECKING:
    from cardinal import Cardinal

# NAME / VERSION / DESCRIPTION / CHANGELOG / COMPAT / MAP_FILE — по одной строке: их читает сайт (/api/plugins)
NAME = "MUVSell Rent"
VERSION = "1.1.0"
DESCRIPTION = "Перепродажа аренды Steam-аккаунтов MUVSell на FunPay: автовыдача, коды Steam Guard, продления, синхронизация наличия и цен, автовыставление лотов, статистика."
CREDITS = "@MUVSell"
UUID = "ce1c0a2b-f7df-4a0d-90d3-31012b5ab720"
SETTINGS_PAGE = True
CHANGELOG = "Первая версия: автовыдача аренды MUVSell на FunPay, коды Steam Guard, продления (в том числе временным лотом по !продление), !кик, !пароль, !время, !данные, !помощь, синхронизация наличия и цен с наценкой (глобальной, по категориям и у каждой привязки), автовыставление лотов с редактором текстов, статистика и прибыль, аренды, карантин проблемных лотов, категории уведомлений, шаблоны сообщений с превью, диагностика. 1.0.1: лимит на раздел считает только лоты плагина, минимальная цена лота 1 ₽ — у дешёвых игр сроки больше не сливаются в одну цену. 1.0.2: «Создать недостающие» пересоздаёт лоты, удалённые с FunPay, и лоты, стоявшие в чужом разделе; исправлены разделы EA SPORTS FC 24 и The Forest; проблемные лоты — одним уведомлением. 1.0.3: новые стандартные тексты лотов со списком команд покупателя ({commands} собирается из настроек). 1.0.4: в «Удалить несколько» — «Отметить все» и подтверждение перед удалением. 1.0.5: в комментарий аренды на MUVSell уходит только номер заказа FunPay, без ника покупателя. 1.0.6: каждая покупка лота выдаёт новый аккаунт, продление — только командой !продление (временный лот); !друг и !прод убраны; новые тексты выдачи, предупреждения и описаний лотов — нажмите «Переписать тексты у существующих лотов», а если меняли шаблоны сами — проверьте их. 1.0.7: автовыставление в Steam «Аккаунты с играми» и в «Прочие игры» — любую игру, и ту, у которой на FunPay нет своего раздела: «Автовыставление» → «🎮 В Steam» / «🧩 В «Прочие игры»» → нажмите на игру, и она выставится на все сроки из «Длительностей» по тем же шаблонам (тип «Аренда», регион Steam настраивается); карточка игры тоже показывает сроки из «Длительностей»; при ошибке связи с MUVSell видна причина (таймаут, DNS, SSL, прокси); обновления плагина и карта разделов тоже идут через прокси из настроек. 1.0.8: в «Прочие игры» — только игры без своего раздела на FunPay (остальные выставляет обычное автовыставление). 1.0.9: свою команду для кода Steam Guard можно задать в «⚙️ Прочее» (любое слово, можно без «!») — если на !код у вас отвечает ещё и другой плагин. У каждой привязки теперь свой ID (rentM-1001): плагин сам дописывает его в конец описания лота и находит оплаченный лот по нему, а не только по названию — одинаковые или переименованные лоты больше не путаются. 1.1.0: ответы покупателю на английском — кто пишет английские команды (!code, !help, !time…), тому плагин отвечает по-английски: коды, время, продления, предупреждения и следующая выдача; в сообщении с выдачей — строка «🇬🇧 English? Type !help». Выключается в «⚙️ Прочее»."
COMPAT = "FunPay Cardinal 0.1.17.15"
MAP_FILE = "muvsell_funpay_map.json"

SITE = "https://muvsell.store"
API_BASE = SITE + "/api/v1"
INFO_URL = SITE + "/api/plugin/info"
MAP_URL = SITE + "/downloads/" + MAP_FILE
# Общие разделы: сюда реселлер сам выставляет любую игру — по кнопке, по лоту на срок (лимит FunPay — на все игры разом)
MANUAL = {"steam": (89, "Steam «Аккаунты с играми»"), "other": (451, "«Прочие игры»")}
STEAM_SUB = MANUAL["steam"][0]
MIN_HOURS, MAX_HOURS = 1, 720  # границы одной аренды или продления на MUVSell
TIMEOUT = 25
UPDATE_EVERY = 1800            # проверка обновлений плагина, сек
CREATE_DELAY = 3.0             # пауза между изменениями лотов — FunPay не любит спешку
Q_CAP = 720                    # потолок паузы проблемного лота, мин
RATE_RX = re.compile(r"много предложений|подождите|too many|слишком часто", re.I)
MISSING_RX = re.compile(r"не найден|not found|404", re.I)
TAG_RX = re.compile(r"\brentM-\d+\b", re.I)  # ID привязки последней строкой описания лота

log = logging.getLogger("FPC.muvsell_rent")
LP = "[MUVSellRent]"
DATA_DIR = os.path.join("storage", "plugins", "muvsell_rent")
SELF_PATH = os.path.abspath(__file__)
esc = html.escape

TEXTS = {  # сообщения покупателю в чат FunPay и тексты временного лота продления
    "delivery": ("🎮 {game} — аккаунт готов!\n\n"
                 "👤 Логин: {login}\n🔑 Пароль: {password}\n"
                 "⏳ Срок: {hours} ч. — до {expires}\n\n"
                 "🔐 Код Steam Guard — {guard}\n⌛ Сколько осталось — !время\n📋 Все команды — !помощь\n\n"
                 "🔄 Продлить этот аккаунт: {word} 3 — на 3 ч, {word} 2д — на 2 дня.\n"
                 "🛒 Новая покупка лота выдаст другой аккаунт. Хорошей игры! 🎯"),
    "extended": ("✅ Готово! Аренда {game} продлена на {hours} ч.\n"
                 "👤 Аккаунт тот же: {login} — вход без изменений.\n🕒 Играйте до {expires}"),
    "ext_usage": ("🔄 Как продлить: напишите {word} и срок — часы или дни.\n"
                  "Например: {word} 3 или {word} 2д\nНесколько аккаунтов? Добавьте логин: {word} 3 логин"),
    "ext_lot_ready": ("🧾 Лот для продления создан специально для вас!\n\n"
                      "🎮 {game} · +{time}\n💰 К оплате: {price} ₽\n👉 {link}\n\n"
                      "⏱ Лот доступен {minutes} мин. После оплаты время само добавится к аккаунту {login}."),
    "ext_lot_fail": ("😔 Лот для продления сейчас создать не вышло.\n"
                     "Попробуйте через пару минут — продавец уже в курсе. Покупка основного лота выдаст новый "
                     "аккаунт, а не продлит этот."),
    "review_offer": ("🎁 Небольшой подарок: оставьте отзыв на {stars}★ к этому заказу — "
                     "и мы бесплатно добавим {bonus} ч. к аренде, пока она идёт."),
    "review_bonus": "💚 Спасибо за отзыв! Аренда {login} продлена на {hours} ч. в подарок.\n🕒 Играйте до {expires}",
    "kick_ok": ("🚪 Готово — все чужие сессии на {login} закрываются (обычно до минуты).\n"
                "Аренда {game} идёт дальше, просто войдите заново."),
    "kick_fail": "⚠️ Не получилось завершить сессии {login}: {reason}",
    "pass_wait": "🔑 Меняю пароль на {login}… Новый пришлю сюда через 1–3 минуты.",
    "pass_ok": ("🔐 Пароль обновлён!\n\n🎮 {game}\n👤 Логин: {login}\n🔑 Новый пароль: {password}\n\n"
                "Срок аренды не изменился. Код Steam Guard — {guard}"),
    "pass_fail": "⚠️ Сменить пароль {login} не удалось: {reason}",
    "code": "🔐 Код Steam Guard для {login}: {code}\n⏱ Действует ещё ~{ttl} сек. — вводите сразу.",
    "code_which": "👥 У вас несколько аккаунтов — уточните логин: {cmd} логин\n{logins}",
    "code_fail": "⚠️ Код сейчас не получить — продавец уже в курсе и поможет вручную.",
    "time_left": "⌛ {game} ({login}): осталось {left} — до {expires}",
    "creds": "👤 {game}\nЛогин: {login}\nПароль: {password}\n🕒 До {expires}",
    "help": "📋 Команды для вашей аренды:\n{commands}",
    "warn": ("⏳ Аренда {game} ({login}) закончится через {left} ({expires}).\n"
             "Продлить этот же аккаунт: напишите {word} и срок, например {word} 3.\n"
             "Новая покупка лота выдаст другой аккаунт."),
    "ended": ("🏁 Аренда {game} ({login}) завершена — доступ к аккаунту закрыт.\n"
              "Спасибо, что были с нами! Понравилось — будем рады отзыву 💚"),
    "no_rental": "🔎 Не вижу у вас активной аренды. Если только что оплатили — подождите минуту и повторите.",
    "problem": "⚠️ Автовыдача не сработала — продавец уже получил уведомление и скоро всё выдаст вручную. Спасибо за терпение!",
    "ext_title_ru": "⏩ ПРОДЛЕНИЕ {game} на {time} #{tag}",
    "ext_title_en": "EXTENSION {game} for {time} #{tag}",
    "ext_desc_ru": ("Персональный лот для продления аренды {game} на {time}. После оплаты время добавится к вашему "
                    "аккаунту автоматически — логин и пароль не меняются. Лот создан по вашему запросу и исчезнет "
                    "после оплаты."),
    "ext_desc_en": ("Personal offer to extend your {game} rental for {time}. After payment the time is added to the same "
                    "account automatically - login and password stay the same. This offer was created on your request "
                    "and will be removed after payment."),
}
TEXTS_EN = {  # те же сообщения для покупателей, которые пишут английские команды (!code, !help…)
    "delivery": ("🎮 {game} — your account is ready!\n\n"
                 "👤 Login: {login}\n🔑 Password: {password}\n"
                 "⏳ Time: {hours} h — until {expires}\n\n"
                 "🔐 Steam Guard code — {guard}\n⌛ Time left — !time\n📋 All commands — !help\n\n"
                 "🔄 Extend this account: {word} 3 — for 3 h, {word} 2d — for 2 days.\n"
                 "🛒 Buying the lot again gives you a different account. Have fun! 🎯"),
    "extended": ("✅ Done! Your {game} rental is extended by {hours} h.\n"
                 "👤 Same account: {login} — log in as before.\n🕒 Play until {expires}"),
    "ext_usage": ("🔄 How to extend: type {word} and the time in hours or days.\n"
                  "For example: {word} 3 or {word} 2d\nSeveral accounts? Add the login: {word} 3 login"),
    "ext_lot_ready": ("🧾 An extension offer was created just for you!\n\n"
                      "🎮 {game} · +{time}\n💰 To pay: {price} ₽\n👉 {link}\n\n"
                      "⏱ The offer is available for {minutes} min. After payment the time is added to {login} "
                      "automatically."),
    "ext_lot_fail": ("😔 Couldn't create the extension offer right now.\n"
                     "Please try again in a couple of minutes — the seller has been notified. Buying the main lot "
                     "gives you a new account, it doesn't extend this one."),
    "review_offer": ("🎁 A small gift: leave a {stars}★ review for this order and we'll add {bonus} h to your rental "
                     "for free while it's active."),
    "review_bonus": "💚 Thanks for the review! Your {login} rental is extended by {hours} h as a gift.\n🕒 Play until {expires}",
    "kick_ok": ("🚪 Done — all other sessions on {login} are being closed (usually within a minute).\n"
                "Your {game} rental continues, just log in again."),
    "kick_fail": "⚠️ Couldn't end the sessions on {login}. Please try again later or contact the seller.",
    "pass_wait": "🔑 Changing the password on {login}… I'll send the new one here in 1–3 minutes.",
    "pass_ok": ("🔐 Password updated!\n\n🎮 {game}\n👤 Login: {login}\n🔑 New password: {password}\n\n"
                "Your rental time hasn't changed. Steam Guard code — {guard}"),
    "pass_fail": "⚠️ Couldn't change the password on {login}. The seller has been notified and will help.",
    "code": "🔐 Steam Guard code for {login}: {code}\n⏱ Valid for ~{ttl} more sec. — enter it right away.",
    "code_which": "👥 You have several accounts — please add the login: {cmd} login\n{logins}",
    "code_fail": "⚠️ Can't get the code right now — the seller has been notified and will help manually.",
    "time_left": "⌛ {game} ({login}): {left} left — until {expires}",
    "creds": "👤 {game}\nLogin: {login}\nPassword: {password}\n🕒 Until {expires}",
    "help": "📋 Commands for your rental:\n{commands}",
    "warn": ("⏳ Your {game} rental ({login}) ends in {left} ({expires}).\n"
             "To extend this account, type {word} and the time, e.g. {word} 3.\n"
             "Buying the lot again gives you a different account."),
    "ended": ("🏁 Your {game} rental ({login}) has ended — access to the account is closed.\n"
              "Thanks for choosing us! If you enjoyed it, we'd love a review 💚"),
    "no_rental": "🔎 I don't see an active rental for you. If you've just paid, wait a minute and try again.",
    "problem": "⚠️ Auto-delivery failed — the seller has been notified and will deliver manually soon. Thanks for your patience!",
}
TEXT_LABELS = {
    "delivery": "🎮 Выдача аккаунта", "extended": "🔄 Аренда продлена (после оплаты)",
    "ext_lot_ready": "🧾 Лот для продления готов", "ext_lot_fail": "❌ Лот продления создать не удалось",
    "ext_usage": "❔ Как продлить (подсказка)", "review_offer": "🎁 Предложение бонуса за отзыв",
    "review_bonus": "🎉 Бонус за отзыв начислен", "kick_ok": "🚪 Сессии Steam завершены (!кик)",
    "kick_fail": "⚠️ !кик не удался", "pass_wait": "⏳ Пароль меняется (!пароль)",
    "pass_ok": "🔐 Пароль изменён (!пароль)", "pass_fail": "⚠️ !пароль не удался",
    "code": "🔑 Код Steam Guard (!код)", "code_which": "👥 Несколько аккаунтов — уточните логин",
    "code_fail": "⚠️ Код не получен", "time_left": "⌛ Сколько осталось (!время)", "creds": "👤 Данные аккаунта (!данные)",
    "help": "📋 Список команд (!помощь)", "warn": "⏳ Аренда скоро закончится", "ended": "🏁 Аренда закончилась",
    "no_rental": "🔎 Нет активной аренды",
    "problem": "🚨 Сбой автовыдачи",
    "ext_title_ru": "🏷 Название лота продления (RU)", "ext_title_en": "🏷 Название лота продления (EN)",
    "ext_desc_ru": "🇷🇺 Описание лота продления (RU)", "ext_desc_en": "🇬🇧 Описание лота продления (EN)",
}
VAR_INFO = {  # переменная шаблона: (что это, пример для превью)
    "game": ("название игры", "Counter-Strike 2"), "login": ("логин Steam", "muv_cs2_017"),
    "password": ("пароль", "Tq8-vN4k"), "hours": ("часы", "3"), "time": ("срок словами", "3 часа"),
    "expires": ("время окончания", "01.10.2026 18:00 МСК"), "left": ("сколько осталось", "45 мин."),
    "code": ("код Steam Guard", "R7K2M"), "ttl": ("сколько секунд живёт код", "24"), "cmd": ("команда", "!код"),
    "logins": ("список логинов", "• muv_cs2_017\n• muv_cs2_042"), "minutes": ("минуты", "10"),
    "word": ("команда продления", "!продление"), "guard": ("команда кода Steam Guard", "!код"), "price": ("цена к оплате, ₽", "45"),
    "link": ("ссылка на лот", "https://funpay.com/lots/offer?id=12345678"),
    "reason": ("причина", "повторить можно через 10 мин."),
    "bonus": ("часов за отзыв", "2"), "stars": ("нужно звёзд", "5"), "commands": ("список команд (собирается сам)", ""),
    "tag": ("метка лота — обязательна, по ней плагин узнаёт оплату", "R7K2M"),
}

# шаблоны автовыставления: {game} — игра, {time} — срок
AP_TEXTS = {
    "title_ru": "{game} | Аренда Steam на {time} | Автовыдача ⚡",
    "title_en": "{game} | Steam rental {time} | Auto delivery",
    "desc_ru": ("🎮 Лицензионный Steam-аккаунт {game} в аренду на {time}.\n"
                "⚡ Логин и пароль придут в чат сами, сразу после оплаты — круглосуточно.\n"
                "🔄 Продлить тот же аккаунт — командой в чате (ниже). Новая покупка лота выдаст другой аккаунт.\n\n"
                "📋 Команды в чате заказа:\n{commands}\n\n"
                "⏳ Когда срок выйдет, доступ закроется автоматически."),
    "desc_en": ("Licensed Steam account {game} for rent for {time}. Login and password arrive in the chat automatically "
                "right after payment, 24/7. Chat commands: !code - Steam Guard code, !time - time left, "
                "!extend 3 - add 3 hours to the same account, !help - all commands. Buying the offer again gives you a new "
                "account."),
}
AP_LABELS = {"title_ru": "🇷🇺 Название (RU)", "title_en": "🇬🇧 Название (EN)",
             "desc_ru": "🇷🇺 Описание (RU)", "desc_en": "🇬🇧 Описание (EN)"}
AP_SAMPLE = ("Counter-Strike 2", 24)
EN_MIN = 140  # короче FunPay английское описание не принимает

NOTIFY_CATS = {
    "sales": ("🆕 Продажи и продления", "Новый оплаченный заказ аренды и продление."),
    "stock": ("📦 Скрытие/активация по наличию",
              "Лот скрыт, потому что аккаунты на MUVSell закончились, и снова активирован, когда они появились."),
    "balance": ("🛑 Низкий баланс MUVSell", "Лоты сняты с витрины из-за нехватки средств и возвращены после пополнения."),
    "prices": ("💰 Изменение цен", "Пересчёт цен лотов по наценке и ценам MUVSell."),
    "ended": ("⏳ Завершение аренды по сроку", "Аренда закончилась и переведена в завершённые."),
    "refunds": ("💸 Возвраты", "Возврат средств покупателю — автоматический или оформленный на FunPay."),
    "bonus": ("🎁 Бонус за отзыв", "Покупателю начислены дополнительные часы за отзыв."),
    "extend": ("🧾 Лоты продления", "Создан временный лот для оплаты продления (по команде покупателя)."),
    "quarantine": ("🚑 Проблемные лоты (карантин)", "Лот поставлен на паузу после ошибок FunPay и вылечен."),
    "commands": ("🧰 Команды покупателя", "Покупатель выбил сессии Steam («!кик») или сменил пароль («!пароль»)."),
    "errors": ("🚨 Ошибки и сбои", "Не удалось выдать аренду, создать лот, возврат не прошёл. Выключать не рекомендуется."),
}

DEFAULTS = {
    "enabled": True,
    "api_key": "",
    "pay": "rub",               # чем платить на MUVSell: rub, usd или auto (рубли, пока они есть)
    "proxy_mode": "none",       # none | fpc (прокси FunPay Cardinal) | custom
    "proxy": "",
    "markup": 50,               # глобальная наценка, %
    "cat_markup": {},           # раздел FunPay → наценка, %
    "vol_discount": True,       # считать цену от цены срока со скидкой, а не от цены часа × часы
    "fp_edit": True,            # плагин может менять цену и видимость лотов на FunPay
    "hide_no_stock": True,      # снимать лоты с продажи, пока на MUVSell нет свободных аккаунтов
    "hide_low_balance": False,  # ...и пока баланс MUVSell ниже порога
    "auto_refund": False,       # возврат на FunPay, если выдать не удалось (нет аккаунтов или баланса)
    "review_bonus": False,
    "notify_end": True,         # сообщение покупателю об окончании аренды
    "notify": {},
    "warn_min": 30,
    "ext_cmd": True,            # !продление N — временный лот на N часов
    "ext_word": "!продление",
    "code_word": "!код",        # своя команда кода Steam Guard — если на !код отвечает ещё и другой плагин
    "en_msgs": True,            # отвечать по-английски тем, кто пишет английские команды (!code, !help…)
    "ext_minutes": 10,          # сколько живёт временный лот продления
    "buyer_cmds": True,         # !кик и !пароль
    "bonus_hours": 2,
    "bonus_stars": 5,
    "balance_min": 0,
    "poll_sec": 60,
    "price_min": 5,
    "q_pause": 30,
    "q_replace": True,
    "q_unbind": True,
    "q_unbind_after": 3,
    "tz": 3,
    "min_price": 1,             # лот не дешевле, ₽ (выше — дешёвые игры на всех сроках получат одну цену)
    "lot_cap": 20,              # не больше стольких лотов плагина в одном разделе FunPay
    "texts": {},
    "ap_durations": [1, 3, 6, 12, 24, 72, 168, 336, 720],
    "ap_texts": {},
    "ap_own": None,             # своя наценка новых лотов, % (None — глобальная)
    "ap_active": True,
    "steam_region": "Россия",   # регион лотов в Steam «Аккаунты с играми» — как в списке на FunPay
}
PARAMS = {  # ключ: (подпись, пояснение, дробное ли, экран возврата)
    "markup": ("Наценка, %", "Цена лота = цена MUVSell × (1 + наценка%). Действует на привязки без своей наценки "
                             "и без наценки категории.", True, "set"),
    "warn_min": ("Предупреждать за, мин", "За сколько минут до конца аренды написать покупателю (0 — не писать).", False, "set"),
    "price_min": ("Интервал цен, мин", "Как часто сверять цены лотов с ценами MUVSell и наценкой.", False, "set"),
    "poll_sec": ("Интервал наличия, сек", "Как часто сверять наличие и баланс MUVSell (не меньше 15).", False, "set"),
    "bonus_hours": ("Бонус за отзыв, ч", "Сколько часов добавить к аренде за отзыв (оплачивается с баланса MUVSell).", False, "bn"),
    "q_pause": ("Пауза после ошибки, мин", f"Базовая пауза лота после ошибки FunPay; при повторах удваивается до {Q_CAP} мин.", False, "q"),
    "q_unbind_after": ("Отвязывать после, ошибок", "Сколько раз подряд лот должен не найтись, чтобы привязка удалилась.", False, "q"),
    "lot_cap": ("Лимит на раздел", "Не создавать больше стольких лотов плагина в одном разделе FunPay "
                                   "(ваши остальные лоты в разделе не считаются).", False, "ac"),
    "ext_minutes": ("Лот продления живёт, мин", "Сколько минут временный лот продления ждёт оплату, потом удаляется.", False, "params"),
    "balance_min": ("Порог баланса", "Ниже этого баланса MUVSell лоты снимаются с продажи (если включён стоп).", True, "params"),
    "tz": ("Часовой пояс", "Смещение от UTC для «Действует до» и статистики (3 = МСК).", False, "params"),
    "min_price": ("Мин. цена лота, ₽", "Цена лота не опустится ниже этой. Слишком высокий порог даёт дешёвым играм "
                                       "одну и ту же цену на всех сроках.", True, "params"),
}
PERIODS = {"today": "Сегодня", "yday": "Вчера", "7": "7 дней", "30": "30 дней", "90": "90 дней", "all": "Всё время"}

S: dict = {}         # настройки
MAPS: list = []      # привязки: {lot_id, subcat, titles, game_id, game, hours, auto, manual, price, markup, reprice, autohide, bonus, off}
RENT: dict = {}      # ник покупателя (нижний регистр) → [аренды]
HIDDEN: dict = {}    # lot_id → почему снят с продажи: stock | balance
DONE: list = []      # обработанные заказы FunPay
SALES: list = []     # журнал продаж: {ts, order, buyer, game_id, game, hours, lot, rid, rev, cost, kind, refunded}
PROBLEMS: dict = {}  # lot_id → {n, err, until, missing, game}
CREATED: dict = {}   # «игра:часы» (ручные разделы — «steam:игра:часы») → лот, созданный плагином (чтобы не плодить дубли)
EXT: dict = {}       # метка → временный лот продления: {lot_id, rid, buyer, chat, game_id, game, hours, price, until, map_lot}

cardinal: "Cardinal | None" = None
tg = None
bot = None
_lock = threading.RLock()
_stop = threading.Event()
_notified: dict = {}    # антиспам уведомлений
_costs: dict = {}       # (game_id, часы) → (ts, ₽)
_market: dict = {}      # раздел FunPay → (ts, [(цена, описание)])
_tmp: dict = {}         # черновики по id пользователя Telegram
_state = {"low": False, "update": None, "job": None, "job_text": "", "poll_at": 0.0, "price_at": 0.0}
_cache = {"api": None, "products": (0.0, None), "map": (0.0, None), "bal": (0.0, None), "rate": (0.0, 90.0)}


# ---------------------------------------------------------------- хранение

def _file(name: str) -> str:
    return os.path.join(DATA_DIR, name + ".json")


def _load(name: str, default):
    try:
        with open(_file(name), encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, type(default)) else default
    except FileNotFoundError:
        return default
    except Exception as e:
        log.error(f"{LP} не читается {name}.json: {e}")
        return default


def _write(name: str, data):
    with _lock:
        try:
            tmp = _file(name) + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=1)
            os.replace(tmp, _file(name))  # атомарно: обрыв посреди записи не портит файл
        except Exception as e:
            log.error(f"{LP} не сохраняется {name}.json: {e}")


def _save(name: str):
    _write(name, {"settings": S, "mappings": MAPS, "rentals": RENT, "hidden": HIDDEN,
                  "handled": DONE, "sales": SALES, "problems": PROBLEMS, "created": CREATED, "extlots": EXT}[name])


def _load_all():
    os.makedirs(DATA_DIR, exist_ok=True)
    saved = _load("settings", {})
    S.clear()
    S.update({**DEFAULTS, **saved})
    S["notify"] = {**{k: True for k in NOTIFY_CATS}, **(saved.get("notify") or {})}
    if saved.get("notify_sales") is False and "notify" not in saved:  # настройка из 1.0.x
        S["notify"]["sales"] = False
    tpl = saved.get("tpl") or {}  # шаблон мастера из 1.0.x
    if tpl and "ap_texts" not in saved:
        S["ap_texts"] = {k: tpl[k] for k in AP_TEXTS if tpl.get(k)}
        S["ap_durations"] = tpl.get("durations") or DEFAULTS["ap_durations"]
        if tpl.get("markup") is not None and "markup" not in saved:
            S["markup"] = tpl["markup"]
    if "ap_durations" not in saved:  # настройки из 1.0.x: их стандартные 15 ₽ и 10 лотов в разделе сплющивали цены
        if saved.get("min_price") == 15:
            S["min_price"] = DEFAULTS["min_price"]
        if saved.get("lot_cap") == 10:
            S["lot_cap"] = DEFAULTS["lot_cap"]
    S.pop("tpl", None)
    S.pop("friend_minutes", None)  # режим «друг» из 1.0.5: теперь каждая покупка — новый аккаунт
    S.pop("notify_sales", None)
    for key in ("texts", "cat_markup", "ap_texts"):
        S[key] = dict(S.get(key) or {})
    MAPS[:] = _load("mappings", [])
    RENT.clear()
    RENT.update(_load("rentals", {}))
    HIDDEN.clear()
    HIDDEN.update(_load("hidden", {}))
    DONE[:] = _load("handled", [])
    SALES[:] = _load("sales", [])
    PROBLEMS.clear()
    PROBLEMS.update(_load("problems", {}))
    CREATED.clear()
    CREATED.update(_load("created", {}))
    EXT.clear()
    EXT.update(_load("extlots", {}))


def _bg(fn, *args):
    """Долгое (FunPay, ожидание пароля) — в фоне, чтобы не держать обработчик сообщений Cardinal."""
    threading.Thread(target=fn, args=args, daemon=True).start()


# ---------------------------------------------------------------- мелочи

def _code_word() -> str:
    return S.get("code_word") or "!код"


def _is_cmd(text) -> bool:
    text = (text or "").strip().lower()
    return text.startswith("!") or text.partition(" ")[0] == _code_word()


def _lang(who) -> str:
    """Язык покупателя: «en», если последней он писал английскую команду (!code, !help…), иначе «ru».
    who — ник покупателя или запись аренды."""
    if not S.get("en_msgs"):
        return "ru"
    if not isinstance(who, dict):
        who = (RENT.get(str(who or "").lower()) or [{}])[-1]
    return "en" if who.get("lang") == "en" else "ru"


def _set_lang(buyer: str, cmd: str):
    lang = "en" if re.fullmatch(r"!?[a-z]+", cmd) else "ru"
    changed = [r for r in RENT.get(buyer, []) if r.get("lang", "ru") != lang]
    for r in changed:
        r["lang"] = lang
    if changed:
        _save("rentals")


def _t(key: str, lang: str = "ru", **kw) -> str:
    text = (TEXTS_EN.get(key) if lang == "en" else None) or (S.get("texts") or {}).get(key) or TEXTS[key]
    kw.setdefault("guard", "!code" if lang == "en" and _code_word() == "!код" else _code_word())
    if lang == "en":
        kw["word"] = "!extend"
    for k, v in kw.items():
        text = text.replace("{" + k + "}", str(v))
    return text


def _ts(iso) -> float:
    try:
        return datetime.fromisoformat(str(iso).replace("Z", "+00:00")).timestamp()
    except (TypeError, ValueError):
        return 0.0


def _tz():
    return timezone(timedelta(hours=int(S.get("tz", 3) or 0)))


def _when(ts: float, lang: str = "ru") -> str:
    off = int(S.get("tz", 3) or 0)
    label = ("MSK" if lang == "en" else "МСК") if off == 3 else f"UTC{off:+d}"
    return datetime.fromtimestamp(ts, _tz()).strftime("%d.%m.%Y %H:%M ") + label


def _plural(n: int, one: str, few: str, many: str) -> str:
    n1, n10 = n % 10, n % 100
    return one if n1 == 1 and n10 != 11 else few if 2 <= n1 <= 4 and not 12 <= n10 <= 14 else many


def _dur(hours: int, lang: str = "ru") -> str:
    """3 часа, 1 день, 30 дней / 3 hours, 1 day — кратное суткам всегда в днях."""
    if hours % 24 == 0:
        d = hours // 24
        return f"{d} day" + ("s" if d > 1 else "") if lang == "en" else f"{d} " + _plural(d, "день", "дня", "дней")
    return f"{hours} hour" + ("s" if hours > 1 else "") if lang == "en" else f"{hours} " + _plural(hours, "час", "часа", "часов")


def _durs(hours_list) -> str:
    return ", ".join(_dur(int(h)) for h in hours_list)


def _short(hours: int) -> str:
    return f"{hours // 24}д" if hours % 24 == 0 else f"{hours}ч"


def _parse_hours(text: str) -> list:
    """«1, 3, 24, 7д, 30 дней» → [1, 3, 24, 168, 720]; дни — с «д»/«d», остальное — часы."""
    out = set()
    for n, unit in re.findall(r"(\d+)\s*(д|d|ч|h)?", text.lower()):
        h = int(n) * (24 if unit in ("д", "d") else 1)
        if MIN_HOURS <= h <= MAX_HOURS:
            out.add(h)
    return sorted(out)


def _left(sec: float) -> str:
    m = max(0, int(sec // 60))
    d, h, m = m // 1440, m % 1440 // 60, m % 60
    return f"{d}д {h}ч" if d else f"{h}ч {m}м" if h else f"{m}м"


def _left_text(sec: float, lang: str = "ru") -> str:
    """Для покупателя: «2 дня 3 ч.», «5 ч. 10 мин.», «45 мин.» / «2 days 3 h», «45 min»."""
    m = max(1, int(sec // 60))
    d, h, m = m // 1440, m % 1440 // 60, m % 60
    en = lang == "en"
    days = f"{d} day" + ("s" if d > 1 else "") if en else f"{d} " + _plural(d, "день", "дня", "дней")
    parts = ([days] if d else []) + ([f"{h} h" if en else f"{h} ч."] if h else []) \
        + ([f"{m} min" if en else f"{m} мин."] if m and not d else [])
    return " ".join(parts)


def _num(v) -> str:
    return f"{float(v):g}"


def _rub(v) -> str:
    return f"{float(v):,.2f}".replace(",", " ").rstrip("0").rstrip(".") + "₽"


def _norm(s) -> str:
    return re.sub(r"\s+", " ", str(s or "")).strip().lower()


def _ascii(s) -> str:
    return re.sub(r"\s+", " ", re.sub(r"[^\x20-\x7E]", " ", str(s or ""))).strip()


def _onoff(v) -> str:
    return "✅" if v else "❌"


def _plugin_on() -> bool:
    p = (getattr(cardinal, "plugins", None) or {}).get(UUID)
    return getattr(p, "enabled", True)


# ---------------------------------------------------------------- API MUVSell

ERRORS = {400: "bad_request", 401: "bad_key", 402: "balance", 403: "forbidden", 404: "not_found", 409: "no_stock",
          429: "wait"}
HUMAN = {
    "bad_key": "неверный API-ключ MUVSell",
    "no_key": "API-ключ MUVSell не задан",
    "balance": "недостаточно средств на балансе MUVSell",
    "no_stock": "на MUVSell нет свободных аккаунтов",
    "not_found": "игра или аренда не найдена на MUVSell",
    "forbidden": "ключ не привязан к аккаунту или аккаунт заблокирован",
    "bad_request": "MUVSell отклонил запрос",
    "wait": "слишком часто",
    "no_account": "аренда создана, но аккаунт не выдан — выдайте вручную с сайта",
    "net": "нет связи с muvsell.store (если не проходит — включите прокси: Настройки → «Прокси MUVSell»)",
}


class Api:
    def __init__(self, key: str, proxies: dict | None = None):
        self.s = requests.Session()
        self.s.headers.update({"X-API-Key": key, "Accept": "application/json", "User-Agent": f"MUVSellRent/{VERSION}"})
        self.s.proxies.update(proxies or {})
        self.error = ""  # текст последней ошибки от сервера

    def call(self, method: str, path: str, body=None):
        """(ответ, None) или (None, код ошибки). POST после отправки не повторяем: повтор мог бы списать баланс дважды."""
        for attempt in range(3):
            try:
                r = self.s.request(method, API_BASE + path, json=body, timeout=TIMEOUT)
            except requests.RequestException as e:
                self.error = str(e)[-200:]  # причина (таймаут, DNS, SSL) — в конце текста requests
                if method != "GET" or attempt == 2:
                    return None, "net"
                time.sleep(2)
                continue
            try:
                data = r.json()
            except ValueError:
                data = {}
            if r.ok:
                self.error = ""
                return data, None
            self.error = str((data.get("error") if isinstance(data, dict) else "") or f"HTTP {r.status_code}")[:200]
            # лимит API срабатывает до обработки — повтор безопасен; 429 с объяснением — это ответ сервиса, не лимит
            if r.status_code == 429 and attempt < 2 and not re.search(r"через|уже", self.error):
                time.sleep(5)
                continue
            if r.status_code >= 500 and method == "GET" and attempt < 2:
                time.sleep(2)
                continue
            return None, ERRORS.get(r.status_code, f"http_{r.status_code}")
        return None, "net"

    def balance(self):
        return self.call("GET", "/account/balance")

    def meta(self):
        return self.call("GET", "/meta")

    def products(self):
        data, err = self.call("GET", "/rental/products")
        return (data.get("products") or [] if data else None), err

    def cost(self, game_id: str, hours: int):
        data, _ = self.call("POST", "/rental/quote", {"gameId": game_id, "durationKey": f"{hours}h", "qty": 1})
        return float(data["totalRub"]) if data and data.get("totalRub") is not None else None

    def rent(self, game_id: str, hours: int, comment: str = ""):
        return self.call("POST", "/rental/create", {"items": [{"gameId": game_id, "durationKey": f"{hours}h", "qty": 1}],
                                                    "payWith": _pay(), "comment": comment})

    def extend(self, rental_id: str, hours: int):
        return self.call("POST", f"/rental/{rental_id}/extend", {"durationKey": f"{hours}h", "payWith": _pay()})

    def rental(self, rental_id: str):
        return self.call("GET", f"/rental/{rental_id}")

    def codes(self, rental_id: str):
        return self.call("GET", f"/rental/{rental_id}/code")

    def kick(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/full-logout", {})

    def change_password(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/change-password", {})

    def terminate(self, rental_id: str):
        return self.call("POST", f"/rental/{rental_id}/terminate", {})


def _proxies() -> dict:
    mode = S.get("proxy_mode") or "none"
    if mode == "fpc":
        return dict(getattr(cardinal, "proxy", None) or {})
    p = (S.get("proxy") or "").strip()
    if mode == "custom" and p:
        p = p if "://" in p else "http://" + p
        return {"http": p, "https": p}
    return {}


def _api() -> "Api | None":
    key = S.get("api_key") or ""
    if not key:
        return None
    px = _proxies()
    sig = key + json.dumps(px, sort_keys=True)
    if not _cache["api"] or _cache["api"][0] != sig:
        _cache["api"] = (sig, Api(key, px))
    return _cache["api"][1]


def _human(err, api=None) -> str:
    text = HUMAN.get(err, err or "неизвестная ошибка")
    detail = getattr(api, "error", "")
    return f"{text}: {detail}" if detail else text


def _balance(force: bool = False):
    """Баланс MUVSell (кэш 1 мин) или None."""
    ts, data = _cache["bal"]
    api = _api()
    if api and (force or data is None or time.time() - ts > 60):
        fresh, _ = api.balance()
        if fresh:
            _cache["bal"] = (time.time(), fresh)
            data = fresh
    return data


def _pay() -> str:
    mode = S.get("pay", "rub")
    if mode != "auto":
        return mode
    bal = _balance() or {}
    return "rub" if float(bal.get("balanceRub") or 0) > 0 else "usd"


def _usd_rate() -> float:
    ts, rate = _cache["rate"]
    api = _api()
    if api and time.time() - ts > 3600:
        data, _ = api.meta()
        rate = float((data or {}).get("usdRateRub") or rate)
        _cache["rate"] = (time.time(), rate)
    return rate


def _to_rub(amount, currency) -> float:
    name = str(getattr(currency, "name", currency or "RUB")).upper()
    if name in ("RUB", "UNKNOWN", "NONE", "₽"):
        return float(amount or 0)
    return float(amount or 0) * _usd_rate() * (1.08 if name == "EUR" else 1)  # ponytail: EUR ≈ USD × 1.08


def _products(force: bool = False):
    """Каталог MUVSell (кэш 5 мин). None — нет ключа или связи."""
    api = _api()
    if not api:
        return None
    ts, data = _cache["products"]
    if force or data is None or time.time() - ts > 300:
        fresh, _ = api.products()
        if fresh is not None:
            _cache["products"] = (time.time(), fresh)
            data = fresh
    return data


def _cost(api: Api, prod: dict, hours: int) -> float:
    """База цены: стоимость срока на MUVSell, ₽ (со скидкой за объём или без неё)."""
    if not S.get("vol_discount") and prod.get("pricePerHourRub") is not None:
        return round(float(prod["pricePerHourRub"]) * hours, 2)
    for p in prod.get("prices") or []:
        if p.get("hours") == hours and p.get("priceRub") is not None:
            return float(p["priceRub"])
    hit = _costs.get((prod["id"], hours))
    if hit and time.time() - hit[0] < 900:
        return hit[1]
    rub = api.cost(prod["id"], hours) if api else None
    if rub is None:
        rub = round(float(prod.get("pricePerHourRub") or 0) * hours, 2)
    _costs[(prod["id"], hours)] = (time.time(), rub)
    return rub


def _markup(m: dict | None = None) -> float:
    """Наценка: своя у привязки → категории (раздела FunPay) → глобальная."""
    m = m or {}
    if m.get("markup") is not None:
        return float(m["markup"])
    cat = (S.get("cat_markup") or {}).get(str(m.get("subcat")))
    return float(cat if cat is not None else S.get("markup") or 0)


def _markup_src(m: dict) -> str:
    if m.get("markup") is not None:
        return "своя"
    return "категория" if str(m.get("subcat")) in (S.get("cat_markup") or {}) else "глобальная"


def _price(api, prod: dict, hours: int, m: dict | None = None) -> int:
    value = _cost(api, prod, hours) * (1 + _markup(m) / 100)
    return int(math.ceil(max(float(S.get("min_price") or 1), value)))


def _auto_price(m: dict) -> bool:
    return bool(m.get("reprice", m.get("auto")))


def _hide_on(m: dict) -> bool:
    return bool(S.get("hide_no_stock") if m.get("autohide") is None else m["autohide"])


def _bonus_on(m: dict | None) -> bool:
    return bool(S.get("review_bonus") if not m or m.get("bonus") is None else m["bonus"])


# ---------------------------------------------------------------- FunPay и Telegram

def _send(chat_id, text: str):
    if cardinal and chat_id and text:
        try:
            cardinal.send_message(chat_id, text, watermark=False)
        except Exception as e:
            log.error(f"{LP} сообщение в чат {chat_id} не отправлено: {e}")


def _notify(text: str, order_id=None, dedup: "str | None" = None, kb=None, cat: str = "errors"):
    """Сообщение админам FPC в Telegram. dedup — одно и то же не чаще раза в минуту; cat — категория уведомлений."""
    if dedup:
        if time.time() - _notified.get(dedup, 0) < 60:
            return
        _notified[dedup] = time.time()
    log.info(f"{LP} {re.sub('<[^>]+>', '', text)}")
    if not bot or not (S.get("notify") or {}).get(cat, True):
        return
    if order_id and kb is None:
        kb = K().add(B("🔗 Открыть заказ", url=f"https://funpay.com/orders/{order_id}/"))
    for uid in list(tg.authorized_users):
        try:
            bot.send_message(uid, f"<b>{NAME}</b>\n{text}", parse_mode="HTML", reply_markup=kb,
                             disable_web_page_preview=True)
        except Exception:
            pass


def _mlabel(m: dict) -> str:
    return f"{m.get('game', '?')} {_short(int(m.get('hours') or 0))}"


# ---------------------------------------------------------------- лоты FunPay и карантин

class _RateLimited(Exception):
    pass


def _fp_error(e) -> str:
    errors = getattr(e, "errors", None) or {}
    return "; ".join(f"{k}: {v}" for k, v in errors.items()) or str(getattr(e, "error_message", "") or e)[:160]


_qbuf: list = []  # события карантина — уходят админу одним сообщением (_flush_q), а не по штуке на лот


def _q_note(text: str):
    with _lock:
        _qbuf.append(text)


def _flush_q():
    with _lock:
        items = list(_qbuf)
        _qbuf.clear()
    if not items:
        return
    hint = ("\n\nЛот удалили на FunPay? «🤖 Автовыставление → 🚀 Создать недостающие» создаст его заново."
            if any("не найден" in t or "пропал" in t for t in items) else "")
    _notify("🚑 <b>Проблемные лоты</b>\n" + "\n".join(f"• {t}" for t in items[:20])
            + (f"\n…и ещё {len(items) - 20}" if len(items) > 20 else "") + hint, cat="quarantine")


def _lot_do(m: dict, fn):
    """Операция с лотом FunPay через карантин: лот на паузе не трогаем, ошибка ставит его на паузу.
    → результат fn(lot_fields) или None."""
    lid = str(m["lot_id"])
    p = PROBLEMS.get(lid)
    if p and p.get("until", 0) > time.time():
        return None
    try:
        res = fn(cardinal.account.get_lot_fields(int(lid)))
    except Exception as e:
        if RATE_RX.search(_fp_error(e)):
            raise _RateLimited(_fp_error(e))
        _lot_failed(m, e)
        return None
    if p:
        with _lock:
            PROBLEMS.pop(lid, None)
        _save("problems")
        _q_note(f"✅ <code>{lid}</code> {esc(_mlabel(m))} — снова в порядке")
    return res


def _lot_failed(m: dict, e):
    lid, err = str(m["lot_id"]), (_fp_error(e) or str(e))[:200]
    missing = bool(MISSING_RX.search(err))
    with _lock:
        p = PROBLEMS.setdefault(lid, {"n": 0, "game": _mlabel(m)})
        p.update(n=p["n"] + 1, err=err, missing=missing, at=time.time())
        p["until"] = time.time() + min(float(S.get("q_pause") or 30) * 2 ** (p["n"] - 1), Q_CAP) * 60
    _save("problems")
    if missing and S.get("q_replace") and _replace_lot(m):
        return
    if missing and S.get("q_unbind") and p["n"] >= int(S.get("q_unbind_after") or 3):
        with _lock:
            MAPS[:] = [x for x in MAPS if x is not m]
            PROBLEMS.pop(lid, None)
            HIDDEN.pop(lid, None)
        for name in ("mappings", "problems", "hidden"):
            _save(name)
        return _q_note(f"🗑 <code>{lid}</code> {esc(_mlabel(m))} — пропал с FunPay, привязка удалена")
    if p["n"] == 1:
        _q_note(f"⏸ <code>{lid}</code> {esc(_mlabel(m))} — пауза {_left(p['until'] - time.time())}: {esc(err)}")


def _replace_lot(m: dict) -> bool:
    """Лот пропал — ищем среди ваших лотов раздела такой же по названию и перепривязываем."""
    try:
        lots = cardinal.account.get_my_subcategory_lots(int(m["subcat"]))
    except Exception:
        return False
    titles, taken = {_norm(t) for t in m.get("titles") or [] if t}, {str(x["lot_id"]) for x in MAPS}
    new = next((lot for lot in lots if _norm(lot.description) in titles and str(lot.id) not in taken), None)
    if not new:
        return False
    old = str(m["lot_id"])
    with _lock:
        m["lot_id"] = str(new.id)
        m["tagged"] = False  # у нового лота ID в описании ещё нет
        PROBLEMS.pop(old, None)
        if old in HIDDEN:
            HIDDEN[str(new.id)] = HIDDEN.pop(old)
    for name in ("mappings", "problems", "hidden"):
        _save(name)
    _q_note(f"🔁 <code>{old}</code> {esc(_mlabel(m))} — пропал, привязка перенесена на такой же лот <code>{new.id}</code>")
    return True


def _set_active(m: dict, active: bool) -> bool:
    def go(lf):
        if lf.active != active:
            lf.active = active
            cardinal.account.save_lot(lf)
        return True
    return bool(_lot_do(m, go))


def _set_price(m: dict, price: int):
    """→ "same" | "set" | None (не вышло)."""
    def go(lf):
        if lf.price is not None and abs(lf.price - price) < 0.01:
            return "same"
        lf.price = price
        cardinal.account.save_lot(lf)
        return "set"
    res = _lot_do(m, go)
    if res:
        m["price"] = price
    return res


# ---------------------------------------------------------------- привязки

def _map_by_lot(lot_id):
    return next((m for m in MAPS if str(m.get("lot_id")) == str(lot_id)), None)


def _lot_info(lot_id):
    """(раздел, [название RU, название EN]) лота FunPay."""
    lf = cardinal.account.get_lot_fields(int(lot_id))
    sub = getattr(lf.subcategory, "id", None) or int(lf.fields.get("node_id") or 0) or None
    return sub, [t for t in (lf.title_ru, lf.title_en) if t]


def _refresh_titles(sub):
    """Продавец мог переименовать лот — перечитываем названия лотов раздела."""
    changed = False
    for m in MAPS:
        if str(m.get("subcat")) != str(sub):
            continue
        try:
            _, titles = _lot_info(m["lot_id"])
        except Exception as e:
            log.warning(f"{LP} лот {m['lot_id']} не читается: {e}")
            continue
        if titles and titles != m.get("titles"):
            m["titles"] = titles
            changed = True
    if changed:
        _save("mappings")


def _match_tag(order):
    """Привязка по ID в описании оплаченного лота (rentM-1001) — надёжнее названия: его могут изменить или повторить."""
    sub = getattr(getattr(order, "subcategory", None), "id", None)
    if not any(m.get("tag") and (not sub or not m.get("subcat") or str(m["subcat"]) == str(sub)) for m in MAPS):
        return None
    try:
        desc = str(getattr(cardinal.account.get_order(order.id), "full_description", "") or "")
    except Exception as e:
        log.warning(f"{LP} заказ {order.id} не читается, ищу по названию: {e}")
        return None
    tags = {t.lower() for t in TAG_RX.findall(desc)}
    return next((m for m in MAPS if str(m.get("tag", "")).lower() in tags), None)


def _match(order) -> list:
    """Привязка по ID в описании лота, иначе — чьё название лота есть в описании заказа
    (самое длинное совпадение, тот же раздел)."""
    tagged = _match_tag(order)
    if tagged:
        return [tagged]
    sub = getattr(getattr(order, "subcategory", None), "id", None)
    desc = _norm(getattr(order, "description", ""))

    def find():
        scored = []
        for m in MAPS:
            if sub and m.get("subcat") and str(m["subcat"]) != str(sub):
                continue
            n = max((len(t) for t in map(_norm, m.get("titles") or []) if t and t in desc), default=0)
            if n:
                scored.append((n, m))
        top = max((n for n, _ in scored), default=0)
        found = [m for n, m in scored if n == top]
        # одинаковые названия у лотов одной игры и срока — выдать можно любым из них
        return found[:1] if len({(m["game_id"], int(m["hours"])) for m in found}) == 1 else found

    found = find()
    if not found and sub and any(str(m.get("subcat")) == str(sub) for m in MAPS):
        _refresh_titles(sub)
        found = find()
    return found


# ---------------------------------------------------------------- журнал продаж

def _sale(kind: str, rec: dict, hours: int, cost: float, order=None, refunded: bool = False):
    oid = getattr(order, "id", None)
    rev = 0.0
    if order is not None and not any(s.get("order") == oid for s in SALES):  # выручка заказа — один раз
        rev = _to_rub(getattr(order, "price", 0) or 0, getattr(order, "currency", None))
    with _lock:
        SALES.append({"ts": time.time(), "order": oid, "buyer": (getattr(order, "buyer_username", None)
                                                                 or rec.get("buyer") or ""),
                      "game_id": rec.get("game_id", ""), "game": rec.get("game", "?"), "hours": int(hours or 0),
                      "lot": rec.get("lot"), "rid": rec.get("id"), "rev": round(rev, 2), "cost": round(float(cost or 0), 2),
                      "kind": kind, "refunded": refunded})
        del SALES[:-20000]
    _save("sales")


# ---------------------------------------------------------------- аренды

def _active(buyer: str) -> list:
    now = time.time()
    return [r for r in RENT.get(buyer, []) if r.get("exp", 0) > now]


def _all_active() -> list:
    now = time.time()
    return sorted((r for lst in list(RENT.values()) for r in lst if r.get("exp", 0) > now), key=lambda r: r["exp"])


def _rec(rid: str):
    return next((r for lst in list(RENT.values()) for r in lst if str(r.get("id")) == str(rid)), None)


def _add_hours(api: Api, rec: dict, hours: int):
    """Продлевает аренду порциями по ≤720 ч. → (сколько часов добавлено, ошибка, стоимость ₽)."""
    added, cost, err = 0, 0.0, None
    while added < hours:
        step = min(hours - added, MAX_HOURS)
        data, err = api.extend(rec["id"], step)
        if err:
            break
        rec["exp"] = _ts(data.get("endsAt")) or rec["exp"]
        cost += float(data.get("cost") or 0)
        added += step
    if added:
        rec["warned"] = False
        _save("rentals")
    return added, err, cost


def _new_rental(api: Api, m: dict, order, hours: int):
    """Арендует аккаунт на MUVSell и выдаёт покупателю. → (запись аренды, None) или (None, ошибка)."""
    buyer = order.buyer_username or ""
    first = min(hours, MAX_HOURS)
    data, err = api.rent(m["game_id"], first, f"FunPay #{order.id}")  # ник покупателя на MUVSell не шлём — чужие ПДн
    if err:
        return None, err
    rental = data.get("rental") or {}
    acc = next((a for it in rental.get("items") or [] for a in it.get("accounts") or []), None)
    if not acc:
        return None, "no_account"
    rec = {"id": rental["id"], "number": rental.get("number"), "game_id": m["game_id"], "game": m["game"],
           "login": acc.get("login", ""), "exp": _ts(rental.get("endsAt")), "order": order.id, "buyer": buyer,
           "chat": order.chat_id, "lot": m.get("lot_id"), "bonus": False, "ended": False, "lang": _lang(buyer)}
    with _lock:
        RENT.setdefault(buyer.lower(), []).append(rec)
    _save("rentals")
    extra, err, extra_cost = _add_hours(api, rec, hours - first)  # больше 720 ч за раз MUVSell не выдаёт — докупаем продлением
    if err:
        _notify(f"⚠️ Выдано {first + extra} ч из {hours}: продление не прошло — {esc(_human(err, api))}", order.id)
    _sale("new", rec, first + extra, float(rental.get("totalRub") or 0) + extra_cost, order)
    lang = rec["lang"]
    hint = "\n\n🇬🇧 English? Type !help" if lang == "ru" and S.get("en_msgs") else ""
    _send(order.chat_id, _t("delivery", lang, game=m["game"], login=rec["login"], password=acc.get("password", ""),
                            hours=first + extra, expires=_when(rec["exp"], lang),
                            word=S.get("ext_word") or "!продление") + hint)
    if _bonus_on(m) and sum(1 for s in SALES if s.get("order") == order.id) == 1:  # одно предложение на заказ
        _send(order.chat_id, _t("review_offer", lang, bonus=S.get("bonus_hours"), stars=S.get("bonus_stars")))
    _notify(f"✅ Выдан <code>{esc(rec['login'])}</code> — {esc(m['game'])}, {first + extra} ч → "
            f"<b>{esc(buyer)}</b> (аренда №{rec['number']})", order.id, cat="sales")
    return rec, None


def _extend(api: Api, rec: dict, hours: int, chat_id, order=None, text: str = "extended", kind: str = "ext"):
    """Продлевает аренду, пишет покупателю и заносит в журнал. → None или код ошибки (если не продлено ни часа).
    order — заказ FunPay (его выручка попадёт в статистику) или просто номер заказа для ссылки."""
    order_id = getattr(order, "id", order)
    added, err, cost = _add_hours(api, rec, hours)
    if not added:
        return err
    if err:
        _notify(f"⚠️ Продлено {added} ч из {hours} — {esc(_human(err, api))}", order_id)
    _sale(kind, rec, added, cost, None if isinstance(order, (str, type(None))) else order)
    lang = _lang(rec)
    _send(chat_id, _t(text, lang, login=rec["login"], game=rec["game"], hours=added, expires=_when(rec["exp"], lang)))
    if kind == "ext":
        _notify(f"✅ Продлён <code>{esc(rec['login'])}</code> — {esc(rec['game'])}, +{added} ч", order_id, cat="sales")
    return None


def _fail(order, err, api=None, m=None):
    _send(order.chat_id, _t("problem", _lang(order.buyer_username)))
    refund = bool(S.get("auto_refund")) and err in ("no_stock", "balance")
    _notify(f"❌ Не удалось выдать аренду: {esc(_human(err, api))}" + ("\n💸 Оформляю возврат." if refund else ""),
            order.id)
    if refund:
        try:
            cardinal.account.refund(order.id)
        except Exception as e:
            return _notify(f"⚠️ Возврат не прошёл: <code>{esc(str(e)[:200])}</code>", order.id)
        if m:
            _sale("new", {"game_id": m["game_id"], "game": m["game"], "lot": m.get("lot_id")}, m["hours"], 0, order, True)
        _notify(f"💸 Возврат по заказу #{order.id} оформлен.", order.id, cat="refunds")


def _process(order):
    found = _match(order)
    if not found:
        return  # не наш лот — обычный заказ FunPay
    if len(found) > 1:
        _send(order.chat_id, _t("problem", _lang(order.buyer_username)))
        return _notify("⚠️ Заказ подходит под несколько привязок с разными играми или сроками — выдайте вручную и "
                       "сделайте названия лотов разными:\n" + "\n".join(f"• {esc(_mlabel(m))} — лот {m['lot_id']}"
                                                                          for m in found), order.id)
    m = found[0]
    api = _api()
    if not api:
        return _fail(order, "no_key", None, m)
    buyer = (order.buyer_username or "").lower()
    qty = max(1, int(order.amount or 1))
    log.info(f"{LP} заказ {order.id}: {m['game']} × {qty}, {m['hours']} ч за шт, покупатель {buyer}")

    # Каждая покупка — новый аккаунт, количество — часы на нём. Продлить свой аккаунт покупатель может
    # только командой продления (временный лот, _pay_ext).
    rec, err = _new_rental(api, m, order, int(m["hours"]) * qty)
    if not rec:
        _fail(order, err, api, m)


def on_new_order(c: "Cardinal", event):
    if not S.get("enabled"):
        return
    order = event.order
    with _lock:
        if order.id in DONE:
            return
        DONE.append(order.id)
        del DONE[:-500]
    _save("handled")
    try:
        ext = _ext_for(order)
        if ext:
            return _pay_ext(order, *ext)
        _process(order)
    except Exception as e:
        log.exception(f"{LP} заказ {order.id}")
        _send(order.chat_id, _t("problem", _lang(getattr(order, "buyer_username", ""))))
        _notify(f"⚠️ Ошибка при обработке заказа: <code>{esc(str(e)[:200])}</code>", order.id)


def on_order_status_changed(c: "Cardinal", event):
    """Возврат на FunPay (вручную или автоматически) — отмечаем в статистике."""
    order = event.order
    if str(getattr(getattr(order, "status", None), "name", "")) not in ("REFUNDED", "PARTIALLY_REFUNDED"):
        return
    try:
        hit = [s for s in SALES if s.get("order") == order.id]
        if hit and all(s.get("refunded") for s in hit):
            return
        if hit:
            for s in hit:
                s["refunded"] = True
            _save("sales")
        elif order.id in DONE:
            found = _match(order)
            m = found[0] if found else {"game_id": "", "game": "?", "hours": 0}
            _sale("new", {"game_id": m["game_id"], "game": m["game"], "lot": m.get("lot_id")}, m["hours"], 0, order, True)
        else:
            return
        _notify(f"↩️ Возврат по заказу #{order.id} ({esc(order.buyer_username or '')}).", order.id, cat="refunds")
    except Exception:
        log.exception(f"{LP} статус заказа")


# ---------------------------------------------------------------- команды покупателя и отзывы

def _guard(api: Api, rec: dict):
    data, _ = api.codes(rec["id"])
    return next((c for c in (data or {}).get("codes") or []
                 if str(c.get("login", "")).lower() == rec["login"].lower()), None)


def _pick_rec(chat_id, buyer: str, arg: str, cmd: str):
    rs, lang = [r for r in _active(buyer) if not arg or r["login"].lower() == arg.lower()], _lang(buyer)
    if not rs:
        return _send(chat_id, _t("no_rental", lang))
    if len(rs) > 1:
        if lang == "en":
            cmd = {"!код": "!code", "!кик": "!kick", "!пароль": "!password"}.get(cmd, "!extend 3" if cmd.endswith(" 3") else cmd)
        return _send(chat_id, _t("code_which", lang, cmd=cmd, logins="\n".join(f"• {r['login']}" for r in rs)))
    return rs[0]


def _cmd_code(chat_id, buyer: str, arg: str):
    rec = _pick_rec(chat_id, buyer, arg, _code_word())
    if not rec:
        return
    api = _api()
    code = _guard(api, rec) if api else None
    if code and int(code.get("expiresIn") or 30) < 5:  # код вот-вот сменится — ждём свежий
        time.sleep(int(code["expiresIn"]) + 1)
        code = _guard(api, rec)
    if not code:
        _send(chat_id, _t("code_fail", _lang(buyer)))
        return _notify(f"⚠️ Не удалось получить код Steam Guard для <code>{esc(rec['login'])}</code>: "
                       f"{esc(_human('no_key') if not api else api.error or 'у аккаунта нет maFile')}", rec.get("order"),
                       dedup=f"code:{rec['id']}")
    _send(chat_id, _t("code", _lang(buyer), login=rec["login"], code=code["code"], ttl=code.get("expiresIn", 30)))


_ext_busy: set = set()  # аренды, для которых сейчас создаётся лот продления


def _ext_texts(game: str, hours: int, tag: str):
    """Название и описание временного лота продления. Метка #tag — в конце названия: по ней узнаём оплату."""
    def title(key, lang):
        text = _t(key, game=game, time=_dur(hours, lang), hours=hours, tag=tag).replace(f"#{tag}", "")
        text = _ascii(text) if lang == "en" else re.sub(r"\s+", " ", text).strip()
        return text[:100 - len(tag) - 2].rstrip() + f" #{tag}"
    fill = dict(game=game, hours=hours, tag=tag)
    desc_en = _ascii(_t("ext_desc_en", time=_dur(hours, "en"), **fill))
    if len(desc_en) < EN_MIN:
        desc_en = _ascii(f"{desc_en} " + TEXTS["ext_desc_en"].replace("{game}", game).replace("{time}", _dur(hours, "en")))
    return title("ext_title_ru", "ru"), title("ext_title_en", "en"), _t("ext_desc_ru", time=_dur(hours), **fill), desc_en


def _ext_ready(rec: dict, e: dict) -> str:
    lang = _lang(rec)
    return _t("ext_lot_ready", lang, game=rec["game"], login=rec["login"], time=_dur(int(e["hours"]), lang),
              hours=e["hours"], price=e["price"], link=f"https://funpay.com/lots/offer?id={e['lot_id']}",
              minutes=max(1, math.ceil((e["until"] - time.time()) / 60)))


def _drop_ext(tag: str):
    with _lock:
        e = EXT.pop(tag, None)
    _save("extlots")
    if e:
        try:
            cardinal.account.delete_lot(int(e["lot_id"]))
        except Exception as err:
            log.warning(f"{LP} лот продления {e['lot_id']} не удалён: {err}")


def _ext_cleanup():
    for tag in [t for t, e in list(EXT.items()) if e.get("until", 0) < time.time()]:
        _drop_ext(tag)


def _cmd_ext_lot(chat_id, buyer: str, arg: str):
    """!продление [срок] [логин] — создаёт временный лот на этот срок; оплата продлевает ту же аренду."""
    word = S.get("ext_word") or "!продление"
    words = arg.split()
    spans = [w for w in words if re.fullmatch(r"\d+[дdчh]?", w.lower())]
    rec = _pick_rec(chat_id, buyer, next((w for w in words if w not in spans), ""), f"{word} 3")
    if not rec:
        return
    m = _map_by_lot(rec.get("lot")) or next((x for x in MAPS if x["game_id"] == rec["game_id"]), None)
    hours = _one_hours(spans[0]) if spans else int((m or {}).get("hours") or 0)
    if not hours:
        return _send(chat_id, _t("ext_usage", _lang(buyer), word=word))
    same = next((e for e in EXT.values() if e["rid"] == rec["id"] and int(e["hours"]) == hours
                 and e["until"] > time.time() + 60), None)
    if same:  # лот на этот срок уже ждёт оплату — повторяем ссылку
        return _send(chat_id, _ext_ready(rec, same))
    _bg(_make_ext_lot, chat_id, buyer, rec, m, hours)


def _make_ext_lot(chat_id, buyer: str, rec: dict, m, hours: int):
    if rec["id"] in _ext_busy:
        return
    _ext_busy.add(rec["id"])
    try:
        for tag in [t for t, e in list(EXT.items()) if e["rid"] == rec["id"]]:  # старый лот на другой срок — убираем
            _drop_ext(tag)
        api, g = _api(), _fp_game(rec["game_id"])
        prod = next((p for p in _products() or [] if p["id"] == rec["game_id"]), None)
        sub = (m or {}).get("subcat") or ((g or {}).get("funpay") or {}).get("subcategory_id")
        lot_id, err, price, tag = None, "нет раздела FunPay или игры в каталоге MUVSell", 0, ""
        if api and prod and sub:
            price = _price(api, prod, hours, m or {"subcat": sub})
            tag = "".join(random.choices("ABCDEFGHJKLMNPQRSTUVWXYZ23456789", k=5))
            try:
                lot_id, err = _create_lot(int(sub), ((g or {}).get("funpay") or {}).get("fields"), rec["game"],
                                          _ext_texts(rec["game"], hours, tag), price, True, 1)
            except Exception as e:
                err = _fp_error(e)
        if not lot_id:
            _send(chat_id, _t("ext_lot_fail", _lang(buyer)))
            return _notify(f"❌ Лот продления для <b>{esc(buyer)}</b> ({esc(rec['game'])}, {_dur(hours)}) не создан: "
                           f"{esc(str(err))}", rec.get("order"))
        e = {"lot_id": str(lot_id), "rid": rec["id"], "buyer": buyer, "chat": chat_id, "game_id": rec["game_id"],
             "game": rec["game"], "hours": hours, "price": price, "map_lot": (m or {}).get("lot_id"),
             "until": time.time() + max(1, int(S.get("ext_minutes") or 10)) * 60}
        with _lock:
            EXT[tag] = e
        _save("extlots")
        _send(chat_id, _ext_ready(rec, e))
        _notify(f"🧾 Лот продления для <b>{esc(buyer)}</b>: {esc(rec['game'])} +{_dur(hours)} за {price}₽ "
                f"(лот <code>{lot_id}</code>).", rec.get("order"), cat="extend")
    finally:
        _ext_busy.discard(rec["id"])


def _ext_for(order):
    """Заказ временного лота продления → (метка, лот) или None."""
    desc = str(getattr(order, "description", "") or "")
    return next(((tag, e) for tag, e in list(EXT.items()) if re.search(rf"#{tag}\b", desc, re.I)), None)


def _pay_ext(order, tag: str, e: dict):
    _bg(_drop_ext, tag)  # лот больше не нужен
    with _lock:
        EXT.pop(tag, None)  # сразу, чтобы второй заказ того же лота не продлил дважды
    api = _api()
    hours = int(e["hours"]) * max(1, int(order.amount or 1))
    rec = _rec(e["rid"])
    m = _map_by_lot(e.get("map_lot")) or {"game_id": e["game_id"], "game": e["game"], "lot_id": None, "hours": e["hours"]}
    if not api:
        return _fail(order, "no_key", None, m)
    if rec and rec.get("exp", 0) > time.time():
        err = _extend(api, rec, hours, order.chat_id, order)
        if not err:
            return
        if err not in ("bad_request", "not_found"):
            return _fail(order, err, api, m)
        rec["exp"] = 0
        _save("rentals")
    new, err = _new_rental(api, m, order, hours)  # аренда уже закончилась — выдаём аккаунт на оплаченное время
    if not new:
        _fail(order, err, api, m)


def _cmd_kick(chat_id, buyer: str, arg: str):
    rec = _pick_rec(chat_id, buyer, arg, "!кик")
    api = _api()
    if not rec or not api:
        return
    _, err = api.kick(rec["id"])
    if err:
        return _send(chat_id, _t("kick_fail", _lang(buyer), login=rec["login"], reason=api.error or _human(err)))
    _send(chat_id, _t("kick_ok", _lang(buyer), login=rec["login"], game=rec["game"]))
    _notify(f"🚪 <b>{esc(buyer)}</b> выкинул сессии <code>{esc(rec['login'])}</code>.", rec.get("order"), cat="commands")


def _cmd_time(chat_id, buyer: str):
    rs, lang = _active(buyer), _lang(buyer)
    if not rs:
        return _send(chat_id, _t("no_rental", lang))
    _send(chat_id, "\n".join(_t("time_left", lang, game=r["game"], login=r["login"],
                                left=_left_text(r["exp"] - time.time(), lang), expires=_when(r["exp"], lang))
                             for r in rs))


def _cmd_creds(chat_id, buyer: str, arg: str):
    rs, lang = [r for r in _active(buyer) if not arg or r["login"].lower() == arg.lower()], _lang(buyer)
    if not rs:
        return _send(chat_id, _t("no_rental", lang))
    api = _api()
    for r in rs:
        pw = _acc_of(api.rental(r["id"])[0], r["login"]).get("password") if api else None
        _send(chat_id, _t("creds", lang, game=r["game"], login=r["login"],
                          password=pw or ("— ask the seller" if lang == "en" else "— напишите продавцу"),
                          expires=_when(r["exp"], lang)))


def _commands_text(lang: str = "ru") -> str:
    if lang == "en":
        lines = [f"• {'!code' if _code_word() == '!код' else _code_word()} — Steam Guard code", "• !time — time left",
                 "• !data — login and password again"]
        if S.get("ext_cmd"):
            lines.append("• !extend 3 — extend this account by 3 h (or !extend 2d — by 2 days)")
        if S.get("buyer_cmds"):
            lines += ["• !kick — kick everyone else out of the account", "• !password — change the password"]
        return "\n".join(lines)
    word = S.get("ext_word") or "!продление"
    lines = [f"• {_code_word()} — код Steam Guard", "• !время — сколько осталось", "• !данные — логин и пароль ещё раз"]
    if S.get("ext_cmd"):
        lines.append(f"• {word} 3 — продлить этот аккаунт на 3 ч (или {word} 2д — на 2 дня)")
    if S.get("buyer_cmds"):
        lines += ["• !кик — выкинуть всех чужих из аккаунта", "• !пароль — сменить пароль"]
    return "\n".join(lines)


def _acc_of(data, login: str) -> dict:
    rental = (data or {}).get("rental") or {}
    return next((a for it in rental.get("items") or [] for a in it.get("accounts") or []
                 if str(a.get("login", "")).lower() == login.lower()), {})


def _change_password(api: Api, rec: dict, chat_id) -> "str | None":
    """Запускает смену пароля и в фоне ждёт новый, чтобы прислать покупателю. → текст ошибки или None."""
    lang = _lang(rec)
    old = _acc_of(api.rental(rec["id"])[0], rec["login"]).get("password")
    _, err = api.change_password(rec["id"])
    if err:
        reason = api.error or _human(err)
        _send(chat_id, _t("pass_fail", lang, login=rec["login"], reason=reason))
        return reason
    _send(chat_id, _t("pass_wait", lang, login=rec["login"]))

    def wait():
        for _ in range(30):
            if _stop.wait(10):
                return
            pw = _acc_of(api.rental(rec["id"])[0], rec["login"]).get("password")
            if pw and pw != old:
                _send(chat_id, _t("pass_ok", lang, game=rec["game"], login=rec["login"], password=pw))
                return _notify(f"🔑 Пароль <code>{esc(rec['login'])}</code> сменён, новый отправлен покупателю.",
                               rec.get("order"), cat="commands")
        _send(chat_id, _t("pass_fail", lang, login=rec["login"], reason="смена затянулась, продавец уже уведомлён"))
        _notify(f"⚠️ Смена пароля <code>{esc(rec['login'])}</code> не завершилась за 5 минут — проверьте на сайте.",
                rec.get("order"))
    _bg(wait)
    return None


def _cmd_password(chat_id, buyer: str, arg: str):
    rec, api = _pick_rec(chat_id, buyer, arg, "!пароль"), _api()
    if rec and api:
        _change_password(api, rec, chat_id)


def _cmd_help(chat_id, buyer: str, arg: str):
    lang = _lang(buyer)
    _send(chat_id, _t("help", lang, commands=_commands_text(lang)))


COMMANDS = [  # (синонимы, обработчик(chat_id, buyer, arg), включена ли)
    (("!код", "!code", "!гуард", "!guard", "!кодстим", "!sg"), _cmd_code, lambda: _code_word() == "!код"),
    (("!время", "!срок", "!time"), lambda c, b, a: _cmd_time(c, b), lambda: True),
    (("!данные", "!логин", "!data", "!acc"), _cmd_creds, lambda: True),
    (("!помощь", "!команды", "!help", "!commands"), _cmd_help, lambda: True),
    (("!extend",), _cmd_ext_lot, lambda: S.get("ext_cmd")),
    (("!кик", "!kick", "!выкинуть"), lambda c, b, a: _bg(_cmd_kick, c, b, a), lambda: S.get("buyer_cmds")),
    (("!пароль", "!password", "!pass"), lambda c, b, a: _bg(_cmd_password, c, b, a), lambda: S.get("buyer_cmds")),
]


def _on_command(chat_id, buyer, text: str):
    if not S.get("enabled") or not buyer:
        return
    cmd, _, arg = (text or "").strip().partition(" ")
    cmd, arg, buyer = cmd.lower(), arg.strip(), buyer.lower()
    if buyer not in RENT:  # плагин ничего ему не выдавал — молчим: на !код может отвечать другой плагин аренды
        return
    if cmd == _code_word():
        handler = _cmd_code
    elif S.get("ext_cmd") and cmd == str(S.get("ext_word") or "!продление").lower():
        handler = _cmd_ext_lot
    else:
        handler = next((h for names, h, enabled in COMMANDS if cmd in names and enabled()), None)
    if handler:
        _set_lang(buyer, cmd)  # английская команда — дальше отвечаем ему по-английски, русская — по-русски
        handler(chat_id, buyer, arg)


def _on_review(msg):
    if msg.type not in (MessageTypes.NEW_FEEDBACK, MessageTypes.FEEDBACK_CHANGED):
        return
    found = re.search(r"#([A-Z0-9]{8})", msg.text or "")
    rec = found and next((r for lst in RENT.values() for r in lst if r.get("order") == found.group(1)), None)
    if not rec or rec.get("bonus") or rec.get("exp", 0) <= time.time() or not _bonus_on(_map_by_lot(rec.get("lot"))):
        return
    try:
        stars = cardinal.account.get_order(found.group(1)).review.stars
    except Exception:
        return
    if not stars or stars < int(S.get("bonus_stars") or 5):
        return
    rec["bonus"] = True  # отмечаем до продления — изменение отзыва не даст второй бонус
    _save("rentals")
    api = _api()
    hours = int(S.get("bonus_hours") or 2)
    err = _extend(api, rec, hours, rec["chat"], rec["order"], "review_bonus", "bonus") if api else "no_key"
    if err:
        return _notify(f"⚠️ Бонус за отзыв не начислен: {esc(_human(err, api))}", rec["order"])
    _notify(f"🎁 <code>{esc(rec['login'])}</code> +{hours} ч за отзыв {stars}★.", rec["order"], cat="bonus")


def on_new_message(c: "Cardinal", event):
    msg = event.message
    try:
        if msg.type != MessageTypes.NON_SYSTEM:
            return _on_review(msg)
        if msg.author_id in (0, c.account.id) or msg.by_bot or not _is_cmd(msg.text):
            return
        _on_command(msg.chat_id, msg.author or msg.chat_name, msg.text)
    except Exception:
        log.exception(f"{LP} сообщение")


def on_last_chat_message_changed(c: "Cardinal", event):
    """В «старом режиме» FPC нет NewMessageEvent — команды приходят только так."""
    chat = event.chat
    try:
        if (getattr(c, "old_mode_enabled", False) and chat.unread and not chat.last_by_bot
                and _is_cmd(chat.last_message_text)):
            _on_command(chat.id, chat.name, chat.last_message_text)
    except Exception:
        log.exception(f"{LP} чат")


# ---------------------------------------------------------------- фон: наличие, цены, окончания, обновления

def _sync_lots():
    """Снимает лоты с продажи, пока на MUVSell нет аккаунтов (или мало баланса), и возвращает, когда появятся."""
    if not S.get("fp_edit"):
        return
    lots = [m for m in MAPS if m.get("lot_id") and not m.get("off")]
    want = {}  # lot_id → причина снятия
    if S.get("hide_low_balance") or any(_hide_on(m) for m in lots):
        api = _api()
        if not api:
            return
        low = False
        if S.get("hide_low_balance"):
            data = _balance(force=True)
            if data is None:
                return  # нет данных — ничего не трогаем
            bal = float(data.get("balanceUsd" if S.get("pay") == "usd" else "balanceRub") or 0)
            low = bal <= float(S.get("balance_min") or 0)
            if low != _state["low"]:
                _state["low"] = low
                _notify(f"🛑 Баланс MUVSell {_num(bal)} — не выше порога, снимаю лоты с продажи. Пополните: {SITE}/profile"
                        if low else f"✅ Баланс MUVSell пополнен ({_num(bal)}) — возвращаю лоты.", cat="balance")
        if low:
            want = {str(m["lot_id"]): "balance" for m in lots}
        else:
            prods = _products(force=True)
            if prods is None:
                return
            stock = {p["id"]: int(p.get("inStock") or 0) if p.get("available") else 0 for p in prods}
            want = {str(m["lot_id"]): "stock" for m in lots if _hide_on(m) and stock.get(m["game_id"], 0) <= 0}
    hid, shown = [], []
    for m in lots:
        lid = str(m["lot_id"])
        if lid in want and lid not in HIDDEN:
            if _set_active(m, False):
                with _lock:
                    HIDDEN[lid] = want[lid]
                _save("hidden")
                hid.append(m)
        elif lid not in want and lid in HIDDEN:
            if _set_active(m, True):
                with _lock:
                    reason = HIDDEN.pop(lid, None)
                _save("hidden")
                shown.append((m, reason))
    gone = [m for m in hid if HIDDEN.get(str(m["lot_id"])) == "stock"]
    if gone:
        _notify("📦 Сняты с продажи — нет аккаунтов на MUVSell:\n" + "\n".join(f"• {esc(_mlabel(m))}" for m in gone[:15]),
                cat="stock")
    back = [m for m, reason in shown if reason == "stock"]
    if back:
        _notify("📦 Снова в продаже — аккаунты появились:\n" + "\n".join(f"• {esc(_mlabel(m))}" for m in back[:15]),
                cat="stock")


def _with_tag(text: str, m: dict) -> str:
    """Описание лота с ID привязки последней строкой (чужие ID — например, у копии лота — убираются)."""
    text = TAG_RX.sub("", text or "").rstrip()
    return f"{text}\n\n{m['tag']}" if text and m.get("tag") else text


def _tag_lots(limit: int = 10):
    """Выдаёт привязкам ID (rentM-1001…, номера не повторяются) и дописывает его в конец описания лота на FunPay:
    по нему заказ находит привязку. За проход — не больше limit лотов, чтобы не упереться в лимиты FunPay."""
    if not S.get("fp_edit"):
        return
    for m in [m for m in MAPS if m.get("lot_id") and not m.get("tagged")][:limit]:
        if not m.get("tag"):
            with _lock:
                n = max([int(S.get("tag_seq") or 1000)] + [int(x["tag"][6:]) for x in MAPS if x.get("tag")]) + 1
                S["tag_seq"], m["tag"] = n, f"rentM-{n}"
            _save("settings")
            _save("mappings")

        def go(lf):
            old = (lf.description_ru, lf.description_en)
            lf.description_ru, lf.description_en = _with_tag(old[0], m), _with_tag(old[1], m)
            if (lf.description_ru, lf.description_en) != old:
                cardinal.account.save_lot(lf)
                time.sleep(CREATE_DELAY)
            return True
        try:
            ok = _lot_do(m, go)
        except _RateLimited:
            return
        if ok:
            m["tagged"] = True
            _save("mappings")


def _reprice(targets: list, prods: dict, on_step=None):
    """Выставляет лотам цену по наценке. → (обновлено, без изменений, ошибок, упёрлись в лимит FunPay, [изменения])."""
    api = _api()
    updated = same = failed = 0
    changes, limited = [], False
    for i, m in enumerate(targets, 1):
        price = _price(api, prods[m["game_id"]], int(m["hours"]), m)
        old = m.get("price")
        try:
            res = _set_price(m, price)
        except _RateLimited:
            limited = True
            break
        if res == "set":
            updated += 1
            changes.append((m, old, price))
            time.sleep(CREATE_DELAY)
        elif res == "same":
            same += 1
        else:
            failed += 1
        if on_step:
            on_step(i, updated, same, failed)
    _save("mappings")
    return updated, same, failed, limited, changes


def _sync_prices():
    prods = {p["id"]: p for p in _products(force=True) or []}
    api = _api()
    targets = [m for m in MAPS if _auto_price(m) and m["game_id"] in prods and not m.get("off")
               and m.get("price") != _price(api, prods[m["game_id"]], int(m["hours"]), m)]
    _state["price_at"] = time.time()
    if not targets:
        return
    updated, _, _, _, changes = _reprice(targets, prods)
    if updated:
        _notify(f"💰 Цены обновлены у {updated} лотов:\n" + "\n".join(
            f"• {esc(_mlabel(m))}: {_num(old) + '₽' if old else '?'} → {price}₽" for m, old, price in changes[:15]),
            cat="prices")


def _end_notices():
    now, api = time.time(), _api()
    for key, lst in list(RENT.items()):
        for r in list(lst):
            if r.get("ended") or not r.get("exp"):
                continue
            left = r["exp"] - now
            if 0 < left <= float(S.get("warn_min") or 0) * 60 and not r.get("warned"):
                r["warned"] = True
                _save("rentals")
                lang = _lang(r)
                _send(r.get("chat"), _t("warn", lang, game=r["game"], login=r["login"], left=_left_text(left, lang),
                                        minutes=max(1, int(left // 60)), expires=_when(r["exp"], lang),
                                        word=S.get("ext_word") or "!продление"))
            if left > 0:
                continue
            if api:  # продлить могли и на сайте — сверяемся, прежде чем прощаться
                data, _ = api.rental(r["id"])
                rental = (data or {}).get("rental") or {}
                if rental.get("status") == "active" and _ts(rental.get("endsAt")) > now:
                    r["exp"] = _ts(rental.get("endsAt"))
                    _save("rentals")
                    continue
            r["ended"] = True
            _save("rentals")
            if S.get("notify_end"):
                _send(r.get("chat"), _t("ended", _lang(r), game=r["game"], login=r["login"]))
            _notify(f"⌛️ Аренда закончилась: <code>{esc(r['login'])}</code> — {esc(r['game'])} "
                    f"({esc(r.get('buyer') or key)})", cat="ended")


def _cleanup():
    cutoff, changed = time.time() - 86400, False
    with _lock:
        for key in list(RENT):
            keep = [r for r in RENT[key] if r.get("exp", 0) > cutoff]
            changed = changed or len(keep) != len(RENT[key])
            if keep:
                RENT[key] = keep
            else:
                del RENT[key]
    if changed:
        _save("rentals")


def _vt(v) -> tuple:
    return tuple(int(x) for x in re.findall(r"\d+", str(v or ""))) or (0,)


def _check_update():
    """Скачивает новую версию плагина с muvsell.store; применится после перезапуска FPC."""
    try:
        info = requests.get(INFO_URL, timeout=20, proxies=_proxies()).json()
        ver = str(info.get("version") or "")
        if _vt(ver) <= _vt(VERSION) or ver == _state["update"]:
            return
        # .py отдаётся как application/octet-stream — кодировку не угадываем, файл всегда UTF-8
        code = requests.get(urljoin(SITE, info.get("download_url") or "/downloads/MUVSellRent.py"),
                            timeout=60, proxies=_proxies()).content.decode("utf-8")
        if f'VERSION = "{ver}"' not in code or "BIND_TO_PRE_INIT" not in code:
            return log.warning(f"{LP} обновление v{ver}: скачан не плагин — пропускаю")
        shutil.copy2(SELF_PATH, SELF_PATH + ".bak")
        with open(SELF_PATH + ".new", "w", encoding="utf-8", newline="\n") as f:
            f.write(code)
        os.replace(SELF_PATH + ".new", SELF_PATH)
        _state["update"] = ver
        notes = re.search(r'^CHANGELOG = "(.*)"$', code, re.M)
        _notify(f"⬆️ Загружена версия <b>v{ver}</b> (сейчас v{VERSION})."
                + (f"\n\n<b>Что нового:</b>\n{esc(notes.group(1).replace(chr(92) + 'n', chr(10)))}" if notes else "")
                + "\n\nПерезапустите FPC, чтобы применить.", kb=K().add(B("♻️ Перезапустить FPC", callback_data=f"{P}:restart")))
    except Exception as e:
        log.warning(f"{LP} проверка обновлений: {e}")


def _poll_loop():
    last_update = last_price = 0.0
    while not _stop.wait(max(15, int(S.get("poll_sec") or 60))):
        if not _plugin_on():
            continue
        try:
            _state["poll_at"] = time.time()
            _ext_cleanup()
            if S.get("enabled"):
                _end_notices()
                _sync_lots()
                if not _state["job"]:
                    _tag_lots()
                if (S.get("fp_edit") and not _state["job"]
                        and time.time() - last_price > max(1, float(S.get("price_min") or 5)) * 60):
                    last_price = time.time()
                    _sync_prices()
            _cleanup()
            if time.time() - last_update > UPDATE_EVERY:
                last_update = time.time()
                _check_update()
        except Exception:
            log.exception(f"{LP} фоновая проверка")
        _flush_q()


# ---------------------------------------------------------------- автовыставление лотов

def _fp_map(force: bool = False) -> dict:
    """Карта «игра MUVSell → раздел FunPay» с muvsell.store (кэш 1 ч, офлайн-копия на диске)."""
    ts, data = _cache["map"]
    if force or not data or time.time() - ts > 3600:
        try:
            r = requests.get(MAP_URL, timeout=TIMEOUT, proxies=_proxies())
            fresh = r.json() if r.ok else None
            if isinstance(fresh, dict) and fresh.get("games"):
                data = fresh
                _cache["map"] = (time.time(), data)
                _write("funpay_map", data)
        except Exception as e:
            log.warning(f"{LP} карта игр не скачалась: {e}")
        data = data or _load("funpay_map", {})
    return data or {}


def _fp_game(game_id: str):
    return next((g for g in _fp_map().get("games", []) if g.get("game_id") == game_id), None)


def _sellable() -> list:
    """[(игра из карты, товар MUVSell)] — есть раздел FunPay и цена на сайте."""
    prods = {p["id"]: p for p in _products() or [] if p.get("available")}
    return [(g, prods[g["game_id"]]) for g in _fp_map().get("games", []) if g.get("game_id") in prods]


def _stale(m: dict) -> str:
    """Почему привязку пора пересоздать: лот удалён с FunPay или лот плагина стоит не в том разделе (карта
    исправлена). → причина или ""."""
    if (PROBLEMS.get(str(m["lot_id"])) or {}).get("missing"):
        return "удалён с FunPay"
    g = m.get("auto") and not m.get("manual") and _fp_game(m["game_id"])  # ручной раздел — вне раздела из карты
    if g and str(g["funpay"]["subcategory_id"]) != str(m.get("subcat")):
        return "в чужом разделе"
    return ""


def _plan(durations=None) -> list:
    have = {(m["game_id"], int(m["hours"])) for m in MAPS if not _stale(m) and not m.get("manual")}
    return [(g, p, h) for g, p in _sellable() for h in durations or S["ap_durations"] if (g["game_id"], h) not in have]


def _ckey(g: dict, hours: int) -> str:
    return f"{g['manual'] + ':' if g.get('manual') else ''}{g['game_id']}:{hours}"


def _drop_stale(g: dict, hours: int):
    """Перед созданием заново: убираем старую привязку; лот плагина в чужом разделе ещё и удаляем с FunPay."""
    game_id = g["game_id"]
    stale = [x for x in MAPS if x["game_id"] == game_id and int(x["hours"]) == hours
             and x.get("manual") == g.get("manual") and _stale(x)]
    if not stale:
        return
    for m in stale:
        if _stale(m) == "в чужом разделе":
            try:
                cardinal.account.delete_lot(int(m["lot_id"]))
            except Exception as e:
                log.warning(f"{LP} лот {m['lot_id']} ({_mlabel(m)}) из чужого раздела не удалён: {e}")
        with _lock:
            MAPS[:] = [x for x in MAPS if x is not m]
            PROBLEMS.pop(str(m["lot_id"]), None)
            HIDDEN.pop(str(m["lot_id"]), None)
            CREATED.pop(_ckey(g, hours), None)
    for name in ("mappings", "problems", "hidden", "created"):
        _save(name)


def _orphans() -> dict:
    """Лоты автовыставления, у которых удалили привязку, а лот на FunPay, возможно, остался."""
    mapped = {str(m["lot_id"]) for m in MAPS}
    return {k: v for k, v in CREATED.items() if str(v.get("lot_id")) not in mapped}


def _ap_text(field: str) -> str:
    return (S.get("ap_texts") or {}).get(field) or AP_TEXTS[field]


def _lot_texts(game: str, hours: int):
    def fill(field, lang):
        return (_ap_text(field).replace("{game}", game).replace("{time}", _dur(hours, lang))
                .replace("{commands}", _commands_text()))
    ru, en = fill("title_ru", "ru"), _ascii(fill("title_en", "en"))
    en = en or _ascii(f"{game} Steam account rental {_dur(hours, 'en')} auto delivery")
    desc_en = _ascii(fill("desc_en", "en"))
    if len(desc_en) < EN_MIN:  # FunPay не принимает короткое английское описание
        desc_en = _ascii(f"{desc_en} " + AP_TEXTS["desc_en"].replace("{game}", game).replace("{time}", _dur(hours, "en")))
    return ru, en[:100], fill("desc_ru", "ru"), desc_en


def _market_prices(sub: int, hours: int) -> list:
    """3 самые низкие цены аренды на такой же срок у других продавцов раздела (для плана)."""
    ts, lots = _market.get(sub, (0, None))
    if lots is None or time.time() - ts > 900:
        try:
            lots = [(float(lot.price), _norm(lot.description)) for lot in
                    cardinal.account.get_subcategory_public_lots(SubCategoryTypes.COMMON, sub)]
        except Exception:
            lots = []
        _market[sub] = (time.time(), lots)
    pats = [rf"(?<!\d){hours}\s*ч"]
    if hours % 24 == 0:
        pats.append(rf"(?<!\d){hours // 24}\s*(?:д|сут)")
    rx = re.compile("|".join(pats))
    return sorted(p for p, d in lots if ("аренд" in d or "rent" in d) and rx.search(d))[:3]


_PREFER = ("аренд", "rent", "steam", "pc", "пк", "windows", "стандарт", "standard", "друг", "любая", "other")
_AVOID = ("android", "ios", "mobile", "(ps)", "ps4", "ps5", "playstation", "xbox", "switch", "nintendo", "epic", "origin")


def _pick(opts: list, game: str) -> str:
    """Вариант для выпадающего списка формы лота: игра по названию, иначе аренда/Steam/PC/«другая игра»,
    иначе первый не мобильный."""
    opts = [(v, t.lower()) for v, t in opts if v]
    g = _norm(game)
    hits = []  # «(PC) Forza Horizon 4» → «forza horizon 4»; самое длинное совпадение, PC раньше консолей
    for v, t in opts:
        core = re.sub(r"^\([^)]*\)\s*", "", t)
        if g and (core == g or (len(core) > 3 and core in g)):
            hits.append((any(a in t for a in _AVOID), -len(core), v))
    if hits:
        return min(hits)[2]
    for word in _PREFER:
        for v, t in opts:
            if word in t:
                return v
    return next((v for v, t in opts if not any(a in t for a in _AVOID)), opts[0][0] if opts else "")


def _new_lot_form(sub: int):
    """Поля и выпадающие списки формы нового лота раздела FunPay."""
    from bs4 import BeautifulSoup
    r = cardinal.account.method("get", f"lots/offerEdit?node={sub}", {}, {}, raise_not_200=True)
    form = BeautifulSoup(r.content.decode(), "html.parser").find("form", class_="form-offer-editor")
    if not form:
        raise RuntimeError(f"FunPay не отдал форму лота для раздела {sub}")
    fields, selects = {}, {}
    for inp in form.find_all("input"):
        name = inp.get("name")
        if name and name != "query" and (inp.get("type") != "checkbox" or inp.has_attr("checked")):
            fields[name] = "on" if inp.get("type") == "checkbox" else inp.get("value") or ""
    for ta in form.find_all("textarea"):
        if ta.get("name"):
            fields[ta["name"]] = ta.text or ""
    for sel in form.find_all("select"):
        group = sel.find_parent(class_="form-group")
        cls = group.get("class") or [] if group else []
        if sel.get("name") and not ("hidden" in cls and "lot-field" not in cls):
            selects[sel["name"]] = [(o.get("value") or "", o.text.strip()) for o in sel.find_all("option")]
            chosen = sel.find("option", selected=True)
            fields[sel["name"]] = chosen.get("value") or "" if chosen else ""
    if fields.get("csrf_token"):
        cardinal.account.csrf_token = fields["csrf_token"]
    return fields, selects


def _create_lot(sub: int, map_fields: dict, game: str, texts: tuple, price: int, active: bool = True, amount: int = 1000):
    """Создаёт лот на FunPay. → (id лота, None) или (None, причина)."""
    acc = cardinal.account
    before = {int(lot.id) for lot in acc.get_my_subcategory_lots(sub)}
    fields, selects = _new_lot_form(sub)
    fields.update({k: str(v) for k, v in (map_fields or {}).items() if v})
    region = (S.get("steam_region") or "").strip().lower()
    want = {"аренда", region} if sub == STEAM_SUB else set()  # Steam: тип и регион выбираем по тексту варианта
    if want and not any(t.lower() == region for opts in selects.values() for _, t in opts):
        regions = [t for opts in selects.values() if not any(t.lower() == "аренда" for _, t in opts) for v, t in opts if v]
        return None, f"в форме FunPay нет региона «{S.get('steam_region')}», есть: {', '.join(regions[:15]) or '—'}"
    for name, opts in selects.items():
        hit = next((v for v, t in opts if v and t.lower() in want), None)
        if hit:
            fields[name] = hit
        elif fields.get(name) not in {v for v, _ in opts if v}:
            fields[name] = _pick(opts, game)
    ru, en, desc_ru, desc_en = texts
    fields.update({"offer_id": "0", "node_id": str(sub), "fields[summary][ru]": ru, "fields[summary][en]": en,
                   "fields[desc][ru]": desc_ru, "fields[desc][en]": desc_en, "price": str(price),
                   "amount": str(amount), "active": "on" if active else ""})
    for key in ("auto_delivery", "secrets"):  # автовыдача FunPay выключена — выдаёт плагин
        fields.pop(key, None)
    subcategory = acc.get_subcategory(SubCategoryTypes.COMMON, sub)
    for _ in range(4):
        fields["csrf_token"] = acc.csrf_token
        try:
            acc.save_lot(LotFields(0, dict(fields), subcategory, acc.currency))
            break
        except Exception as e:
            reason = _fp_error(e)
            if RATE_RX.search(reason):
                raise _RateLimited(reason)
            changed = False
            for name in getattr(e, "errors", None) or {}:  # FunPay назвал незаполненные поля — дозаполняем
                if not fields.get(name):
                    fields[name] = _pick(selects[name], game) if name in selects else "1"
                    changed = True
            if not changed:
                return None, reason
    else:
        return None, "FunPay не принял лот"
    for pause in (0, 3, 6):  # FunPay показывает новый лот в списке не мгновенно
        time.sleep(pause)
        new = [lot for lot in acc.get_my_subcategory_lots(sub) if int(lot.id) not in before]
        lot = next((x for x in new if _norm(x.description) == _norm(ru)), new[0] if len(new) == 1 else None)
        if lot:
            return int(lot.id), None
    return None, "лот создан, но FunPay его пока не показывает — привяжите его вручную"


def _progress(chat_id, msg_id, title: str, done: int, total: int, stats: str):
    bar = "█" * round(done / max(total, 1) * 14)
    _state["job_text"] = f"{title}: {done}/{total} · {stats}"
    if bot and chat_id and msg_id and (done % 3 == 0 or done == total):
        try:
            bot.edit_message_text(f"🚀 <b>{title}</b>\n\n<code>{bar:░<14} {done}/{total}</code>\n\n{stats}\n"
                                  f"<i>Можно закрыть — работа идёт в фоне.</i>", chat_id, msg_id, parse_mode="HTML")
        except Exception:
            pass


def _finish_job(chat_id, msg_id, text: str, back: str = "ac"):
    _state["job"] = None
    _state["job_text"] = ""
    _flush_q()
    kb = K().add(B("🔙 Назад", callback_data=f"{P}:{back}"))
    try:
        bot.edit_message_text(text, chat_id, msg_id, parse_mode="HTML", reply_markup=kb)
    except Exception:
        _notify(text)


def _new_map(g: dict, lot_id, hours: int, titles: list, price: int) -> dict:
    m = {"lot_id": str(lot_id), "subcat": int(g["funpay"]["subcategory_id"]), "titles": titles, "game_id": g["game_id"],
         "game": g["name"], "hours": hours, "auto": True, "price": price, "markup": S.get("ap_own")}
    if g.get("manual"):
        m["manual"] = g["manual"]
    with _lock:
        MAPS.append(m)
        CREATED[_ckey(g, hours)] = {"lot_id": str(lot_id), "subcat": m["subcat"], "titles": titles}
    _save("mappings")
    _save("created")
    return m


def _run_create(chat_id, msg_id, plan: list):
    api, cap = _api(), int(S.get("lot_cap") or 20)
    created = restored = skipped = failed = 0
    reasons, counts, limited = Counter(), {}, False

    def step(i):
        _progress(chat_id, msg_id, "Создание лотов", i, len(plan), f"✅ {created} · ♻️ {restored} · ⏭ {skipped} · ❌ {failed}")
    try:
        for i, (g, prod, hours) in enumerate(plan, 1):
            _drop_stale(g, hours)  # лот удалён с FunPay или стоит в чужом разделе — создаём заново
            sub = int(g["funpay"]["subcategory_id"])
            price = _price(api, prod, hours, {"subcat": sub, "markup": S.get("ap_own")})
            old = CREATED.get(_ckey(g, hours))
            if old and str(old.get("lot_id")) not in {str(m["lot_id"]) for m in MAPS}:
                try:  # привязку удаляли, а лот на FunPay остался — возвращаем привязку, дубль не создаём
                    cardinal.account.get_lot_fields(int(old["lot_id"]))
                    _new_map(g, old["lot_id"], hours, old.get("titles") or [], price)
                    restored += 1
                    step(i)
                    continue
                except Exception:
                    CREATED.pop(_ckey(g, hours), None)
            if sub not in counts:  # лимит — только на лоты плагина: ваши остальные лоты в разделе не мешают
                counts[sub] = sum(1 for m in MAPS if m.get("auto") and str(m.get("subcat")) == str(sub))
            if counts[sub] >= cap:
                skipped += 1
                log.info(f"{LP} автовыставление: {g['name']} {_short(hours)} пропущен — в разделе {sub} уже {cap} лотов плагина")
            else:
                texts = _lot_texts(g["name"], hours)
                try:
                    lot_id, err = _create_lot(sub, g["funpay"].get("fields"), g["name"], texts, price,
                                              bool(S.get("ap_active", True)))
                except _RateLimited:
                    limited = True
                    break
                except Exception as e:
                    lot_id, err = None, str(e)[:160]
                if lot_id:
                    _new_map(g, lot_id, hours, [texts[0], texts[1]], price)
                    counts[sub] += 1
                    created += 1
                else:
                    failed += 1
                    reasons[f"{err} (напр. {g['name']}, {_short(hours)})"] += 1
                    log.warning(f"{LP} автовыставление: {g['name']} {_short(hours)} (раздел {sub}) не создан — {err}")
                time.sleep(CREATE_DELAY)
            step(i)
    except Exception as e:
        log.exception(f"{LP} автовыставление")
        reasons[str(e)[:160]] += 1
    text = ("⛔️ <b>FunPay временно запретил создавать лоты</b> (обычно на несколько часов).\n"
            "Позже нажмите «Создать недостающие» — плагин дозальёт только оставшиеся.\n\n" if limited
            else "🤖 <b>Создание лотов завершено.</b>\n\n")
    text += (f"✅ Создано: <b>{created}</b>\n♻️ Восстановлено привязок: <b>{restored}</b>\n"
             f"⏭ Пропущено (лимит раздела): <b>{skipped}</b>\n❌ Ошибок: <b>{failed}</b>")
    if reasons:
        text += "\n\n<b>Причины:</b>\n" + "\n".join(f"• {n}× {esc(r)}" for r, n in reasons.most_common(5))
    _save("created")
    _finish_job(chat_id, msg_id, text)


def _run_reprice(chat_id, msg_id):
    prods = {p["id"]: p for p in _products(force=True) or []}
    targets = [m for m in MAPS if _auto_price(m) and m["game_id"] in prods]
    updated, same, failed, limited, _ = _reprice(targets, prods, lambda i, u, s, f: _progress(
        chat_id, msg_id, "Пересчёт цен", i, len(targets), f"✅ {u} · ➖ {s} · ❌ {f}"))
    manual = sum(1 for m in MAPS if not _auto_price(m))
    _finish_job(chat_id, msg_id, ("⛔️ <b>FunPay временно ограничил изменения.</b> Повторите позже.\n\n" if limited
                                  else "🔁 <b>Пересчёт цен завершён.</b>\n\n")
                + f"✅ Обновлено: <b>{updated}</b>\n➖ Без изменений: <b>{same}</b>\n❌ Ошибок: <b>{failed}</b>"
                + (f"\n✋ С ручной ценой (не трогались): <b>{manual}</b>" if manual else ""), "main")


def _run_titles(chat_id, msg_id):
    """Перечитывает названия и цены всех привязанных лотов (заодно проверяет, что лоты живы)."""
    ok = failed = 0
    targets = list(MAPS)
    for i, m in enumerate(targets, 1):
        def go(lf, m=m):
            m["titles"] = [t for t in (lf.title_ru, lf.title_en) if t] or m.get("titles")
            if lf.price is not None:
                m["price"] = lf.price
            return True
        try:
            res = _lot_do(m, go)
        except _RateLimited:
            break
        ok, failed = ok + bool(res), failed + (not res)
        _progress(chat_id, msg_id, "Обновление названий", i, len(targets), f"✅ {ok} · ❌ {failed}")
    _save("mappings")
    _finish_job(chat_id, msg_id, f"🔄 <b>Названия обновлены.</b>\n\n✅ Прочитано: <b>{ok}</b>\n❌ Ошибок: <b>{failed}</b>"
                                 + ("\nПроблемные лоты — в «🚑 Проблемные лоты»." if failed else ""), "main")


def _run_retext(chat_id, msg_id):
    """Переписывает название и описание у лотов автовыставления по текущим шаблонам."""
    targets = [m for m in MAPS if m.get("auto")]
    done = failed = 0
    limited = False
    for i, m in enumerate(targets, 1):
        ru, en, desc_ru, desc_en = _lot_texts(m["game"], int(m["hours"]))

        def go(lf):
            lf.title_ru, lf.title_en = ru, en
            lf.description_ru, lf.description_en = _with_tag(desc_ru, m), _with_tag(desc_en, m)
            cardinal.account.save_lot(lf)
            return True
        try:
            res = _lot_do(m, go)
        except _RateLimited:
            limited = True
            break
        if res:
            m["titles"] = [ru, en]
            done += 1
            time.sleep(CREATE_DELAY)
        else:
            failed += 1
        _progress(chat_id, msg_id, "Перезапись текстов", i, len(targets), f"✅ {done} · ❌ {failed}")
    _save("mappings")
    _finish_job(chat_id, msg_id, ("⛔️ <b>FunPay временно ограничил изменения.</b> Повторите позже.\n\n" if limited
                                  else "✏️ <b>Тексты переписаны.</b>\n\n")
                + f"✅ Обновлено: <b>{done}</b>\n❌ Ошибок: <b>{failed}</b>")


def _run_delete(chat_id, msg_id, targets=None, lots: bool = True, back: str = "ac"):
    targets = [m for m in MAPS if m.get("auto")] if targets is None else targets
    deleted = failed = 0
    for i, m in enumerate(targets, 1):
        gone = True
        if lots:
            try:
                cardinal.account.delete_lot(int(m["lot_id"]))
            except Exception as e:
                gone = bool(MISSING_RX.search(str(e)))  # уже удалён на FunPay — чистим привязку
            time.sleep(0.5)
        if gone:
            with _lock:
                MAPS[:] = [x for x in MAPS if x is not m]
                HIDDEN.pop(str(m["lot_id"]), None)
                PROBLEMS.pop(str(m["lot_id"]), None)
                if lots:
                    CREATED.pop(f"{m['game_id']}:{m['hours']}", None)
            deleted += 1
        else:
            failed += 1
        _progress(chat_id, msg_id, "Удаление", i, len(targets), f"🗑 {deleted} · ❌ {failed}")
    for name in ("mappings", "hidden", "problems", "created"):
        _save(name)
    _finish_job(chat_id, msg_id, f"🗑 <b>Удаление завершено.</b>\n\nУдалено: <b>{deleted}</b>\n❌ Ошибок: <b>{failed}</b>\n"
                                 f"Осталось привязок: <b>{len(MAPS)}</b>", back)


def _start_job(call, name: str, target, *args):
    with _lock:
        if _state["job"]:
            return _alert(call, f"Уже идёт: {_state['job']} — дождитесь окончания")
        _state["job"] = name
    _edit(call, f"🚀 <b>{name}…</b>")
    threading.Thread(target=target, args=(call.message.chat.id, call.message.id, *args), daemon=True).start()


# ---------------------------------------------------------------- статистика

def _day(ts: float):
    return datetime.fromtimestamp(ts, _tz()).date()


def _in_period(p: str):
    today = datetime.now(_tz()).date()
    if p == "today":
        return lambda d: d == today
    if p == "yday":
        return lambda d: d == today - timedelta(days=1)
    if p == "all":
        return lambda d: True
    return lambda d: (today - d).days < int(p)


def _sales(p: str) -> list:
    f = _in_period(p)
    return [s for s in SALES if f(_day(s["ts"]))]


def _sold(lst: list) -> list:
    return [s for s in lst if s["kind"] in ("new", "ext") and s.get("order")]


def _agg(lst: list) -> dict:
    sold = _sold(lst)
    orders = {s["order"] for s in sold}
    refunded = {s["order"] for s in sold if s.get("refunded")}
    rev = sum(s["rev"] for s in lst)
    cost = sum(s["cost"] for s in lst)
    refund = sum(s["rev"] for s in lst if s.get("refunded"))
    return {"n": len(orders), "rev": rev, "cost": cost, "gross": rev - cost, "refunds": len(refunded),
            "refund": refund, "net": rev - cost - refund}


def _profit(lst: list) -> float:
    return sum(s["rev"] - s["cost"] - (s["rev"] if s.get("refunded") else 0) for s in lst)


# ---------------------------------------------------------------- Telegram: общее

P = "mvs"


def _btn(text: str, data: str):
    return B(text, callback_data=f"{P}:{data}")


def _kb(*rows):
    kb = K()
    for row in rows:
        if row:
            kb.row(*row)
    return kb


def _back(data: str = "main"):
    return [_btn("🔙 Назад", data)]


def _edit(call, text: str, kb=None):
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.id, parse_mode="HTML", reply_markup=kb,
                              disable_web_page_preview=True)
    except Exception as e:
        if "not modified" not in str(e):
            bot.send_message(call.message.chat.id, text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)
    try:
        bot.answer_callback_query(call.id)
    except Exception:
        pass


def _alert(call, text: str):
    try:
        bot.answer_callback_query(call.id, text[:200], show_alert=True)
    except Exception:
        pass


def _wait(call, text: str = "⏳ Загружаю…"):
    try:
        bot.answer_callback_query(call.id, text)
    except Exception:
        pass


def _ask(call, state: str, text: str, back: str = "main"):
    """Просит ввести значение: следующее сообщение пользователя уйдёт в обработчик INPUTS[state]."""
    tg.set_state(call.message.chat.id, call.message.id, call.from_user.id, f"{P}:{state}")
    _edit(call, text, _kb(_back(back)))


def _nav(prefix: str, page: int, total: int, per: int):
    pages = max(1, math.ceil(total / per))
    if pages == 1:
        return None
    return ([_btn("⬅️", f"{prefix}:{page - 1}")] if page > 0 else []) + [_btn(f"{page + 1}/{pages}", "noop")] + \
        ([_btn("➡️", f"{prefix}:{page + 1}")] if page + 1 < pages else [])


def _page(items: list, page, per: int):
    page = max(0, int(page or 0))
    if page * per >= len(items):
        page = max(0, math.ceil(len(items) / per) - 1)
    return page, items[page * per:(page + 1) * per]


def _uid(call) -> dict:
    return _tmp.setdefault(call.from_user.id, {})


# ---------------------------------------------------------------- Telegram: главное меню

HELP = (
    f"<b>ℹ️ {NAME} — как это работает</b>\n\n"
    "1. На <b>muvsell.store</b>: Профиль → API → создайте ключ и пополните баланс.\n"
    "2. Здесь: ⚙️ Настройки → «🔑 API ключ» → отправьте ключ.\n"
    "3. Лоты: «🤖 Автовыставление» создаст лоты по всем играм MUVSell, «🎮 Создать привязку» — по одной игре, "
    "«🔗 Привязать лот» — привяжет ваш готовый лот. В конец описания каждого привязанного лота плагин сам "
    "допишет его ID (<code>rentM-1001</code>) и по нему узнаёт оплаченный лот — не удаляйте эту строку.\n"
    "4. Покупатель оплачивает лот → плагин арендует аккаунт на MUVSell (с вашего баланса) "
    "и сразу присылает логин и пароль в чат FunPay.\n\n"
    "<b>Команды покупателя</b> (в чате FunPay)\n"
    "• <code>!код</code> / <code>!гуард</code> — код Steam Guard (свою команду — в «⚙️ Прочее», если на !код "
    "отвечает ещё и другой плагин)\n"
    "• <code>!время</code> — сколько осталось, <code>!данные</code> — логин и пароль ещё раз\n"
    "• <code>!продление 3</code> или <code>!продление 2д</code> — плагин создаёт временный лот на этот срок, "
    "оплата продлевает ту же аренду, лот удаляется\n"
    "• <code>!кик</code> — выкинуть чужие сессии Steam, <code>!пароль</code> — сменить пароль (новый придёт в чат)\n"
    "• <code>!помощь</code> — список команд\n"
    "🇬🇧 Кто пишет английские команды (<code>!code</code>, <code>!help</code>…), тому плагин отвечает по-английски "
    "(выключается в «⚙️ Прочее»).\n\n"
    "<b>Время</b>: за заказ — часы привязки × количество. Лот на 1 час = почасовой: покупатель сам выбирает "
    "число часов количеством. Каждая покупка выдаёт новый аккаунт; продлить текущий покупатель может только "
    "командой <code>!продление</code> (если она включена).\n\n"
    "<b>Цены</b>: цена лота = цена MUVSell × (1 + наценка). Наценка берётся у привязки, иначе у категории, "
    "иначе глобальная. Лоты с автоценой пересчитываются сами.\n\n"
    "<b>Наличие</b>: пока на MUVSell нет свободных аккаунтов игры, её лоты сняты с продажи "
    "и возвращаются сами, когда аккаунты появятся."
)


def _paused(m: dict) -> bool:
    return PROBLEMS.get(str(m["lot_id"]), {}).get("until", 0) > time.time()


def _active_maps() -> int:
    return sum(1 for m in MAPS if not m.get("off") and str(m["lot_id"]) not in HIDDEN and not _paused(m))


def scr_main(call, *_):
    upd = _state["update"]
    rentals = len(_all_active())
    warn = "" if S["api_key"] else "\n\n⚠️ API-ключ не задан: ⚙️ Настройки → 🔑 API ключ"
    job = f"\n\n⏳ {esc(_state['job_text'] or _state['job'])}" if _state["job"] else ""
    text = (f"🔌 <b>{NAME}</b> <i>v{VERSION}</i>\n\n"
            f"🔗 Привязок: {len(MAPS)}\n"
            f"🎮 Игр в привязках: {len({m['game_id'] for m in MAPS})}\n"
            f"📋 Активных аренд: {rentals}\n"
            f"📈 Прибыль: {_rub(_agg(SALES)['gross'])}\n"
            f"🛡 Автоскрытие: {_onoff(S.get('hide_no_stock'))}\n"
            f"{'🟢 Автовыдача включена' if S['enabled'] else '🔴 Автовыдача выключена'}\n\n"
            f"🌐 {SITE}" + warn + (f"\n\n⬆️ Загружена v{upd} — перезапустите FPC." if upd else "") + job)
    _edit(call, text, _kb(
        [_btn("🎮 Создать привязку", "cg:0")],
        [_btn("🤖 Автовыставление лотов", "ac")],
        [_btn(f"🔗 Привязки ({_active_maps()}✅/{len(MAPS)})", "maps:0")],
        [_btn(f"📋 Аренды ({rentals})", "rl:0")],
        [_btn("📊 Статистика", "st:all"), _btn("💰 Прибыль", "pr")],
        [_btn("💳 Баланс", "bal"), _btn("🔁 Пересчитать все лоты", "rpa")],
        [_btn(f"🛡 Автоскрытие: {_onoff(S.get('hide_no_stock'))} (глобально)", "t:hide_no_stock")],
        [_btn("🔗 Привязать лот", "alm"), _btn("🔄 Обновить названия", "rt")],
        [_btn("🔎 Диагностика", "dg")],
        [_btn("⚙️ Настройки", "set")],
        [_btn(f"♻️ Перезапустить FPC (v{upd})", "restart")] if upd else None,
        [B("🔙 К плагинам", callback_data=f"{CBT.EDIT_PLUGIN}:{UUID}:0"), _btn("❌ Закрыть", "close")],
    ))


def act_close(call, *_):
    try:
        bot.delete_message(call.message.chat.id, call.message.id)
    except Exception:
        _edit(call, "Закрыто.")


def act_balance(call, *_):
    data = _balance(force=True)
    if not data:
        api = _api()
        return _alert(call, "❌ " + _human("no_key" if not api else "net", api))
    pay = {"rub": "₽ рубли", "usd": "$ крипто", "auto": f"авто (сейчас → {_pay().upper()})"}[S.get("pay", "rub")]
    _edit(call, f"💳 <b>Баланс</b>\n\n👤 {esc(str(data.get('username')))}\n💵 ${_num(data.get('balanceUsd') or 0)}\n"
                f"💴 {_rub(data.get('balanceRub') or 0)}\n\n💱 Валюта аренды: <b>{pay}</b>\n\nПополнить: {SITE}/profile",
          _kb([_btn("💱 Сменить валюту аренды", "pay")], _back()))


def act_pay(call, *_):
    S["pay"] = {"rub": "usd", "usd": "auto", "auto": "rub"}[S.get("pay", "rub")]
    _save("settings")
    act_balance(call)


def act_reprice_all(call, *_):
    if not any(_auto_price(m) for m in MAPS):
        return _alert(call, "Нет привязок с автоценой. Включите «💲 Цена: авто» у нужных привязок.")
    if not S.get("fp_edit"):
        return _alert(call, "Изменение лотов на FunPay выключено в настройках.")
    _start_job(call, "Пересчёт цен", _run_reprice)


def act_titles(call, *_):
    if not MAPS:
        return _alert(call, "Привязок пока нет")
    _start_job(call, "Обновление названий", _run_titles)


def scr_diag(call, *_):
    _wait(call, "🔎 Проверяю…")
    lines, api = [f"🔎 <b>Диагностика</b> · v{VERSION}\n"], _api()
    if not api:
        lines.append("❌ API-ключ MUVSell не задан")
    else:
        t0 = time.time()
        data, err = api.balance()
        ms = int((time.time() - t0) * 1000)
        lines.append(f"✅ MUVSell: {ms} мс, аккаунт <b>{esc(str(data.get('username')))}</b>, "
                     f"{_rub(data.get('balanceRub') or 0)} / ${_num(data.get('balanceUsd') or 0)}" if data
                     else f"❌ MUVSell: {esc(_human(err, api))}")
    lines.append(f"🌐 Прокси MUVSell: {_proxy_label()}")
    prods = _products() if api else None
    lines.append(f"🎮 Каталог MUVSell: {len(prods)} игр" if prods is not None else "❌ Каталог MUVSell не загружен")
    lines.append(f"🗺 Карта FunPay: {len(_fp_map().get('games', []))} игр")
    acc = getattr(cardinal, "account", None)
    lines.append(f"👤 FunPay: {esc(str(getattr(acc, 'username', None) or getattr(acc, 'id', '?')))}")
    if MAPS:
        t0 = time.time()
        try:
            cardinal.account.get_lot_fields(int(MAPS[0]["lot_id"]))
            lines.append(f"✅ Лоты FunPay читаются: {int((time.time() - t0) * 1000)} мс")
        except Exception as e:
            lines.append(f"❌ Лот {MAPS[0]['lot_id']} не читается: {esc(str(e)[:120])}")
    off = sum(1 for m in MAPS if m.get("off"))
    lines.append(f"\n🔗 Привязок: {len(MAPS)} · снято: {len(HIDDEN)} · выключено: {off} · на паузе: "
                 f"{sum(1 for m in MAPS if _paused(m))}")
    lines.append(f"📋 Активных аренд: {len(_all_active())}")
    lines.append(f"🛒 Менять лоты на FunPay: {_onoff(S.get('fp_edit'))}")
    for key, label in (("poll_at", "Проверка наличия"), ("price_at", "Сверка цен")):
        ts = _state[key]
        lines.append(f"⏱ {label}: {_left(time.time() - ts) + ' назад' if ts else 'ещё не было'}")
    if _state["update"]:
        lines.append(f"⬆️ Загружена v{_state['update']} — перезапустите FPC")
    if not S.get("enabled"):
        lines.append("\n🔴 Автовыдача выключена — заказы не обрабатываются")
    _edit(call, "\n".join(lines), _kb([_btn("🔄 Проверить ещё раз", "dg")], _back()))


def act_restart(call, *_):
    _edit(call, "♻️ Перезапускаю FPC…")
    from Utils.cardinal_tools import restart_program
    restart_program()


def act_help(call, *_):
    _edit(call, HELP, _kb(_back("set")))


# ---------------------------------------------------------------- Telegram: привязки

def _map_status(m: dict) -> str:
    return "⏸" if m.get("off") else "🚑" if _paused(m) else "⛔" if str(m["lot_id"]) in HIDDEN else "✅"


def scr_maps(call, page="0"):
    q = _uid(call).get("mq")
    items = [m for m in MAPS if not q or q in m["game"].lower()]
    page, chunk = _page(items, page, 8)
    rows = [[_btn(f"{_map_status(m)}🏷{'🛡' if _hide_on(m) else ''} {m['game'][:28]} | {_short(int(m['hours']))} | "
                  f"{_num(m['price']) + '₽' if m.get('price') else '?'}", f"map:{m['lot_id']}")] for m in chunk]
    head = f"🔗 <b>Привязки ({len(items)})</b>" + (f" · поиск «{esc(q)}»" if q else "")
    _edit(call, head + "\n\n✅=актив | ⛔=нет акк. | ⏸=выкл вручную | 🚑=карантин\n🏷=привязан | 🛡=автоскрытие",
          _kb(*rows, _nav("maps", page, len(items), 8),
              [_btn("✖️ Сбросить поиск", "mqx")] if q else [_btn("🔍 Найти игру", "mq")],
              [_btn("🎮 Создать", "cg:0")], [_btn("🗑 Удалить несколько", "mdel:0")], _back()))


def act_maps_search_clear(call, *_):
    _uid(call).pop("mq", None)
    scr_maps(call)


def _tri(v, inherit: bool) -> str:
    return f"наследовать ({_onoff(inherit)})" if v is None else _onoff(v)


def scr_map(call, lot_id):
    m = _map_by_lot(lot_id)
    if not m:
        return scr_maps(call)
    prod = next((p for p in _products() or [] if p["id"] == m["game_id"]), None)
    status = {"⏸": "⏸ выключен вручную", "🚑": "🚑 на паузе после ошибки FunPay",
              "⛔": "⛔ снят с продажи: " + {"stock": "нет аккаунтов", "balance": "низкий баланс"}.get(
                  HIDDEN.get(str(lot_id)), "?"), "✅": "✅ активен"}[_map_status(m)]
    p = PROBLEMS.get(str(lot_id))
    hours = int(m["hours"])
    _edit(call, f"🔗 <b>Привязка</b>\n\n🎮 {esc(m['game'])} (<code>{esc(m['game_id'])}</code>)\n"
                f"🆔 Лот: <a href=\"https://funpay.com/lots/offer?id={lot_id}\">{lot_id}</a>\n"
                f"🏷 Название: <code>{esc((m.get('titles') or ['—'])[0])}</code>\n"
                f"🔖 ID в описании: " + (f"<code>{m['tag']}</code>" if m.get("tagged") else "ставится…" if S.get("fp_edit")
                                          else "нет — плагину запрещено менять лоты") + "\n"
                f"⏱ За 1 шт: <b>{_dur(hours)}</b>\n"
                f"💰 Цена FP: <b>{_num(m['price']) + '₽' if m.get('price') else '?'}</b>"
                + (f" (база MUVSell {_rub(_cost(_api(), prod, hours))} → по наценке {_price(_api(), prod, hours, m)}₽)"
                   if prod else "")
                + f"\n➗ Наценка: <b>{_num(_markup(m))}%</b> ({_markup_src(m)})\n"
                f"💲 Цена: {'авто по наценке' if _auto_price(m) else 'вручную (плагин не меняет)'}\n"
                f"🛡 Автоскрытие: {_tri(m.get('autohide'), S.get('hide_no_stock'))}\n"
                f"🎁 Бонус за отзыв: {_tri(m.get('bonus'), S.get('review_bonus'))}\n"
                f"Статус: {status}" + (f"\n❗ {esc(p.get('err', ''))}" if p else ""),
          _kb([_btn("⏱ Часы", f"mh:{lot_id}"), _btn("➗ Наценка", f"mm:{lot_id}")],
              [_btn(f"💲 Цена: {'авто' if _auto_price(m) else 'вручную'}", f"mrp:{lot_id}"),
               _btn("🔁 Пересчитать", f"mnow:{lot_id}")],
              [_btn("🛡 Автоскрытие", f"mah:{lot_id}"), _btn("🎁 Бонус", f"mbn:{lot_id}")],
              [_btn("▶️ Включить" if m.get("off") else "⏸ Выключить", f"moff:{lot_id}")],
              [_btn("🗑 Удалить привязку", f"md:{lot_id}")], _back("maps:0")))


def act_map_hours(call, lot_id):
    _ask(call, f"hours:{lot_id}", f"<b>⏱ Срок за 1 шт</b>\n\nСколько аренды выдавать за 1 шт лота {lot_id}? "
                                  f"Часы числом или дни с «д» (напр. <code>3</code>, <code>7д</code>), "
                                  f"от {MIN_HOURS} до {MAX_HOURS} ч:", f"map:{lot_id}")


def act_map_markup(call, lot_id):
    m = _map_by_lot(lot_id)
    if not m:
        return scr_maps(call)
    _ask(call, f"mapmk:{lot_id}", f"<b>➗ Наценка привязки</b>\n\nСейчас: <b>{_num(_markup(m))}%</b> ({_markup_src(m)}).\n"
                                  "Отправьте процент, или <code>-</code> — наследовать (категория / глобальная):",
         f"map:{lot_id}")


def _map_cycle(call, lot_id, key):
    m = _map_by_lot(lot_id)
    if not m:
        return scr_maps(call)
    m[key] = {None: True, True: False, False: None}[m.get(key)]
    _save("mappings")
    scr_map(call, lot_id)


def act_map_reprice_mode(call, lot_id):
    m = _map_by_lot(lot_id)
    if m:
        m["reprice"] = not _auto_price(m)
        _save("mappings")
    scr_map(call, lot_id)


def act_map_reprice_now(call, lot_id):
    m = _map_by_lot(lot_id)
    prod = m and next((p for p in _products(force=True) or [] if p["id"] == m["game_id"]), None)
    if not prod:
        return _alert(call, "Игра не найдена в каталоге MUVSell")
    price = _price(_api(), prod, int(m["hours"]), m)
    try:
        res = _set_price(m, price)
    except _RateLimited:
        return _alert(call, "FunPay временно ограничил изменения — попробуйте позже")
    _save("mappings")
    _alert(call, {"set": f"✅ Цена {price}₽ выставлена", "same": f"➖ Цена уже {price}₽"}.get(
        res, "❌ Лот не открылся — он в «🚑 Проблемных лотах»"))
    scr_map(call, lot_id)


def act_map_off(call, lot_id):
    m = _map_by_lot(lot_id)
    if not m:
        return scr_maps(call)
    off = not m.get("off")
    if S.get("fp_edit") and not _set_active(m, not off and str(lot_id) not in HIDDEN):
        return _alert(call, "❌ Лот не открылся на FunPay — попробуйте позже")
    m["off"] = off
    _save("mappings")
    scr_map(call, lot_id)


def act_map_delete(call, lot_id):
    _edit(call, f"Удалить привязку лота {lot_id}?\nСам лот на FunPay останется.",
          _kb([_btn("✅ Удалить", f"mdy:{lot_id}"), _btn("❌ Нет", f"map:{lot_id}")]))


def act_map_delete_yes(call, lot_id):
    m = _map_by_lot(lot_id)
    with _lock:
        MAPS[:] = [x for x in MAPS if str(x.get("lot_id")) != str(lot_id)]
        was_hidden = HIDDEN.pop(str(lot_id), None)
        PROBLEMS.pop(str(lot_id), None)
    _save("mappings")
    _save("problems")
    if was_hidden and m:  # плагин снимал лот с продажи — возвращаем, иначе он так и останется выключенным
        _save("hidden")
        threading.Thread(target=_set_active, args=(m, True), daemon=True).start()
    scr_maps(call)


def scr_multi_delete(call, page="0"):
    sel = _uid(call).setdefault("sel", set())
    page, chunk = _page(MAPS, page, 8)
    rows = [[_btn(f"{'☑️' if str(m['lot_id']) in sel else '⬜️'} {m['game'][:28]} | {_short(int(m['hours']))} | {m['lot_id']}",
                  f"mdt:{m['lot_id']}:{page}")] for m in chunk]
    _edit(call, f"🗑 <b>Удалить несколько</b>\n\nОтмечено: <b>{len(sel)}</b> из {len(MAPS)}. Нажмите на привязки, "
                "которые нужно удалить, или отметьте все сразу.",
          _kb(*rows, _nav("mdel", page, len(MAPS), 8),
              [_btn(f"☑️ Отметить все ({len(MAPS)})", "mdall")] if len(sel) < len(MAPS) else None,
              [_btn(f"🗑 Только привязки ({len(sel)})", "mdgo:maps")] if sel else None,
              [_btn(f"🗑 Привязки и лоты FunPay ({len(sel)})", "mdgo:lots")] if sel else None,
              [_btn("✖️ Снять отметки", "mdclr")] if sel else None, _back("maps:0")))


def act_multi_all(call, *_):
    _uid(call)["sel"] = {str(m["lot_id"]) for m in MAPS}
    scr_multi_delete(call)


def act_multi_toggle(call, arg):
    lot_id, _, page = arg.rpartition(":")
    _uid(call).setdefault("sel", set()).symmetric_difference_update({lot_id})
    scr_multi_delete(call, page)


def act_multi_clear(call, *_):
    _uid(call).pop("sel", None)
    scr_multi_delete(call)


def act_multi_go(call, mode):
    """Подтверждение: одним нажатием теперь можно отметить все привязки."""
    targets = [m for m in MAPS if str(m["lot_id"]) in (_uid(call).get("sel") or set())]
    if not targets:
        return scr_maps(call)
    manual = sum(1 for m in targets if not m.get("auto"))
    what = (f"<b>{len(targets)}</b> привязок и их лоты <b>с FunPay</b>" +
            (f"\n⚠️ Среди них {manual} ваших собственных лотов, привязанных вручную, — они тоже удалятся с FunPay."
             if manual else "") if mode == "lots" else f"<b>{len(targets)}</b> привязок (лоты на FunPay останутся)")
    _edit(call, f"🗑 Удалить {what}?\n\nЭто нельзя отменить.",
          _kb([_btn("✅ Да, удалить", f"mdgoy:{mode}"), _btn("❌ Нет", "mdel:0")]))


def act_multi_go_yes(call, mode):
    sel = _uid(call).pop("sel", set())
    targets = [m for m in MAPS if str(m["lot_id"]) in sel]
    if not targets:
        return scr_maps(call)
    _start_job(call, "Удаление", _run_delete, targets, mode == "lots", "maps:0")


def scr_products(call, page="0"):
    """Шаг «выбор игры» при привязке своего лота."""
    info = _uid(call)
    if "lot_id" not in info:
        return scr_maps(call)
    prods = [p for p in _products() or [] if not info.get("q") or info["q"] in p["name"].lower()]
    page, chunk = _page(prods, page, 8)
    rows = [[_btn(f"{p['name']} · {p.get('inStock', 0)} акк."[:60], f"pp:{p['id']}")] for p in chunk]
    head = f"🔗 <b>Привязка лота — игра MUVSell</b>\n\nЛот: <code>{esc((info.get('titles') or [info['lot_id']])[0])}</code>\n"
    _edit(call, head + ("Выберите игру:" if prods else "Ничего не найдено (или API-ключ не задан)."),
          _kb(*rows, _nav("pl", page, len(prods), 8), [_btn("🔍 Поиск", "ps")], _back("maps:0")))


def act_pick_product(call, game_id):
    info = _uid(call)
    prod = next((p for p in _products() or [] if p["id"] == game_id), None)
    if "lot_id" not in info or not prod:
        return scr_maps(call)
    info.update(game_id=game_id, game=prod["name"])
    _ask(call, "newmap", f"<b>🔗 Привязка лота — срок</b>\n\nИгра: <b>{esc(prod['name'])}</b>\n\n"
                         "Сколько аренды выдавать за 1 шт лота? Часы числом или дни с «д» "
                         f"(напр. <code>3</code>, <code>7д</code>), от {MIN_HOURS} до {MAX_HOURS} ч:", "maps:0")


def act_bind_lot(call, *_):
    _tmp.pop(call.from_user.id, None)
    _ask(call, "lot", "🔗 <b>Привязать лот</b>\n\nОтправьте <b>ID лота</b> или <b>ссылку</b> на лот FunPay.\n\n"
                      "Например:\n<code>123456789</code>\nили\n<code>https://funpay.com/lots/offer?id=123456789</code>\n\n"
                      "📌 Название лота определится автоматически.")


# ---------------------------------------------------------------- Telegram: создать привязку (игра → сроки)

def scr_games(call, page="0"):
    _wait(call)
    q = _uid(call).get("gq")
    prods = _products()
    if prods is None:
        return _edit(call, "🔑 Сначала задайте API-ключ (⚙️ Настройки) — без него каталог MUVSell не загрузить.", _kb(_back()))
    mapped = {m["game_id"] for m in MAPS}
    items = sorted((p for p in prods if not q or q in p["name"].lower()),
                   key=lambda p: (not int(p.get("inStock") or 0), p["name"].lower()))
    page, chunk = _page(items, page, 8)
    usd = S.get("pay") == "usd"
    rows = [[_btn(f"{'✅' if int(p.get('inStock') or 0) else '⛔'}{'🔗' if p['id'] in mapped else '🆕'} {p['name'][:26]} | "
                  + (f"${_num(p.get('pricePerHourUsd') or 0)}/ч" if usd else f"{_num(p.get('pricePerHourRub') or 0)}₽/ч")
                  + f" | {int(p.get('inStock') or 0)} акк.", f"gm:{p['id']}")] for p in chunk]
    _edit(call, f"🎮 <b>Выберите игру</b> ({len(items)} шт.)" + (f" · поиск «{esc(q)}»" if q else "")
          + f"\n\nФормула: цена MUVSell × (1 + {_num(S.get('markup') or 0)}%)\n"
            "🔗 — на игру уже есть привязка (хотя бы на один срок); 🆕 — привязок ещё нет\n"
            "✅ — есть свободные аккаунты; ⛔ — сейчас нет",
          _kb(*rows, _nav("cg", page, len(items), 8),
              [_btn("✖️ Сбросить поиск", "cgx")] if q else [_btn("🔍 Поиск", "cgs")], _back()))


def act_games_search_clear(call, *_):
    _uid(call).pop("gq", None)
    scr_games(call)


def scr_game(call, game_id):
    prod = next((p for p in _products() or [] if p["id"] == game_id), None)
    if not prod:
        return scr_games(call)
    api, g = _api(), _fp_game(game_id)
    sub = int(g["funpay"]["subcategory_id"]) if g else None
    have = {int(m["hours"]): m for m in MAPS if m["game_id"] == game_id and not m.get("manual")}
    pm = {"subcat": sub, "markup": S.get("ap_own")}
    lines, rows, row = [], [], []
    for h in S["ap_durations"]:
        price = _price(api, prod, h, pm)
        m = have.get(h)
        lines.append(f"{'🔗' if m else '🆕'} {_dur(h)}: {_rub(_cost(api, prod, h))} → <b>{price}₽</b>"
                     + (f" (лот {m['lot_id']})" if m else ""))
        row.append(_btn(f"🔗 {_dur(h)}" if m else f"🆕 {_dur(h)} · {price}₽",
                        f"map:{m['lot_id']}" if m else f"gc:{game_id}:{h}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    rows.append(row)
    missing = sum(1 for h in S["ap_durations"] if h not in have)
    _edit(call, f"🎮 <b>{esc(prod['name'])}</b>\n\n📦 Свободно аккаунтов: <b>{int(prod.get('inStock') or 0)}</b>\n"
                f"🗂 Раздел FunPay: " + (f"<code>{sub}</code>" if g else "❌ своего раздела нет — выставьте в Steam "
                                                                        "или «Прочие игры» (🤖 Автовыставление) или "
                                                                        "привяжите свой лот")
                + f"\n➗ Наценка новых лотов: <b>{_num(_markup(pm))}%</b>\n\n<i>Срок: база MUVSell → цена лота</i>\n"
                + "\n".join(lines),
          _kb(*(rows if g else []), [_btn(f"➕ Создать все недостающие ({missing})", f"gca:{game_id}")] if g and missing else None,
              [_btn("🔗 Привязать свой лот", f"gb:{game_id}")], _back("cg:0")))


def act_game_create(call, arg):
    game_id, _, hours = arg.rpartition(":")
    g = _fp_game(game_id)
    prod = next((p for p in _products() or [] if p["id"] == game_id), None)
    if not g or not prod:
        return _alert(call, "Для этой игры нет раздела FunPay — привяжите свой лот")
    have = {int(m["hours"]) for m in MAPS if m["game_id"] == game_id and not m.get("manual")}
    todo = [h for h in (S["ap_durations"] if hours == "all" else [int(hours)]) if h not in have]
    if not todo:
        return scr_game(call, game_id)
    _start_job(call, "Создание лотов", _run_create, [(g, prod, h) for h in todo])


def _manual_game(prod: dict, kind: str) -> dict:
    """Игра для общего раздела (Steam / «Прочие игры») — в формате записи карты."""
    g = _fp_game(prod["id"])  # название из карты — по нему в «Прочих играх» выбирается игра в списке FunPay
    return {"game_id": prod["id"], "name": (g or prod)["name"], "manual": kind,
            "funpay": {"subcategory_id": MANUAL[kind][0], "fields": {}}}


def _manual_games(kind: str) -> list:
    """Игры каталога для общего раздела: в Steam — любая, в «Прочие игры» — только без своего раздела в карте."""
    return [p for p in _products() or [] if kind != "other" or not _fp_game(p["id"])]


def _manual_todo(kind: str, game_id: str) -> list:
    """Сроки из «Длительностей», на которые игры ещё нет в общем разделе."""
    have = {int(m["hours"]) for m in MAPS if m["game_id"] == game_id and m.get("manual") == kind and not _stale(m)}
    return [h for h in S["ap_durations"] if h not in have]


def scr_manual(call, arg):
    """Автовыставление в общий раздел (Steam / «Прочие игры»): нажали на игру — она выставляется на все сроки."""
    kind, _, page = arg.partition(":")
    if kind not in MANUAL:
        return scr_ac(call)
    if _products() is None:
        return _edit(call, "🔑 Сначала задайте API-ключ (⚙️ Настройки) — без него каталог MUVSell не загрузить.", _kb(_back("ac")))
    sub, label = MANUAL[kind]
    items = sorted(_manual_games(kind), key=lambda p: (not int(p.get("inStock") or 0), p["name"].lower()))
    page, chunk = _page(items, page or "0", 8)
    total = len(S["ap_durations"])
    rows = []
    for p in chunk:
        left = len(_manual_todo(kind, p["id"]))
        rows.append([_btn(f"{'✅' if not left else '🔗' if left < total else '🆕'} {p['name'][:30]} · {total - left}/{total} "
                          f"· {int(p.get('inStock') or 0)} акк.", f"gxc:{kind}:{p['id']}")])
    in_sub = sum(1 for m in MAPS if m.get("auto") and str(m.get("subcat")) == str(sub))
    _edit(call, f"🤖 <b>Автовыставление → {label}</b>\n\n"
                + ("Общий раздел Steam, тип «Аренда». " if kind == "steam" else
                   "Раздел «Аккаунты прочих игр», тип «Аренда». Здесь только игры, у которых на FunPay нет своего "
                   "раздела (остальные выставляет обычное автовыставление). Игра выбирается в списке FunPay по "
                   "названию, нет её там — «Другая игра». ")
                + "Нажмите на игру — плагин сразу выставит её на все сроки из «Длительностей», по тем же шаблонам, "
                  "что и обычное автовыставление. Лимит предложений в разделе общий на все игры — выбирайте только "
                  "нужные игры.\n\n"
                + (f"🌍 Регион лота: <b>{esc(S.get('steam_region') or '')}</b>\n" if kind == "steam" else "")
                + f"⏱ Сроки: <code>{_durs(S['ap_durations'])}</code>\n"
                  f"🔢 Лотов плагина в разделе: <b>{in_sub}</b> из {S['lot_cap']}\n"
                  f"<b>0/{len(S['ap_durations'])}</b> — на сколько сроков из «Длительностей» игра уже выставлена "
                  "(🆕 ни на один · 🔗 не на все · ✅ на все); <b>акк.</b> — свободных аккаунтов на MUVSell сейчас",
          _kb(*rows, _nav(f"gx:{kind}", page, len(items), 8),
              [_btn(f"🌍 Регион: {S.get('steam_region') or ''}"[:60], "gsr")] if kind == "steam" else None,
              [_btn("⏱ Длительности", "apd"), _btn("📝 Тексты лотов", "apt")], _back("ac")))


def act_game_manual_create(call, arg):
    kind, _, game_id = arg.partition(":")
    if kind not in MANUAL:
        return scr_ac(call)
    prod = next((p for p in _manual_games(kind) if p["id"] == game_id), None)
    if not prod:
        return scr_manual(call, f"{kind}:0")
    todo = _manual_todo(kind, game_id)
    if not todo:
        return _alert(call, f"{prod['name']} уже выставлена на все сроки")
    _start_job(call, "Создание лотов", _run_create, [(_manual_game(prod, kind), prod, h) for h in todo])


def act_game_bind(call, game_id):
    prod = next((p for p in _products() or [] if p["id"] == game_id), None)
    if not prod:
        return scr_games(call)
    _tmp[call.from_user.id] = {"game_id": game_id, "game": prod["name"]}
    _ask(call, "lot", f"🔗 <b>Привязать свой лот к {esc(prod['name'])}</b>\n\nОтправьте ID лота или ссылку на лот FunPay:",
         f"gm:{game_id}")


# ---------------------------------------------------------------- Telegram: аренды

def scr_rentals(call, page="0"):
    items = _all_active()
    page, chunk = _page(items, page, 8)
    now = time.time()
    rows = [[_btn(f"{r['login']} · {r['game'][:18]} · {r.get('buyer') or '?'} · ⏳{_left(r['exp'] - now)}"[:60],
                  f"rn:{r['id']}")] for r in chunk]
    _edit(call, f"📋 <b>Активные аренды ({len(items)})</b>" + ("" if items else "\n\nСейчас активных аренд нет."),
          _kb(*rows, _nav("rl", page, len(items), 8), [_btn("🔄 Обновить", "rl:0")], _back()))


def scr_rental(call, rid):
    r = _rec(rid)
    if not r:
        return scr_rentals(call)
    paid = [s for s in SALES if s.get("rid") == r["id"]]
    _edit(call, f"📋 <b>Аренда №{r.get('number') or '?'}</b>\n\n🎮 {esc(r['game'])}\n👤 Логин: <code>{esc(r['login'])}</code>\n"
                f"🛒 Покупатель: <b>{esc(r.get('buyer') or '?')}</b>\n"
                f"🧾 Заказ: <a href=\"https://funpay.com/orders/{r.get('order')}/\">#{r.get('order')}</a>\n"
                f"🕒 До: {_when(r['exp'])} (ещё {_left(r['exp'] - time.time())})\n"
                f"💰 Выручка {_rub(sum(s['rev'] for s in paid))} · расход {_rub(sum(s['cost'] for s in paid))}",
          _kb([_btn("🔐 Код", f"rc:{rid}"), _btn("🚪 Кик сессий", f"rk:{rid}")],
              [_btn("🔑 Сменить пароль", f"rp:{rid}"), _btn("➕ Продлить", f"rx:{rid}")],
              [_btn("⛔ Завершить досрочно", f"rtm:{rid}")], _back("rl:0")))


def act_rental_code(call, rid):
    r, api = _rec(rid), _api()
    code = _guard(api, r) if r and api else None
    _alert(call, f"🔐 {r['login']}: {code['code']} (ещё ~{code.get('expiresIn', 30)} с)" if code
           else "❌ Код не получен: " + (api.error if api and api.error else "нет maFile или аренда закрыта"))


def act_rental_kick(call, rid):
    r, api = _rec(rid), _api()
    if not r or not api:
        return scr_rentals(call)
    _, err = api.kick(r["id"])
    _alert(call, "✅ Сессии выкинуты" if not err else f"❌ {api.error or _human(err)}")


def act_rental_password(call, rid):
    r, api = _rec(rid), _api()
    if not r or not api:
        return scr_rentals(call)
    err = _change_password(api, r, r.get("chat"))
    _alert(call, f"❌ {err}" if err else "🔑 Пароль меняется — новый придёт покупателю в чат FunPay")


def act_rental_extend(call, rid):
    _ask(call, f"rext:{rid}", f"➕ <b>Продлить аренду</b>\n\nНа сколько? Часы числом или дни с «д» (напр. <code>5</code>, "
                              f"<code>2д</code>), до {MAX_HOURS} ч.\nСпишется с баланса MUVSell, покупатель получит сообщение.",
         f"rn:{rid}")


def act_rental_terminate(call, rid):
    _edit(call, "⛔ Завершить аренду досрочно? Деньги на MUVSell не вернутся, покупатель потеряет доступ.",
          _kb([_btn("✅ Завершить", f"rty:{rid}"), _btn("❌ Нет", f"rn:{rid}")]))


def act_rental_terminate_yes(call, rid):
    r, api = _rec(rid), _api()
    if not r or not api:
        return scr_rentals(call)
    _, err = api.terminate(r["id"])
    if err:
        return _alert(call, f"❌ {api.error or _human(err)}")
    r.update(exp=time.time(), ended=True)
    _save("rentals")
    scr_rentals(call)


# ---------------------------------------------------------------- Telegram: статистика и прибыль

def scr_stats(call, p="all"):
    p = p if p in PERIODS else "all"
    table = ["Период     Прод  Выручка  Прибыль"]
    for key in ("today", "yday", "7", "30", "all"):
        a = _agg(_sales(key))
        table.append(f"{PERIODS[key]:<10}{a['n']:>5}{a['rev']:>9,.0f}{a['gross']:>9,.0f}".replace(",", " "))
    lst = _sales(p)
    a, sold = _agg(lst), _sold(lst)
    buyers = Counter(s["buyer"].lower() for s in sold if s["buyer"])
    active = _all_active()
    active_ids = {r["id"] for r in active}
    top = Counter(s["game"] for s in _sold(_sales("30")))
    lead_line = ""
    if top:
        g, n = top.most_common(1)[0]
        lead_line = f"\n🏆 Лидер за 30 дней: <b>{esc(g)}</b> — {n} шт · {_rub(_profit([s for s in _sales('30') if s['game'] == g]))}\n"
    icons = {"new": "🆕", "ext": "🔄", "bonus": "🎁", "admin": "🛠"}
    last = "\n".join(f"{'↩️' if s.get('refunded') else icons.get(s['kind'], '•')} {esc(s['game'])} · "
                     f"{esc(s['buyer'] or '—')} · {'+' if s['rev'] - s['cost'] >= 0 else ''}{_rub(s['rev'] - s['cost'])} "
                     f"<i>({datetime.fromtimestamp(s['ts'], _tz()).strftime('%d.%m %H:%M')})</i>" for s in SALES[-5:][::-1])
    text = (f"📊 <b>Статистика MUVSell</b>\n<i>суммы в ₽</i>\n\n<pre>{esc(chr(10).join(table))}</pre>\n"
            f"💼 <b>Сейчас</b>\n🔗 Привязок: {len(MAPS)} (активных {_active_maps()})\n"
            f"📋 Активных аренд: {len(active)} на {_rub(sum(s['rev'] for s in SALES if s.get('rid') in active_ids))}\n\n"
            f"{'♾' if p == 'all' else '📅'} <b>{'За всё время' if p == 'all' else PERIODS[p]}</b>\n"
            f"📈 Маржа: {(a['gross'] / a['rev'] * 100 if a['rev'] else 0):.1f}%\n"
            f"💳 Средний чек: {_rub(a['rev'] / a['n'] if a['n'] else 0)}\n"
            f"👥 Покупателей: {len(buyers)} (🔁 повторных: {sum(1 for n in buyers.values() if n > 1)})\n"
            f"🎮 Игр продавалось: {len({s['game_id'] for s in sold})}\n"
            f"↩️ Возвратов: {a['refunds']} ({_rub(a['refund'])}, {(a['refunds'] / a['n'] * 100 if a['n'] else 0):.1f}% от продаж)\n"
            + lead_line + ("\n🧾 <b>Последние продажи</b>\n" + last if last else ""))
    _edit(call, text, _kb([_btn(PERIODS[k], f"st:{k}") for k in ("today", "yday", "7")],
                          [_btn(PERIODS[k], f"st:{k}") for k in ("30", "90", "all")],
                          [_btn("🏆 Топ игр", f"sx:games:{p}"), _btn("👥 Покупатели", f"sx:buyers:{p}")],
                          [_btn("⏳ Длительности", f"sx:hours:{p}"), _btn("⏰ Активность", f"sx:activity:{p}")],
                          [_btn("📈 По дням", f"sx:days:{p}"), _btn("🔗 Привязки", f"sx:maps:{p}")], _back()))


def scr_stats_detail(call, arg):
    kind, _, p = arg.partition(":")
    p = p if p in PERIODS else "all"
    groups = defaultdict(list)
    title = {"games": "🏆 Топ игр", "buyers": "👥 Покупатели", "hours": "⏳ Длительности", "activity": "⏰ Активность",
             "days": "📈 По дням", "maps": "🔗 Привязки"}.get(kind, "📊")
    key = {"games": lambda s: s["game"], "buyers": lambda s: s["buyer"] or "—", "hours": lambda s: s["hours"],
           "activity": lambda s: datetime.fromtimestamp(s["ts"], _tz()).hour,
           "days": lambda s: _day(s["ts"]).isoformat(), "maps": lambda s: s.get("lot") or "—"}.get(kind, lambda s: "")
    for s in _sales(p):
        groups[key(s)].append(s)
    if kind == "activity":
        counts = {h: len(_sold(groups.get(h, []))) for h in range(24)}
        top = max(counts.values()) or 1
        lines = [f"<code>{h:02d}  {'▇' * round(c / top * 12):<12} {c}</code>" for h, c in counts.items()]
    elif kind == "days":
        lines = [f"{d}: +{_num(round(sum(s['rev'] for s in groups[d])))} -{_num(round(sum(s['cost'] for s in groups[d])))} = "
                 f"<b>{_rub(_profit(groups[d]))}</b>" for d in sorted(groups, reverse=True)[:31]]
    else:
        names = {str(m["lot_id"]): _mlabel(m) for m in MAPS}
        lines = []
        for i, (k, g) in enumerate(sorted(groups.items(), key=lambda kv: (-_profit(kv[1]), -len(kv[1])))[:20], 1):
            label = _dur(int(k)) if kind == "hours" and k else names.get(str(k), f"лот {k}") if kind == "maps" else str(k)
            n = len({s["order"] for s in _sold(g)})
            lines.append(f"{i}. {esc(label)} — {n} шт · {_rub(sum(s['rev'] for s in g))} → <b>{_rub(_profit(g))}</b>")
    _edit(call, f"{title} · <b>{PERIODS[p]}</b>\n\n" + ("\n".join(lines) or "Продаж за период нет."),
          _kb([_btn(PERIODS[k], f"sx:{kind}:{k}") for k in ("7", "30", "all")], _back(f"st:{p}")))


def scr_profit(call, *_):
    a, today = _agg(SALES), _agg(_sales("today"))
    days = defaultdict(list)
    for s in _sales("7"):
        days[_day(s["ts"]).isoformat()].append(s)
    by_day = "\n".join(f"  {d}: +{_num(round(sum(s['rev'] for s in g)))} -{_num(round(sum(s['cost'] for s in g)))} = "
                       f"{_rub(_profit(g))}" for d, g in sorted(days.items(), reverse=True))
    _edit(call, f"💰 <b>Прибыль</b>\n\n💵 Выручка: {_rub(a['rev'])}\n💸 Расходы: {_rub(a['cost'])}\n"
                f"📈 Валовая: {_rub(a['gross'])}\n↩️ Возвраты: -{_rub(a['refund'])}\n✅ Чистая: <b>{_rub(a['net'])}</b>\n"
                f"📊 Маржа: {(a['gross'] / a['rev'] * 100 if a['rev'] else 0):.1f}%\n\n"
                f"📅 Сегодня: +{_rub(today['net'])}\n\n<b>По дням:</b>\n" + (by_day or "  продаж за 7 дней нет"),
          _kb([_btn("📊 Подробная статистика", "st:all")], [_btn("📈 Динамика по дням", "sx:days:30")], _back()))


# ---------------------------------------------------------------- Telegram: настройки

def _proxy_label() -> str:
    mode = S.get("proxy_mode") or "none"
    return {"none": "без прокси", "fpc": "🤖 прокси FunPay Cardinal"}.get(mode) or f"свой ({esc(S.get('proxy') or '—')})"


def _ntf_on() -> int:
    return sum(1 for k in NOTIFY_CATS if S["notify"].get(k, True))


def _stock_label() -> str:
    sec = int(S.get("poll_sec") or 60)
    return f"{sec // 60}м" if sec % 60 == 0 else f"{sec}с"


def scr_settings(call, *_):
    key = S.get("api_key") or ""
    paused = sum(1 for m in MAPS if _paused(m))
    ntf = _ntf_on()
    warn = int(S["warn_min"])
    text = (f"⚙️ <b>Настройки</b>\n\n"
            f"{'🟢 Автовыдача: ВКЛ' if S['enabled'] else '🔴 Автовыдача: ВЫКЛ'}\n"
            f"🔑 API: <code>{esc(key[:10] + '...' + key[-4:] if len(key) > 16 else key or 'не задан')}</code>\n"
            f"🌐 Прокси MUVSell: {_proxy_label()}\n"
            f"➗ Наценка: {_num(S['markup'])}%\n"
            f"🏷 Учитывать скидку за объём: {_onoff(S['vol_discount'])} {'вкл' if S['vol_discount'] else 'выкл'}\n"
            f"🛒 Менять цену/видимость на FunPay: {_onoff(S['fp_edit'])}\n"
            f"💸 Автовозврат: {_onoff(S['auto_refund'])}\n"
            f"🛑 Стоп при низком балансе: {_onoff(S['hide_low_balance'])}\n"
            f"⏳ Предупреждение о сроке: {f'{warn} мин.' if warn else 'выкл'}\n"
            f"🎁 Бонус за отзыв (глобально): {_onoff(S['review_bonus'])} +{S['bonus_hours']}ч\n"
            f"🔄 Продление по команде: {_onoff(S['ext_cmd'])} {esc(S['ext_word'])} (временный лот, "
            f"{int(S['ext_minutes'])} мин.)\n"
            f"🧰 Команды покупателя (!кик, !пароль): {_onoff(S['buyer_cmds'])}\n"
            f"🔔 Уведомления: {'все включены' if ntf == len(NOTIFY_CATS) else f'{ntf} из {len(NOTIFY_CATS)}'}\n"
            f"🔄 Интервал цен: {_num(S['price_min'])} мин.\n"
            f"📦 Интервал наличия: {_stock_label()}\n"
            f"🚑 Лотов на паузе после ошибки: {paused}\n\n"
            f"Формула (по умолчанию): <code>Цена FP = Цена MUVSell × (1 + {_num(S['markup'])}%)</code>\n"
            "ℹ️ У каждой привязки можно задать свою наценку, автоскрытие и бонус (наследовать / включить / выключить).")
    _edit(call, text, _kb(
        [_btn("🟢 Автовыдача: ВКЛ" if S["enabled"] else "🔴 Автовыдача: ВЫКЛ", "t:enabled")],
        [_btn("🔑 API ключ", "key")],
        [_btn(f"🌐 Прокси MUVSell: {_proxy_label()}"[:60], "px")],
        [_btn(f"➗ Наценка ({_num(S['markup'])}%)", "p:markup")],
        [_btn("♻️ Применить глобальную наценку ко ВСЕМ", "mka")],
        [_btn("📦 Наценка по категориям", "mkc")],
        [_btn(f"🏷 Скидка за объём: {_onoff(S['vol_discount'])}", "t:vol_discount")],
        [_btn(f"🛒 Менять лоты на FunPay: {_onoff(S['fp_edit'])}", "t:fp_edit")],
        [_btn(f"⏳ Предупреждать за: {warn} мин.", "p:warn_min")],
        [_btn(f"🎁 Бонус за отзыв: {_onoff(S['review_bonus'])} +{S['bonus_hours']}ч", "bn")],
        [_btn(f"🔄 Цены ({_num(S['price_min'])}м)", "p:price_min"), _btn(f"📦 Наличие ({_stock_label()})", "p:poll_sec")],
        [_btn(f"💸 Автовозврат: {_onoff(S['auto_refund'])}", "t:auto_refund")],
        [_btn(f"🛑 Стоп при низком балансе: {_onoff(S['hide_low_balance'])}", "t:hide_low_balance")],
        [_btn(f"🔄 Продление по команде: {_onoff(S['ext_cmd'])} {S['ext_word']}"[:60], "t:ext_cmd")],
        [_btn(f"🧰 Команды покупателя: {_onoff(S['buyer_cmds'])}", "t:buyer_cmds")],
        [_btn(f"🔔 Уведомления ({ntf}/{len(NOTIFY_CATS)})", "ntf")],
        [_btn("📝 Шаблоны сообщений", "texts")],
        [_btn(f"🚑 Проблемные лоты ({paused})", "q")],
        [_btn("⚙️ Прочее", "params"), _btn("ℹ️ Справка", "help")],
        _back(),
    ))


def act_key(call, *_):
    cur = S.get("api_key") or ""
    _ask(call, "key", f"<b>🔑 API-ключ MUVSell</b>\n\nСоздайте ключ: {SITE}/profile → API.\n"
                      f"Текущий: <code>{esc(cur[:8] + '…' + cur[-4:] if len(cur) > 16 else cur or 'не задан')}</code>\n\n"
                      "Отправьте ключ одним сообщением:", "set")


def scr_proxy(call, *_):
    mode = S.get("proxy_mode") or "none"

    def opt(m, label):
        return [_btn(("🔘 " if mode == m else "⚪️ ") + label, f"pxm:{m}")]
    _edit(call, f"🌐 <b>Прокси для запросов к MUVSell</b>\n\nСейчас: {_proxy_label()}\n\n"
                "Нужен, если сервер, где работает FunPay Cardinal, не видит muvsell.store.",
          _kb(opt("none", "Без прокси"), opt("fpc", "🤖 Прокси FunPay Cardinal"), opt("custom", "✍️ Свой прокси"),
              _back("set")))


def act_proxy_mode(call, mode):
    if mode == "custom":
        return _ask(call, "proxy", "✍️ <b>Свой прокси</b>\n\nФормат: <code>http://логин:пароль@ip:порт</code> "
                                   "или <code>socks5://ip:порт</code>:", "px")
    S["proxy_mode"] = mode
    _save("settings")
    scr_proxy(call)


def act_markup_all(call, *_):
    own = sum(1 for m in MAPS if m.get("markup") is not None)
    _edit(call, f"♻️ Применить глобальную наценку <b>{_num(S['markup'])}%</b> ко всем?\n\n"
                f"Сбросится своя наценка у <b>{own}</b> привязок и наценки всех категорий "
                f"({len(S.get('cat_markup') or {})}), затем пересчитаются цены лотов с автоценой.",
          _kb([_btn("✅ Применить", "mkay"), _btn("❌ Нет", "set")]))


def act_markup_all_yes(call, *_):
    for m in MAPS:
        m["markup"] = None
    S["cat_markup"] = {}
    _save("mappings")
    _save("settings")
    if not S.get("fp_edit"):
        return _alert(call, "Наценка сброшена. Изменение лотов на FunPay выключено — цены не пересчитаны.")
    _start_job(call, "Пересчёт цен", _run_reprice)


def _sub_label(sub) -> str:
    games = sorted({m["game"] for m in MAPS if str(m.get("subcat")) == str(sub)})
    return (", ".join(games[:2]) + (f" +{len(games) - 2}" if len(games) > 2 else "")) or str(sub)


def scr_cat_markup(call, page="0"):
    subs = sorted({str(m["subcat"]) for m in MAPS if m.get("subcat")}, key=_sub_label)
    page, chunk = _page(subs, page, 10)
    cat = S.get("cat_markup") or {}
    rows = [[_btn(f"📦 {_sub_label(s)[:36]} — {_num(cat[s]) + '%' if s in cat else 'глоб.'}", f"mkcs:{s}")] for s in chunk]
    _edit(call, f"📦 <b>Наценка по категориям</b>\n\nКатегория = раздел FunPay. Наценка категории действует на привязки "
                f"без своей наценки. «глоб.» — берётся глобальная ({_num(S['markup'])}%).",
          _kb(*rows, _nav("mkc", page, len(subs), 10), [_btn("🔁 Пересчитать все лоты", "rpa")], _back("set")))


def act_cat_markup(call, sub):
    cur = (S.get("cat_markup") or {}).get(sub)
    _ask(call, f"catmk:{sub}", f"📦 <b>{esc(_sub_label(sub))}</b>\n\nСейчас: <b>{_num(cur) + '%' if cur is not None else 'глобальная'}</b>\n"
                               "Отправьте процент, или <code>-</code> — вернуть глобальную:", "mkc")


def scr_bonus(call, *_):
    _edit(call, f"🎁 <b>Бонус за отзыв</b>\n\nСтатус (глобально): {_onoff(S['review_bonus'])}\n"
                f"Часов в подарок: <b>{S['bonus_hours']}</b>\nЗа отзыв от <b>{S['bonus_stars']}★</b>\n\n"
                "Покупатель оставил отзыв на заказ, аренда ещё идёт → плагин продлевает её за ваш счёт (один раз). "
                "У привязки можно включить или выключить бонус отдельно.",
          _kb([_btn(f"{_onoff(S['review_bonus'])} Бонус за отзыв", "t:review_bonus")],
              [_btn(f"⏱ Часов: {S['bonus_hours']}", "p:bonus_hours"), _btn(f"⭐ От {S['bonus_stars']}★", "stars")],
              _back("set")))


def act_stars(call, *_):
    S["bonus_stars"] = int(S.get("bonus_stars") or 5) % 5 + 1
    _save("settings")
    scr_bonus(call)


def scr_notify(call, *_):
    lines = [f"{_onoff(S['notify'].get(k, True))} <b>{label}</b>\n<i>{hint}</i>" for k, (label, hint) in NOTIFY_CATS.items()]
    _edit(call, f"🔔 <b>Уведомления в Telegram</b>\n\nВключено категорий: <b>{_ntf_on()}</b> из {len(NOTIFY_CATS)}.\n"
                "Нажмите на категорию, чтобы включить или выключить её.\n\n" + "\n".join(lines)
          + "\n\nℹ️ Выключение влияет только на сообщения в Telegram — сама работа плагина не меняется: лоты так же "
            "скрываются и возвращаются, возвраты так же оформляются. Всё продолжает писаться в лог плагина.",
          _kb(*[[_btn(f"{_onoff(S['notify'].get(k, True))} {label}", f"nt:{k}")] for k, (label, _) in NOTIFY_CATS.items()],
              [_btn("✅ Включить все", "nta:1"), _btn("❌ Выключить все", "nta:0")], _back("set")))


def act_notify(call, cat):
    S["notify"][cat] = not S["notify"].get(cat, True)
    _save("settings")
    scr_notify(call)


def act_notify_all(call, on):
    S["notify"] = {k: on == "1" for k in NOTIFY_CATS}
    _save("settings")
    scr_notify(call)


def scr_problems(call, *_):
    now = time.time()
    items = sorted(PROBLEMS.items(), key=lambda kv: kv[1].get("until", 0))
    paused = sum(1 for _, p in items if p.get("until", 0) > now)
    lines = [f"🆔 <code>{lid}</code> — {esc(p.get('game', '?'))}\n  ❌ {esc(p.get('err', ''))[:150]}\n"
             f"  📌 {'лот не найден на FunPay' if p.get('missing') else 'ошибка FunPay'} | ошибок: {p.get('n', 0)}\n"
             f"  {'⏸ ещё ' + _left(p['until'] - now) if p.get('until', 0) > now else '🕓 ждёт повторной проверки'}"
             for lid, p in items[:10]]
    _edit(call, f"🚑 <b>Проблемные лоты FunPay</b>\n\n⏸ Сейчас на паузе: <b>{paused}</b>\n"
                f"🕓 Ждут повторной проверки: <b>{len(items) - paused}</b>\n"
                f"⏱ Базовая пауза: {_num(S['q_pause'])} мин. (потолок {Q_CAP} мин.)\n"
                f"🔁 Автопоиск замены: {_onoff(S['q_replace'])}\n"
                f"🗑 Автоотвязка пропавших: {_onoff(S['q_unbind'])} после {S['q_unbind_after']}\n\n"
                + ("<b>Список:</b>\n\n" + "\n\n".join(lines) if lines else "Проблемных лотов нет 👍")
                + (f"\n\n…и ещё {len(items) - 10}" if len(items) > 10 else ""),
          _kb([_btn("▶️ Снять все паузы (проверить сейчас)", "qclr")] if items else None,
              [_btn(f"⏱ Пауза после ошибки: {_num(S['q_pause'])} мин.", "p:q_pause")],
              [_btn(f"🔁 Автопоиск замены: {_onoff(S['q_replace'])}", "t:q_replace")],
              [_btn(f"🗑 Автоотвязка пропавших: {_onoff(S['q_unbind'])}", "t:q_unbind"),
               _btn(f"после {S['q_unbind_after']}", "p:q_unbind_after")],
              [_btn(f"🔔 Уведомления о лотах: {_onoff(S['notify'].get('quarantine', True))}", "qn")],
              [_btn("🔄 Обновить", "q")], _back("set")))


def act_problems_clear(call, *_):
    _wait(call, "⏳ Проверяю лоты…")
    for lid in list(PROBLEMS):
        m = _map_by_lot(lid)
        if not m:
            PROBLEMS.pop(lid, None)
            continue
        PROBLEMS[lid]["until"] = 0
        try:
            _lot_do(m, lambda lf: True)
        except _RateLimited:
            break
    _save("problems")
    with _lock:
        _qbuf.clear()  # итог и так на экране — отдельное уведомление не нужно
    scr_problems(call)


def act_problems_notify(call, *_):
    S["notify"]["quarantine"] = not S["notify"].get("quarantine", True)
    _save("settings")
    scr_problems(call)


def scr_params(call, *_):
    rows = [[_btn(f"{label}: {_num(S[key])}", f"p:{key}")] for key, (label, _, _, back) in PARAMS.items() if back == "params"]
    rows += [[_btn(f"✏️ Команда продления: {S['ext_word']}", "extw")],
             [_btn(f"🔐 Команда кода Steam Guard: {_code_word()}", "codew")],
             [_btn(f"{_onoff(S['en_msgs'])} 🇬🇧 Английский для !code, !help…", "t:en_msgs")],
             [_btn(f"{_onoff(S['notify_end'])} Сообщение покупателю об окончании аренды", "t:notify_end")]]
    _edit(call, "⚙️ <b>Прочее</b>\n\nНажмите, чтобы изменить.", _kb(*rows, _back("set")))


def act_param(call, key):
    label, hint, _, back = PARAMS[key]
    _ask(call, f"param:{key}", f"<b>{label}</b>\n\n{hint}\n\nСейчас: <b>{_num(S[key])}</b>\nОтправьте новое число:", back)


EXT_LOT_KEYS = ("ext_title_ru", "ext_title_en", "ext_desc_ru", "ext_desc_en")


def _text_preview(key: str) -> str:
    if key in EXT_LOT_KEYS:
        return dict(zip(EXT_LOT_KEYS, _ext_texts(VAR_INFO["game"][1], 3, VAR_INFO["tag"][1])))[key]
    sample = {n: v for n, (_, v) in VAR_INFO.items()}
    sample.update(word=S.get("ext_word") or "!продление", bonus=S.get("bonus_hours"), stars=S.get("bonus_stars"),
                  commands=_commands_text())
    return re.sub(r"\{(\w+)\}", lambda mt: str(sample.get(mt.group(1), mt.group(0))), _t(key))


def scr_texts(call, *_):
    custom = S.get("texts") or {}
    rows = [[_btn(f"{label}{' ✏️' if key in custom else ''}", f"tx:{key}")] for key, label in TEXT_LABELS.items()]
    _edit(call, "📝 <b>Шаблоны сообщений</b>\n\nЧто плагин пишет покупателю в чат FunPay, и тексты временного лота "
                "продления. Нажмите, чтобы изменить; ✏️ — уже изменён вами.\n\n"
                "ℹ️ Тексты <b>основных</b> лотов (которые создаёт автовыставление) редактируются отдельно: "
                "«Автовыставление лотов» → «Тексты лотов».",
          _kb(*rows, [_btn("📝 Тексты основных лотов", "apt")], [_btn("♻️ Сбросить все шаблоны", "txra")], _back("set")))


def act_text(call, key):
    names = [n for n in dict.fromkeys(re.findall(r"\{(\w+)\}", TEXTS[key])) if n in VAR_INFO]
    lines = "\n".join(f"• <code>{{{n}}}</code> — {VAR_INFO[n][0]}" for n in names) or "<i>переменных нет — текст статичный.</i>"
    hint = ("\n\n⚠️ Название ≤ 100 символов; метка <code>#{tag}</code> всегда ставится в конец — без неё плагин не "
            "узнает оплату." if key.startswith("ext_title") else
            f"\n\n⚠️ Английское описание — минимум ~{EN_MIN} символов, короткое плагин дополнит сам."
            if key == "ext_desc_en" else "")
    _ask(call, f"text:{key}", f"✏️ <b>{TEXT_LABELS[key]}</b>\n\nТекущий шаблон:\n<code>{esc(_t(key))}</code>\n\n"
                              f"Превью:\n<code>{esc(_text_preview(key))}</code>\n\n🔤 <b>Доступные переменные:</b>\n"
                              f"{lines}{hint}\n\nОтправьте новый текст одним сообщением (или <code>-</code> чтобы "
                              "вернуть стандартный).", "texts")


def act_texts_reset_all(call, *_):
    S["texts"] = {}
    _save("settings")
    scr_texts(call)


# ---------------------------------------------------------------- Telegram: автовыставление

def scr_ac(call, *_):
    _wait(call, "⏳ Загружаю каталог…")
    api = _api()
    prods = _products() if api else None
    warn = ("🔑 Сначала задайте API-ключ.\n\n" if not api else
            f"⛔️ MUVSell не отвечает или ключ неверный: {esc(api.error or 'нет ответа')}\n\n" if prods is None else "")
    matched = len(_sellable()) if prods is not None else 0
    missing = len(_plan()) if prods is not None else 0
    own = S.get("ap_own")
    mk = f"своя ({_num(own)}%)" if own is not None else f"глобальная ({_num(S['markup'])}%)"
    auto = sum(1 for m in MAPS if m.get("auto"))
    text = (f"🤖 <b>Автовыставление лотов</b>\n\n{warn}"
            f"🗺 Игр в карте: <b>{len(_fp_map().get('games', []))}</b>\n"
            f"🎯 Сопоставлено с каталогом MUVSell: <b>{matched}</b>\n"
            f"🆕 Недостающих лотов: <b>{missing}</b>\n♻️ Лотов без привязки (привязку удаляли): <b>{len(_orphans())}</b>\n"
            f"🔁 Пересоздать (лот удалён с FunPay или стоит в чужом разделе): "
            f"<b>{sum(1 for m in MAPS if _stale(m) and not m.get('manual'))}</b>\n\n"
            f"⏱ Длительности: <code>{_durs(S['ap_durations'])}</code>\n"
            f"🔢 Лимит на раздел: <b>{S['lot_cap']}</b>\n➗ Наценка новых лотов: <b>{mk}</b>\n"
            f"👁 Создавать активными: {_onoff(S['ap_active'])}\n\n"
            + ("✏️ Новые лоты получают <b>свою</b> наценку и дальше не реагируют на смену глобальной. Вернуть их на "
               "глобальную можно кнопкой «Применить глобальную наценку ко ВСЕМ» в настройках.\n\n" if own is not None else
               "✏️ Новые лоты следуют за глобальной наценкой (и наценкой категории) — меняете её, меняются цены.\n\n")
            + "ℹ️ Создаются только НЕДОСТАЮЩИЕ лоты: по одному на каждую игру и срок, каждый со своей привязкой.\n"
              "♻️ Если привязку удаляли, а лот на FunPay остался — привязка восстановится к тому же лоту (дубль не "
              "создаётся). Если лот на FunPay тоже удалён — он будет создан заново.")
    _edit(call, text, _kb(
        [_btn(f"⏳ {_state['job']} — обновить", "ac")] if _state["job"] else None,
        [_btn(f"📋 Показать план ({missing})", "acp:0")],
        [_btn("🚀 Создать недостающие", "acgo")],
        [_btn("🎮 В Steam «Аккаунты с играми»", "gx:steam:0"), _btn("🧩 В «Прочие игры»", "gx:other:0")],
        [_btn("📝 Тексты лотов (название/описание)", "apt")],
        [_btn("✏️ Переписать тексты у существующих лотов", "aprw")],
        [_btn("⏱ Длительности", "apd"), _btn(f"🔢 Лимит ({S['lot_cap']})", "p:lot_cap")],
        [_btn(f"➗ Наценка новых лотов: {mk}"[:60], "apm")],
        [_btn(f"✏️ Своя наценка ({_num(own if own is not None else S['markup'])}%)", "apmo")],
        [_btn(f"👁 Создавать активными: {_onoff(S['ap_active'])}", "t:ap_active")],
        [_btn("📦 Наценка уже созданных лотов (по категориям)", "mkc")],
        [_btn("🔄 Обновить каталог", "acf")],
        [_btn(f"🗑 Удалить созданные плагином ({auto})", "acd")] if auto else None,
        _back(),
    ))


def act_ac_refresh(call, *_):
    _fp_map(force=True)
    _products(force=True)
    _costs.clear()
    _market.clear()
    scr_ac(call)


def act_ap_markup_mode(call, *_):
    S["ap_own"] = None if S.get("ap_own") is not None else float(S.get("markup") or 0)
    _save("settings")
    scr_ac(call)


def scr_preview(call, page="0"):
    api = _api()
    if not api:
        return scr_ac(call)
    _wait(call, "⏳ Считаю цены…")
    plan = _plan()
    if not plan:
        return _edit(call, "✅ <b>Всё уже создано</b> — недостающих лотов нет.", _kb(_back("ac")))
    games = list(dict.fromkeys(g["game_id"] for g, _, _ in plan))
    page, chunk = _page(games, page, 4)
    lines = [f"📋 <b>План</b> · лотов: <b>{len(plan)}</b>\n<i>Срок: база MUVSell → ваша цена · мин. у конкурентов</i>"]
    for gid in chunk:
        items = [(g, p, h) for g, p, h in plan if g["game_id"] == gid]
        lines.append(f"\n🎮 <b>{esc(items[0][0]['name'])}</b>")
        for g, prod, h in items:
            sub = int(g["funpay"]["subcategory_id"])
            low = _market_prices(sub, h)
            price = _price(api, prod, h, {"subcat": sub, "markup": S.get("ap_own")})
            lines.append(f"  {_dur(h)}: {_rub(_cost(api, prod, h))} → <b>{price}₽</b>"
                         f" · FP: {' / '.join(_num(x) for x in low) + '₽' if low else '—'}")
    _edit(call, "\n".join(lines), _kb(_nav("acp", page, len(games), 4), [_btn(f"🚀 Создать {len(plan)} лотов", "acgo")],
                                      _back("ac")))


def act_create(call, *_):
    plan = _plan()
    if not plan:
        return _alert(call, "Нечего создавать")
    _start_job(call, "Создание лотов", _run_create, plan)


def act_retext(call, *_):
    n = sum(1 for m in MAPS if m.get("auto"))
    if not n:
        return _alert(call, "Нет лотов, созданных плагином")
    _edit(call, f"✏️ Переписать название и описание у <b>{n}</b> лотов автовыставления по текущим шаблонам?\n"
                "Ваши ручные лоты не тронутся.", _kb([_btn("✅ Переписать", "aprwy"), _btn("❌ Нет", "ac")]))


def act_retext_yes(call, *_):
    _start_job(call, "Перезапись текстов", _run_retext)


def act_delete_auto(call, *_):
    n = sum(1 for m in MAPS if m.get("auto"))
    _edit(call, f"🗑 Удалить с FunPay <b>{n}</b> лотов, созданных плагином, и их привязки?\nВаши ручные лоты не тронутся.",
          _kb([_btn("✅ Да, удалить", "acdy"), _btn("❌ Нет", "ac")]))


def act_delete_auto_yes(call, *_):
    _start_job(call, "Удаление лотов", _run_delete)


def act_ap_durations(call, *_):
    _ask(call, "apdur", f"⏱ <b>Длительности автовыставления</b>\n\nСейчас: <code>{_durs(S['ap_durations'])}</code>\n\n"
                        f"Введите сроки через запятую ({MIN_HOURS}–{MAX_HOURS} ч): часы — числом, дни — с «д».\n"
                        "Например: <code>1, 3, 12, 1д, 3д, 7д, 30д</code> (или то же в часах: "
                        "<code>1, 3, 12, 24, 72, 168, 720</code>)\n\n"
                        "ℹ️ Значение <b>1</b> создаёт почасовой лот: покупатель сам задаёт число часов количеством при "
                        "покупке.", "ac")


def _ap_preview(field: str) -> str:
    ru, en, desc_ru, desc_en = _lot_texts(*AP_SAMPLE)
    return {"title_ru": ru, "title_en": en, "desc_ru": desc_ru, "desc_en": desc_en}[field]


def scr_ap_texts(call, *_):
    _edit(call, "📝 <b>Тексты создаваемых лотов</b>\n\nЗдесь задаются шаблоны названия и описания, по которым "
                "автовыставление создаёт лоты — обычное, в Steam и в «Прочие игры».\n\n🔤 <b>Переменные</b> "
                "(подставляются автоматически):\n"
                "• <code>{game}</code> — название игры\n• <code>{time}</code> — срок аренды (напр. «1 день», «3 часа»)\n\n"
                "⚠️ <b>Лимиты FunPay:</b>\n• Название (краткое описание) — не длиннее 100 символов: это предел FunPay "
                "(EN плагин обрежет сам).\n• Английское описание не должно быть коротким — минимум "
                f"~{EN_MIN} символов, иначе FunPay отклонит лот. Если ваше EN-описание короче — плагин сам дополнит его "
                f"стандартным текстом.\n\nНажмите на поле, чтобы изменить. В скобках — длина превью для примера "
                f"«{AP_SAMPLE[0]}», {_dur(AP_SAMPLE[1])}.",
          _kb(*[[_btn(f"{label} ({len(_ap_preview(f))})", f"apf:{f}")] for f, label in AP_LABELS.items()],
              [_btn("♻️ Сбросить все тексты", "aptr")], _back("ac")))


def act_ap_field(call, field):
    hint = (f"⚠️ Для EN-описания минимум ~{EN_MIN} символов (иначе FunPay отклонит; короткое плагин дополнит сам)."
            if field == "desc_en" else "⚠️ Лимит названия: ≤ 100 символов — это предел FunPay."
            if field.startswith("title") else "ℹ️ Описание может быть любой разумной длины.")
    preview = _ap_preview(field)
    _ask(call, f"aptext:{field}", f"✏️ <b>{AP_LABELS[field]}</b>\n\nТекущий шаблон:\n<code>{esc(_ap_text(field))}</code>\n\n"
                                  f"Превью ({len(preview)}):\n<code>{esc(preview)}</code>\n\n"
                                  f"🔤 Переменные: <code>{{game}}</code> — игра, <code>{{time}}</code> — срок"
                                  + (", <code>{commands}</code> — команды покупателя (список собирается из ваших "
                                     "настроек: выключите !кик — он пропадёт и из описания)" if field == "desc_ru" else "")
                                  + f".\n{hint}\n\n"
                                  "Отправьте новый текст одним сообщением (или <code>-</code> чтобы сбросить это поле "
                                  "к стандартному).", "apt")


def act_ap_texts_reset(call, *_):
    S["ap_texts"] = {}
    _save("settings")
    scr_ap_texts(call)


TOGGLE_SCREENS = {"hide_no_stock": scr_main, "review_bonus": scr_bonus, "q_replace": scr_problems,
                  "q_unbind": scr_problems, "notify_end": scr_params, "en_msgs": scr_params, "ap_active": scr_ac}


def act_toggle(call, key):
    S[key] = not S.get(key)
    _save("settings")
    TOGGLE_SCREENS.get(key, scr_settings)(call)


ACTIONS = {
    "main": scr_main, "close": act_close, "t": act_toggle, "bal": act_balance, "pay": act_pay, "rpa": act_reprice_all,
    "rt": act_titles, "dg": scr_diag, "restart": act_restart, "help": act_help,
    "maps": scr_maps, "mq": lambda call, *_: _ask(call, "mapsearch", "🔍 Введите часть названия игры:", "maps:0"),
    "mqx": act_maps_search_clear, "map": scr_map, "mh": act_map_hours, "mm": act_map_markup,
    "mrp": act_map_reprice_mode, "mnow": act_map_reprice_now, "mah": lambda call, lid: _map_cycle(call, lid, "autohide"),
    "mbn": lambda call, lid: _map_cycle(call, lid, "bonus"), "moff": act_map_off,
    "md": act_map_delete, "mdy": act_map_delete_yes, "mdel": scr_multi_delete, "mdt": act_multi_toggle,
    "mdclr": act_multi_clear, "mdall": act_multi_all, "mdgo": act_multi_go, "mdgoy": act_multi_go_yes,
    "alm": act_bind_lot, "pl": scr_products, "pp": act_pick_product,
    "ps": lambda call, *_: _ask(call, "search", "Введите часть названия игры:", "pl:0"),
    "cg": scr_games, "cgs": lambda call, *_: _ask(call, "gamesearch", "🔍 Введите часть названия игры:", "cg:0"),
    "cgx": act_games_search_clear, "gm": scr_game, "gc": act_game_create,
    "gca": lambda call, gid: act_game_create(call, f"{gid}:all"), "gb": act_game_bind,
    "gx": scr_manual, "gxc": act_game_manual_create,
    "gsr": lambda call, *_: _ask(call, "stregion", "🌍 <b>Регион лотов в Steam «Аккаунты с играми»</b>\n\n"
                                                  "Напишите регион точно как в списке FunPay "
                                                  "(напр. <code>Россия</code>):", "gx:steam:0"),
    "rl": scr_rentals, "rn": scr_rental, "rc": act_rental_code, "rk": act_rental_kick, "rp": act_rental_password,
    "rx": act_rental_extend, "rtm": act_rental_terminate, "rty": act_rental_terminate_yes,
    "st": scr_stats, "sx": scr_stats_detail, "pr": scr_profit,
    "set": scr_settings, "key": act_key, "px": scr_proxy, "pxm": act_proxy_mode, "mka": act_markup_all,
    "mkay": act_markup_all_yes, "mkc": scr_cat_markup, "mkcs": act_cat_markup, "bn": scr_bonus, "stars": act_stars,
    "ntf": scr_notify, "nt": act_notify, "nta": act_notify_all, "q": scr_problems, "qclr": act_problems_clear,
    "qn": act_problems_notify, "params": scr_params, "p": act_param,
    "extw": lambda call, *_: _ask(call, "extword", "✏️ Команда, по которой покупатель получает ссылки на продление "
                                                   "(напр. <code>!продление</code>):", "params"),
    "codew": lambda call, *_: _ask(call, "codeword", "🔐 Команда, по которой покупатель получает код Steam Guard — "
                                                     "любое слово, можно без «!» (напр. <code>!гуард</code> или "
                                                     "<code>код</code>). Пригодится, если на <code>!код</code> отвечает "
                                                     "ещё и другой плагин. Вернуть как было — <code>!код</code>:",
                                   "params"),
    "texts": scr_texts, "tx": act_text, "txra": act_texts_reset_all,
    "ac": scr_ac, "acf": act_ac_refresh, "acp": scr_preview, "acgo": act_create, "acd": act_delete_auto,
    "acdy": act_delete_auto_yes, "apt": scr_ap_texts, "apf": act_ap_field, "aptr": act_ap_texts_reset,
    "aprw": act_retext, "aprwy": act_retext_yes, "apd": act_ap_durations, "apm": act_ap_markup_mode,
    "apmo": lambda call, *_: _ask(call, "apown", "✏️ <b>Своя наценка новых лотов</b>, %:", "ac"),
    "noop": lambda call, *_: bot.answer_callback_query(call.id),
}


# ---------------------------------------------------------------- Telegram: ввод текста

def _one_hours(text: str):
    hours = _parse_hours(text)
    return hours[0] if len(hours) == 1 else None


def _float(text: str):
    try:
        return round(float(text.replace(",", ".").rstrip("%").strip()), 2)
    except ValueError:
        return None


BAD_HOURS = f"❌ Нужен срок от {MIN_HOURS} до {MAX_HOURS} ч: число часов или дни с «д» (напр. <code>3</code>, <code>7д</code>)."


def in_key(uid, text, _):
    key = "".join(ch for ch in text.strip().strip("\"'`") if ch.isprintable() and not ch.isspace())
    if not key:
        return "❌ Пустой ключ.", [_back("set")], None
    S["api_key"] = key
    _save("settings")
    _cache["products"] = (0.0, None)
    _cache["bal"] = (0.0, None)
    api = _api()
    data, err = api.balance()
    if not data:
        return f"⚠️ Ключ сохранён, но проверить не вышло: {esc(_human(err, api))}", [_back("set")], None
    return (f"✅ Ключ работает. Аккаунт <b>{esc(str(data.get('username')))}</b>, баланс "
            f"{_num(data.get('balanceRub') or 0)} ₽ / {_num(data.get('balanceUsd') or 0)} $", [_back("set")], None)


def in_hours(uid, text, lot_id):
    m, hours = _map_by_lot(lot_id), _one_hours(text)
    if not m or hours is None:
        return BAD_HOURS, [_back(f"map:{lot_id}")], None
    m["hours"] = hours
    _save("mappings")
    return f"✅ За 1 шт: {_dur(hours)}", [_back(f"map:{lot_id}")], None


def in_map_markup(uid, text, lot_id):
    m = _map_by_lot(lot_id)
    value = None if text.strip() == "-" else _float(text)
    if not m or (value is None and text.strip() != "-"):
        return "❌ Нужно число или <code>-</code>.", [_back(f"map:{lot_id}")], None
    m["markup"] = value
    if value is not None:
        m["reprice"] = True  # своя наценка без автоцены смысла не имеет
    _save("mappings")
    return (f"✅ Наценка привязки: {_num(_markup(m))}% ({_markup_src(m)}).",
            [[_btn("🔁 Выставить цену сейчас", f"mnow:{lot_id}")], _back(f"map:{lot_id}")], None)


def in_lot(uid, text, _):
    found = re.search(r"id=(\d+)", text) or re.search(r"(\d{4,})", text)
    info = _tmp.setdefault(uid, {})
    if not found:
        return "❌ Не вижу ID лота.", [_back("maps:0")], None
    if _map_by_lot(found.group(1)):
        return f"ℹ️ Лот {found.group(1)} уже привязан.", [[_btn("🔗 Открыть привязку", f"map:{found.group(1)}")]], None
    try:
        sub, titles = _lot_info(found.group(1))
    except Exception as e:
        return f"❌ Лот {found.group(1)} не открывается: {esc(str(e)[:150])}", [_back("maps:0")], None
    info.update(lot_id=found.group(1), subcat=sub, titles=titles)
    name = f"<code>{esc(titles[0] if titles else found.group(1))}</code>"
    if "game_id" in info:  # игру уже выбрали на экране игры
        return (f"✅ Лот {name} → <b>{esc(info['game'])}</b>\n\nСколько аренды выдавать за 1 шт лота? Часы числом или "
                f"дни с «д» (напр. <code>3</code>, <code>7д</code>):", [_back("maps:0")], "newmap")
    return f"✅ Лот {name}", [[_btn("➡️ Выбрать игру", "pl:0")]], None


def in_search(uid, text, _):
    _tmp.setdefault(uid, {})["q"] = text.lower()
    return f"🔍 Поиск: <b>{esc(text)}</b>", [[_btn("➡️ Показать", "pl:0")]], None


def in_map_search(uid, text, _):
    _tmp.setdefault(uid, {})["mq"] = text.lower()
    return f"🔍 Поиск: <b>{esc(text)}</b>", [[_btn("➡️ Показать", "maps:0")]], None


def in_game_search(uid, text, _):
    _tmp.setdefault(uid, {})["gq"] = text.lower()
    return f"🔍 Поиск: <b>{esc(text)}</b>", [[_btn("➡️ Показать", "cg:0")]], None


def in_newmap(uid, text, _):
    info, hours = _tmp.get(uid) or {}, _one_hours(text)
    if "game_id" not in info or "lot_id" not in info or hours is None:
        return BAD_HOURS, [_back("maps:0")], None
    with _lock:
        MAPS[:] = [m for m in MAPS if str(m.get("lot_id")) != info["lot_id"]]
        MAPS.append({"lot_id": info["lot_id"], "subcat": info.get("subcat"), "titles": info.get("titles") or [],
                     "game_id": info["game_id"], "game": info["game"], "hours": hours, "auto": False, "reprice": False})
    _save("mappings")
    _tmp.pop(uid, None)
    return (f"✅ Привязано: лот {info['lot_id']} → {esc(info['game'])}, {hours} ч за шт ({_dur(hours)}).\n\n"
            "💲 Цену лота плагин не меняет. Чтобы она следовала за наценкой — откройте привязку и включите «💲 Цена: авто».",
            [[_btn("🔗 Открыть привязку", f"map:{info['lot_id']}")], _back("maps:0")], None)


def in_param(uid, text, key):
    label, _, is_float, back = PARAMS[key]
    value = _float(text)
    if value is None:
        return "❌ Нужно число.", [_back(back)], None
    if not is_float:
        value = int(value)
    lo = {"poll_sec": 15, "tz": -12, "price_min": 1, "q_pause": 1, "q_unbind_after": 1, "bonus_hours": 1, "lot_cap": 1}.get(key, 0)
    S[key] = min(max(value, lo), 14) if key == "tz" else max(value, lo)
    _save("settings")
    _costs.clear()
    rows = [[_btn("🔁 Пересчитать все лоты", "rpa")]] if key == "markup" else []
    return f"✅ {label}: {_num(S[key])}", rows + [_back(back)], None


def in_cat_markup(uid, text, sub):
    value = None if text.strip() == "-" else _float(text)
    if value is None and text.strip() != "-":
        return "❌ Нужно число или <code>-</code>.", [_back("mkc")], None
    if value is None:
        S["cat_markup"].pop(sub, None)
    else:
        S["cat_markup"][sub] = value
    _save("settings")
    return (f"✅ {esc(_sub_label(sub))}: {_num(value) + '%' if value is not None else 'глобальная наценка'}",
            [[_btn("🔁 Пересчитать все лоты", "rpa")], _back("mkc")], None)


def in_proxy(uid, text, _):
    S["proxy"], S["proxy_mode"] = text.strip(), "custom"
    _save("settings")
    api = _api()
    data, err = api.balance() if api else (None, "no_key")
    return ("✅ Прокси сохранён, MUVSell отвечает." if data else
            f"⚠️ Прокси сохранён, но проверка не прошла: {esc(_human(err, api))}"), [_back("px")], None


def in_rental_extend(uid, text, rid):
    r, api, hours = _rec(rid), _api(), _one_hours(text)
    if not r or not api or hours is None:
        return BAD_HOURS, [_back(f"rn:{rid}")], None
    err = _extend(api, r, hours, r.get("chat"), r.get("order"), kind="admin")
    return (f"❌ Не продлено: {esc(_human(err, api))}" if err else f"✅ Продлено на {_dur(hours)}, до {_when(r['exp'])}."), \
        [_back(f"rn:{rid}")], None


def in_ext_word(uid, text, _):
    word = text.strip().split()[0] if text.strip() else ""
    if not word.startswith("!"):
        return "❌ Команда должна начинаться с «!».", [_back("params")], None
    S["ext_word"] = word
    _save("settings")
    return f"✅ Команда продления: {esc(word)}", [_back("params")], None


def in_code_word(uid, text, _):
    word = text.strip().split()[0].lower() if text.strip() else ""
    taken = {n for names, _, _ in COMMANDS[1:] for n in names} | {str(S.get("ext_word") or "").lower()}
    if not word or word in taken:
        return "❌ Нужно одно слово, не занятое другой командой (!время, !продление…).", [_back("params")], None
    S["code_word"] = word
    _save("settings")
    return f"✅ Команда кода Steam Guard: {esc(word)}", [_back("params")], None


def in_text(uid, text, key):
    if text.strip() == "-":
        S.setdefault("texts", {}).pop(key, None)
    else:
        S.setdefault("texts", {})[key] = text
    _save("settings")
    return (f"✅ {TEXT_LABELS[key]}: {'вернул стандартный' if text.strip() == '-' else 'сохранено'}.\n\n"
            f"Превью:\n<code>{esc(_text_preview(key))}</code>", [[_btn("✏️ Изменить ещё раз", f"tx:{key}")], _back("texts")], None)


def in_ap_text(uid, text, field):
    if text.strip() == "-":
        S["ap_texts"].pop(field, None)
    else:
        S["ap_texts"][field] = text
    _save("settings")
    preview = _ap_preview(field)
    return (f"✅ {AP_LABELS[field]} сохранено.\n\nПревью ({len(preview)}):\n<code>{esc(preview)}</code>",
            [_back("apt")], None)


def in_ap_durations(uid, text, _):
    hours = _parse_hours(text)
    if not hours:
        return ("❌ Пример: <code>1, 3, 24, 7д, 30д</code>. Отправьте ещё раз:", [_back("ac")], "apdur")
    S["ap_durations"] = hours
    _save("settings")
    return f"✅ Длительности: <code>{_durs(hours)}</code>", [_back("ac")], None


def in_ap_own(uid, text, _):
    value = _float(text)
    if value is None:
        return "❌ Нужно число, напр. <code>100</code>:", [_back("ac")], "apown"
    S["ap_own"] = value
    _save("settings")
    return f"✅ Своя наценка новых лотов: {_num(value)}%.", [_back("ac")], None


def in_steam_region(uid, text, _):
    if not text.strip():
        return "❌ Пустой регион.", [_back("gx:steam:0")], None
    S["steam_region"] = text.strip()
    _save("settings")
    return (f"✅ Регион лотов в Steam: <b>{esc(S['steam_region'])}</b>. Если на FunPay такого нет — при выставлении "
            "плагин покажет список доступных.", [_back("gx:steam:0")], None)


INPUTS = {
    "key": in_key, "hours": in_hours, "mapmk": in_map_markup, "lot": in_lot, "search": in_search,
    "mapsearch": in_map_search, "gamesearch": in_game_search, "newmap": in_newmap, "param": in_param,
    "catmk": in_cat_markup, "proxy": in_proxy, "rext": in_rental_extend, "extword": in_ext_word, "text": in_text,
    "codeword": in_code_word,
    "aptext": in_ap_text, "apdur": in_ap_durations, "apown": in_ap_own, "stregion": in_steam_region,
}


def _on_input(message):
    chat_id, uid = message.chat.id, message.from_user.id
    state = str((tg.get_state(chat_id, uid) or {}).get("state", ""))
    tg.clear_state(chat_id, uid, True)
    _, name, *rest = state.split(":", 2)
    text, rows, next_state = INPUTS[name](uid, (message.text or "").strip(), rest[0] if rest else "")
    sent = bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=_kb(*rows), disable_web_page_preview=True)
    if next_state:
        tg.set_state(chat_id, sent.message_id, uid, f"{P}:{next_state}")


def _on_callback(call):
    _, action, *args = call.data.split(":", 2)
    ACTIONS[action](call, *args)


def _safe(handler):
    def wrapper(obj):
        try:
            handler(obj)
        except Exception as e:
            log.exception(f"{LP} Telegram: {handler.__name__}")
            if getattr(obj, "data", None):
                _alert(obj, f"Ошибка: {str(e)[:150]}")
    return wrapper


# ---------------------------------------------------------------- запуск

def init(c: "Cardinal"):
    global cardinal, tg, bot
    cardinal, tg = c, c.telegram
    bot = tg.bot if tg else None
    _load_all()
    if tg:
        tg.cbq_handler(_safe(scr_main), lambda q: q.data.startswith(f"{CBT.PLUGIN_SETTINGS}:{UUID}"))
        tg.cbq_handler(_safe(_on_callback), lambda q: q.data.startswith(f"{P}:"))
        tg.msg_handler(_safe(_on_input), func=lambda m: str((tg.get_state(m.chat.id, m.from_user.id) or {})
                                                            .get("state", "")).startswith(f"{P}:"))
    _stop.clear()
    threading.Thread(target=_poll_loop, daemon=True, name="muvsell-rent").start()
    log.info(f"{LP} v{VERSION} запущен: привязок {len(MAPS)}, ключ {'задан' if S['api_key'] else 'не задан'}")


def _shutdown(*_):
    _stop.set()


BIND_TO_PRE_INIT = [init]
BIND_TO_NEW_ORDER = [on_new_order]
BIND_TO_NEW_MESSAGE = [on_new_message]
BIND_TO_LAST_CHAT_MESSAGE_CHANGED = [on_last_chat_message_changed]
BIND_TO_ORDER_STATUS_CHANGED = [on_order_status_changed]
BIND_TO_DELETE = _shutdown
