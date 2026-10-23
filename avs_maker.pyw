# -*- coding: utf-8 -*-
"""
AVS かんたん作成ツール
  ・動画をドラッグ＆ドロップ → 設定 → avsを一括作成
  ・右側のプレビューで、補正のかかり具合を見ながら調整
  ・カット編集（残す区間を複数登録）
  ・色ノイズ除去 CCD（VirtualDubのCCDフィルタを内蔵）
  ・そのまま ffmpeg(HEVC/NVENC) で mp4 にエンコード

必要なもの:
  pip install tkinterdnd2          （ドラッグ＆ドロップ用）
  pip install pillow numpy         （プレビュー・カット編集用）
  ffmpeg / ffprobe                  （PATHに通っていればOK。avs読み込み対応のもの）
どれも入っていなくても動きますが、その機能だけ使えなくなります。
"""
import base64
import hashlib
import io
import json
import math
import os
import queue
import re
import shutil
import subprocess
import threading
import time
import zlib
from fractions import Fraction
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter import font as tkfont

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    HAS_DND = True
except ImportError:
    HAS_DND = False

try:
    import numpy as np
    from PIL import Image
    HAS_IMG = True
except Exception:
    HAS_IMG = False
try:
    from PIL import ImageTk
    HAS_TKIMG = True
except Exception:
    HAS_TKIMG = False
HAS_PREVIEW = HAS_IMG and HAS_TKIMG

APP_TITLE = "AVS かんたん作成ツール"
APP_VERSION = "1.2.1"

# 更新の確認先（GitHub）。version.json に最新の版番号と変更内容、avs_maker.pyw に本体を置く
UPDATE_REPO = "tatata17/avs-maker"
UPDATE_BRANCH = "main"
UPDATE_RAW = f"https://raw.githubusercontent.com/{UPDATE_REPO}/{UPDATE_BRANCH}/"
UPDATE_PAGE = f"https://github.com/{UPDATE_REPO}"
HELP_PAGE = "https://tatata17.github.io/avs-maker/"     # 使い方のページ（GitHub Pages）
SETTINGS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "avs_maker_settings.json")
VIDEO_EXTS = {".avi", ".mp4", ".mkv", ".m2ts", ".ts", ".mts", ".mov",
              ".wmv", ".mpg", ".mpeg", ".flv", ".webm", ".m2v", ".vob"}
NOCONSOLE = 0x08000000 if os.name == "nt" else 0   # ffmpeg実行時に黒い窓を出さない
PREVIEW_MAX_W, PREVIEW_MAX_H = 480, 360

# ---------------------------------------------------------------- 設定の初期値
DEFAULTS = {
    "source": "自動（拡張子で判断）",
    "deint": True,
    "field": "TFF",
    "levels": False,      # 明るさ補正は初期はオフ
    "in_low": "16",
    "gamma": "1.0",
    "in_high": "220",
    "out_low": "16",
    "out_high": "235",
    "tweak": False,       # 色相・彩度も初期はオフ
    "hue": "-16",         # ＋で赤寄り、－で緑寄り
    "sat": "1.0",         # 1.0 = そのまま
    "anime24": False,     # アニメを24pにする（QTGMC+SRestore）。区間なし＝全体／区間あり＝新しい区間の初期値
    "plug24": r"C:\avs_srestore",   # 24p化に使うプラグインのフォルダ（空ならなし）
    "ccd": False,         # 色ノイズ除去（CCD）も初期はオフ
    "ccd_th": "30",       # VirtualDubのCCDの初期値と同じ
    "resize": True,
    "width": "1440",
    "height": "1056",
    "color": True,
    "out_mode": "same",   # same = 動画と同じ場所 / folder = 指定フォルダ
    "out_dir": "",
    "cq": "20",           # エンコードの画質（小さいほど高画質）
    # ffmpegの場所の初期値（初回起動時だけ使う。変えると、次からは変えた場所が使われる）
    "ffmpeg": r"C:\ffmpeg\ffmpegNEW.exe",     # 通常用（AviSynth Neo を読む側）
    "ffmpeg24": r"C:\ffmpeg\NEW\ffmpeg.exe",  # 24p用（AviSynth+ 3.7.5 の avisynth.dll と同じフォルダ）
}

# 動画ごとに別々に持つ設定（それ以外の ffmpeg の場所・保存先・画質などは全部の動画で共通）
FILE_KEYS = ["source", "deint", "field", "anime24", "levels", "in_low", "gamma", "in_high",
             "out_low", "out_high", "tweak", "hue", "sat", "ccd", "ccd_th",
             "resize", "width", "height", "color"]

# 動画ごとの設定とプリセットをまとめて保存するファイル（ツールと同じフォルダに1つだけ）
RECORD_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "avs_maker_動画ごとの設定とプリセット.json")
RECORD_MAX_FILES = 2000          # 覚えておく動画の数の上限（古いものから忘れる）

# 「値が違う項目」の表示用に、設定をまとまりごとに名前を付ける
KEY_GROUPS = [
    ("読み込み方法", ["source"]),
    ("インターレース解除", ["deint", "field"]),
    ("24p化", ["anime24"]),
    ("明るさ補正", ["levels", "in_low", "gamma", "in_high", "out_low", "out_high"]),
    ("色相・彩度", ["tweak", "hue", "sat"]),
    ("CCD", ["ccd", "ccd_th"]),
    ("リサイズ", ["resize", "width", "height"]),
    ("色空間変換", ["color"]),
]


def settings_row(s, cuts):
    """一覧に出す、動画1本ぶんの設定の要約（処理 / 明るさ / 色 / CCD）"""
    n24 = sum(1 for c in (cuts or []) if len(c) > 2 and c[2])
    if cuts:
        mode = f"区間{len(cuts)}" + (f"（24p {n24}）" if n24 else "")
        if not n24:
            mode += "・KFM" if s.get("deint") else ""
    elif s.get("anime24"):
        mode = "24p化"
    else:
        mode = "KFM" if s.get("deint") else "解除なし"
    if s.get("levels"):
        lv = f"{s.get('in_low')}〜{s.get('in_high')}"
        if str(s.get("gamma")) not in ("1", "1.0"):
            lv += f" γ{s.get('gamma')}"
    else:
        lv = "なし"
    if s.get("tweak"):
        parts = []
        if str(s.get("hue")) not in ("0", "0.0"):
            parts.append(f"色相{s.get('hue')}")
        if str(s.get("sat")) not in ("1", "1.0"):
            parts.append(f"彩度{s.get('sat')}")
        tw = " ".join(parts) or "なし"
    else:
        tw = "なし"
    ccd = str(s.get("ccd_th")) if s.get("ccd") else "なし"
    return mode, lv, tw, ccd


SOURCE_CHOICES = [
    "自動（拡張子で判断）",
    "AviSource",
    "LWLibavVideoSource",
    "FFVideoSource",
]

# ---------------------------------------------------------------- 内蔵CCDフィルタ（VirtualDub用 .vdf, 64bit）
# Camcorder Color Denoise 1.9 (Stolyarevskiy Sergey) をそのまま圧縮して埋め込んでいます。
CCD_VDF_ZB64 = (
    "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"
    "WC1l6dudF1kZyhY+lRmmyQnnKSGbtp7ismLJ3xugbYyl251X9Y/RrLf4GixL5vEgliVnmZao2NMKHoOyZCMvy5JNHIslm03Vsacw"
    "R2TJG3l1LPlxjsWSj3IslvwPjsWSfuepy59oy3P5hDFGkx/koCM0+QAHsSg8lc/L2GJXKQctoMn1HFRPkx3OE7q7LeoAu2LpYmPy"
    "4X3bUMcJAfGERTQYkT3obo7I0oxtjMgeNgiILF0vIrKHTgGRpf0i4mQaZzUrgDHbGBJgQxbjgM7L0ncJeI9aFG/XodlfGQ+aWHKZ"
    "MpkQhxdstyvYPomCfruC8tBcQX87OKssebGJVfYU44gseaMJ8Ubn0PLjCRsvs9Jux0q7DSvtdqy027DSbsdK+yRY8dux4rdhxW/H"
    "it+GFb8dK7KCJi13p4I3Ks4rJ5Nm31qQYX2AzzVZ8rAiLGE4ERyiv2mK1nSa7vQaslRg41LZXzYXRrbz7PgWk3zY02c4Ikt+NqEg"
    "WXUhHqiELO/MUV03SxN5yfeeoL+PcO4fsbx0T+wWUnlBlpydsGAp/V3OC7Lkir9NwWpLWAizO5q8OmFBhtXFC3ZZCuZCwXlrb3br"
    "pWV66QL0MNdxU8dBZzUwSgNKghfR9PcI54Yln+DLBSx50tSyk9LSfRdLfseEyJ6W8MUClixPOBP+Of09y/2aFYXtHz+Xv+U411K3"
    "jWh+bnnxYSeaCraDlM/fWXKLiWv2tI0jsuQu3mKWjCVsMVsOeZnX9bJluwhqIUu+aqqLPb3Oy7Lkar6szbYlbHY5ep+3aKkqHn+z"
    "Ui3OITkrVTCJfQ+f4XEzS95n2uTAnr7EEVny65wFlnzVlUim7IX8D/nE4GfSpgbJRM5aXtAjDliSh/hdLFloisnZ0zxeliUP8bIf"
    "oclPao4y3UKz2uhvijKOhqS5R9nzdh67s+QRzbGvNEmlpFavpll1vBaW3MjiX8RDRJk777C60cKdjSnNsIyDNiir6W8V92RVko90"
    "fGPLB+YOlvyQyfmwp6MckSV/YYC6WfJ1U1n29BvF8Y2CzEe7HR/tBh98yaedJV/jzXzNho92Gz4kedwjee02lnyVy55V9B8c6z+k"
    "uiUNMfc7jTsWlryQOyWW3GFySuzpo85voWfTrJWCM14pLZ62s5p2c9B+S+V2LmeBpXZUjCXX8wFivfN6JmehbYe8SDMkrUR17Jea"
    "LPVEtmhzDy/Fkg+ZxMeenuCIT1jGA4L4b5a1FYTIkorZO9KnVO5ZWTLbhMie8jkiSxaZENlTGUdkyYUJHbMshXY7KbTbSKHdTgrt"
    "NlJot5NCuyGFDL5ZLcNGCu02Umi3k0K7jRTa7aTQPgkp+O2k4LeRgt9OCn4bKfjtpOC3kYLfTgp+Gyn47aTgt5GC304Kzkvn//z7"
    "3/F3Bf09QH/Z3p4n2QopNbg01zsr/xH6+0n6e6cDfWOftMWdOdFjG4w/QMuVWvb/Wv/YdmeF4dPfRQ4HEVxumY9dy+IDy3at5x3K"
    "r6J81NPfi9guYsuuSus7erYRxfr3LC1/mv6eT/HW0t8u+nuRZR/Sbof6fJZAdwb9nWvZK8V2jFj/2Baif7PsCfmtA/5LFvz/TILv"
    "cZtXZ2fT30WWnVmrHNr3AQq/iv5+jP4es2yxut+hfDI9SUu4lndH91vemrH3sy862P8qy+y00xKQWf+utmzVv57+3qKa++txh/Ls"
    "U4fn6O/3LRNVNvn8D4fy2yx2HaC/g/Q3Ynl7Y/27lcLvoL9HLTPJB+nvYw7l2euZt9luLs08vSulv4sc7OuYZZT2ucx+xPpnHaxL"
    "LaPg//a/8sHQCCwYwvfJf34bQmLj2GPT3yWGGy1VNAfbGFfwDSL4W15N1bnT5fEKXqYtTYJzH10XA1oExnbFpCjsS+FvwnzGnbge"
    "vKaUhFYuAp1IUs/5KvnmPhFOKwK1JcEJIlB1EpzLEKgiCQ5sqIUVGKwL4oUQ5EySVjyrkv3rXKo/gfM6EtAqh081heFTU2Hv+mKz"
    "/Qz0xfuEMna2Ub4rxtbfiQZV2ZmWT/CKPBinUsaJcBw3xoH3HhkSHrz4hWPrvTbtMvigYsnCOG0IXdqQh29FZqv3mvqCrUdh/iAP"
    "41zvtcM5l+JkGjzLzoMtzOVjHJ9tD2ti254xzr+67NrVxV7iYpwttv0UfPYBQ+85tjiX0HpyMA6cSKPb+o1G0W/gz4i552D2A3sn"
    "VSfbeAf24zPsR3Fs17EE7WI8+w2eO8bDbVE4qzoSEfD2uhjPpcbKsvXvATh7xp287/C2L0OcFf1N2s76TqXRd/Id+06F0XcyFH7q"
    "glmGJw0ZFjjK8BJDhji6kQz62wiy0+ssQyYfggO0skoUy47Xv7Z8mgz5VDvKZ20C+ZRHOUNEPscc7fDMJGR4uSFDuN8dPjA3G+Kv"
    "wcbmJZchwQFaN//NbezQJGTYNAkZHpuEDIGZZDK8zZAhOUzc1JGhV8IZR+ckjluq4fymc8SRcQJBSs8VIbcgSHW5CIGx9IAJMgvO"
    "ETIg9SMjWxBLyhkTDt6GsUyExN2CdnDqSgSpNuEcRZA2A8L0TtoF8mlN4VspnPQO78Eyk+jd56j3U4bemxz13mXoHTZAz7LVe7XK"
    "dAr8pNrqvXQSer/H0HtseGxvIDwWigVF7X8eMbJz2ST8zzImQz2Fn4JglmG1mrzvlE6i78ConqzvPDuJvgNzLCKfE459p3oSMnyK"
    "9x3LrRTk7yk4P+u8xOPgDxHOgfOslklKOYxEU5Kqc8TYZkhVd5Tqi4ZUixW7M24gGoQYkESDr7jtcCAahBiQRIMfVJwivYokkR5E"
    "cRC7kSjux7bRKWhwZ0ryCA3ishyjV7pttfyGoWXL9RzstRIqdvi8xB7yTah6lTjjSPOQeIPMyOLDwUAs2B+rMs3RCuEcrtWiH4OZ"
    "TYUJZwOCHE4yc4E5yrEkOHd4yPlryeKxw4ZlvuQ4l5mMZVYk8pm0n8JaBOFH7j3Mev2G9VY5Wu9Zw3rL6KxGtt7Kmcx6v5ajyJ9s"
    "YuuFNUJivXMd5zIwgyFzmZDuZOE7JzGXAV9H5jIVLqe5zCMa6wVLHecyW4y5jNd5LjOJnnLc6ClvSR6A9ZR8lfUUfjeJ+PcY2PMF"
    "zv4wUr565YqKKm4/GPodOFXuArEX/BTOcUtgq4EAEEeyWSOW+qOH7FYifcfwtBcwe4Yd3qlJ7FmeCzN7rp6Epz1s2Gqxo62CDJPZ"
    "6n+VM1s97rHGJMxW96cyW81XnWz1dznMVj/r6I0PT8Ibv+phdjhddfLGxyZhY7CbnNjYIUcbW8ttTLzkxfiDKKRiTeIxd3YKeR/h"
    "shn1WAtXp5BP3hPh9CIc31rRxkZTyJsc7p+vSCFrBRxyQwqZ1WomOyQ843UJVYr9qB22TcKvGtTV2zxOdnjcsMNSRzusUp1HfOaf"
    "jVZgH+6ytdU7Kpmt7kM/M21t9Sad2er3HG31SC6z1TO2Nga2enIStgpdnNhqperkM7cZPnOao888OQl7hjV0Ys+POEYXfaqw/iNc"
    "wMP+PgM2ti6xPQMvJ9eLdvgCgjSliFb3Kthhqgj5TQrx/Bzye5Q8sUGaJa1jlglzr5lTtsxqRks96XKcJU3CMtsSeEhjlmRYZqqt"
    "xMAyC+uYZW4t4PtYzZY5kMYsc8DlZJlX5DPL/KDj6uXZSVhmpc4s80+OljlmWGal88rJJCzzjGGZZxw97bhhmcJVPtaVk5rkK5Nt"
    "Dl7UtLLtTbwyCfoa8DN9wUqgbquvUxlMX1c6jmilKtNFqe3cAXSxPI3pwmPLEejiTkMXxc4rMKnJV1PvM+RsXEBkfuOcyuTsPL+Y"
    "jXCO1YgeoBxBdiaMkSYGAnStCa/zE8il5M2R1/AJDeAva6X5qaH3O+m6hqz3nZPwCVzvzisnr08iaoon8gl1HV1l/pb6qgRvNChO"
    "XUUiHOpb2hykyuup720z1aPY4dQ0JcJBpsDm72kYZ5E8ghCee6uT0mqpWZSEVllvb+9Og5YDTk0NPtHSCYf105suYv30X5Fqz7Ht"
    "p5syWT+92XHE98xifrVHcxrxq9XkfnVVOuvLmY5+9TGjL8927Mulqcn9Ksygc4xVWXu/+k0+4vObuix+tbQ2uV+dTP/yJfCrxDbq"
    "evWk9lNXoyTFae4tTY5T40uAw+wnPMDs54uq0zrST7KY/fQ4+vnIJPx8XQazjYudVwIn4cNfM3QqXFEm/LWnMp06R3EXI5zTCTx2"
    "XxzqRTiSN+bW8gx9I/s3sBb2ftnFvLHP0RvfpiZfLSwdZFp+MYWsdMhaXp3NtHyZo5e4eA7zEr9znsNOwkt8yrCEBsc57M5JeADY"
    "50A8QMQx5oddpHRFkV3hZvq7DNE5W5t4xL8FxuU6ccQ/jiAVJsiXEeSACfIs2GG9CPklRBcmCJjeCRMkH0GqG0RImQ43rIiQGgQ5"
    "02C1zLOGZcLnGN6/qWX6DMvc6WiZJ1TnNyzMMt8aYZYZRUPCLlvL/KKPWWaH47ygey6zzOc9TpZ5Uk2+Eghv18hK4AnHXQ2vZTLr"
    "fcNxjHvZGOO6nFcCJ2Hhpw0Lhz00+bYWPsclvt3u1+3eHB1u/GuPcS7HMeWS/UynmmrtlUyn7jym08WOnuTsJMaUF7OZLoacd1lM"
    "YkxZa8hQuNWP1TGID2yPExnajykURTFwbCSv/UWSL51Er4wYvdLt2CsXuRLvqQANjh5gGnxCcdJg+SQ0CF4i2Viwwcc0GHV8u3Ry"
    "MmOBznqKTItpeadLmP3ROxDFv71wZ0dj4rHgY+CfveJKzt26oB0MeRBWFzaKHvs0giwy4fwc7uEw4Wgov6LJaj/HDPuBXZzz/gr2"
    "0+RoP3HDfpY42k+lK/F+NrCfcz/A7Od61MqVtvbjN+znYcd4Y+Ei5tXPSXGysWpXcq8Oey/zHUYrZodfMOxwwjEmOTMJOzxs2KHP"
    "cR9aVLRDerOk1WOfbnonHtvtvEY9idWef/kQ09cDtj4B9JVZkLy/R1zJPfY5uUzOFzmv5OjJPfZVhgwH+3YH7ds1/GHWrnsc/dhq"
    "o135jrZxjcHzZfIqhKSvFY76ikzmnUISfeEYO4nN4/c7XvFtu70/vNWQIb/X09ouX3NyO/xrtAv0lfsRpq83M5z0tdnQV8xRPicn"
    "YYdqHtPpEedVCD35vhT4UpnIULhpVPgr8jIZJt7bw+Wc8jeTM/PzxyYRJwxMIk5IuY3pq9DlpK8nDH0NOerrzCTihKOGvp53jBOq"
    "9eT++XVvgjiBzfGZLmTJy3JWykOAVLa6Syf+3oCcN6xZIJWHVQtk1f0pBoRSXzQl6mUSdV2iXiFRXyBRr5gS9RaJul+ifkCifrtE"
    "vWpK1Csk6qUS9SaJ+jaJevWUqC+SqPsk6lUS9UqJetOUqC+RqBdL1Ksl6o0S9bYpUV8rUa+SqO+UqMcl6v4pUd8pUT8gUT8uUX9W"
    "or5zStRLJeqKRH2RRL1Yoj48JeptEvWdEvVDEvW7JOqRKVEfkajfJlE/KVH/d4n6xJSo10vUmyTqEYn6hyXqB6ZE3S9Rj0jUb5Oo"
    "PyJRPzQl6jsk6hMS9WMS9a9L1A9PiXqlRH2RRL1Nor5Lon7blKjPkKjDF5Zm6qUS9TSJ+rEpUa+WqFdLbR+WqB+QqB+fEvUqiXqF"
    "RN0vUb9Eon5iStQHJOqHJOonJOovSNQfmRL1YYn6YYn6IxL1MxL1k1Oi3iRRb5OoT0jUb+TU6UyhXXOesQ6H+0YBxK13MD48Ht5N"
    "viE2t+L032FGRluxIl+h1PHsWLPDkXuc2Ctp2+9O0PZ3oV2VpxjPdu9PaSuOaUlxVkeYbajpjjO701OyusOS1Z2WrO4tyerqU63W"
    "8uKUqB+TqJ+VqBdbfe+qmyXqZ6ZE/TaJ+hmJui5RD0vUX58S9csl6scl6qclyf+35G3OTon6tRL1UxL1sxL1VVLb35oS9dsl6q9L"
    "1H2S5K+SqCubpkL9Zon6ixJ1RaLul6jrU6J+SKJ+UqL+uiT5xRJ135SoXyVRf0SifkaiXiJRL54S9QMS9RMS9Rcl6nqq1c8/OIkx"
    "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"
)

_ccd_cache = None


def ccd_vdf_path():
    """内蔵のCCDをツールと同じフォルダに書き出して、そのパスを返す"""
    global _ccd_cache
    if _ccd_cache and os.path.isfile(_ccd_cache):
        return _ccd_cache
    data = zlib.decompress(base64.b64decode(CCD_VDF_ZB64))
    digest = hashlib.sha256(data).hexdigest()
    dirs = [os.path.dirname(os.path.abspath(__file__))]
    if os.environ.get("LOCALAPPDATA"):
        dirs.append(os.path.join(os.environ["LOCALAPPDATA"], "AVS_Maker"))
    last = None
    for d in dirs:
        path = os.path.join(d, "ccd_64bit.vdf")
        try:
            ok = False
            if os.path.isfile(path):
                with open(path, "rb") as f:
                    ok = hashlib.sha256(f.read()).hexdigest() == digest
            if not ok:
                os.makedirs(d, exist_ok=True)
                with open(path, "wb") as f:
                    f.write(data)
            _ccd_cache = path
            return path
        except OSError as e:
            last = e
    raise ValueError(f"CCDフィルタの書き出しに失敗しました: {last}")


# ---------------------------------------------------------------- 数字・時間の整形
def _num(text, name, as_int=False):
    text = str(text).strip()
    try:
        if as_int:
            return str(int(text))
        float(text)
        return text
    except ValueError:
        raise ValueError(f"「{name}」には数字を入れてください（今の値: {text!r}）")


def fmt_tc(frame, fps):
    tenths = int(round((frame / fps if fps else 0.0) * 10))   # 先に 0.1秒単位に丸める（59.96秒が「60.0」にならないように）
    h, rest = divmod(tenths, 36000)
    m, rest = divmod(rest, 600)
    return f"{h}:{m:02d}:{rest // 10:02d}.{rest % 10}"


def fmt_dur(sec):
    sec = max(0, int(sec))
    h, rest = divmod(sec, 3600)
    m, s = divmod(rest, 60)
    if h:
        return f"{h}時間{m:02d}分"
    return f"{m}分{s:02d}秒"


def fmt_num(x, decimals):
    """増減した数字を見やすく整える（-16 / 1.05 / 1.0 のように）"""
    s = f"{round(x, decimals):.{decimals}f}"
    if decimals > 0:
        s = s.rstrip("0")
        if s.endswith("."):
            s += "0"
    if s in ("-0", "-0.0"):
        s = s[1:]
    return s


def bump_value(text, sign, step, lo, hi, decimals, big=False):
    """入力欄の文字を数値として step だけ増減して返す。数字でなければ None"""
    try:
        x = float(str(text).strip())
    except ValueError:
        return None
    x += sign * step * (5 if big else 1)
    x = min(max(x, lo), hi)
    return fmt_num(x, decimals)


def make_spin(parent, var, step, lo, hi, decimals=0, width=6):
    """↑↓キー（Shiftで5倍）・マウスホイール・▲▼ボタンで値を増減できる入力欄"""
    def bump(sign, big=False):
        new = bump_value(var.get(), sign, step, lo, hi, decimals, big)
        if new is not None:
            var.set(new)
        return "break"

    def tidy():   # ▲▼ボタンで増減したあとの桁そろえ
        new = bump_value(var.get(), 0, step, lo, hi, decimals)
        if new is not None:
            var.set(new)

    if hasattr(ttk, "Spinbox"):
        w = ttk.Spinbox(parent, textvariable=var, width=width, from_=lo, to=hi,
                        increment=step, command=tidy)
    else:                       # 古いPythonではSpinboxがないので普通の入力欄＋キー操作
        w = ttk.Entry(parent, textvariable=var, width=width)
    w.bind("<Up>", lambda e: bump(+1))
    w.bind("<Down>", lambda e: bump(-1))
    w.bind("<Shift-Up>", lambda e: bump(+1, True))
    w.bind("<Shift-Down>", lambda e: bump(-1, True))
    w.bind("<MouseWheel>", lambda e: bump(1 if e.delta > 0 else -1, bool(e.state & 0x1)))
    return w


# ---------------------------------------------------------------- カット（残す区間）
def normalize_cuts(cuts):
    """開始順に並べて、重なりを整理する。区間は (開始, 終了, 24p化するか)（両端を含むフレーム番号）。
    区間は自動では結合しない（利用者が分けた区間はそのまま残す）。
    前の区間と一部が重なるときは、あとの区間の開始を前の区間の次のフレームにずらす（同じコマを2回使わないため）。
    前の区間に完全に含まれる区間は取り除く"""
    items = []
    for c in cuts:
        s, e = int(c[0]), int(c[1])
        f = bool(c[2]) if len(c) > 2 else False
        if e >= s:
            items.append((s, e, f))
    items.sort(key=lambda x: (x[0], -x[1]))
    out = []
    for s, e, f in items:
        if out:
            pe = out[-1][1]
            if e <= pe:
                continue
            if s <= pe:
                s = pe + 1
        out.append((s, e, f))
    return out


def trim_expr(s, e, nframes=0):
    """1区間ぶんの Trim(…)"""
    if nframes and e >= nframes - 1:
        return f"Trim({s}, 0)"            # 最後まで
    if e == 0:
        return f"Trim({s}, -1)"           # 0フレーム目だけ（Trim(0,0)は全体になるため）
    return f"Trim({s}, {e})"


def cut_expression(cuts, nframes=0):
    """avsの Trim(…) ++ Trim(…) の1行を作る。区間がなければ空文字"""
    cuts = normalize_cuts(cuts or [])
    return " ++ ".join(trim_expr(s, e, nframes) for s, e, _ in cuts)


def kept_frames(cuts, nframes):
    cuts = normalize_cuts(cuts or [])
    if not cuts:
        return nframes
    return sum(e - s + 1 for s, e, _ in cuts)


# ---------------------------------------------------------------- avs生成
def parse_color(o):
    """明るさ補正・色相彩度の設定を数値にして返す（プレビューとavs生成で共通）"""
    c = {}
    if o["levels"]:
        il = float(_num(o["in_low"], "入力 黒"))
        g = float(_num(o["gamma"], "ガンマ"))
        ih = float(_num(o["in_high"], "入力 白"))
        ol = float(_num(o["out_low"], "出力 黒"))
        oh = float(_num(o["out_high"], "出力 白"))
        if ih <= il:
            raise ValueError("「入力 白」は「入力 黒」より大きくしてください")
        if g <= 0:
            raise ValueError("「ガンマ」は0より大きくしてください")
        c["levels"] = (il, g, ih, ol, oh)
    if o["tweak"]:
        hue = float(_num(o["hue"], "色相"))
        sat = float(_num(o["sat"], "彩度"))
        if not -180 <= hue <= 180:
            raise ValueError("「色相」は -180 〜 180 の間で入れてください")
        if sat < 0:
            raise ValueError("「彩度」は0以上にしてください")
        c["tweak"] = (hue, sat)
    return c


def build_script(path, o, cuts=None, nframes=0):
    """動画パスと設定dictから avs の文字列を作る"""
    L = []
    segs = normalize_cuts(cuts or [])
    if segs:
        flags = {f for _, _, f in segs}
    else:
        flags = {bool(o.get("anime24"))}
    mixed = len(flags) == 2            # 24pにする区間としない区間が混ざっている
    all24 = flags == {True}
    any24 = all24 or mixed             # AviSynth+ 3.7.5 で処理する

    plug = (o.get("plug24") or "").strip()
    if any24:
        # 24p化は AviSynth+ 3.7.5 側で動かす。元のavsと同じく、標準のプラグインは読み込まない
        L.append("ClearAutoloadDirs()")
        if plug:
            L.append(f'AddAutoloadDir("{plug}")')
        L.append("")
    elif o["deint"]:
        L.append("SetMemoryMax(2048, type=DEV_TYPE_CUDA)")
    L.append(f'srcfile="{path}"')

    src = o["source"]
    if src.startswith("自動"):
        src = "AviSource" if os.path.splitext(path)[1].lower() == ".avi" else "LWLibavVideoSource"

    # SRestoreのあとに AssumeFPS で正確に 24000/1001 にそろえる（長い動画での音ズレ防止）
    qtgmc = ["QTGMC(Preset=\"Slower\", TR2=3)", "SRestore(frate=24000.0/1001)",
             "AssumeFPS(24000, 1001)"]
    kfm = ['KFMDeint(mode=1, preset="Slower", nr=true, cuda=true)']

    if mixed:
        # 24p化する区間としない区間を、1本のavsの中でつなぐ（QTGMCで59.94pにしてから区間ごとに切り出す）。
        # 24p化する区間は、SRestoreで24pにしたあと、59.94pに戻して（コマの複製）つなぐ。
        L += ["", "# アニメ部分：24pに間引いてから59.94に戻す",
              "function Anime24(clip c) {",
              "    return c.SRestore(frate=24000.0/1001).AssumeFPS(24000, 1001)"
              ".RequestLinear(rlim=100, clim=100).ChangeFPS(60000, 1001)",
              "}", "",
              f"src = {src}(srcfile).ConvertToYV12(interlaced=true).Assume{o['field']}()",
              'bob = src.QTGMC(Preset="Slower", TR2=3)       # 2倍のコマ数（59.94p）になる',
              "", "# 残す区間（カット編集）。コマ番号は、取り込んだままのコマ数の2倍で切る",
              ]
        names = []
        for i, (s_, e_, f) in enumerate(segs, 1):
            if nframes and e_ >= nframes - 1:
                t = f"bob.Trim({2 * s_}, 0)"
            else:
                t = f"bob.Trim({2 * s_}, {2 * e_ + 1})"
            L.append(f"seg{i} = {t}" + (".Anime24()" if f else "") + (f"      # 24p化" if f else ""))
            names.append(f"seg{i}")
        L += ["", " ++ ".join(names), ""]
    else:
        L.append(f"{src}(srcfile)")
        expr = cut_expression(cuts, nframes)
        if expr:   # 取り込んだままのフレーム番号で切る（インターレース解除の前）
            L += ["", "# 残す区間（カット編集）", expr, ""]
        if all24:
            L += ["# アニメを24pにする（QTGMC + SRestore）", "ConvertToYV12(interlaced=true)",
                  f"Assume{o['field']}()"] + qtgmc
        elif o["deint"]:
            L.append("ConvertToYV12(interlaced=true)")
            L.append(f"Assume{o['field']}()")
            L.append("OnCPU(2)")
            L += kfm
            L.append("OnCUDA(2)")
        else:
            L.append("ConvertToYV12()")

    color = parse_color(o)   # 数字のまちがいはここでエラーにする

    if "levels" in color:
        il = _num(o["in_low"], "入力 黒", True)
        g = _num(o["gamma"], "ガンマ")
        ih = _num(o["in_high"], "入力 白", True)
        ol = _num(o["out_low"], "出力 黒", True)
        oh = _num(o["out_high"], "出力 白", True)
        L += ["", "# 明るさ補正", f"Levels({il}, {g}, {ih}, {ol}, {oh}, coring=false)"]

    if "tweak" in color:
        hue, sat = color["tweak"]
        parts = []
        if hue != 0:
            parts.append(f"hue={_num(o['hue'], '色相')}")
        if sat != 1:
            parts.append(f"sat={_num(o['sat'], '彩度')}")
        if parts:
            L += ["", "# 色相・彩度の補正（hue: ＋で赤寄り／－で緑寄り）",
                  f"Tweak({', '.join(parts)}, coring=false)"]

    if o["resize"]:
        w = _num(o["width"], "横幅", True)
        h = _num(o["height"], "縦幅", True)
        L += ["", f"Spline36Resize({w}, {h})"]

    if o["color"]:
        if any24:
            # AviSynth+ 3.7.5 では ConvertToYV12 は8bit専用なので、16bitのまま使える関数で変換する
            L += ["", "# 色空間変換（BT.601 → BT.709）RGB経由版",
                  "ConvertBits(16)",
                  'ConvertToPlanarRGB(matrix="Rec601")',
                  'ConvertToYUV420(matrix="Rec709")',
                  "ConvertBits(8, dither=0)"]
        else:
            L += ["", "# 色空間変換（BT.601 → BT.709）RGB経由版",
                  "ConvertBits(16)",
                  'ConvertToRGB48(matrix="Rec601")',
                  'ConvertToYV12(matrix="Rec709")',
                  "ConvertBits(8)"]

    # 24p化（SRestore）は Prefetch を付けない。SRestoreは前のコマの判定を引き継ぎながら
    # 順番に処理するので、マルチスレッドにすると間引きが狂うことがある
    if not any24 and o["deint"]:
        L += ["", "OnCPU(2)"]

    if o["ccd"]:   # CCDはCPUで動く8bit RGB32専用のフィルタなので、最後（CPUに戻した後）に掛ける
        th = int(_num(o["ccd_th"], "CCDの閾値", True))
        if not 0 <= th <= 100:
            raise ValueError("「CCDの閾値」は 0 〜 100 の間で入れてください")
        matrix = "Rec709" if o["color"] else "Rec601"
        il = "" if (o["deint"] or any24) else ", interlaced=true"
        L += ["", "# 色ノイズ除去（VirtualDubのCCD。RGB32に変換して掛け、YV12に戻す）",
              f'ConvertToRGB32(matrix="{matrix}"{il})',
              f'LoadVirtualDubPlugin("{ccd_vdf_path()}", "CCD", 1)',
              f"CCD({th}, 1)",
              f'ConvertToYV12(matrix="{matrix}"{il})']

    return "\n".join(L) + "\n"


def split_parts(cuts, anime24):
    """動画1本ぶんの処理のまとまりを返す：[(AviSynth+ 3.7.5 で処理するか, 区間のリスト)]。
    24p化する区間が1つでもあれば、動画全体を1本のavsにして 3.7.5 側で処理する
    （通常の区間も、KFMDeintではなく QTGMC で処理して、24p区間と同じavsの中でつなぐ）"""
    segs = normalize_cuts(cuts or [])
    if not segs:
        return [(bool(anime24), [])]
    return [(any(f for _, _, f in segs), segs)]


def build_part_scripts(path, o, cuts=None, nframes=0):
    """動画1本ぶんのavsを、パートごとに作る。戻り値：[(24p化するか, 区間, avsの文字列)]
    （AviSynth Neo と AviSynth+ 3.7.5 は同じavsに混ぜられないため、別々のavsにする）"""
    return [(f, c, build_script(path, o, c if c else None, nframes))
            for f, c in split_parts(cuts, o.get("anime24"))]


def write_avs(out_path, text):
    """AviSynthは日本語環境のANSI(cp932)で読むことが多いので、まずcp932で保存。
    無理な文字があればUTF-8(BOM付き)で保存して False を返す"""
    try:
        with open(out_path, "w", encoding="cp932", newline="\r\n") as f:
            f.write(text)
        return True
    except UnicodeEncodeError:
        with open(out_path, "w", encoding="utf-8-sig", newline="\r\n") as f:
            f.write(text)
        return False


# ---------------------------------------------------------------- プレビュー用の計算
def simulate(rgb, o):
    """RGB画像(uint8)に、avsのLevels / Tweak と同じ補正をかけた見本を返す。
    （インターレース解除・リサイズ・色空間変換・CCDは再現しません）"""
    c = parse_color(o)
    if not c:
        return rgb
    a = rgb.astype(np.float32)
    R, G, B = a[..., 0], a[..., 1], a[..., 2]
    Yf = 0.299 * R + 0.587 * G + 0.114 * B
    Y = 16 + Yf * (219 / 255)                      # 放送レンジ(16-235)の輝度
    U = (B - Yf) / 1.772 * (224 / 255)             # 中心0の色差
    V = (R - Yf) / 1.402 * (224 / 255)

    if "levels" in c:
        il, g, ih, ol, oh = c["levels"]
        t = np.clip((Y - il) / (ih - il), 0, 1) ** (1.0 / g)
        Y = np.clip(t * (oh - ol) + ol, 0, 255)

    if "tweak" in c:
        hue, sat = c["tweak"]
        th = math.radians(hue)
        cs, sn = math.cos(th), math.sin(th)
        # AviSynthのTweakと同じ回転（hue>0で赤寄り）
        U, V = (U * cs + V * sn) * sat, (V * cs - U * sn) * sat
        U = np.clip(U, -127, 127)
        V = np.clip(V, -127, 127)

    Yf = (Y - 16) * (255 / 219)
    Cb = U * (255 / 224)
    Cr = V * (255 / 224)
    R = Yf + 1.402 * Cr
    B = Yf + 1.772 * Cb
    G = (Yf - 0.299 * R - 0.114 * B) / 0.587
    out = np.stack([R, G, B], axis=-1)
    return np.clip(out + 0.5, 0, 255).astype(np.uint8)


# ---------------------------------------------------------------- 比較画像（補正前｜補正後）
def _load_font(size):
    """日本語が出せるフォントを探す（なければPillowの標準フォント）"""
    from PIL import ImageFont
    fdir = os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts")
    for name in ("meiryo.ttc", "YuGothM.ttc", "msgothic.ttc", "BIZ-UDGothicR.ttc"):
        p = os.path.join(fdir, name)
        if os.path.isfile(p):
            try:
                return ImageFont.truetype(p, size), True
            except OSError:
                pass
    try:
        return ImageFont.load_default(size=size), False
    except TypeError:            # 古いPillow
        return ImageFont.load_default(), False


def settings_summary(o):
    """比較画像の下に書く、今の設定の要約（Claudeなどに見せるとき用）"""
    items = []
    if o.get("anime24"):
        items.append("24p化(QTGMC+SRestore)")
    elif o.get("deint"):
        items.append(f"KFMDeint({o['field']})")
    if o.get("levels"):
        items.append(f"Levels({o['in_low']}, {o['gamma']}, {o['in_high']}, {o['out_low']}, {o['out_high']})")
    if o.get("tweak"):
        items.append(f"Tweak(hue={o['hue']}, sat={o['sat']})")
    if o.get("ccd"):
        items.append(f"CCD({o['ccd_th']}) ※画像には未反映")
    if o.get("resize"):
        items.append(f"Resize {o['width']}x{o['height']}")
    if o.get("color"):
        items.append("BT.601→709")
    return " / ".join(items) if items else "補正なし"


def make_compare_image(raw, o, title="", show_settings=True):
    """補正前を左、補正後を右に並べ、見出しと設定の要約を付けた画像を作る"""
    from PIL import ImageDraw
    aspect = display_aspect(raw.width, raw.height, o)
    h = raw.height
    w = max(1, int(round(h * aspect)))
    before = raw.resize((w, h), Image.LANCZOS) if (w, h) != raw.size else raw.copy()
    after = Image.fromarray(simulate(np.asarray(before), o))

    gap, head = 8, 34
    font, jp = _load_font(18)
    small, _ = _load_font(15)
    lines = [l for l in (title, settings_summary(o) if (jp and show_settings) else "") if l]
    foot = 10 + 22 * len(lines)
    W, H = w * 2 + gap, head + h + foot
    img = Image.new("RGB", (W, H), (32, 32, 32))
    img.paste(before, (0, head))
    img.paste(after, (w + gap, head))
    d = ImageDraw.Draw(img)
    d.text((8, 7), "補正前" if jp else "BEFORE", fill=(235, 235, 235), font=font)
    d.text((w + gap + 8, 7), "補正後（Levels/Tweakの見本）" if jp else "AFTER", fill=(235, 235, 235), font=font)
    y = head + h + 6
    for line in lines:
        d.text((8, y), line, fill=(200, 200, 200), font=small)
        y += 22
    return img


def stack_compare_images(imgs, o):
    """複数の比較画像を縦に並べ、いちばん下に設定の要約を1回だけ書く"""
    from PIL import ImageDraw
    gap = 6
    font, jp = _load_font(15)
    foot = 34 if jp else 0
    W = max(i.width for i in imgs)
    H = sum(i.height for i in imgs) + gap * (len(imgs) - 1) + foot
    out = Image.new("RGB", (W, H), (32, 32, 32))
    y = 0
    for i in imgs:
        out.paste(i, (0, y))
        y += i.height + gap
    if jp:
        ImageDraw.Draw(out).text((8, H - foot + 6), settings_summary(o), fill=(200, 200, 200), font=font)
    return out


def parse_position(text, fps, nframes):
    """「18743」→ フレーム番号、「10:25.4」「1:02:03」→ 時間 として、フレーム番号を返す"""
    t = str(text).strip().replace("：", ":").replace("　", "").replace(" ", "")
    t = t.translate(str.maketrans("０１２３４５６７８９．", "0123456789."))
    if not t:
        raise ValueError("フレーム番号か時間を入れてください")
    if re.fullmatch(r"\d+", t):
        n = int(t)
    elif re.fullmatch(r"\d+(:\d+(\.\d+)?){1,2}", t) or re.fullmatch(r"\d+:\d+:\d+(\.\d+)?", t):
        sec = 0.0
        for part in t.split(":"):
            sec = sec * 60 + float(part)
        if not fps:
            raise ValueError("動画の長さを調べられていないため、時間では移動できません")
        n = int(round(sec * fps))
    else:
        raise ValueError(f"「{text}」は読み取れませんでした。\n"
                         "フレーム番号（例：18743）か、時間（例：10:25.4 や 1:02:03）で入れてください")
    if nframes:
        n = min(max(n, 0), nframes - 1)
    return max(n, 0)


def copy_image_to_clipboard(img):
    """Windowsのクリップボードに画像を入れる（チャットに貼り付け用）。できなければ False"""
    if os.name != "nt":
        return False
    import ctypes
    from ctypes import wintypes
    buf = io.BytesIO()
    img.convert("RGB").save(buf, "BMP")
    data = buf.getvalue()[14:]               # BMPのファイルヘッダーを除いた部分がDIB
    CF_DIB, GMEM_MOVEABLE = 8, 0x0002
    k32, u32 = ctypes.windll.kernel32, ctypes.windll.user32
    k32.GlobalAlloc.restype = wintypes.HGLOBAL
    k32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
    k32.GlobalLock.restype = wintypes.LPVOID
    k32.GlobalLock.argtypes = [wintypes.HGLOBAL]
    k32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
    u32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
    u32.SetClipboardData.restype = wintypes.HANDLE
    h = k32.GlobalAlloc(GMEM_MOVEABLE, len(data))
    if not h:
        return False
    p = k32.GlobalLock(h)
    ctypes.memmove(p, data, len(data))
    k32.GlobalUnlock(h)
    if not u32.OpenClipboard(None):
        return False
    try:
        u32.EmptyClipboard()
        return bool(u32.SetClipboardData(CF_DIB, h))
    finally:
        u32.CloseClipboard()


# ---------------------------------------------------------------- ffmpeg まわり
def find_tool(name, custom=""):
    """ffmpeg / ffprobe を探す。指定された場所 → 同じフォルダ → PATH の順。
    ffmpeg は、選ばれたファイルを名前にかかわらずそのまま使う（ffmpegNEW.exe のように名前を変えていても可）"""
    if custom and os.path.isfile(custom):
        stem, ext = os.path.splitext(os.path.basename(custom))
        if name == "ffmpeg" or stem.lower() == name:
            return custom
        d = os.path.dirname(custom)
        cands = []
        if stem.lower().startswith("ffmpeg"):          # ffmpegNEW.exe → ffprobeNEW.exe も探す
            cands.append(name + stem[len("ffmpeg"):] + ext)
        cands += [name + ".exe", name]
        for cand in cands:
            p = os.path.join(d, cand)
            if os.path.isfile(p):
                return p
    return shutil.which(name)


def _parse_fraction(text):
    try:
        f = Fraction(str(text))
        return f if f > 0 else None
    except (ValueError, ZeroDivisionError):
        return None


def probe_video(ffprobe, path):
    """動画のフレームレートとフレーム数を調べる。失敗したら None"""
    if not ffprobe:
        return None
    try:
        r = subprocess.run([ffprobe, "-v", "error", "-select_streams", "v:0",
                            "-show_entries", "stream=r_frame_rate,avg_frame_rate,nb_frames,duration:format=duration",
                            "-of", "json", path],
                           capture_output=True, timeout=30, creationflags=NOCONSOLE)
        j = json.loads(r.stdout.decode("utf-8", "replace"))
        st = j["streams"][0]
        fps = _parse_fraction(st.get("avg_frame_rate")) or _parse_fraction(st.get("r_frame_rate"))
        if not fps:
            return None
        nb = st.get("nb_frames")
        if nb and str(nb).isdigit() and int(nb) > 0:
            n = int(nb)
        else:
            dur = st.get("duration") or j.get("format", {}).get("duration")
            n = int(float(dur) * float(fps))
        return {"fps": float(fps), "nframes": max(n, 1)}
    except Exception:
        return None


def grab_frame(ffmpeg, path, t, deint, field):
    """動画のt秒付近の1コマをPIL画像(RGB)で返す"""
    vf = []
    if deint:   # 見た目確認用の簡易インターレース解除
        vf.append(f"yadif=mode=0:parity={0 if field == 'TFF' else 1}")
    vf.append("scale='min(960,iw)':-2")
    cmd = [ffmpeg, "-v", "error", "-ss", f"{t:.3f}", "-i", path, "-frames:v", "1",
           "-vf", ",".join(vf), "-f", "image2pipe", "-vcodec", "png", "-"]
    r = subprocess.run(cmd, capture_output=True, timeout=40, creationflags=NOCONSOLE)
    if r.returncode != 0 or not r.stdout:
        msg = r.stderr.decode(errors="replace").strip().splitlines()
        raise RuntimeError(msg[-1] if msg else "ffmpegが画像を返しませんでした")
    return Image.open(io.BytesIO(r.stdout)).convert("RGB")


def display_aspect(sw, sh, o):
    """プレビューの縦横比。リサイズがオンなら出力サイズの比率に合わせる"""
    if o["resize"]:
        try:
            w, h = int(o["width"]), int(o["height"])
            if w > 0 and h > 0:
                return w / h
        except ValueError:
            pass
    if sw == 720 and sh in (480, 486, 576):
        return 4 / 3
    return sw / sh


def aspect_arg(o):
    """-aspect に渡す値（1440x1056 → 15:11）。リサイズしないときは指定しない"""
    if o["resize"]:
        try:
            w, h = int(o["width"]), int(o["height"])
            g = math.gcd(w, h)
            if g > 0 and w > 0 and h > 0:
                return f"{w // g}:{h // g}"
        except ValueError:
            pass
    return None


def encoder_supports(ffmpeg, encoder, word):
    """そのffmpegのエンコーダーが、指定の語（例: tuneのuhq）に対応しているか。調べられなければ None"""
    try:
        r = subprocess.run([ffmpeg, "-hide_banner", "-h", f"encoder={encoder}"],
                           capture_output=True, timeout=20, creationflags=NOCONSOLE)
        text = (r.stdout + r.stderr).decode("utf-8", "replace")
        if encoder not in text or "Unknown encoder" in text or "is not recognized" in text:
            return None
        return word in text
    except Exception:
        return None


def build_ffmpeg_cmd(ffmpeg, avs, out_mp4, o, video_args=None):
    """VirtualDubで使っていた設定と同じ内容のffmpegコマンドを作る"""
    cq = int(_num(o["cq"], "画質(CQ)", True))
    if not 0 <= cq <= 51:
        raise ValueError("「画質(CQ)」は 0 〜 51 の間で入れてください")
    if video_args is None:
        # 古いffmpegは uhq 非対応なので、そのときは一段下の hq で代わりにする
        tune = ["-tune", "uhq" if o.get("uhq", True) else "hq"]
        video_args = ["-c:v", "hevc_nvenc", "-preset", "p7"] + tune + [
                      "-rc", "vbr",
                      "-cq", str(cq), "-b:v", "0", "-spatial-aq", "1", "-temporal-aq", "1",
                      "-pix_fmt", "p010le", "-profile:v", "main10", "-tag:v", "hvc1"]
    cmd = [ffmpeg, "-hide_banner", "-y", "-nostdin", "-loglevel", "error",
           "-progress", "pipe:1", "-nostats", "-i", avs] + video_args
    asp = aspect_arg(o)
    if asp:
        cmd += ["-aspect", asp]
    cmd += ["-colorspace", "bt709", "-color_primaries", "bt709", "-color_trc", "bt709",
            "-color_range", "tv",
            "-c:a", "flac", "-compression_level", "8",
            out_mp4]
    return cmd


_PROGRESS_LINE = re.compile(r"^[A-Za-z0-9_]+=\S*$")   # frame=… / stream_0_0_q=… / speed=… などの進捗情報


def run_ffmpeg(cmd, total_sec, on_progress, on_start):
    """ffmpegを実行して (終了コード, エラーメッセージの行たち) を返す。
    on_progress(割合 or None, 経過秒) が進捗のたびに呼ばれる"""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         stdin=subprocess.DEVNULL, creationflags=NOCONSOLE,
                         text=True, encoding="utf-8", errors="replace")
    on_start(p)
    lines = []
    for line in p.stdout:
        line = line.strip()
        if line.startswith("out_time_us="):
            try:
                sec = int(line.split("=", 1)[1]) / 1e6
            except ValueError:      # 開始直後は N/A
                continue
            if sec >= 0:
                on_progress(min(sec / total_sec, 1.0) if total_sec else None, sec)
        elif _PROGRESS_LINE.match(line):
            continue
        elif line:
            lines.append(line)
            del lines[:-200]
    p.wait()
    return p.returncode, lines


def exit_code_text(code):
    """Windowsのクラッシュ(0xC0000005など)も分かる形にする"""
    return f"終了コード {code}" + (f"（0x{code & 0xFFFFFFFF:08X}）" if code is not None and code < 0 or (code or 0) > 255 else "")


# ---------------------------------------------------------------- 更新（GitHub から最新版を取ってくる）
def _version_tuple(v):
    """'1.2.10' → (1, 2, 10)。数字でない部分は 0 とみなす"""
    out = []
    for part in str(v).strip().split("."):
        m = re.match(r"\d+", part)
        out.append(int(m.group()) if m else 0)
    return tuple(out)


def _http_get(url, timeout=20):
    import urllib.request
    req = urllib.request.Request(
        f"{url}?t={int(time.time())}",          # 古い版がキャッシュから返らないように
        headers={"User-Agent": f"avs_maker/{APP_VERSION}", "Cache-Control": "no-cache"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def fetch_latest_info():
    """GitHub の version.json を読む → {"version": "1.2.0", "notes": [...]}"""
    data = json.loads(_http_get(UPDATE_RAW + "version.json").decode("utf-8"))
    if not isinstance(data, dict) or "version" not in data:
        raise ValueError("version.json の中身が正しくありません")
    return data


def download_new_version(expected_version):
    """新しい avs_maker.pyw を取ってきて、プログラムとして正しく読めるか確かめてから返す（bytes）"""
    data = _http_get(UPDATE_RAW + "avs_maker.pyw", timeout=60)
    text = data.decode("utf-8")
    compile(text, "avs_maker.pyw", "exec")             # 壊れたファイルなら、ここでエラーになる
    m = re.search(r'^APP_VERSION\s*=\s*"([^"]+)"', text, re.M)
    if not m or _version_tuple(m.group(1)) != _version_tuple(expected_version):
        raise ValueError("ダウンロードしたファイルの版番号が、案内された版と一致しません。"
                         "少し時間をおいてから、もう一度お試しください。")
    return data


def install_new_version(data):
    """今の版を avs_maker_old.pyw として残し、新しい版に入れ替える"""
    me = os.path.abspath(__file__)
    folder = os.path.dirname(me)
    backup = os.path.join(folder, os.path.splitext(os.path.basename(me))[0] + "_old.pyw")
    tmp = me + ".new"
    with open(tmp, "wb") as f:
        f.write(data)
    shutil.copy2(me, backup)
    os.replace(tmp, me)
    return backup


# ---------------------------------------------------------------- ツールチップ（マウスを置くと説明が出る）
class ToolTip:
    """ウィジェットにマウスを置いて少し待つと、説明の小窓を出す"""
    DELAY_MS = 600

    def __init__(self, widget, text):
        self.widget, self.text = widget, text
        self.job = None
        self.win = None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
        widget.bind("<ButtonPress>", self._leave, add="+")
        widget.bind("<MouseWheel>", self._leave, add="+")

    def _enter(self, _=None):
        self._cancel()
        self.job = self.widget.after(self.DELAY_MS, self._show)

    def _leave(self, _=None):
        self._cancel()
        if self.win is not None:
            try:
                self.win.destroy()
            except tk.TclError:
                pass
            self.win = None

    def _cancel(self):
        if self.job:
            try:
                self.widget.after_cancel(self.job)
            except tk.TclError:
                pass
            self.job = None

    def _show(self):
        self.job = None
        if self.win is not None or not self.widget.winfo_exists():
            return
        self.win = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        try:
            tw.wm_attributes("-topmost", True)
        except tk.TclError:
            pass
        lbl = tk.Label(tw, text=self.text, justify="left", wraplength=420,
                       background="#ffffe8", foreground="#222", relief="solid", borderwidth=1,
                       padx=8, pady=5)
        lbl.pack()
        tw.update_idletasks()
        # マウスの右下に出す。画面からはみ出すときは内側に寄せる
        x = self.widget.winfo_pointerx() + 14
        y = self.widget.winfo_pointery() + 18
        w, h = tw.winfo_reqwidth(), tw.winfo_reqheight()
        sw, sh = self.widget.winfo_screenwidth(), self.widget.winfo_screenheight()
        if x + w > sw - 4:
            x = max(4, sw - w - 4)
        if y + h > sh - 40:
            y = max(4, self.widget.winfo_pointery() - h - 10)
        tw.wm_geometry(f"+{x}+{y}")


# ボタン・チェックボックスの説明（表示されている文字で対応づけ）
TIPS_BY_TEXT = {
    # ① 動画ファイル
    "ファイルを追加…": "動画ファイルを選んで一覧に追加します。ドラッグ＆ドロップでも追加できます（フォルダごとでもOK）。",
    "選んだものを削除": "一覧で選んだ動画を外します（ファイル自体は消えません）。Deleteキーでも外せます。",
    "全部クリア": "一覧を空にします（ファイル自体は消えません）。",
    # ② 設定
    "インターレース解除（KFMDeint）":
        "Neo（CUDA）の KFMDeint でインターレースを解除します。\n"
        "24コマのアニメ部分は元のコマを組み直し、60iの部分（スクロールする文字など）は"
        "なめらかなまま 59.94p で出力します。普通のアニメや実写はこれでOK。\n"
        "※24p化する区間があるときは、この設定は使われず QTGMC で処理されます。",
    "アニメを24pにする（QTGMC＋SRestore）":
        "動画全体を QTGMC で 59.94p にしてから、SRestore で混ざっていないコマを選んで 24p にします。\n"
        "口や手が二重に見える（フィールドがブレンドされた）アニメ向け。AviSynth+ 3.7.5 で処理します。\n"
        "※区間を登録しているときは、右の区間リストの ☑／□ が優先されます。ここは新しく登録する区間の初期値です。",
    "明るさ補正（Levels）":
        "Levels で明るさの範囲を広げます。\n"
        "入力 黒：この明るさ以下を黒にする（上げると黒が締まる。上げすぎると暗部がつぶれる）\n"
        "入力 白：この明るさ以上を白にする（下げると明るくなる。下げすぎると白飛びする）\n"
        "比較画像で、一番明るい場面と暗い場面の両方を確認して決めてください。",
    "色相・彩度の補正（Tweak）":
        "Tweak で色の向きと濃さを変えます。\n"
        "色相：－で緑寄り／＋で赤寄りに全体の色を回します（肌がピンクっぽいテープは －10 くらい）。\n"
        "彩度：1.0 がそのまま。上げると色が濃くなります（1.1〜1.15 くらいまでが目安）。\n"
        "※白やグレーの色かぶりは、色相では直りません。",
    "色ノイズ除去（CCD）":
        "VirtualDub の Color Camcorder Denoise（CCD）で、色のザラつき・色ノイズを取ります。\n"
        "閾値を大きくするほど強く効きます（30 が目安）。強すぎると細かい色が薄くなります。\n"
        "※24p化するときは、プラグインのフォルダに VDubFilter.dll が必要です。\n"
        "※効果は右の比較画像には出ません。",
    "リサイズ（Spline36Resize）":
        "出力の大きさを変えます。1440×1056 は、4:3 の映像を正方形ピクセルにした大きさ（15:11）です。",
    "色空間変換（BT.601 → BT.709）":
        "SD（BT.601）の色を、HD 用（BT.709）の色に変換します。\n"
        "1440×1056 などHDの大きさで出力するときは、オンにしておくと色が正しく再生されます。",
    # ③ 保存先
    "動画と同じフォルダに保存": "avs と mp4 を、元の動画と同じフォルダに作ります。",
    "このフォルダに保存：": "avs と mp4 を、右で指定したフォルダにまとめて作ります。",
    # 動画ごとの設定・プリセット
    "設定をコピー": "今表示している動画の設定（② の内容）を覚えます。\nほかの動画を選んで「選んだ動画に貼り付け」で、同じ設定にできます。",
    "選んだ動画に貼り付け": "「設定をコピー」で覚えた設定を、一覧で選んでいる動画（複数可）に貼り付けます。\nカット区間はそのままです。",
    "全部の動画に適用": "今の設定を、一覧にある全部の動画に適用します（確認が出ます）。カット区間はそのままです。",
    "選んだ動画に適用": "左で選んだプリセットの設定を、一覧で選んでいる動画（複数可）に適用します。",
    "今の設定を保存…": "今の設定に名前を付けて、プリセットとして保存します（例：日本一の男の魂 2巻）。\n同じ名前なら上書きします。",
    "プリセットを削除": "左で選んでいるプリセットを削除します。",
    # 実行
    "avsだけ作成": "avs ファイルだけを作ります（エンコードはしません）。VirtualDub などで開いて確認したいとき用。",
    "avsを作成してエンコード":
        "avs を作り、そのまま ffmpeg（HEVC / NVENC）で mp4 にエンコードします。\n"
        "24p化する区間がある動画は「24p用ffmpeg」、それ以外は「通常用ffmpeg」を使います。",
    "エンコードを中止": "今のエンコードを止めます。途中までのファイルは削除されます。",
    "使い方": "使い方のページ（説明書）をブラウザで開きます。",
    "更新を確認": "インターネット（GitHub）に新しい版があるか確認します。\n"
                  "あれば変更内容を表示し、「はい」で自動で入れ替えます。設定とプリセットはそのまま残ります。\n"
                  "前の版は avs_maker_old.pyw として残るので、不具合があればそれを起動すれば戻せます。",
    # プレビュー
    "◀◀ 1秒": "1秒前に戻ります（画像を押したあと Shift+← でも同じ）。",
    "◀ 1コマ": "1コマ前に戻ります（画像を押したあと ← でも同じ）。",
    "1コマ ▶": "1コマ先に進みます（画像を押したあと → でも同じ）。",
    "1秒 ▶▶": "1秒先に進みます（画像を押したあと Shift+→ でも同じ）。",
    "この場面を取り直す":
        "今の位置の1コマを、動画から読み直します。表示がおかしい・真っ黒なときに押してください\n"
        "（動画の長さを調べられていなければ、調べ直します）。",
    "ffmpegの場所を指定…": "プレビュー用の ffmpeg.exe を選びます（「通常用ffmpeg」の欄と同じ設定です）。",
    "補正アシスタント…": "別ウインドウで、覚えた場面を大きく表示して補正を詰めます（上級者向け）。\n"
                          "・白飛び・黒潰れを場面ごとに判定し、潰れている所を色で表示\n"
                          "・全部の場面で潰れにくい「入力 黒」「入力 白」のおすすめ値\n"
                          "・肌をクリックして、自然な肌色になる色相のおすすめ値\n"
                          "先にメイン画面で、明るい場面・暗い場面・顔のアップを「この場面を覚える」で登録しておくと便利です。",
    "この場面を覚える": "今表示している場面を「チェックする場面」に登録します（1本の動画に8つまで）。\n"
                        "明るい場面・暗い場面・顔のアップなどを覚えておくと、設定を変えたあとすぐ見直せます。\n"
                        "覚えた場面は動画ごとに記録され、次に同じ動画を追加したときも残っています。",
    "選んだ場面を忘れる": "リストで選んだ場面を消します（Delete キーでも可）。",
    "まとめてコピー": "覚えた場面すべての比較画像（左＝補正前／右＝補正後）を縦に並べた1枚を、クリップボードにコピーします。\n"
                      "設定を変えるたびに押せば、全場面の見え方を一度に確認・相談できます。",
    "まとめて保存…": "覚えた場面すべての比較画像を縦に並べた1枚を、PNG / JPEG で保存します。",
    "移動": "左の欄に入れたフレーム番号か時間の場面へ移動します（Enter キーでも可）。",
    "コピー":
        "左に補正前、右に補正後を並べた比較画像を、クリップボードにコピーします。\n"
        "チャットに Ctrl+V で貼り付けられます。下にファイル名・フレーム番号・設定も入ります。",
    "保存…": "比較画像（左＝補正前／右＝補正後）を PNG / JPEG で保存します。",
    # カット編集
    "ここを開始点に": "今表示しているコマを、残す区間の開始点にします。",
    "ここを終了点に": "今表示しているコマを、残す区間の終了点にします。",
    "この区間を残す ＋":
        "開始点〜終了点を「残す区間」として登録します。\n"
        "開始点だけなら最後まで、終了点だけなら先頭からそこまでになります。",
    "選んだ区間を削除": "リストで選んだ区間を消します（Delete / BackSpace キーでも可）。",
    "全部削除（カットなし）": "登録した区間を全部消して、動画全体を使う状態に戻します。",
}

# 入力欄の説明（設定の名前で対応づけ）
TIPS_BY_VAR = {
    "source": "動画の読み込み方法です。自動なら、avi は AviSource、mp4 / mkv などは LWLibavVideoSource を使います。",
    "field": "インターレースのフィールドの順番です。VHSの取り込みは、ほぼ TFF（トップファースト）です。",
    "plug24": "24p化（AviSynth+ 3.7.5）で読み込むプラグインのフォルダです。\n"
              "SRestore.avsi・QTGMC.avsi・Zs_RF_Shared.avsi と、masktools2 / RgTools / mvtools2 / nnedi3 /\n"
              "TIVTC / Average / grunt の dll、CCDを使うなら VDubFilter.dll を入れておきます。",
    "in_low": "入力 黒：この明るさ以下を黒にします（標準は16）。上げると黒が締まります。",
    "in_high": "入力 白：この明るさ以上を白にします（標準は235）。下げると明るくなりますが、下げすぎると白飛びします。",
    "gamma": "ガンマ：中間の明るさを調整します。1.0 がそのまま、大きくすると中間が明るくなります。",
    "out_low": "出力 黒：黒をどの明るさにするか（ふつうは16のまま）。",
    "out_high": "出力 白：白をどの明るさにするか（ふつうは235のまま）。",
    "hue": "色相：－で緑寄り／＋で赤寄り。肌がピンクっぽいときは －10 くらい。",
    "sat": "彩度：1.0 がそのまま。上げると色が濃くなります。",
    "ccd_th": "CCDの閾値：大きいほど強く効きます（VirtualDubのCCDと同じ値。30 が目安）。",
    "width": "出力の横幅です。",
    "height": "出力の縦幅です。",
    "out_dir": "avs と mp4 をまとめて保存するフォルダです。",
    "cq": "画質（CQ）：小さいほど高画質でファイルが大きくなります。VHSの保存用なら 18〜20 が目安。",
    "ffmpeg": "通常用（KFMDeint / Neo）の ffmpeg.exe です。\n"
              "同じフォルダに avisynth.dll を置かないこと（置くとNeoではなくそのdllが使われ、CUDAのエラーになります）。",
    "ffmpeg24": "24p化用の ffmpeg.exe です。\n"
                "AviSynth+ 3.7.5 の avisynth.dll と同じフォルダに置いたものを選んでください。",
}

TIP_CHOOSE = {
    "out_dir": "avs と mp4 を保存するフォルダを選びます。",
    "ffmpeg": "通常用（Neo）の ffmpeg.exe を選びます。",
    "ffmpeg24": "24p用（AviSynth+ 3.7.5 の avisynth.dll と同じフォルダ）の ffmpeg.exe を選びます。",
}


# ---------------------------------------------------------------- 補正アシスタント（判定・おすすめ値・肌の色）
# 自然な肌色の色相の目安（度）。アニメは作品ごとに塗りが違うので広めにとり、
# 外れているときだけ、範囲の少し内側まで動かす（直しすぎない）
SKIN_RANGE = (24.0, 42.0)
SKIN_PULL = (27.0, 39.0)


def video_luma(rgb):
    """表示用RGB(0-255) → 映像の明るさ(16-235の範囲)"""
    a = rgb.astype(np.float32)
    return 16.0 + (0.299 * a[..., 0] + 0.587 * a[..., 1] + 0.114 * a[..., 2]) * (219.0 / 255.0)


def judge_area(h, w):
    """判定に使う範囲（VHSの端の黒い縁や、下のノイズの線を除く）"""
    return (int(h * 0.02), int(h * 0.95), int(w * 0.03), int(w * 0.97))


def levels_params(o):
    """(入力黒, ガンマ, 入力白, 出力黒, 出力白)。明るさ補正がオフなら変換なしの値"""
    c = parse_color(o)
    return c.get("levels", (16.0, 1.0, 235.0, 16.0, 235.0))


def analyze_scene(raw, o):
    """1場面の判定。白飛び・黒潰れの割合（%）、補正後の一番暗い所、元の暗い所・明るい所"""
    a = np.asarray(raw)
    y0, y1, x0, x1 = judge_area(*a.shape[:2])
    yv = video_luma(a[y0:y1, x0:x1])
    il, g, ih, ol, oh = levels_params(o)
    t = np.clip((yv - il) / max(ih - il, 1e-6), 0, 1) ** (1.0 / g)
    out_disp = (ol + t * (oh - ol) - 16.0) * (255.0 / 219.0)
    return {
        "white": float((yv >= ih - 0.5).mean() * 100),
        "black": float((yv <= il + 0.5).mean() * 100),
        "darkest": float(np.percentile(out_disp, 0.5)),
        "src_lo": float(np.percentile(yv, 0.5)),
        "src_hi": float(np.percentile(yv, 99.9)),
    }


def recommend_levels(stats, flags):
    """覚えた場面すべてで白飛び・黒潰れしにくい「入力 黒」「入力 白」を出す。
    stats: {フレーム: analyze_scene の結果} / flags: {フレーム: {"b": 黒は演出, "w": 白は演出}}"""
    lows = {n: s["src_lo"] for n, s in stats.items() if not flags.get(n, {}).get("b")}
    highs = {n: s["src_hi"] for n, s in stats.items() if not flags.get(n, {}).get("w")}
    lo = int(min(max(math.floor(min(lows.values())) - 1, 16), 80)) if lows else 16
    hi = int(max(min(math.ceil(max(highs.values())) + 1, 235), lo + 40)) if highs else 235
    lo_by = min(lows, key=lows.get) if lows else None     # 黒の値を決めた場面
    hi_by = max(highs, key=highs.get) if highs else None  # 白の値を決めた場面
    return lo, hi, len(lows), len(highs), lo_by, hi_by


def patch_mean(raw, xr, yr):
    """画像の (xr, yr)（0〜1の位置）のまわりの小さな範囲の平均色"""
    a = np.asarray(raw)
    h, w = a.shape[:2]
    r = max(3, w // 120)
    cx, cy = int(xr * w), int(yr * h)
    p = a[max(0, cy - r):cy + r + 1, max(0, cx - r):cx + r + 1].reshape(-1, 3).astype(np.float32)
    return p.mean(axis=0)


def hue_of(rgb):
    import colorsys
    hdeg = colorsys.rgb_to_hsv(*(np.clip(np.asarray(rgb, dtype=float), 0, 255) / 255.0))[0] * 360
    return hdeg - 360 if hdeg > 180 else hdeg            # 赤のあたりを 0° 前後の数字にそろえる


def skin_hue(means, o):
    """肌の見本（平均色のリスト）に設定を当てたときの、色相の平均"""
    arr = np.clip(np.round(np.array(means, dtype=np.float32)), 0, 255).astype(np.uint8).reshape(-1, 1, 3)
    out = simulate(arr, o).reshape(-1, 3)
    return float(np.mean([hue_of(c) for c in out]))


def suggest_hue(means, o):
    """肌の見本が自然な範囲に入る、いちばん小さな色相（Tweak の hue）を探す。(おすすめの値, そのときの色相)"""
    sat = o.get("sat", "1.0") if o.get("tweak") else "1.0"
    now = skin_hue(means, o)
    target = min(max(now, SKIN_PULL[0]), SKIN_PULL[1])
    best = None
    for h in range(-30, 31):
        o2 = dict(o, tweak=True, hue=str(h), sat=sat)
        v = skin_hue(means, o2)
        d = abs(v - target)
        if best is None or d < best[2] - 1e-6 or (abs(d - best[2]) < 1e-6 and abs(h) < abs(best[0])):
            best = (h, v, d)
    return best[0], best[1]


class AssistWindow:
    """別ウインドウ：覚えた場面を大きく表示して、白飛び・黒潰れの判定、おすすめの明るさ、肌の色を見る"""

    def __init__(self, app):
        self.app = app
        self.win = tk.Toplevel(app.root)
        self.win.geometry("1240x800")
        self.win.minsize(900, 600)
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        self.raws = {}            # フレーム → 1コマ
        self.stats = {}           # フレーム → 判定
        self.cur = None           # 表示中の場面（フレーム番号）
        self.key = None           # 読み込んだ条件（動画・インターレース解除など）
        self.q = queue.Queue()
        self.loading = set()
        self.tkimg = None
        self.img_box = None       # 画像を描いた位置 (x, y, 幅, 高さ)
        self._render_job = None
        self._refresh_job = None
        self.rec = None
        self.hue_rec = None
        self.build()
        self.refresh(reload=True)
        self.win.after(150, self.poll)

    # ----- 画面
    def build(self):
        w = self.win
        top = ttk.Frame(w)
        top.pack(fill="x", padx=10, pady=(8, 4))
        self.title_label = ttk.Label(top, text="", font=self.app.font_bold)
        self.title_label.pack(side="left")
        self.mode = tk.StringVar(value="split")
        self.zebra = tk.BooleanVar(value=True)
        right = ttk.Frame(top)
        right.pack(side="right")
        ttk.Label(right, text="表示").pack(side="left")
        for val, text in (("after", "補正後"), ("before", "補正前"), ("split", "左右で比べる")):
            ttk.Radiobutton(right, text=text, value=val, variable=self.mode,
                            command=self.schedule_render).pack(side="left", padx=3)
        ttk.Checkbutton(right, text="白飛び・黒潰れを色で表示", variable=self.zebra,
                        command=self.schedule_render).pack(side="left", padx=(10, 0))

        body = ttk.PanedWindow(w, orient="horizontal")
        body.pack(fill="both", expand=True, padx=10, pady=4)

        left = ttk.Frame(body)
        body.add(left, weight=3)
        self.canvas = tk.Canvas(left, background="#1b1b1b", highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self.schedule_render())
        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<Button-3>", self.on_right_click)
        srow = ttk.Frame(left)
        srow.pack(fill="x", pady=(4, 0))
        ttk.Label(srow, text="左右の境目").pack(side="left")
        self.split = tk.DoubleVar(value=0.5)
        self.split_scale = ttk.Scale(srow, from_=0.0, to=1.0, variable=self.split,
                                     command=lambda e: self.schedule_render())
        self.split_scale.pack(side="left", fill="x", expand=True, padx=6)
        self.legend = ttk.Label(left, foreground="#666", text=(
            "赤の斜線＝白飛び ／ 青の斜線＝黒潰れ ／ 黄色の点線の外＝判定しない所（VHSの端の縁など）\n"
            "肌の部分をクリック＝肌の見本に登録 ／ 右クリック＝近くの見本を消す"))
        self.legend.pack(anchor="w", pady=(2, 0))

        side = ttk.Frame(body, width=400)
        body.add(side, weight=1)

        f1 = ttk.LabelFrame(side, text="覚えた場面と判定")
        f1.pack(fill="both", expand=True, pady=(0, 6))
        cols = ("t", "white", "black", "dark", "b", "w")
        self.tree = ttk.Treeview(f1, columns=cols, show="headings", height=8, selectmode="browse")
        for c, text, wid in (("t", "場面", 78), ("white", "白飛び", 54), ("black", "黒潰れ", 54),
                             ("dark", "最暗部", 48), ("b", "黒は演出", 58), ("w", "白は演出", 58)):
            self.tree.heading(c, text=text)
            self.tree.column(c, width=wid, minwidth=40, anchor="center", stretch=(c == "t"))
        self.tree.tag_configure("warn", foreground="#b00020")
        self.tree.tag_configure("muted", foreground="#888")
        self.tree.pack(fill="both", expand=True, padx=6, pady=(6, 2))
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.on_tree_select())
        self.tree.bind("<Button-1>", self.on_tree_click, add="+")
        brow = ttk.Frame(f1)
        brow.pack(fill="x", padx=6, pady=(0, 4))
        ttk.Button(brow, text="メイン画面の今の場面を追加", command=self.add_current).pack(side="left")
        ttk.Button(brow, text="選んだ場面を忘れる", command=self.forget_scene).pack(side="left", padx=4)
        self.summary = ttk.Label(f1, text="", wraplength=380, justify="left")
        self.summary.pack(anchor="w", padx=6, pady=(0, 6))

        f2 = ttk.LabelFrame(side, text="おすすめの明るさ（Levels）")
        f2.pack(fill="x", pady=(0, 6))
        self.rec_label = ttk.Label(f2, text="", wraplength=380, justify="left")
        self.rec_label.pack(anchor="w", padx=6, pady=(6, 2))
        self.b_rec = ttk.Button(f2, text="この値を使う", command=self.apply_rec, state="disabled")
        self.b_rec.pack(anchor="w", padx=6, pady=(0, 6))

        f3 = ttk.LabelFrame(side, text="肌の色")
        f3.pack(fill="x")
        self.skin_label = ttk.Label(f3, text="", wraplength=380, justify="left")
        self.skin_label.pack(anchor="w", padx=6, pady=(6, 2))
        r3 = ttk.Frame(f3)
        r3.pack(fill="x", padx=6, pady=(0, 6))
        self.b_hue = ttk.Button(r3, text="おすすめの色相にする", command=self.apply_hue, state="disabled")
        self.b_hue.pack(side="left")
        ttk.Button(r3, text="肌の見本を全部消す", command=self.clear_skins).pack(side="left", padx=4)

        for wdg, tip in (
            (self.tree, "覚えた場面ごとの判定です。行を選ぶと左に大きく表示します。\n"
                        "白飛び・黒潰れ：模様が消えている部分の割合（判定する範囲の中で）。赤字は多めです。\n"
                        "最暗部：補正後の一番暗い所の明るさ（0＝真っ黒）。大きいと黒が浮いています。\n"
                        "「黒は演出」「白は演出」の欄を押すと ☑ になり、その場面のその判定を、おすすめ値の計算から外します\n"
                        "（夜の場面の真っ黒な空、光っている物など、潰れていて正しい場面に使います）。"),
            (self.b_rec, "おすすめの値を、メイン画面の「明るさ補正」に入れます（選んでいる動画に反映）。"),
            (self.b_hue, "肌の見本が自然な肌色の範囲に入る色相を、メイン画面の「色相・彩度の補正」に入れます。"),
        ):
            ToolTip(wdg, tip)

    # ----- 状態
    def path(self):
        return self.app.cur_path

    def frames(self):
        return list(self.app.marks.get(self.path(), [])) if self.path() else []

    def flags(self):
        return self.app.mflags.setdefault(self.path(), {}) if self.path() else {}

    def skins(self):
        return self.app.skins.setdefault(self.path(), []) if self.path() else []

    def options(self):
        return self.app.options()

    def load_key(self):
        o = self.options()
        return (self.path(), o["deint"], o["field"], self.app.tool("ffmpeg"))

    def on_app_change(self):
        """メイン画面で設定や場面が変わったとき"""
        if self._refresh_job:
            self.win.after_cancel(self._refresh_job)
        self._refresh_job = self.win.after(200, lambda: self.refresh(reload=self.load_key() != self.key))

    def refresh(self, reload=False):
        self._refresh_job = None
        if not self.win.winfo_exists():
            return
        path = self.path()
        self.win.title(f"補正アシスタント － {os.path.basename(path)}" if path else "補正アシスタント")
        if reload:
            self.key = self.load_key()
            self.raws, self.stats = {}, {}
            self.loading = set()
        frames = self.frames()
        for n in list(self.raws):
            if n not in frames:
                self.raws.pop(n, None)
                self.stats.pop(n, None)
        if self.cur not in frames:
            self.cur = frames[0] if frames else None
        self.start_loading()
        self.analyze_all()

    def start_loading(self):
        path, info = self.path(), self.app.cur_info()
        _, deint, field, ffmpeg = self.key or (None, None, None, None)
        need = []
        for n in self.frames():
            if n in self.raws or n in self.loading:
                continue
            cached = self.app.frame_cache.get((path, n, deint, field, ffmpeg))
            if cached is not None:
                self.raws[n] = cached
            else:
                need.append(n)
        if not need or not ffmpeg or not path:
            return
        self.loading.update(need)
        key = self.key

        def work():
            for n in need:
                try:
                    t = max(0.0, (n - 0.3) / info["fps"]) if info else 0.0
                    self.q.put((key, n, grab_frame(ffmpeg, path, t, deint, field), None))
                except Exception as e:
                    self.q.put((key, n, None, e))
        threading.Thread(target=work, daemon=True).start()

    def poll(self):
        try:
            if not self.win.winfo_exists():
                return
        except tk.TclError:
            return
        changed = False
        try:
            while True:
                key, n, img, err = self.q.get_nowait()
                if key != self.key:
                    continue
                self.loading.discard(n)
                if img is not None:
                    self.raws[n] = img
                    self.app.cache_frame((key[0], n, key[1], key[2], key[3]), img)
                    changed = True
        except queue.Empty:
            pass
        try:
            if changed:
                self.analyze_all()
            self.win.after(150, self.poll)
        except tk.TclError:          # ウインドウを閉じた
            pass

    # ----- 判定
    def analyze_all(self):
        o = self.options()
        try:
            parse_color(o)
        except ValueError as e:
            self.summary.config(text=f"設定にまちがいがあります：{e}", foreground="#b00020")
            return
        self.stats = {n: analyze_scene(img, o) for n, img in self.raws.items() if n in self.frames()}
        self.update_tree()
        self.update_recommend(o)
        self.update_skin(o)
        self.schedule_render()

    def update_tree(self):
        info = self.app.cur_info()
        flags = self.flags()
        sel = self.cur
        self.tree.delete(*self.tree.get_children())
        for n in self.frames():
            f = flags.get(n, {})
            s = self.stats.get(n)
            t = fmt_tc(n, info["fps"]) if info else str(n)
            if s is None:
                vals = (t, "…", "…", "…", "☑" if f.get("b") else "☐", "☑" if f.get("w") else "☐")
                tags = ("muted",)
            else:
                w_txt = "なし" if s["white"] < 0.1 else f"{s['white']:.1f}%"
                b_txt = "なし" if s["black"] < 0.3 else f"{s['black']:.1f}%"
                if f.get("w"):
                    w_txt = "（演出）"
                if f.get("b"):
                    b_txt = "（演出）"
                vals = (t, w_txt, b_txt, f"{s['darkest']:.0f}",
                        "☑" if f.get("b") else "☐", "☑" if f.get("w") else "☐")
                bad = ((not f.get("w") and s["white"] >= 0.5) or (not f.get("b") and s["black"] >= 2.0))
                tags = ("warn",) if bad else ()
            self.tree.insert("", "end", iid=str(n), values=vals, tags=tags)
        if sel is not None and self.tree.exists(str(sel)):
            self.tree.selection_set(str(sel))
            self.tree.see(str(sel))

        if not self.frames():
            self.summary.config(foreground="#b00020", text=(
                "覚えた場面がありません。メイン画面で見比べたい場面を表示して「この場面を覚える」"
                "（またはここの「メイン画面の今の場面を追加」）を押してください。\n"
                "一番明るい場面・一番暗い場面・顔のアップを入れると、判定が正確になります。"))
            return
        if self.loading:
            self.summary.config(foreground="", text=f"場面を読み込んでいます…（残り {len(self.loading)}）")
            return
        flags = self.flags()
        nw = sum(1 for n, s in self.stats.items() if not flags.get(n, {}).get("w") and s["white"] >= 0.5)
        nb = sum(1 for n, s in self.stats.items() if not flags.get(n, {}).get("b") and s["black"] >= 2.0)
        darks = [s["darkest"] for n, s in self.stats.items() if not flags.get(n, {}).get("b")]
        lines = [f"白飛び：{'多めの場面が ' + str(nw) + ' つ' if nw else '問題なし'}",
                 f"黒潰れ：{'多めの場面が ' + str(nb) + ' つ' if nb else '問題なし'}"]
        if darks and min(darks) > 30:
            lines.append(f"黒の浮き：どの場面も一番暗い所が {min(darks):.0f} 以上です。黒が浮いています"
                         "（「入力 黒」を上げる余地があります）")
        else:
            lines.append("黒の浮き：問題なし")
        self.summary.config(foreground="#b00020" if (nw or nb) else "", text="\n".join(lines))

    def update_recommend(self, o):
        if not self.stats or self.loading:
            self.rec = None
            self.rec_label.config(text="（場面を読み込むと表示されます）")
            self.b_rec.config(state="disabled")
            return
        lo, hi, nl, nh, lo_by, hi_by = recommend_levels(self.stats, self.flags())
        self.rec = (lo, hi)
        il, g, ih, ol, oh = levels_params(o)
        info = self.app.cur_info()
        tc = (lambda n: fmt_tc(n, info["fps"])) if info else str
        now = f"今：入力 黒 {il:.0f}・入力 白 {ih:.0f}" if o.get("levels") else "今：明るさ補正なし"
        text = (f"入力 黒 {lo}・入力 白 {hi}\n（{now}）\n"
                f"覚えた場面のうち、黒は {nl} 場面、白は {nh} 場面をもとに、どれも潰れにくい値を出しています。")
        if lo_by is not None:
            text += (f"\n黒の値は {tc(lo_by)} の場面、白の値は {tc(hi_by)} の場面で決まっています。"
                     "その場面の暗さ・明るさが演出なら、「黒は演出」「白は演出」に ☑ を入れると、ほかの場面に合わせた値になります。")
        if nl == 0 or nh == 0:
            text += "\n※演出のチェックで、計算に使える場面がなくなっています。"
        if len(self.stats) < 3:
            text += "\n※場面が少ないと当てにならないので、明るい場面と暗い場面を足してください。"
        self.rec_label.config(text=text)
        self.b_rec.config(state="normal")

    def update_skin(self, o):
        means = []
        for n, xr, yr in self.skins():
            if n in self.raws:
                means.append(patch_mean(self.raws[n], xr, yr))
        total = len(self.skins())
        if not total:
            self.hue_rec = None
            self.b_hue.config(state="disabled")
            self.skin_label.config(foreground="", text=(
                "左の画像で、顔や手など肌の部分をクリックしてください（場面をまたいで何点でも）。\n"
                f"自然な肌色の目安は {SKIN_RANGE[0]:.0f}〜{SKIN_RANGE[1]:.0f}° です（0°＝赤、60°＝黄色）。"))
            return
        if not means:
            self.skin_label.config(text="（場面を読み込むと表示されます）")
            return
        before = skin_hue(means, dict(o, levels=False, tweak=False))
        now = skin_hue(means, o)
        h, v = suggest_hue(means, o)
        cur_h = int(float(o.get("hue", 0))) if o.get("tweak") else 0
        ok = SKIN_RANGE[0] <= now <= SKIN_RANGE[1]
        text = (f"肌の見本 {len(means)} 点：元の色 {before:.0f}° → 今の設定 {now:.0f}°"
                f"（{'自然な肌色の範囲です' if ok else f'自然な肌色（{SKIN_RANGE[0]:.0f}〜{SKIN_RANGE[1]:.0f}°）から外れています'}）\n")
        if abs(h - cur_h) >= 3 and not ok:
            text += f"色相を {h:+d} にすると、{v:.0f}° になります。"
            self.hue_rec = h
            self.b_hue.config(state="normal", text=f"色相を {h:+d} にする")
        else:
            text += "今の色相のままで大丈夫です。"
            self.hue_rec = None
            self.b_hue.config(state="disabled", text="おすすめの色相にする")
        text += "\n※作品によって肌の塗りは違います。参考画像があれば、そちらに合わせるのが確実です。"
        self.skin_label.config(foreground="" if ok else "#b00020", text=text)

    # ----- 操作
    def on_tree_select(self):
        sel = self.tree.selection()
        if sel:
            n = int(sel[0])
            if n != self.cur:
                self.cur = n
                self.schedule_render()

    def on_tree_click(self, event):
        if self.tree.identify_region(event.x, event.y) != "cell":
            return
        col = self.tree.identify_column(event.x)
        row = self.tree.identify_row(event.y)
        if not row or col not in ("#5", "#6"):
            return
        n = int(row)
        f = self.flags().setdefault(n, {})
        k = "b" if col == "#5" else "w"
        f[k] = not f.get(k)
        self.app.schedule_save()
        self.analyze_all()

    def add_current(self):
        self.app.add_mark()
        self.app.root.after(50, lambda: self.refresh())

    def forget_scene(self):
        if self.cur is None:
            return
        self.app.forget_mark(self.cur)
        self.refresh()

    def on_click(self, event):
        n = self.cur
        if n is None or n not in self.raws or not self.img_box:
            return
        x, y, w, h = self.img_box
        if not (x <= event.x < x + w and y <= event.y < y + h):
            return
        self.skins().append([n, round((event.x - x) / w, 4), round((event.y - y) / h, 4)])
        self.app.schedule_save()
        self.update_skin(self.options())
        self.schedule_render()

    def on_right_click(self, event):
        if not self.img_box or self.cur is None:
            return
        x, y, w, h = self.img_box
        best, bi = 18 ** 2, None
        for i, (n, xr, yr) in enumerate(self.skins()):
            if n != self.cur:
                continue
            d = (x + xr * w - event.x) ** 2 + (y + yr * h - event.y) ** 2
            if d <= best:
                best, bi = d, i
        if bi is not None:
            del self.skins()[bi]
            self.app.schedule_save()
            self.update_skin(self.options())
            self.schedule_render()

    def clear_skins(self):
        if self.path() and self.app.skins.get(self.path()):
            if messagebox.askyesno(APP_TITLE, "この動画の肌の見本を全部消しますか？", parent=self.win):
                self.app.skins[self.path()] = []
                self.app.schedule_save()
                self.update_skin(self.options())
                self.schedule_render()

    def apply_rec(self):
        if not self.rec:
            return
        lo, hi = self.rec
        v = self.app.vars
        v["levels"].set(True)
        v["in_low"].set(str(lo))
        v["in_high"].set(str(hi))
        self.app.status.config(text=f"明るさ補正を 入力 黒 {lo}・入力 白 {hi} にしました")

    def apply_hue(self):
        if self.hue_rec is None:
            return
        v = self.app.vars
        if not v["tweak"].get():
            v["sat"].set("1.0")
        v["tweak"].set(True)
        v["hue"].set(str(self.hue_rec))
        self.app.status.config(text=f"色相を {self.hue_rec:+d} にしました")

    # ----- 描画
    def schedule_render(self):
        if self._render_job:
            self.win.after_cancel(self._render_job)
        self._render_job = self.win.after(60, self.render)

    def render(self):
        self._render_job = None
        c = self.canvas
        if not c.winfo_exists():
            return
        c.delete("all")
        cw, ch = max(c.winfo_width(), 50), max(c.winfo_height(), 50)
        n = self.cur
        raw = self.raws.get(n) if n is not None else None
        info = self.app.cur_info()
        if n is not None:
            self.title_label.config(text=f"場面 {self.frames().index(n) + 1}/{len(self.frames())}　"
                                         f"フレーム {n}" + (f"（{fmt_tc(n, info['fps'])}）" if info else ""))
        else:
            self.title_label.config(text="")
        if raw is None:
            self.img_box = None
            msg = "読み込んでいます…" if n is not None else "覚えた場面がありません"
            c.create_text(cw // 2, ch // 2, text=msg, fill="#bbb")
            return
        o = self.options()
        aspect = display_aspect(raw.width, raw.height, o)
        if cw / ch > aspect:
            h = ch - 8
            w = int(h * aspect)
        else:
            w = cw - 8
            h = int(w / aspect)
        w, h = max(w, 10), max(h, 10)
        base = raw.resize((w, h), Image.BILINEAR)
        b = np.asarray(base)
        try:
            a = simulate(b, o)
        except ValueError:
            a = b
        if self.zebra.get():
            a = a.copy()
            yv = video_luma(b)
            il, g, ih, ol, oh = levels_params(o)
            yy, xx = np.mgrid[0:h, 0:w]
            stripe = ((xx + yy) // 4) % 2 == 0
            a[(yv >= ih - 0.5) & stripe] = (235, 40, 40)
            a[(yv <= il + 0.5) & stripe] = (40, 120, 255)
        mode = self.mode.get()
        if mode == "before":
            out = b
        elif mode == "after":
            out = a
        else:
            sx = int(w * self.split.get())
            out = np.concatenate([b[:, :sx], a[:, sx:]], axis=1)
        self.tkimg = ImageTk.PhotoImage(Image.fromarray(np.ascontiguousarray(out)))
        x0, y0 = (cw - w) // 2, (ch - h) // 2
        self.img_box = (x0, y0, w, h)
        c.create_image(x0, y0, anchor="nw", image=self.tkimg)
        if mode == "split":
            sx = x0 + int(w * self.split.get())
            c.create_line(sx, y0, sx, y0 + h, fill="#ffffff", width=2)
            c.create_text(x0 + 8, y0 + 8, anchor="nw", text="補正前", fill="#fff")
            c.create_text(x0 + w - 8, y0 + 8, anchor="ne", text="補正後", fill="#fff")
        ay0, ay1, ax0, ax1 = judge_area(h, w)
        c.create_rectangle(x0 + ax0, y0 + ay0, x0 + ax1, y0 + ay1, outline="#ffd24d", dash=(4, 4))
        k = 0
        for sn, xr, yr in self.skins():
            k += 1
            if sn != n:
                continue
            px, py = x0 + xr * w, y0 + yr * h
            c.create_oval(px - 7, py - 7, px + 7, py + 7, outline="#ffffff", width=2)
            c.create_oval(px - 8, py - 8, px + 8, py + 8, outline="#000000", width=1)
            c.create_text(px + 11, py - 11, text=str(k), fill="#ffffff", anchor="sw")

    def close(self):
        self.app.assistant = None
        self.win.destroy()


# ---------------------------------------------------------------- GUI
class App:
    def __init__(self, root):
        self.root = root
        root.title(APP_TITLE)
        # 画面に収まる大きさにする（ノートPCなど、画面が低くても下のボタンが隠れないように）
        global PREVIEW_MAX_W, PREVIEW_MAX_H
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        ww, wh = min(1340, sw - 30), min(980, sh - 110)
        root.geometry(f"{ww}x{wh}+10+10")
        root.minsize(min(1000, ww), min(600, wh))
        PREVIEW_MAX_H = max(220, min(360, wh - 640))      # 低い画面では、プレビュー画像を小さくする
        PREVIEW_MAX_W = int(PREVIEW_MAX_H * 4 / 3)

        self.files = []
        self.cuts = {}             # 動画のパス → [(開始フレーム, 終了フレーム), ...]
        self.fsets = {}            # 動画のパス → その動画の設定（FILE_KEYS の分）
        self.marks = {}            # 動画のパス → チェックする場面（フレーム番号のリスト）
        self.mflags = {}           # 動画のパス → {フレーム: {"b": 黒は演出, "w": 白は演出}}
        self.skins = {}            # 動画のパス → 肌の見本 [[フレーム, x(0-1), y(0-1)], ...]
        self.assistant = None      # 補正アシスタントのウインドウ
        self.frame_cache = {}      # 取り出した1コマの控え（同じ場面をすぐ出すため）
        self._batch_running = False
        self.clip = None           # 「設定をコピー」で覚えた設定
        self._loading = False      # 動画を選び替えて設定欄を書き換えている最中か
        self._save_job = None
        self.vars = {}
        for key, val in DEFAULTS.items():
            self.vars[key] = tk.BooleanVar() if isinstance(val, bool) else tk.StringVar()
            self.vars[key].set(val)
        self.load_settings()
        self.record = self.load_record()

        # プレビュー・カット編集用の状態
        self.raw = None            # 取り出した元の1コマ(PIL)
        self.frame_key = None
        self.cur_path = None
        self.finfo = {}            # パス → {"fps":…, "nframes":…}
        self.pend = {"s": None, "e": None}
        self.pos = tk.DoubleVar(value=0.0)
        self.before_img = self.after_img = None
        self.job = None

        # エンコード用の状態
        self.running = False
        self.cancel_flag = False
        self.proc = None
        self.q = queue.Queue()

        self.build_ui()
        self.add_tooltips()
        self.update_edit_label()
        self.update_states()
        self.refresh_preview()

        for key, var in self.vars.items():
            var.trace_add("write", lambda *a, k=key: self.on_var(k))

        root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------- ツールチップ
    def add_tooltips(self):
        """画面の部品を順に見て、対応する説明をツールチップとして付ける"""
        var_names = {str(v): k for k, v in self.vars.items()}

        def var_key(w):
            try:
                return var_names.get(str(w.cget("textvariable")))
            except tk.TclError:
                return None

        def walk(w):
            yield w
            for c in w.winfo_children():
                yield from walk(c)

        for w in walk(self.root):
            cls = w.winfo_class()
            tip = None
            if cls in ("TButton", "TCheckbutton", "TRadiobutton", "Button", "Checkbutton"):
                try:
                    text = str(w.cget("text"))
                except tk.TclError:
                    text = ""
                if text == "選ぶ…":            # 同じ文字のボタンは、隣の入力欄で見分ける
                    for sib in w.master.winfo_children():
                        k = var_key(sib)
                        if k in TIP_CHOOSE:
                            tip = TIP_CHOOSE[k]
                            break
                else:
                    tip = TIPS_BY_TEXT.get(text)
            elif cls in ("TEntry", "Entry", "TSpinbox", "Spinbox", "TCombobox"):
                tip = TIPS_BY_VAR.get(var_key(w))
            if tip:
                ToolTip(w, tip)

        # 文字のない部品
        ToolTip(self.listbox, "追加した動画の一覧です。右の列は、その動画の設定の要約です。\n"
                              "選んだ動画の設定が ② に出て、② を変えると、選んでいる動画にだけ反映されます。\n"
                              "Ctrl／Shift で複数選ぶと、変えた項目だけ選んだ全部にまとめて反映されます（Ctrl+A で全部選択）。\n"
                              "設定はファイル名ごとに自動で記録され、同じ名前の動画を次に追加したときに戻ります。\n"
                              "ここに動画やフォルダをドラッグ＆ドロップしても追加できます。")
        ToolTip(self.e_jump, "移動したい場面を入れて Enter。\n"
                             "数字だけならフレーム番号（例：18743）、「:」を入れると時間（例：10:25.4、1:02:03）です。")
        ToolTip(self.marklist, "覚えた場面のリストです。クリックすると、その場面へ移動します。")
        ToolTip(self.cb_preset, "保存してあるプリセットです。選んでから「選んだ動画に適用」を押します。")
        ToolTip(self.edit_label, "② の設定が、どの動画に反映されるかを表示しています。")
        ToolTip(self.img_label, "押している間は「補正前」、離すと「補正後（Levels/Tweakの見本）」を表示します。\n"
                                "押したあとは ←→ キーで1コマ、Shift+←→ で1秒移動できます。")
        ToolTip(self.scale, "動画の中の位置です。動かして離すと、その場面を表示します。")
        ToolTip(self.seglist, "残す区間のリストです。\n"
                              "左端の □ を押すと、その区間だけ 24p化（QTGMC＋SRestore）が ☑ オン／□ オフになります。\n"
                              "下から上に流れる文字（警告文・スクロールするクレジット）の区間はオフのまま（59.94p）にします。\n"
                              "区間名をダブルクリックすると、その区間の開始位置へ移動します。")
        ToolTip(self.preview, "今の設定で作られる avs の中身です（一覧で選んだ動画の分）。")

    # ---------- 画面づくり
    def fit_main(self):
        """本体の幅は窓に合わせ、高さは中身が収まる大きさ（窓より低ければ窓いっぱい）にする"""
        try:
            w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
            need = self.main.winfo_reqheight()
            self.canvas.itemconfigure(self._win, width=max(w, 1), height=max(h, need))
            self.canvas.configure(scrollregion=(0, 0, max(w, 1), max(h, need)))
            want = need > h > 1
            if want != self.vsb_shown:
                self.vsb_shown = want
                if want:
                    self.vsb.pack(side="right", fill="y", before=self.canvas)
                else:
                    self.vsb.pack_forget()
        except Exception:
            pass

    def on_main_wheel(self, event):
        """数字欄・リスト・スライダーの上以外でホイールを回すと、画面全体を上下にスクロール"""
        try:
            cls = event.widget.winfo_class()
            if cls in ("Spinbox", "TSpinbox", "Entry", "TEntry", "TCombobox", "Text",
                       "Treeview", "Listbox", "TScale", "Scale"):
                return
            if self.main.winfo_reqheight() > self.canvas.winfo_height():
                self.canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        except Exception:
            pass

    def build_ui(self):
        root = self.root
        # 太字の見出しは、画面のふつうの文字と同じ書体で太くする
        # （書体名を空にすると、古い書体が代わりに使われて字の間隔がおかしくなるため）
        self.font_bold = tkfont.nametofont("TkDefaultFont").copy()
        self.font_bold.configure(weight="bold")
        pad = {"padx": 10, "pady": 5}
        v = self.vars

        # 一番下の実行ボタンは、画面が低くても必ず見えるよう、ウィンドウの下に固定する
        bottom = ttk.Frame(root)
        bottom.pack(side="bottom", fill="x", padx=10, pady=(2, 10))

        # その上の本体は、画面に収まらないときは縦にスクロールできるようにする
        holder = ttk.Frame(root)
        holder.pack(side="top", fill="both", expand=True)
        try:
            bg = ttk.Style().lookup("TFrame", "background") or "#f0f0f0"
        except Exception:
            bg = "#f0f0f0"
        self.canvas = tk.Canvas(holder, highlightthickness=0, borderwidth=0, background=bg)
        self.vsb = ttk.Scrollbar(holder, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.vsb_shown = False
        main = ttk.Frame(self.canvas)
        self.main = main
        self._win = self.canvas.create_window((0, 0), window=main, anchor="nw")
        self.canvas.bind("<Configure>", lambda e: self.fit_main())
        main.bind("<Configure>", lambda e: self.fit_main())
        root.bind_all("<MouseWheel>", self.on_main_wheel, add="+")

        self.left = ttk.Frame(main)
        self.left.pack(side="left", fill="both", expand=True)
        self.right = ttk.Frame(main)
        self.right.pack(side="right", fill="y", padx=(0, 10), pady=5)
        left = self.left

        # --- 1. ファイル一覧
        f1 = ttk.LabelFrame(left, text="① 動画ファイル（ここにドラッグ＆ドロップ。複数OK）")
        f1.pack(fill="both", expand=False, **pad)

        inner = ttk.Frame(f1)
        inner.pack(fill="both", expand=True, padx=6, pady=6)

        cols = ("name", "mode", "levels", "tweak", "ccd")
        self.listbox = ttk.Treeview(inner, columns=cols, show="headings", height=6,
                                    selectmode="extended")
        for c, title, w, st in (("name", "ファイル名", 300, True), ("mode", "処理", 120, False),
                                ("levels", "明るさ", 90, False), ("tweak", "色相・彩度", 120, False),
                                ("ccd", "CCD", 50, False)):
            self.listbox.heading(c, text=title, anchor="w")
            self.listbox.column(c, width=w, minwidth=40, stretch=st, anchor="w")
        sb = ttk.Scrollbar(inner, orient="vertical", command=self.listbox.yview)
        self.listbox.configure(yscrollcommand=sb.set)
        self.listbox.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")

        btns = ttk.Frame(inner)
        btns.grid(row=0, column=2, sticky="n", padx=(8, 0))
        ttk.Button(btns, text="ファイルを追加…", command=self.add_dialog).pack(fill="x", pady=2)
        ttk.Button(btns, text="選んだものを削除", command=self.remove_selected).pack(fill="x", pady=2)
        ttk.Button(btns, text="全部クリア", command=self.clear_all).pack(fill="x", pady=2)
        inner.columnconfigure(0, weight=1)

        self.hint = ttk.Label(f1, foreground="#666")
        self.hint.pack(anchor="w", padx=8, pady=(0, 6))
        self.update_hint()

        self.listbox.bind("<<TreeviewSelect>>", lambda e: self.on_select())
        self.listbox.bind("<Delete>", lambda e: self.remove_selected())
        self.listbox.bind("<Control-a>", lambda e: (self.listbox.selection_set(self.files), "break")[1])

        if HAS_DND:
            for w in (self.root, self.listbox):
                w.drop_target_register(DND_FILES)
                w.dnd_bind("<<Drop>>", self.on_drop)

        # --- 2. 設定
        f2 = ttk.LabelFrame(left, text="② 設定（チェックを外すとその処理はしません）")
        f2.pack(fill="x", **pad)
        f2.columnconfigure(1, weight=1)
        self.f2 = f2

        # どの動画の設定を編集しているか
        hrow = ttk.Frame(f2)
        hrow.grid(row=0, column=0, columnspan=3, sticky="ew", padx=8, pady=(4, 0))
        self.edit_label = ttk.Label(hrow, text="", font=self.font_bold)
        self.edit_label.pack(side="left")
        ttk.Button(hrow, text="補正アシスタント…", command=self.open_assistant).pack(side="right")
        self.mixed_label = ttk.Label(f2, text="", foreground="#b00020")
        self.mixed_label.grid(row=1, column=0, columnspan=3, sticky="w", padx=8)

        # コピー・貼り付け・全部に適用
        crow = ttk.Frame(f2)
        crow.grid(row=2, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 2))
        ttk.Button(crow, text="設定をコピー", command=self.copy_settings).pack(side="left")
        self.b_paste = ttk.Button(crow, text="選んだ動画に貼り付け", command=self.paste_settings,
                                  state="disabled")
        self.b_paste.pack(side="left", padx=4)
        ttk.Button(crow, text="全部の動画に適用", command=self.apply_to_all).pack(side="left", padx=(4, 0))

        # プリセット
        prow = ttk.Frame(f2)
        prow.grid(row=3, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 6))
        ttk.Label(prow, text="プリセット").pack(side="left")
        self.preset_var = tk.StringVar()
        self.cb_preset = ttk.Combobox(prow, textvariable=self.preset_var, state="readonly", width=28)
        self.cb_preset.pack(side="left", padx=6)
        ttk.Button(prow, text="選んだ動画に適用", command=self.apply_preset).pack(side="left")
        ttk.Button(prow, text="今の設定を保存…", command=self.save_preset).pack(side="left", padx=4)
        ttk.Button(prow, text="プリセットを削除", command=self.delete_preset).pack(side="left")
        self.refresh_presets()

        ttk.Separator(f2).grid(row=4, column=0, columnspan=3, sticky="ew", padx=8, pady=(0, 4))

        r = 5
        ttk.Label(f2, text="読み込み方法").grid(row=r, column=0, sticky="w", padx=8, pady=4)
        ttk.Combobox(f2, textvariable=v["source"], values=SOURCE_CHOICES,
                     state="readonly", width=26).grid(row=r, column=1, sticky="w", pady=4)
        ttk.Label(f2, text="※aviならAviSource、mp4/mkvなどはLWLibavVideoSource",
                  foreground="#666").grid(row=r, column=2, sticky="w", padx=8)

        r += 1
        ttk.Checkbutton(f2, text="インターレース解除（KFMDeint）",
                        variable=v["deint"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        ttk.Label(row, text="フィールド順").pack(side="left")
        self.cb_field = ttk.Combobox(row, textvariable=v["field"], values=["TFF", "BFF"],
                                     state="readonly", width=6)
        self.cb_field.pack(side="left", padx=6)
        ttk.Label(row, text="（VHSキャプチャは通常TFF）", foreground="#666").pack(side="left")

        r += 1
        ttk.Checkbutton(f2, text="アニメを24pにする（QTGMC＋SRestore）",
                        variable=v["anime24"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        ttk.Label(row, text="プラグインのフォルダ").pack(side="left")
        self.e_plug = ttk.Entry(row, textvariable=v["plug24"], width=22)
        self.e_plug.pack(side="left", padx=6)
        ttk.Label(row, text="※区間を登録しているときは、右の「カット編集」で区間ごとに切り替え。\n"
                            "　ここは「全体」または「新しく登録する区間」の初期値になります。",
                  foreground="#666", justify="left").pack(side="left")

        r += 1
        ttk.Checkbutton(f2, text="明るさ補正（Levels）",
                        variable=v["levels"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        self.levels_entries = []
        def lv(label, key, step=1, lo=0, hi=255, dec=0):
            ttk.Label(row, text=label).pack(side="left", padx=(6, 2))
            e = make_spin(row, v[key], step, lo, hi, dec, width=5)
            e.pack(side="left")
            self.levels_entries.append(e)
        ttk.Label(row, text="入力").pack(side="left")
        lv("黒", "in_low"); lv("白", "in_high")
        lv("　ガンマ", "gamma", 0.05, 0.1, 5.0, 2)
        ttk.Label(row, text="　出力").pack(side="left")
        lv("黒", "out_low"); lv("白", "out_high")

        r += 1
        ttk.Checkbutton(f2, text="色相・彩度の補正（Tweak）",
                        variable=v["tweak"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        ttk.Label(row, text="色相").pack(side="left")
        self.e_hue = make_spin(row, v["hue"], 1, -180, 180, 0, width=6)
        self.e_hue.pack(side="left", padx=(2, 0))
        ttk.Label(row, text="（＋赤寄り／－緑寄り）", foreground="#666").pack(side="left", padx=(2, 12))
        ttk.Label(row, text="彩度").pack(side="left")
        self.e_sat = make_spin(row, v["sat"], 0.05, 0, 5, 2, width=6)
        self.e_sat.pack(side="left", padx=(2, 0))
        ttk.Label(row, text="（1.0＝そのまま）", foreground="#666").pack(side="left", padx=2)

        r += 1
        ttk.Checkbutton(f2, text="色ノイズ除去（CCD）",
                        variable=v["ccd"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        ttk.Label(row, text="閾値").pack(side="left")
        self.e_ccd = make_spin(row, v["ccd_th"], 1, 0, 100, 0, width=6)
        self.e_ccd.pack(side="left", padx=(2, 0))
        ttk.Label(row, text="（VirtualDubのCCDと同じもの・ツールに内蔵。大きいほど強く効く）",
                  foreground="#666").pack(side="left", padx=6)

        r += 1
        ttk.Checkbutton(f2, text="リサイズ（Spline36Resize）",
                        variable=v["resize"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)
        row = ttk.Frame(f2); row.grid(row=r, column=1, columnspan=2, sticky="w")
        self.e_w = make_spin(row, v["width"], 8, 16, 8192, 0, width=7); self.e_w.pack(side="left")
        ttk.Label(row, text=" × ").pack(side="left")
        self.e_h = make_spin(row, v["height"], 8, 16, 8192, 0, width=7); self.e_h.pack(side="left")
        ttk.Label(row, text="（横 × 縦）", foreground="#666").pack(side="left", padx=6)

        r += 1
        ttk.Checkbutton(f2, text="色空間変換（BT.601 → BT.709）",
                        variable=v["color"]).grid(row=r, column=0, sticky="w", padx=8, pady=4)

        r += 1
        ttk.Label(f2, text="※数字の欄は、クリックして ↑↓キー（Shiftで5倍）かマウスホイールで増減できます。",
                  foreground="#666").grid(row=r, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 8))

        # --- 3. 保存先
        f3 = ttk.LabelFrame(left, text="③ avsとmp4の保存先")
        f3.pack(fill="x", **pad)
        ttk.Radiobutton(f3, text="動画と同じフォルダに保存", value="same",
                        variable=v["out_mode"]).grid(row=0, column=0, sticky="w", padx=8, pady=3)
        ttk.Radiobutton(f3, text="このフォルダに保存：", value="folder",
                        variable=v["out_mode"]).grid(row=1, column=0, sticky="w", padx=8, pady=3)
        self.e_out = ttk.Entry(f3, textvariable=v["out_dir"])
        self.e_out.grid(row=1, column=1, sticky="ew", padx=4)
        self.b_out = ttk.Button(f3, text="選ぶ…", command=self.choose_outdir)
        self.b_out.grid(row=1, column=2, padx=8, pady=3)
        f3.columnconfigure(1, weight=1)

        # --- 4. エンコード設定
        f_enc = ttk.LabelFrame(left, text="④ エンコード（ffmpeg → mp4）")
        f_enc.pack(fill="x", **pad)
        row = ttk.Frame(f_enc); row.pack(fill="x", padx=8, pady=(6, 2))
        ttk.Label(row, text="画質 CQ").pack(side="left")
        self.e_cq = make_spin(row, v["cq"], 1, 0, 51, 0, width=5)
        self.e_cq.pack(side="left", padx=(4, 0))
        ttk.Label(row, text="（小さいほど高画質・ファイルが大きい）", foreground="#666").pack(side="left", padx=6)
        ttk.Label(f_enc, text="HEVC（NVENC）p7 / Main10 / BT.709 / 音声はFLAC（圧縮レベル8）。avsを直接ffmpegに渡します。",
                  foreground="#666").pack(anchor="w", padx=8, pady=(0, 2))
        for label, key in (("通常用ffmpeg（Neo）", "ffmpeg"), ("24p用ffmpeg（3.7.5）", "ffmpeg24")):
            r_ = ttk.Frame(f_enc); r_.pack(fill="x", padx=8, pady=1)
            ttk.Label(r_, text=label, width=20).pack(side="left")
            ttk.Entry(r_, textvariable=v[key]).pack(side="left", fill="x", expand=True, padx=4)
            ttk.Button(r_, text="選ぶ…", command=lambda k=key: self.choose_ffmpeg(k)).pack(side="left")
        ttk.Label(f_enc, text="24p用は、AviSynth+ 3.7.5 の avisynth.dll と同じフォルダにある ffmpeg.exe を選びます。\n"
                              "24p化する部分を含む動画は、通常の部分もQTGMCで処理して、1本のavsでエンコードします。",
                  foreground="#666", justify="left").pack(anchor="w", padx=8, pady=(2, 6))

        # --- 5. avsの中身
        f4 = ttk.LabelFrame(left, text="作られるavsの中身（一覧で選んだファイルの分）")
        f4.pack(fill="both", expand=True, **pad)
        self.preview = tk.Text(f4, height=6, wrap="none", font=("Consolas", 10),
                               background="#f6f6f6", state="disabled")
        self.preview.pack(fill="both", expand=True, padx=6, pady=6)

        self.build_bottom(bottom)
        self.build_image_preview()
        self.build_marks_panel()
        self.build_cut_panel()

    def build_bottom(self, bottom):
        """進捗バーと実行ボタン（画面が狭くても隠れないよう、一番下に固定）"""
        self.pbar = ttk.Progressbar(bottom, mode="determinate", maximum=100)
        self.pbar.pack(fill="x")
        self.status = ttk.Label(bottom, text="", wraplength=760, justify="left")
        self.status.pack(anchor="w", pady=2)
        brow = ttk.Frame(bottom)
        brow.pack(fill="x", pady=(2, 0))
        self.b_cancel = ttk.Button(brow, text="エンコードを中止", command=self.cancel_encode,
                                   state="disabled")
        self.b_cancel.pack(side="left")
        self.b_update = ttk.Button(brow, text="更新を確認", command=self.check_update)
        self.b_update.pack(side="left", padx=(8, 4))
        ttk.Button(brow, text="使い方", command=self.open_help).pack(side="left", padx=(0, 8))
        ttk.Label(brow, text=f"v{APP_VERSION}", foreground="#888").pack(side="left")
        self.b_enc = ttk.Button(brow, text="avsを作成してエンコード",
                                command=lambda: self.make_all(True))
        self.b_enc.pack(side="right", ipadx=10, ipady=4)
        self.b_avs = ttk.Button(brow, text="avsだけ作成", command=lambda: self.make_all(False))
        self.b_avs.pack(side="right", padx=8, ipadx=6, ipady=4)

    def build_image_preview(self):
        f5 = ttk.LabelFrame(self.right, text="画像プレビュー（補正のかかり具合）")
        f5.pack(fill="x")

        holder = tk.Frame(f5, width=PREVIEW_MAX_W, height=PREVIEW_MAX_H, bg="#222")
        holder.pack_propagate(False)
        holder.pack(padx=8, pady=(8, 4))
        self.img_label = tk.Label(holder, bg="#222", fg="#ccc", wraplength=PREVIEW_MAX_W - 40,
                                  justify="center", cursor="hand2", takefocus=True)
        self.img_label.pack(expand=True)
        self.img_label.bind("<ButtonPress-1>", self._on_img_press)
        self.img_label.bind("<ButtonRelease-1>", lambda e: self.show_after())
        self.img_label.bind("<Leave>", lambda e: self.show_after())
        self.img_label.bind("<Left>", lambda e: self.step(-1))
        self.img_label.bind("<Right>", lambda e: self.step(+1))
        self.img_label.bind("<Shift-Left>", lambda e: self.step(-1, True))
        self.img_label.bind("<Shift-Right>", lambda e: self.step(+1, True))

        self.state_label = ttk.Label(f5, text="", font=self.font_bold)
        self.state_label.pack()
        ttk.Label(f5, text="画像を押している間は「補正前」を表示／押したあと ←→キーで1コマ、Shift+←→で1秒移動",
                  foreground="#666", wraplength=PREVIEW_MAX_W).pack(pady=(0, 6))

        trow = ttk.Frame(f5)
        trow.pack(fill="x", padx=8, pady=2)
        self.scale = ttk.Scale(trow, from_=0, to=1, variable=self.pos,
                               orient="horizontal", command=self.on_slide)
        self.scale.pack(side="left", fill="x", expand=True)
        self.scale.bind("<ButtonRelease-1>", lambda e: self.load_frame())
        self.scale.bind("<KeyRelease>", lambda e: self.load_frame())

        self.time_label = ttk.Label(f5, text="", font=("Consolas", 10))
        self.time_label.pack(pady=(2, 0))

        jrow = ttk.Frame(f5)
        jrow.pack(pady=(2, 0))
        ttk.Label(jrow, text="移動先").pack(side="left")
        self.jump_var = tk.StringVar()
        self.e_jump = ttk.Entry(jrow, textvariable=self.jump_var, width=12)
        self.e_jump.pack(side="left", padx=4)
        self.e_jump.bind("<Return>", lambda e: self.jump_to())
        self.e_jump.bind("<KP_Enter>", lambda e: self.jump_to())
        ttk.Button(jrow, text="移動", width=6, command=self.jump_to).pack(side="left")
        ttk.Label(jrow, text="例：18743 / 10:25.4", foreground="#666").pack(side="left", padx=(6, 0))

        srow = ttk.Frame(f5)
        srow.pack(pady=4)
        ttk.Button(srow, text="◀◀ 1秒", width=8, command=lambda: self.step(-1, True)).pack(side="left", padx=2)
        ttk.Button(srow, text="◀ 1コマ", width=8, command=lambda: self.step(-1)).pack(side="left", padx=2)
        ttk.Button(srow, text="1コマ ▶", width=8, command=lambda: self.step(+1)).pack(side="left", padx=2)
        ttk.Button(srow, text="1秒 ▶▶", width=8, command=lambda: self.step(+1, True)).pack(side="left", padx=2)

        self.note = ttk.Label(f5, text="", foreground="#b00020", wraplength=PREVIEW_MAX_W)
        self.note.pack(fill="x", padx=8, pady=2)

        brow = ttk.Frame(f5)
        brow.pack(fill="x", padx=8, pady=(2, 8))
        ttk.Button(brow, text="この場面を取り直す", command=lambda: self.load_frame(force=True)
                   ).pack(side="left")
        ttk.Button(brow, text="ffmpegの場所を指定…", command=self.choose_ffmpeg
                   ).pack(side="right")

        crow = ttk.Frame(f5)
        crow.pack(fill="x", padx=8, pady=(0, 8))
        ttk.Label(crow, text="比較画像（左＝補正前／右＝補正後）:").pack(side="left")
        self.b_cmp_copy = ttk.Button(crow, text="コピー", command=self.copy_compare)
        self.b_cmp_copy.pack(side="left", padx=4)
        self.b_cmp_save = ttk.Button(crow, text="保存…", command=self.save_compare)
        self.b_cmp_save.pack(side="left")
        if not HAS_PREVIEW:
            self.b_cmp_copy.config(state="disabled")
            self.b_cmp_save.config(state="disabled")
        elif os.name != "nt":
            self.b_cmp_copy.config(state="disabled")

        if not HAS_PREVIEW:
            self.set_message("プレビュー・カット編集を使うには、コマンドプロンプトで\n"
                             "pip install pillow numpy\nを実行して、再起動してください")
        else:
            self.set_message("動画を追加すると、ここに1コマ表示されます")

    def build_marks_panel(self):
        f = ttk.LabelFrame(self.right, text="チェックする場面（同じ場面をすぐ見直す用）")
        f.pack(fill="x", pady=(8, 0))
        row = ttk.Frame(f); row.pack(fill="x", padx=8, pady=(6, 2))
        self.b_mark = ttk.Button(row, text="この場面を覚える", command=self.add_mark)
        self.b_mark.pack(side="left")
        ttk.Button(row, text="選んだ場面を忘れる", command=self.delete_mark).pack(side="left", padx=4)
        lrow = ttk.Frame(f); lrow.pack(fill="x", padx=8, pady=2)
        self.marklist = tk.Listbox(lrow, height=4, exportselection=False, activestyle="none")
        sb = ttk.Scrollbar(lrow, orient="vertical", command=self.marklist.yview)
        self.marklist.configure(yscrollcommand=sb.set)
        self.marklist.pack(side="left", fill="x", expand=True)
        sb.pack(side="left", fill="y")
        self.marklist.bind("<<ListboxSelect>>", lambda e: self.goto_mark())
        self.marklist.bind("<Delete>", lambda e: self.delete_mark())
        crow = ttk.Frame(f); crow.pack(fill="x", padx=8, pady=(2, 8))
        ttk.Label(crow, text="覚えた場面の比較画像：").pack(side="left")
        self.b_mcopy = ttk.Button(crow, text="まとめてコピー", command=lambda: self.batch_compare("copy"))
        self.b_mcopy.pack(side="left", padx=4)
        self.b_msave = ttk.Button(crow, text="まとめて保存…", command=lambda: self.batch_compare("save"))
        self.b_msave.pack(side="left")
        if not HAS_PREVIEW:
            for b in (self.b_mark, self.b_mcopy, self.b_msave):
                b.config(state="disabled")
        elif os.name != "nt":
            self.b_mcopy.config(state="disabled")

    def build_cut_panel(self):
        f = ttk.LabelFrame(self.right, text="カット編集（残す区間を登録。登録しなければ全体を使います）")
        f.pack(fill="x", pady=(8, 0))

        self.pend_label = ttk.Label(f, text="", font=("Consolas", 10))
        self.pend_label.pack(anchor="w", padx=8, pady=(6, 2))

        row = ttk.Frame(f); row.pack(fill="x", padx=8, pady=2)
        self.b_s = ttk.Button(row, text="ここを開始点に", command=self.set_start)
        self.b_s.pack(side="left", padx=(0, 4))
        self.b_e = ttk.Button(row, text="ここを終了点に", command=self.set_end)
        self.b_e.pack(side="left", padx=4)
        self.b_add = ttk.Button(row, text="この区間を残す ＋", command=self.add_segment)
        self.b_add.pack(side="right")

        # 削除ボタンは、画面が低くても隠れないよう、リストの上に置く
        row2 = ttk.Frame(f); row2.pack(fill="x", padx=8, pady=(2, 0))
        ttk.Button(row2, text="選んだ区間を削除", command=self.delete_segment).pack(side="left")
        ttk.Button(row2, text="全部削除（カットなし）", command=self.clear_segments).pack(side="left", padx=6)
        self.cut_total = ttk.Label(row2, text="", foreground="#333")
        self.cut_total.pack(side="right")

        lrow = ttk.Frame(f); lrow.pack(fill="x", padx=8, pady=4)
        self.seglist = ttk.Treeview(lrow, columns=("seg",), height=4, selectmode="extended")
        self.seglist.heading("#0", text="24p化")
        self.seglist.heading("seg", text="残す区間", anchor="w")
        self.seglist.column("#0", width=64, minwidth=64, stretch=False, anchor="center")
        self.seglist.column("seg", width=380, anchor="w")
        sb = ttk.Scrollbar(lrow, orient="vertical", command=self.seglist.yview)
        self.seglist.configure(yscrollcommand=sb.set)
        self.seglist.pack(side="left", fill="x", expand=True)
        sb.pack(side="left", fill="y")
        self.seglist.bind("<Button-1>", self.on_seg_click, add="+")
        self.seglist.bind("<Double-Button-1>", self.on_seg_double)
        self.seglist.bind("<Delete>", lambda e: self.delete_segment())
        self.seglist.bind("<BackSpace>", lambda e: self.delete_segment())
        self.seglist.bind("<Button-3>", self.on_seg_rightclick)

        ttk.Label(f, text="開始点だけ決めて追加＝そこから最後まで／終了点だけ＝先頭からそこまで。\n"
                          "左端の □ を押すと、その区間だけ 24p化（アニメ用）が ☑ オン／□ オフ になります。\n"
                          "（24p区間を含むときは、通常の区間もQTGMCで処理し、59.94pのまま1本につなぎます）\n"
                          "リストの区間名をダブルクリックすると、その区間の開始位置に移動します。",
                  foreground="#666", justify="left").pack(anchor="w", padx=8, pady=(2, 8))

        if not HAS_PREVIEW:
            for b in (self.b_s, self.b_e, self.b_add):
                b.config(state="disabled")
        self.update_pos_labels()

    # ---------- ファイル操作
    def update_hint(self):
        if HAS_DND:
            self.hint.config(text=f"{len(self.files)} 個のファイル　／　フォルダをドロップすると中の動画をまとめて追加します")
        else:
            self.hint.config(text="※ドラッグ＆ドロップするには、コマンドプロンプトで  pip install tkinterdnd2  を実行して再起動してください")

    def add_files(self, paths):
        added = 0
        self._restored = 0
        first_new = len(self.files)          # 追加したうち最初のファイルの位置
        base = self.current_file_settings()  # 新しい動画は、今選んでいる動画の設定を引き継ぐ
        for p in paths:
            p = os.path.normpath(p)
            if os.path.isdir(p):
                for name in sorted(os.listdir(p)):
                    fp = os.path.join(p, name)
                    if os.path.isfile(fp) and os.path.splitext(fp)[1].lower() in VIDEO_EXTS:
                        added += self._add_one(fp, base)
            elif os.path.isfile(p):
                added += self._add_one(p, base)
        self.update_hint()
        if added == 0 and paths:
            self.status.config(text="追加できるファイルがありませんでした（すでに追加済み？）")
        else:
            msg = f"{added} 個追加しました"
            if self._restored:
                msg += f"（うち {self._restored} 個は、前回の設定を復元しました）"
            self.status.config(text=msg)
        if added:                            # 追加したファイルを選んで、プレビューに出す
            self.select_index(first_new)
        elif self.files and not self.listbox.selection():
            self.select_index(0)
        self.schedule_save()

    def select_index(self, i):
        """一覧の i 番目を選んだ状態にして、見える位置までスクロールする"""
        if not self.files:
            self.on_select()
            return
        i = min(max(i, 0), len(self.files) - 1)
        iid = self.files[i]
        self.listbox.selection_set(iid)
        self.listbox.focus(iid)
        self.listbox.see(iid)
        self.on_select()

    def _add_one(self, path, base):
        if path in self.files:
            return 0
        self.forget_file(path)      # 以前同じ名前のファイルを読んでいても、調べ直す
        settings, cuts, marks, mflags, skins = self.recall(path)
        if settings is not None:
            self._restored += 1
            s = dict(base)
            s.update({k: v for k, v in settings.items() if k in FILE_KEYS})
            self.fsets[path] = s
            self.cuts[path] = cuts
            self.marks[path] = marks
            self.mflags[path] = mflags
            self.skins[path] = skins
        else:
            self.fsets[path] = dict(base)
        self.files.append(path)
        self.listbox.insert("", "end", iid=path, values=(os.path.basename(path),) + self.row_of(path))
        return 1

    # ---------- 動画ごとの設定
    def current_file_settings(self):
        """今の設定欄の値（動画ごとに持つ分）"""
        return {k: self.vars[k].get() for k in FILE_KEYS}

    def sel_paths(self):
        """一覧で選んでいる動画（一覧の順）"""
        sel = set(self.listbox.selection())
        return [p for p in self.files if p in sel]

    def row_of(self, path):
        return settings_row(self.fsets.get(path, {}), self.cuts.get(path))

    def update_row(self, path):
        if path in self.files and self.listbox.exists(path):
            self.listbox.item(path, values=(os.path.basename(path),) + self.row_of(path))

    def on_select(self):
        """一覧で選んだ動画の設定を、設定欄に出す"""
        sel = self.sel_paths()
        if sel:
            s = self.fsets.get(sel[0], {})
            self._loading = True
            try:
                for k in FILE_KEYS:
                    if k in s and self.vars[k].get() != s[k]:
                        self.vars[k].set(s[k])
            finally:
                self._loading = False
        self.update_edit_label()
        self.on_change()

    def update_edit_label(self):
        sel = self.sel_paths()
        if not self.files:
            self.edit_label.config(text="② の設定は、これから追加する動画に使われます")
            self.mixed_label.config(text="")
        elif len(sel) <= 1:
            p = sel[0] if sel else self.files[0]
            self.edit_label.config(text=f"編集中：{os.path.basename(p)}")
            self.mixed_label.config(text="")
        else:
            self.edit_label.config(text=f"編集中：{len(sel)} 本を選択中（変えた項目だけ、選んだ全部に反映されます）")
            diff = [name for name, keys in KEY_GROUPS
                    if any(len({str(self.fsets.get(p, {}).get(k)) for p in sel}) > 1 for k in keys)]
            self.mixed_label.config(
                text=("※選んだ動画で値が違う項目：" + "、".join(diff) +
                      "（表示は1本目の値。触らなければ、それぞれの値のまま）") if diff else "")
        try:
            self.b_paste.config(state="normal" if (self.clip and sel) else "disabled")
        except AttributeError:
            pass

    def on_var(self, key):
        """設定欄が変わったとき：動画ごとの項目なら、選んでいる動画（全部）に書き込む"""
        if self._loading:
            return
        if key in FILE_KEYS and self.files:
            targets = self.sel_paths() or [self.files[0]]
            val = self.vars[key].get()
            for p in targets:
                self.fsets.setdefault(p, {})[key] = val
                self.update_row(p)
            if len(targets) > 1:
                self.update_edit_label()
        self.schedule_save()          # ffmpegの場所などの共通の設定も、変えたらすぐ覚える
        self.on_change()

    def copy_settings(self):
        self.clip = self.current_file_settings()
        self.status.config(text="今の設定をコピーしました。ほかの動画を選んで「選んだ動画に貼り付け」を押してください。")
        self.update_edit_label()

    def _apply_settings(self, targets, s):
        for p in targets:
            self.fsets.setdefault(p, {}).update({k: v for k, v in s.items() if k in FILE_KEYS})
            self.update_row(p)
        self.on_select()            # 設定欄を選んでいる動画の値に戻す
        self.schedule_save()

    def paste_settings(self):
        sel = self.sel_paths()
        if not (self.clip and sel):
            return
        self._apply_settings(sel, self.clip)
        self.status.config(text=f"{len(sel)} 本に設定を貼り付けました（カット区間はそのままです）")

    def apply_to_all(self):
        if not self.files:
            return
        if not messagebox.askyesno(APP_TITLE, f"今の設定を、一覧の全部の動画（{len(self.files)} 本）に適用しますか？\n"
                                              "（カット区間はそのままです）"):
            return
        self._apply_settings(self.files, self.current_file_settings())
        self.status.config(text=f"{len(self.files)} 本すべてに今の設定を適用しました")

    # ---------- プリセット
    def refresh_presets(self):
        names = sorted(self.record.get("presets", {}))
        self.cb_preset.config(values=names)
        if self.preset_var.get() not in names:
            self.preset_var.set(names[0] if names else "")

    def apply_preset(self):
        name = self.preset_var.get()
        s = self.record.get("presets", {}).get(name)
        if not s:
            messagebox.showinfo(APP_TITLE, "プリセットがありません。先に「今の設定を保存…」で作ってください。")
            return
        targets = self.sel_paths()
        if not targets:
            for k, v in s.items():          # 動画がないときは、設定欄（これから追加する動画用）に入れる
                if k in FILE_KEYS:
                    self.vars[k].set(v)
            return
        self._apply_settings(targets, s)
        self.status.config(text=f"プリセット「{name}」を {len(targets)} 本に適用しました")

    def save_preset(self):
        from tkinter import simpledialog
        name = simpledialog.askstring(APP_TITLE, "プリセットの名前（例：日本一の男の魂 2巻）",
                                      initialvalue=self.preset_var.get(), parent=self.root)
        if not name or not name.strip():
            return
        name = name.strip()
        presets = self.record.setdefault("presets", {})
        if name in presets and not messagebox.askyesno(APP_TITLE, f"「{name}」はすでにあります。上書きしますか？"):
            return
        presets[name] = self.current_file_settings()
        self.refresh_presets()
        self.preset_var.set(name)
        self.save_record()
        self.status.config(text=f"プリセット「{name}」を保存しました")

    def delete_preset(self):
        name = self.preset_var.get()
        presets = self.record.get("presets", {})
        if name not in presets:
            return
        if not messagebox.askyesno(APP_TITLE, f"プリセット「{name}」を削除しますか？"):
            return
        del presets[name]
        self.refresh_presets()
        self.save_record()

    # ---------- 設定の記録（動画ごとの設定とプリセットを1つのjsonに）
    def load_record(self):
        try:
            with open(RECORD_FILE, encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                raise ValueError
        except (OSError, ValueError):
            data = {}
        data.setdefault("files", {})
        data.setdefault("presets", {})
        return data

    def recall(self, path):
        """記録から、この動画の設定とカット区間を探す。(設定 or None, 区間 or None)
        同じ場所の同じファイル → 同じ名前のファイル の順に探す。
        カット区間は、ファイルの大きさが同じとき（同じ中身のとき）だけ戻す"""
        files = self.record.get("files", {})
        ent = files.get(os.path.basename(path).lower())
        if not ent:
            return None, None, [], {}, []
        settings = ent.get("settings")
        sig = self._file_sig(path)
        if sig and ent.get("size") == sig[0]:
            try:
                cuts = normalize_cuts(ent.get("cuts") or [])
            except (ValueError, TypeError):
                cuts = []
            try:
                marks = sorted({int(x) for x in ent.get("marks") or []})
            except (ValueError, TypeError):
                marks = []
            try:
                mflags = {int(k): {"b": bool(v.get("b")), "w": bool(v.get("w"))}
                          for k, v in (ent.get("mflags") or {}).items()}
            except (ValueError, TypeError, AttributeError):
                mflags = {}
            try:
                skins = [[int(a), float(b), float(c)] for a, b, c in ent.get("skins") or []]
            except (ValueError, TypeError):
                skins = []
        else:      # 同じ名前でも中身が違う（取り込み直した）ので、前の区間・場面・見本は使わない
            cuts, marks, mflags, skins = [], [], {}, []
        return (settings if isinstance(settings, dict) else None), cuts, marks, mflags, skins

    def remember_files(self):
        """一覧にある動画の設定を、記録に書き込む（ファイル名ごとに1件）"""
        files = self.record.setdefault("files", {})
        now = time.time()
        for p in self.files:
            sig = self._file_sig(p)
            files[os.path.basename(p).lower()] = {
                "name": os.path.basename(p),
                "path": p,
                "size": sig[0] if sig else None,
                "updated": now,
                "settings": dict(self.fsets.get(p, {})),
                "cuts": [list(x) for x in self.cuts.get(p, [])],
                "marks": list(self.marks.get(p, [])),
                "mflags": {str(k): v for k, v in self.mflags.get(p, {}).items() if v.get("b") or v.get("w")},
                "skins": [list(x) for x in self.skins.get(p, [])],
            }
        if len(files) > RECORD_MAX_FILES:      # 古いものから忘れる
            for k in sorted(files, key=lambda k: files[k].get("updated", 0))[:len(files) - RECORD_MAX_FILES]:
                del files[k]

    def save_record(self):
        tmp = RECORD_FILE + ".tmp"
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.record, f, ensure_ascii=False, indent=1)
            os.replace(tmp, RECORD_FILE)      # 書いている途中で落ちても、元の記録が壊れないように
        except OSError:
            pass

    def schedule_save(self):
        """設定を変えるたびに書くと重いので、少し待ってからまとめて保存する"""
        if self._save_job:
            self.root.after_cancel(self._save_job)
        self._save_job = self.root.after(1000, self.save_settings)

    def on_drop(self, event):
        self.add_files(self.root.tk.splitlist(event.data))

    def add_dialog(self):
        paths = filedialog.askopenfilenames(
            title="動画ファイルを選択",
            filetypes=[("動画ファイル", " ".join("*" + e for e in sorted(VIDEO_EXTS))),
                       ("すべてのファイル", "*.*")])
        if paths:
            self.add_files(paths)

    def remove_selected(self):
        sel = self.sel_paths()
        if not sel:
            return
        self.remember_files()                # 消す前に、設定を記録しておく（また追加すれば戻る）
        first = self.files.index(sel[0])
        for p in sel:
            self.listbox.delete(p)
            self.forget_file(p)
            self.files.remove(p)
            self.fsets.pop(p, None)
            self.marks.pop(p, None)
            self.mflags.pop(p, None)
            self.skins.pop(p, None)
        self.select_index(first)             # 消したところの次（なければ前）のファイルを選び直す
        self.update_hint()
        self.save_settings()

    def clear_all(self):
        self.remember_files()
        for p in self.files:
            self.listbox.delete(p)
            self.forget_file(p)
            self.fsets.pop(p, None)
            self.marks.pop(p, None)
            self.mflags.pop(p, None)
            self.skins.pop(p, None)
        self.files.clear()
        self.update_hint()
        self.on_select()
        self.save_settings()

    def choose_outdir(self):
        d = filedialog.askdirectory(title="avsとmp4の保存先フォルダを選択")
        if d:
            self.vars["out_dir"].set(os.path.normpath(d))

    def tool(self, name):
        """プレビュー用に、ffmpeg / ffprobe を探す（通常用 → 24p用 → PATH の順）"""
        return (find_tool(name, self.vars["ffmpeg"].get())
                or find_tool(name, self.vars["ffmpeg24"].get()))

    def choose_ffmpeg(self, key="ffmpeg"):
        p = filedialog.askopenfilename(
            title="24p用の ffmpeg.exe を選択" if key == "ffmpeg24" else "ffmpeg.exe を選択",
            filetypes=[("ffmpeg", "ffmpeg.exe ffmpeg"), ("すべてのファイル", "*.*")])
        if p:
            self.vars[key].set(os.path.normpath(p))
            self.cur_path = None          # 動画の情報を調べ直す
            self.load_frame(force=True)

    # ---------- 設定
    def options(self):
        return {k: v.get() for k, v in self.vars.items()}

    def opts_for(self, path):
        """その動画で使う設定（共通の設定＋その動画の設定）"""
        o = self.options()
        o.update(self.fsets.get(path, {}))
        return o

    def on_change(self):
        self.update_states()
        self.refresh_preview()
        self.notify_assistant()

    def notify_assistant(self):
        if self.assistant is not None:
            try:
                self.assistant.on_app_change()
            except tk.TclError:
                self.assistant = None

    def open_assistant(self):
        if not HAS_PREVIEW:
            messagebox.showinfo(APP_TITLE, "補正アシスタントを使うには pillow と numpy が必要です。")
            return
        if not self.files:
            messagebox.showinfo(APP_TITLE, "先に動画を追加して、一覧で選んでください。")
            return
        if self.assistant is not None:
            try:
                self.assistant.win.deiconify()
                self.assistant.win.lift()
                self.assistant.win.focus_force()
                return
            except tk.TclError:
                self.assistant = None
        if not self.cur_path:
            self.load_frame(force=True)
        self.assistant = AssistWindow(self)

    def update_states(self):
        v = self.vars
        def st(on): return "normal" if on else "disabled"
        self.cb_field.config(state="readonly" if (v["deint"].get() or v["anime24"].get()
                                                  or self.any_cut_24()) else "disabled")
        self.e_plug.config(state="normal" if (v["anime24"].get() or self.any_cut_24()) else "disabled")
        for e in self.levels_entries:
            e.config(state=st(v["levels"].get()))
        self.e_hue.config(state=st(v["tweak"].get()))
        self.e_sat.config(state=st(v["tweak"].get()))
        self.e_ccd.config(state=st(v["ccd"].get()))
        self.e_w.config(state=st(v["resize"].get()))
        self.e_h.config(state=st(v["resize"].get()))
        folder = v["out_mode"].get() == "folder"
        self.e_out.config(state=st(folder))
        self.b_out.config(state=st(folder))

    def selected_path(self):
        sel = self.sel_paths()
        if sel:
            return sel[0]
        return self.files[0] if self.files else None

    def refresh_preview(self):
        """avsの中身を更新し、画像プレビューの更新を予約する"""
        path = self.selected_path() or r"C:\動画\sample.avi"
        info = self.finfo.get(path)
        try:
            parts = build_part_scripts(path, self.options(), self.cuts.get(path),
                                       info["nframes"] if info else 0)
            text = parts[0][2]
        except ValueError as e:
            text = f"（設定にまちがいがあります）\n{e}"
        self.preview.config(state="normal")
        self.preview.delete("1.0", "end")
        self.preview.insert("1.0", text)
        self.preview.config(state="disabled")
        self.schedule_image()

    # ---------- 画像プレビュー・位置の移動
    def schedule_image(self):
        if not HAS_PREVIEW:
            return
        if self.job:
            self.root.after_cancel(self.job)
        self.job = self.root.after(150, self.load_frame)

    def set_message(self, text):
        self.img_label.config(image="", text=text)
        self.img_label.image = None
        self.state_label.config(text="")

    def _on_img_press(self, event):
        self.img_label.focus_set()     # ←→キーで動かせるようにする
        self.show_before()

    def cur_frame(self):
        return int(round(self.pos.get()))

    def cur_info(self):
        return self.finfo.get(self.cur_path) if self.cur_path else None

    @staticmethod
    def _file_sig(path):
        """ファイルの大きさと更新日時（同じ名前で上書きされたかを見分ける用）"""
        try:
            st = os.stat(path)
            return (st.st_size, st.st_mtime_ns)
        except OSError:
            return None

    def info_for(self, path):
        """動画のフレームレート・フレーム数を調べる（調べた結果は覚えておく）。
        同じ名前でも、中身が変わっていれば（大きさ・更新日時が違えば）調べ直す"""
        sig = self._file_sig(path)
        old = self.finfo.get(path)
        if old is None or old.get("sig") != sig:
            info = probe_video(self.tool("ffprobe"), path)
            if info:
                info["sig"] = sig
                self.finfo[path] = info
            else:
                self.finfo.pop(path, None)
            return info
        return old

    def forget_file(self, path):
        """一覧から消した・入れ直したファイルの、覚えていた長さや表示中の情報を捨てる"""
        self.finfo.pop(path, None)
        if path == self.cur_path:
            self.cur_path = None
            self.raw = None
            self.frame_key = None

    def update_pos_labels(self):
        info = self.cur_info()
        if info:
            n, last = self.cur_frame(), info["nframes"] - 1
            self.time_label.config(
                text=f"{fmt_tc(n, info['fps'])}  （フレーム {n}）  /  全体 {fmt_tc(last, info['fps'])}")
            s, e = self.pend["s"], self.pend["e"]
            self.pend_label.config(
                text="開始点: " + (f"{fmt_tc(s, info['fps'])} (#{s})" if s is not None else "先頭") +
                     "   終了点: " + (f"{fmt_tc(e, info['fps'])} (#{e})" if e is not None else "最後"))
        else:
            self.time_label.config(text="")
            self.pend_label.config(text="（動画を選ぶと、ここに開始点・終了点が出ます）")

    def on_slide(self, _=None):
        self.update_pos_labels()

    def step(self, direction, big=False):
        info = self.cur_info()
        if not info:
            return "break"
        d = (max(1, int(round(info["fps"]))) if big else 1) * direction
        n = min(max(self.cur_frame() + d, 0), info["nframes"] - 1)
        self.pos.set(n)
        self.update_pos_labels()
        self.schedule_image()
        return "break"

    def load_frame(self, force=False):
        self.job = None
        if not HAS_PREVIEW:
            return
        path = self.selected_path()
        if not path:
            self.raw = None
            self.cur_path = None
            self.set_message("動画を追加すると、ここに1コマ表示されます")
            self.update_pos_labels()
            self.refresh_cut_list()
            return
        ffmpeg = self.tool("ffmpeg")
        if not ffmpeg:
            self.raw = None
            self.set_message("ffmpegが見つかりません。\n右下の「ffmpegの場所を指定…」から\nffmpeg.exe を選んでください")
            return

        # 別のファイルを選んだ（または「取り直す」で、まだ長さを調べられていない）→ 長さを調べて、初期の場面を決める
        cached = self.finfo.get(path)
        changed = cached is not None and cached.get("sig") != self._file_sig(path)   # 同じ名前で上書きされた
        if path != self.cur_path or changed or (force and cached is None):
            self.cur_path = path
            self.pend = {"s": None, "e": None}
            info = self.info_for(path)
            if info:
                self.scale.config(to=max(info["nframes"] - 1, 1))
                self.pos.set(min(int(info["nframes"] * 0.1), int(120 * info["fps"])))
            else:
                self.scale.config(to=1)
                self.pos.set(0)
            self.update_pos_labels()
            self.refresh_cut_list()

        info = self.cur_info()
        o = self.options()
        n = self.cur_frame()
        key = (path, n, o["deint"], o["field"], ffmpeg)
        if force or key != self.frame_key or self.raw is None:
            t = max(0.0, (n - 0.3) / info["fps"]) if info else 0.0   # そのコマが確実に出る位置
            self.root.config(cursor="watch")
            self.root.update_idletasks()
            try:
                if not force and key in self.frame_cache:
                    self.raw = self.frame_cache[key]
                else:
                    self.raw = grab_frame(ffmpeg, path, t, o["deint"], o["field"])
                    self.cache_frame(key, self.raw)
                self.frame_key = key
            except Exception as e:
                self.raw = None
                self.frame_key = None
                self.set_message(f"1コマを取り出せませんでした。\n{e}")
                return
            finally:
                self.root.config(cursor="")
        self.render_preview()

    def render_preview(self):
        if self.raw is None:
            return
        o = self.options()
        aspect = display_aspect(self.raw.width, self.raw.height, o)
        if aspect >= PREVIEW_MAX_W / PREVIEW_MAX_H:
            w, h = PREVIEW_MAX_W, int(PREVIEW_MAX_W / aspect)
        else:
            w, h = int(PREVIEW_MAX_H * aspect), PREVIEW_MAX_H
        base = self.raw.resize((max(w, 1), max(h, 1)), Image.BILINEAR)
        self.before_img = ImageTk.PhotoImage(base)
        msg, color = "", "#666"
        try:
            after = Image.fromarray(simulate(np.asarray(base), o))
            self.after_img = ImageTk.PhotoImage(after)
            if o["ccd"]:
                msg = "※CCD（色ノイズ除去）の効果は、このプレビューには出ません"
        except ValueError as e:
            self.after_img = self.before_img
            msg, color = f"設定にまちがいがあります：{e}", "#b00020"
        if not self.cur_info():
            msg, color = ("※動画の長さを調べられなかったため、先頭のコマを表示しています。\n"
                          "（ffprobe が見つからないか、読めない動画です。真っ黒なら「この場面を取り直す」を）",
                          "#b00020")
        self.note.config(text=msg, foreground=color)
        self.show_after()

    def _show(self, img, label):
        if img is None:
            return
        self.img_label.config(image=img, text="")
        self.img_label.image = img
        self.state_label.config(text=label)

    def show_after(self):
        self._show(self.after_img, "▼ 補正後（avsで出る見た目の目安）")

    def show_before(self):
        self._show(self.before_img, "▼ 補正前")

    # ---------- 移動先の入力・チェックする場面
    def cache_frame(self, key, img):
        self.frame_cache[key] = img
        while len(self.frame_cache) > 24:          # 古いものから捨てる
            self.frame_cache.pop(next(iter(self.frame_cache)))

    def jump_to(self):
        info = self.cur_info()
        if not self.cur_path:
            return "break"
        try:
            n = parse_position(self.jump_var.get(), info["fps"] if info else 0,
                               info["nframes"] if info else 0)
        except ValueError as e:
            messagebox.showwarning(APP_TITLE, str(e))
            return "break"
        self.goto_frame(n)
        return "break"

    def goto_frame(self, n):
        self.pos.set(n)
        self.update_pos_labels()
        self.schedule_image()

    def refresh_marks(self):
        self.marklist.delete(0, "end")
        info = self.cur_info()
        for i, n in enumerate(self.marks.get(self.cur_path, []) if self.cur_path else [], 1):
            t = fmt_tc(n, info["fps"]) if info else "?"
            self.marklist.insert("end", f"{i}.  {t}   （フレーム {n}）")

    def add_mark(self):
        if not self.cur_path or not self.cur_info():
            messagebox.showinfo(APP_TITLE, "先に動画を選んで、画像プレビューに場面を表示してください。")
            return
        n = self.cur_frame()
        lst = self.marks.setdefault(self.cur_path, [])
        if n in lst:
            self.status.config(text=f"フレーム {n} はもう覚えています")
            return
        if len(lst) >= 8:
            messagebox.showinfo(APP_TITLE, "覚えておける場面は8つまでです。いらない場面を「選んだ場面を忘れる」で消してください。")
            return
        lst.append(n)
        lst.sort()
        self.refresh_marks()
        self.marklist.selection_set(lst.index(n))
        self.status.config(text=f"フレーム {n} を覚えました（{len(lst)} 場面）")
        self.schedule_save()
        self.notify_assistant()

    def delete_mark(self):
        sel = self.marklist.curselection()
        lst = self.marks.get(self.cur_path, [])
        if not sel or not lst:
            return
        for i in reversed(sel):
            if i < len(lst):
                self.forget_mark(lst[i], refresh=False)
        self.refresh_marks()
        self.schedule_save()
        self.notify_assistant()

    def forget_mark(self, n, refresh=True):
        """覚えた場面を1つ忘れる（その場面の演出チェック・肌の見本も消す）"""
        p = self.cur_path
        if p in self.marks and n in self.marks[p]:
            self.marks[p].remove(n)
        self.mflags.get(p, {}).pop(n, None)
        if p in self.skins:
            self.skins[p] = [x for x in self.skins[p] if x[0] != n]
        if refresh:
            self.refresh_marks()
            self.schedule_save()

    def goto_mark(self):
        sel = self.marklist.curselection()
        lst = self.marks.get(self.cur_path, [])
        if sel and sel[0] < len(lst):
            self.goto_frame(lst[sel[0]])

    def batch_compare(self, mode):
        """覚えた場面の比較画像（補正前｜補正後）を、縦に並べた1枚にする"""
        if self._batch_running:
            return
        path, info = self.cur_path, self.cur_info()
        frames = list(self.marks.get(path, [])) if path else []
        if not frames:
            messagebox.showinfo(APP_TITLE, "覚えた場面がありません。\n"
                                           "見比べたい場面で「この場面を覚える」を押してください。")
            return
        ffmpeg = self.tool("ffmpeg")
        if not ffmpeg:
            messagebox.showwarning(APP_TITLE, "ffmpegが見つかりません。")
            return
        o = self.options()
        try:
            parse_color(o)
        except ValueError as e:
            messagebox.showwarning(APP_TITLE, str(e))
            return
        save_to = None
        if mode == "save":
            base = os.path.splitext(os.path.basename(path))[0]
            save_to = filedialog.asksaveasfilename(
                title="比較画像の保存先", defaultextension=".png",
                initialdir=os.path.dirname(path), initialfile=f"{base}_比較_{len(frames)}場面.png",
                filetypes=[("PNG画像", "*.png"), ("JPEG画像", "*.jpg")])
            if not save_to:
                return
        self._batch_running = True
        for b in (self.b_mcopy, self.b_msave):
            b.config(state="disabled")
        name = os.path.basename(path)
        prog = {"i": 0, "result": None}          # 作業スレッドとのやりとり（画面の操作は表のスレッドだけで行う）

        def work():
            try:
                imgs = []
                for i, n in enumerate(frames, 1):
                    prog["i"] = i
                    key = (path, n, o["deint"], o["field"], ffmpeg)
                    raw = self.frame_cache.get(key)
                    if raw is None:
                        t = max(0.0, (n - 0.3) / info["fps"]) if info else 0.0
                        raw = grab_frame(ffmpeg, path, t, o["deint"], o["field"])
                    title = f"{name}   フレーム {n}" + (f"（{fmt_tc(n, info['fps'])}）" if info else "")
                    imgs.append(make_compare_image(raw, o, title, show_settings=False))
                prog["result"] = ("ok", stack_compare_images(imgs, o))
            except Exception as e:
                prog["result"] = ("err", e)

        def poll():
            if prog["result"] is None:
                self.status.config(text=f"比較画像を作っています…（{prog['i']}/{len(frames)} 場面）")
                self.root.after(150, poll)
                return
            kind, val = prog["result"]
            if kind == "ok":
                self._batch_done(val, mode, save_to, len(frames))
            else:
                self._batch_done(None, mode, save_to, 0, val)

        threading.Thread(target=work, daemon=True).start()
        self.root.after(150, poll)

    def _batch_done(self, img, mode, save_to, count, err=None):
        self._batch_running = False
        self.b_msave.config(state="normal")
        if os.name == "nt":
            self.b_mcopy.config(state="normal")
        if img is None:
            self.status.config(text="")
            messagebox.showwarning(APP_TITLE, f"比較画像を作れませんでした。\n{err}")
            return
        if mode == "copy":
            try:
                ok = copy_image_to_clipboard(img)
            except Exception:
                ok = False
            if ok:
                self.status.config(text=f"{count} 場面の比較画像をコピーしました。チャットなどに Ctrl+V で貼り付けられます。")
            else:
                messagebox.showwarning(APP_TITLE, "クリップボードにコピーできませんでした。「まとめて保存…」を使ってください。")
        else:
            try:
                if save_to.lower().endswith((".jpg", ".jpeg")):
                    img.save(save_to, quality=95)
                else:
                    img.save(save_to)
                self.status.config(text=f"{count} 場面の比較画像を保存しました：{save_to}")
            except OSError as e:
                messagebox.showwarning(APP_TITLE, f"保存できませんでした。\n{e}")

    # ---------- 比較画像（補正前｜補正後）
    def _compare_image(self):
        """今表示している場面の比較画像を作る。作れなければメッセージを出して None"""
        if self.raw is None or not self.cur_path:
            messagebox.showinfo(APP_TITLE, "先に動画を選んで、画像プレビューに場面を表示してください。")
            return None
        info = self.cur_info()
        n = self.cur_frame()
        title = os.path.basename(self.cur_path) + f"   フレーム {n}"
        if info:
            title += f"（{fmt_tc(n, info['fps'])}）"
        try:
            return make_compare_image(self.raw, self.options(), title)
        except ValueError as e:
            messagebox.showwarning(APP_TITLE, str(e))
        except Exception as e:
            messagebox.showwarning(APP_TITLE, f"比較画像を作れませんでした。\n{e}")
        return None

    def copy_compare(self):
        img = self._compare_image()
        if img is None:
            return
        try:
            ok = copy_image_to_clipboard(img)
        except Exception:
            ok = False
        if ok:
            self.status.config(text="比較画像をコピーしました。チャットなどに Ctrl+V で貼り付けられます。")
        else:
            messagebox.showwarning(APP_TITLE, "クリップボードにコピーできませんでした。「保存…」を使ってください。")

    def save_compare(self):
        img = self._compare_image()
        if img is None:
            return
        base = os.path.splitext(os.path.basename(self.cur_path))[0]
        path = filedialog.asksaveasfilename(
            title="比較画像の保存先", defaultextension=".png",
            initialdir=os.path.dirname(self.cur_path),
            initialfile=f"{base}_f{self.cur_frame()}_比較.png",
            filetypes=[("PNG画像", "*.png"), ("JPEG画像", "*.jpg")])
        if not path:
            return
        try:
            if path.lower().endswith((".jpg", ".jpeg")):
                img.save(path, quality=95)
            else:
                img.save(path)
            self.status.config(text=f"比較画像を保存しました：{path}")
        except OSError as e:
            messagebox.showwarning(APP_TITLE, f"保存できませんでした。\n{e}")

    # ---------- カット編集
    def set_start(self):
        if not self.cur_info():
            return
        n = self.cur_frame()
        self.pend["s"] = n
        if self.pend["e"] is not None and self.pend["e"] < n:
            self.pend["e"] = None
        self.update_pos_labels()

    def set_end(self):
        if not self.cur_info():
            return
        n = self.cur_frame()
        self.pend["e"] = n
        if self.pend["s"] is not None and self.pend["s"] > n:
            self.pend["s"] = None
        self.update_pos_labels()

    def add_segment(self):
        info = self.cur_info()
        if not info:
            return
        s = self.pend["s"] if self.pend["s"] is not None else 0
        e = self.pend["e"] if self.pend["e"] is not None else info["nframes"] - 1
        if e < s:
            messagebox.showwarning(APP_TITLE, "終了点が開始点より前になっています。")
            return
        lst = list(self.cuts.get(self.cur_path, []))
        fps = info["fps"]
        inside = next((i for i, (a, b, _) in enumerate(lst) if a <= s and e <= b), None)
        if inside is not None:
            a, b, f = lst[inside]
            if (a, b) == (s, e):
                messagebox.showinfo(APP_TITLE, "同じ区間がすでに登録されています。")
                return
            # すでに登録した区間の中を選んだ → 黙って吸収せず、範囲を狭めるか確認する
            if not messagebox.askyesno(
                    APP_TITLE,
                    f"選んだ範囲は、登録済みの区間 {inside + 1}"
                    f"（{fmt_tc(a, fps)} 〜 {fmt_tc(b, fps)}）の中にあります。\n\n"
                    f"区間 {inside + 1} を、この範囲\n（{fmt_tc(s, fps)} 〜 {fmt_tc(e, fps)}）に置き換えますか？\n\n"
                    "「はい」＝置き換える（範囲が狭くなります）\n「いいえ」＝何もしない"):
                return
            lst[inside] = (s, e, f)
        else:
            lst.append((s, e, bool(self.vars["anime24"].get())))
        self.cuts[self.cur_path] = normalize_cuts(lst)
        self.pend = {"s": None, "e": None}
        self.update_pos_labels()
        self.refresh_cut_list()
        self.refresh_preview()
        self.save_settings()

    def delete_segment(self):
        if not self.cur_path or not self.cuts.get(self.cur_path):
            return
        sel = self.seg_selection()
        if not sel:
            messagebox.showinfo(APP_TITLE, "削除したい区間を、リストの中から押して選んでください。\n"
                                           "（右クリックでも削除できます）")
            return
        lst = list(self.cuts.get(self.cur_path, []))
        for i in reversed(sel):
            if i < len(lst):
                del lst[i]
        self.cuts[self.cur_path] = lst
        self.refresh_cut_list()
        self.refresh_preview()
        self.save_settings()

    def clear_segments(self):
        if self.cur_path and self.cuts.get(self.cur_path):
            self.cuts[self.cur_path] = []
            self.refresh_cut_list()
            self.refresh_preview()
            self.save_settings()

    def seg_selection(self):
        return sorted(int(i) for i in self.seglist.selection())

    def any_cut_24(self):
        return any(c[2] for c in self.cuts.get(self.cur_path, []) or [])

    def on_seg_click(self, event):
        """左端のチェック欄を押したら、その区間の24p化を切り替える"""
        if self.seglist.identify_region(event.x, event.y) != "tree":
            return
        iid = self.seglist.identify_row(event.y)
        if not iid or self.seglist.identify_column(event.x) != "#0":
            return
        lst = list(self.cuts.get(self.cur_path, []))
        i = int(iid)
        if i >= len(lst):
            return
        s, e, f = lst[i]
        lst[i] = (s, e, not f)
        self.cuts[self.cur_path] = lst          # 並べ直しや結合はしない（切り替えたあとで区間が減らないように）
        self.refresh_cut_list()
        self.seglist.selection_set(str(i))
        self.update_states()
        self.refresh_preview()
        self.save_settings()
        return "break"

    def on_seg_rightclick(self, event):
        """右クリックで、その区間を選んで「削除」メニューを出す"""
        iid = self.seglist.identify_row(event.y)
        if not iid:
            return
        if iid not in self.seglist.selection():
            self.seglist.selection_set(iid)
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label="選んだ区間を削除", command=self.delete_segment)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def on_seg_double(self, event):
        if self.seglist.identify_column(event.x) == "#0":
            return "break"
        self.goto_segment()

    def goto_segment(self):
        sel = self.seg_selection()
        lst = self.cuts.get(self.cur_path, [])
        if sel and sel[0] < len(lst):
            self.pos.set(lst[sel[0]][0])
            self.update_pos_labels()
            self.load_frame()

    def refresh_cut_list(self):
        self.refresh_marks()
        if self.cur_path:
            self.update_row(self.cur_path)          # 一覧の「処理」列（区間の数・24p）を更新
        self.seglist.delete(*self.seglist.get_children())
        info = self.cur_info()
        lst = self.cuts.get(self.cur_path, []) if self.cur_path else []
        if not info:
            self.cut_total.config(text="")
            return
        fps = info["fps"]
        for i, (s, e, f) in enumerate(lst):
            self.seglist.insert(
                "", "end", iid=str(i), text="☑" if f else "☐",
                values=(f"{i + 1}: {fmt_tc(s, fps)} 〜 {fmt_tc(e, fps)}   （{fmt_dur((e - s + 1) / fps)}）",))
        n = kept_frames(lst, info["nframes"])
        self.cut_total.config(
            text=f"残す合計 {fmt_dur(n / fps)} ／ 全体 {fmt_dur(info['nframes'] / fps)}" if lst
            else f"カットなし（全体 {fmt_dur(info['nframes'] / fps)}）")
        self.update_states()

    # ---------- 設定の保存
    def load_settings(self):
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, ValueError):
            return
        for k, var in self.vars.items():
            if k in data:
                var.set(data[k])
        try:   # 古い版で保存したカット区間（パスごと）も読み込んでおく
            self.cuts = {p: normalize_cuts(c) for p, c in data.get("_cuts", {}).items()}
        except (ValueError, TypeError, AttributeError):
            self.cuts = {}

    def save_settings(self):
        """共通の設定（ffmpegの場所など）と、一覧にある動画ごとの設定を保存する"""
        self._save_job = None
        data = self.options()        # 動画ごとの項目は「次に追加する動画の初期値」として残る
        try:
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except OSError:
            pass
        self.remember_files()
        self.save_record()

    def on_close(self):
        if self.running:
            if not messagebox.askyesno(APP_TITLE, "エンコード中です。中止して終了しますか？"):
                return
            self.cancel_encode()
        self.save_settings()
        self.root.destroy()

    # ---------- 使い方・更新
    def open_help(self):
        import webbrowser
        try:
            webbrowser.open(HELP_PAGE)
        except Exception:
            messagebox.showinfo(APP_TITLE, f"ブラウザを開けませんでした。次のページを開いてください。\n{HELP_PAGE}")

    def check_update(self):
        if self.running:
            messagebox.showinfo(APP_TITLE, "エンコード中は更新できません。終わってから押してください。")
            return
        self.b_update.config(state="disabled")
        self.status.config(text="更新を確認しています…")

        def work():
            try:
                info = fetch_latest_info()
                self.root.after(0, lambda: self._update_found(info))
            except Exception as e:
                self.root.after(0, lambda e=e: self._update_failed(e))
        threading.Thread(target=work, daemon=True).start()

    def _update_failed(self, e):
        self.b_update.config(state="normal")
        self.status.config(text="")
        messagebox.showwarning(APP_TITLE, "更新を確認できませんでした。\n"
                                          "インターネットにつながっているか確認してください。\n\n"
                                          f"{e}")

    def _update_found(self, info):
        self.b_update.config(state="normal")
        latest = str(info.get("version", ""))
        if _version_tuple(latest) <= _version_tuple(APP_VERSION):
            self.status.config(text=f"最新版です（v{APP_VERSION}）")
            messagebox.showinfo(APP_TITLE, f"最新版です（v{APP_VERSION}）。")
            return
        notes = info.get("notes") or []
        if isinstance(notes, str):
            notes = [notes]
        text = "\n".join(f"・{n}" for n in notes[:15]) or "（変更内容の説明はありません）"
        if not messagebox.askyesno(
                APP_TITLE,
                f"新しい版があります。\n\nv{APP_VERSION} → v{latest}\n\n{text}\n\n"
                "更新しますか？\n（設定とプリセットはそのまま残ります。"
                "今の版は avs_maker_old.pyw として残すので、戻すこともできます）"):
            self.status.config(text="")
            return
        self.b_update.config(state="disabled")
        self.status.config(text=f"v{latest} をダウンロードしています…")

        def work():
            try:
                data = download_new_version(latest)
                self.root.after(0, lambda: self._update_install(data, latest))
            except Exception as e:
                self.root.after(0, lambda e=e: self._update_failed(e))
        threading.Thread(target=work, daemon=True).start()

    def _update_install(self, data, latest):
        try:
            backup = install_new_version(data)
        except OSError as e:
            self.b_update.config(state="normal")
            messagebox.showwarning(APP_TITLE, f"入れ替えに失敗しました（今の版のままです）。\n{e}")
            return
        self.save_settings()
        self.status.config(text=f"v{latest} に更新しました")
        if messagebox.askyesno(APP_TITLE, f"v{latest} に更新しました。\n"
                                          f"（前の版は {os.path.basename(backup)} に残してあります）\n\n"
                                          "今すぐ再起動しますか？"):
            import sys
            try:
                subprocess.Popen([sys.executable, os.path.abspath(__file__)],
                                 cwd=os.path.dirname(os.path.abspath(__file__)))
            except OSError:
                messagebox.showinfo(APP_TITLE, "自動で再起動できませんでした。手で起動し直してください。")
            self.root.destroy()
        else:
            self.b_update.config(state="normal")

    # ---------- 出力・エンコード
    def make_all(self, encode=False):
        if self.running:
            return
        if not self.files:
            messagebox.showinfo(APP_TITLE, "先に動画ファイルを追加してください。")
            return
        o = self.options()
        if o["out_mode"] == "folder":
            if not o["out_dir"] or not os.path.isdir(o["out_dir"]):
                messagebox.showwarning(APP_TITLE, "保存先フォルダを選んでください。")
                return

        # 動画ごとに、24pと通常のパートに分ける
        splits = {src: split_parts(self.cuts.get(src), self.opts_for(src)["anime24"]) for src in self.files}
        need = {f for parts in splits.values() for f, _ in parts}      # 必要な処理：False=通常 / True=24p

        ffs, no_uhq = {}, set()
        if encode:
            for f in sorted(need):
                key, label = ("ffmpeg24", "24p用ffmpeg") if f else ("ffmpeg", "通常用ffmpeg")
                if f and not (o["ffmpeg24"] and os.path.isfile(o["ffmpeg24"])):
                    messagebox.showwarning(
                        APP_TITLE,
                        "24p化する部分があるのに、「24p用ffmpeg」が選ばれていません。\n\n"
                        "「④ エンコード」の「24p用ffmpeg（3.7.5）」で、AviSynth+ 3.7.5 の avisynth.dll と\n"
                        "同じフォルダにある ffmpeg.exe を選んでください。")
                    return
                ff = find_tool("ffmpeg", o[key])
                if not ff:
                    messagebox.showwarning(APP_TITLE, f"{label}が見つかりません。「④ エンコード」の欄から選んでください。")
                    return
                ffs[f] = ff
            if True in ffs and not os.path.isfile(os.path.join(os.path.dirname(ffs[True]), "avisynth.dll")):
                if not messagebox.askyesno(
                        APP_TITLE,
                        "24p用ffmpegと同じフォルダに avisynth.dll が見つかりません。\n\n"
                        f"{ffs[True]}\n\n"
                        "このままだと、パソコンに入っている AviSynth（Neo）が使われ、\n"
                        "SRestore のエラーになる可能性があります。続けますか？"):
                    return
            try:                      # 設定のまちがいを、始める前に見つける
                build_ffmpeg_cmd(next(iter(ffs.values())), "x.avs", "x.mp4", o)
            except ValueError as e:
                messagebox.showwarning(APP_TITLE, str(e))
                return
            for ff in ffs.values():
                if encoder_supports(ff, "hevc_nvenc", "uhq") is False:
                    if not messagebox.askyesno(
                            APP_TITLE,
                            "このffmpegは「-tune uhq」に対応していません（古いバージョンです）。\n\n"
                            f"{ff}\n\n"
                            "［はい］ uhqの代わりに hq でエンコードを続ける（画質の差はごくわずかです）\n"
                            "［いいえ］ やめる（uhqに対応した新しいffmpegを選んでください）"):
                        return
                    no_uhq.add(ff)

        # 出力パスを決める（同名がぶつかったら _2, _3 …。元の動画を上書きしない）
        jobs, used_avs, used_mp4 = [], set(), set()
        for src in self.files:
            base = os.path.splitext(os.path.basename(src))[0]
            folder = o["out_dir"] if o["out_mode"] == "folder" else os.path.dirname(src)
            avs = os.path.join(folder, base + ".avs")
            n = 2
            while avs.lower() in used_avs:
                avs = os.path.join(folder, f"{base}_{n}.avs")
                n += 1
            used_avs.add(avs.lower())
            mp4 = os.path.join(folder, base + ".mp4")
            n = 2
            while mp4.lower() in used_mp4 or os.path.normcase(mp4) == os.path.normcase(src):
                mp4 = os.path.join(folder, f"{base}_{n}.mp4")
                n += 1
            used_mp4.add(mp4.lower())
            files = [(avs, mp4)]
            jobs.append((src, mp4, files))

        # 上書き確認
        exists = []
        for _, mp4, files in jobs:
            for a_, m_ in files:
                exists += [a_] + ([m_] if encode else [])
        exists = [p_ for p_ in exists if os.path.exists(p_)]
        if exists:
            names = "\n".join(os.path.basename(p_) for p_ in exists[:8])
            more = f"\n…ほか{len(exists) - 8}個" if len(exists) > 8 else ""
            if not messagebox.askyesno(APP_TITLE, f"次のファイルはすでにあります。上書きしますか？\n\n{names}{more}"):
                return

        ok, utf8_files, errors, plan = 0, [], [], []
        for src, mp4, files in jobs:
            try:
                info = self.info_for(src)
                nframes = info["nframes"] if info else 0
                o_src = self.opts_for(src)          # その動画の設定
                scripts = build_part_scripts(src, o_src, self.cuts.get(src), nframes)
                parts = []
                for (flag, cuts_, text), (avs, pmp4) in zip(scripts, files):
                    if not write_avs(avs, text):
                        utf8_files.append(os.path.basename(avs))
                    total = (kept_frames(cuts_, nframes) / info["fps"]) if info else 0
                    parts.append({"flag": flag, "avs": avs, "mp4": pmp4, "total": total})
                ok += 1
                plan.append({"src": src, "mp4": mp4, "parts": parts, "o": o_src})
            except ValueError as e:      # 数字の入力ミス
                messagebox.showwarning(APP_TITLE, f"{os.path.basename(src)} の設定：\n{e}")
                return
            except OSError as e:
                errors.append(f"{os.path.basename(files[0][0])}: {e}")

        self.save_settings()
        if not encode:
            nfiles = ok
            msg = f"{nfiles} 個のavsを作成しました。"
            if utf8_files:
                msg += "\n\n※次のファイルはパスに日本語環境で扱えない文字があったため、UTF-8で保存しました。\n" + "\n".join(utf8_files)
            if errors:
                msg += "\n\n【失敗】\n" + "\n".join(errors)
            self.status.config(text=f"{nfiles} 個作成しました")
            messagebox.showinfo(APP_TITLE, msg)
            return

        if errors:
            messagebox.showwarning(APP_TITLE, "avsを作れなかったファイルがあります。\n\n" + "\n".join(errors))
            if not plan:
                return
        self.start_encode(plan, ffs, o, no_uhq)

    def start_encode(self, plan, ffs, o, no_uhq):
        self.running = True
        self.cancel_flag = False
        self.b_enc.config(state="disabled")
        self.b_avs.config(state="disabled")
        self.b_cancel.config(state="normal")
        self.pbar.config(value=0)
        self.status.config(text="エンコードを始めています…（AviSynthの準備に少しかかります）")
        threading.Thread(target=self._encode_worker, args=(plan, dict(ffs), dict(o), set(no_uhq)),
                         daemon=True).start()
        self.root.after(200, self.poll_queue)

    def _encode_worker(self, plan, ffs, o, no_uhq):
        results = []
        for i, item in enumerate(plan):
            src, mp4, part = item["src"], item["mp4"], item["parts"][0]
            name = os.path.basename(src)
            if self.cancel_flag:
                results.append((name, "中止", ""))
                continue
            t0 = time.time()

            def on_prog(frac, sec, i=i, name=name, t0=t0):
                self.q.put(("progress", i, len(plan), frac, sec, time.time() - t0, name))

            ff = ffs[part["flag"]]
            cmd = []
            try:
                cmd = build_ffmpeg_cmd(ff, part["avs"], mp4,
                                       dict(item.get("o", o), uhq=(ff not in no_uhq)))
                code, lines = run_ffmpeg(cmd, part["total"], on_prog, self._set_proc)
            except Exception as e:
                code, lines = -1, [str(e)]
            if self.cancel_flag:
                results.append((name, "中止", ""))
                code = None
            elif code == 0:
                results.append((name, "完了", mp4))
            else:
                log = os.path.splitext(mp4)[0] + "_ffmpeg.log"
                try:      # あとで原因を調べられるよう、実行したコマンドと出力をそのまま保存する
                    with open(log, "w", encoding="utf-8") as f:
                        f.write("【実行したコマンド】\n" + subprocess.list2cmdline(cmd) + "\n\n")
                        f.write(f"【結果】{exit_code_text(code)}\n\n【ffmpegの出力】\n" + "\n".join(lines) + "\n")
                    note = f"\n（詳しい内容は {os.path.basename(log)} に保存しました）"
                except OSError:
                    note = ""
                detail = "\n".join(lines[-6:]) if lines else "ffmpegがエラーメッセージを出さずに終了しました"
                results.append((name, "失敗", f"{exit_code_text(code)}\n{detail}{note}"))
            if code != 0:       # 途中までのファイルは残さない
                self._remove(mp4)
        self.q.put(("done", results))

    @staticmethod
    def _remove(path):
        try:
            if os.path.exists(path):
                os.remove(path)
        except OSError:
            pass

    def _set_proc(self, p):
        self.proc = p
        if self.cancel_flag:         # 起動の直前に「中止」が押されていた場合
            try:
                p.terminate()
            except OSError:
                pass

    def poll_queue(self):
        try:
            while True:
                msg = self.q.get_nowait()
                if msg[0] == "progress":
                    _, i, n, frac, sec, elapsed, name = msg
                    if frac is None:
                        self.pbar.config(value=0)
                        text = f"{i + 1}/{n} 本目  {name}  （{fmt_dur(sec)} ぶん処理済み）"
                    else:
                        self.pbar.config(value=frac * 100)
                        eta = elapsed * (1 - frac) / frac if frac > 0.005 else 0
                        text = (f"{i + 1}/{n} 本目  {name}  {frac * 100:.0f}%   "
                                f"経過 {fmt_dur(elapsed)}" + (f"  残り約 {fmt_dur(eta)}" if eta else ""))
                    self.status.config(text=text)
                elif msg[0] == "done":
                    self.finish_encode(msg[1])
                    return
        except queue.Empty:
            pass
        if self.running:
            self.root.after(200, self.poll_queue)

    def finish_encode(self, results):
        self.running = False
        self.proc = None
        self.b_enc.config(state="normal")
        self.b_avs.config(state="normal")
        self.b_cancel.config(state="disabled")
        done = [r for r in results if r[1] == "完了"]
        failed = [r for r in results if r[1] == "失敗"]
        canceled = [r for r in results if r[1] == "中止"]
        self.pbar.config(value=100 if not failed and not canceled else 0)
        self.status.config(text=f"エンコード終了：完了 {len(done)} 本／失敗 {len(failed)} 本／中止 {len(canceled)} 本")
        msg = f"完了 {len(done)} 本"
        if failed:
            msg += "\n\n【失敗】\n" + "\n".join(f"{n}: {d}" for n, _, d in failed)
        if canceled:
            msg += f"\n\n中止 {len(canceled)} 本"
        (messagebox.showwarning if failed else messagebox.showinfo)(APP_TITLE, msg)

    def cancel_encode(self):
        self.cancel_flag = True
        p = self.proc
        if p is not None and p.poll() is None:
            try:
                p.terminate()
            except OSError:
                pass
        self.status.config(text="中止しています…")


def main():
    root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
