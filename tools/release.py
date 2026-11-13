#!/usr/bin/env python3
"""公開前の確認と、version.json・changelog.json の書き出し。

  python tools/release.py "更新内容のひとこと"
  python tools/release.py "1つめの内容" "2つめの内容" "3つめの内容"   … 内容が複数あるときは、1つずつ並べる
  python tools/release.py                                           … 同じ版の書き直し(今の内容と日付を残す)

本体(avs_maker.pyw)の APP_VERSION を読み、この1回で次の2つを書く。notes は必ず同じ内容になる。
  version.json    version / date / sha256 / notes   (アプリの「更新を確認」が読む)
  changelog.json  releases の先頭に {version, date, notes}   (更新の案内と、使い方ページの更新履歴が読む)

SHA-256 は、改行を LF にそろえた中身で計算する(アプリが更新のときに、同じ計算で照合する)。
構文エラーがある・版番号が上がっていない・本体が小さすぎる、のどれかなら、何も書かずに止まる。
同じ本体でもう一度実行すると、2つとも同じ中身になる。
"""
import datetime
import hashlib
import json
import os
import py_compile
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
APP_FILE = "avs_maker.pyw"
MIN_SIZE = 100_000   # アプリ側(UPDATE_MIN_SIZE)は、これより小さいファイルを「壊れている」として受け付けない
CHANGELOG_NOTE = "更新履歴。新しい版を出すたびに、いちばん上に追加する（version.json と同じ版番号・内容）"


def vkey(version):
    """'1.4.8' → (1, 4, 8)。3つの数字の形でなければ None"""
    m = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", str(version).strip())
    return tuple(int(x) for x in m.groups()) if m else None


def as_notes(value):
    """notes を、空でない文字列のリストにそろえる(文字列1つだけの古い書き方も受ける)"""
    if isinstance(value, str):
        value = [value]
    if not isinstance(value, list):
        return []
    return [str(n).strip() for n in value if str(n).strip()]


def read_json(path, what):
    """JSON を読む。無い・空・壊れているときは None(止めずに、あとで正しい内容に書き直す)"""
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (ValueError, OSError):
        print(f"注意: 今の {what} が読めません(空か、壊れています)。正しい内容で書き直します")
        return None
    if not isinstance(data, dict):
        print(f"注意: 今の {what} の形が正しくありません。正しい内容で書き直します")
        return None
    return data


def changelog_from_git():
    """changelog.json が壊れていたとき用: 最後にコミットした中身を取り出す(過去の履歴をなくさないため)"""
    try:
        r = subprocess.run(["git", "show", "HEAD:changelog.json"], cwd=ROOT, capture_output=True, timeout=20)
        data = json.loads(r.stdout.decode("utf-8")) if r.returncode == 0 else None
    except (OSError, ValueError, subprocess.SubprocessError):
        data = None
    if isinstance(data, dict) and isinstance(data.get("releases"), list):
        print("  → 過去の履歴は、最後にコミットした changelog.json から取り出しました")
        return data
    print("  → 過去の履歴は取り出せませんでした。今回の版だけの履歴になります(必要なら git の履歴から戻してください)")
    return None


def dump(data):
    return json.dumps(data, ensure_ascii=False, indent=2) + "\n"


def main():
    args = sys.argv[1:]
    if args and args[0] in ("-h", "--help"):
        sys.exit(__doc__)
    new_notes = as_notes(args)
    if args and len(new_notes) != len(args):
        sys.exit("更新内容に、空の文があります(何も変えていません)")

    # ---- 本体の確認
    src = ROOT / APP_FILE
    raw = src.read_bytes().replace(b"\r\n", b"\n")      # リポジトリの中身(LF)と同じにして計算する
    try:
        py_compile.compile(str(src), doraise=True)
    except py_compile.PyCompileError as e:
        sys.exit(f"{APP_FILE}: 構文エラーがあります(何も変えていません)\n{e.msg}")
    if len(raw) < MIN_SIZE:
        sys.exit(f"{APP_FILE}: 小さすぎます ({len(raw)} バイト)。アプリ側の確認に通りません(何も変えていません)")
    m = re.search(r'^APP_VERSION\s*=\s*"([^"]+)"', raw.decode("utf-8"), re.M)   # アプリ側の確認と同じ読み方
    if not m:
        sys.exit(f"{APP_FILE}: APP_VERSION が見つかりません(何も変えていません)")
    ver = m.group(1)
    if vkey(ver) is None:
        sys.exit(f'{APP_FILE}: APP_VERSION "{ver}" が 1.4.8 のような3つの数字の形ではありません(何も変えていません)')
    sha = hashlib.sha256(raw).hexdigest()

    # ---- 今の version.json と比べる
    out_v = ROOT / "version.json"
    old = read_json(out_v, "version.json") or {}
    old_key = vkey(old.get("version", ""))
    same_version = old_key == vkey(ver)
    if old_key is not None:
        # 版が下がる・同じ版なのに中身が違う、は止める(sha256 の無い古い version.json に、初めて付けるときは通す)
        if vkey(ver) < old_key or (same_version and old.get("sha256") and sha != str(old["sha256"]).lower()):
            sys.exit(f"版番号が上がっていません (今 {old['version']})。APP_VERSION を上げてください(何も変えていません)")
    notes = new_notes or (as_notes(old.get("notes")) if same_version else [])
    if not notes:
        sys.exit("更新内容がありません。 python tools/release.py \"更新内容のひとこと\" のように書いてください(何も変えていません)")
    # 同じ版の書き直しなら、最初に公開した日付を残す(もう一度実行しても同じ結果になるように)
    old_date = str(old.get("date", ""))
    date = old_date if same_version and re.fullmatch(r"\d{4}-\d{2}-\d{2}", old_date) else datetime.date.today().isoformat()
    info = {"version": ver, "date": date, "sha256": sha, "notes": notes}

    # ---- changelog.json: 同じ版があれば入れ替え、なければ先頭に足す(ほかのキーと過去の履歴はそのまま)
    out_c = ROOT / "changelog.json"
    log = read_json(out_c, "changelog.json")
    if log is None or not isinstance(log.get("releases"), list):
        if out_c.exists():
            log = changelog_from_git()
        log = log or {"note": CHANGELOG_NOTE, "releases": []}
    entry = {"version": ver, "date": date, "notes": notes}
    releases = [r for r in log["releases"]
                if not (isinstance(r, dict) and vkey(r.get("version", "")) == vkey(ver))]
    log = dict(log, releases=[entry] + releases)

    # ---- 空のファイルが残らないように、別名に書ききって、読み直して確かめてから入れ替える
    jobs = [(out_v, info), (out_c, log)]
    tmps = []
    for path, data in jobs:
        tmp = path.with_suffix(".json.tmp")
        tmp.write_text(dump(data), encoding="utf-8", newline="\n")
        tmps.append(tmp)
        if json.loads(tmp.read_text(encoding="utf-8")) != data:
            for t in tmps:
                t.unlink()
            sys.exit(f"{path.name} の書き出しを確かめられませんでした(何も変えていません)")
    for (path, _), tmp in zip(jobs, tmps):
        os.replace(tmp, path)

    print(f"version.json と changelog.json を書きました: v{ver} ({date})  sha256 {sha[:12]}…")
    for n in notes:
        print(f"  ・{n}")


if __name__ == "__main__":
    main()
