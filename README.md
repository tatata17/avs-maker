# avs-maker

VHS の取り込み動画から AviSynth の avs を作り、ffmpeg（HEVC / NVENC）でエンコードする GUI ツール（`avs_maker.pyw`）。

## 更新のしかた
ツール左下の「更新を確認」ボタンを押すと、このリポジトリの最新版と比べて、新しい版があれば自動で入れ替えます。
設定（`avs_maker_settings.json`）と、動画ごとの設定・プリセット（`avs_maker_動画ごとの設定とプリセット.json`）は消えません。
前の版は `avs_maker_old.pyw` として残ります。

## ファイル
- `avs_maker.pyw` … ツール本体（`APP_VERSION` が版番号）
- `version.json` … 最新の版番号と変更内容（更新ボタンが読みに来る）

新しい版を出すときは、`avs_maker.pyw` の `APP_VERSION` と `version.json` の `version` を同じ番号に上げてください。
