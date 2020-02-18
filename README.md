# PlusCal を使って TLA+ でモデル走査する。

チェシャ猫さんが Developers Summit 2020 でお話されていた、[「厳密な共通言語」としての形式手法](https://speakerdeck.com/ytaka23/developers-summit-2020)の内容を参考に、PlusCal(TLA+)を使ったモデル走査を試してみました。

TLA+, PlusCalについては [Learn TLA+](https://learntla.com/) のサイトを見て調べました。

### IDEを準備する。

[[TLA+] TLA+と形式仕様言語 [目的と準備]](https://dev.classmethod.jp/planning/what-is-tlaplus/)のページを見て、以下をインストールしました。

- TLA+ IDE
- pdflatex

これだけでも使うことはできますが、普段で使っている IDE が Visual Studio Code の人は、

- [TLA+ の vscode extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)

も入れると良いかもしれません。インストール後に[こちら](https://github.com/alygin/vscode-tlaplus/wiki/Automatic-Module-Parsing)に書いてある設定をしておくと、ファイルを保存したときに PlusCal から TLA+ への変換を自動で実行してくれるようになり便利です。