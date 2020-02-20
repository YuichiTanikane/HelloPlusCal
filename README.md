# PlusCal (TLA+) を使ってモデル走査を試す。

チェシャ猫さんの Developers Summit 2020 の発表[「厳密な共通言語」としての形式手法](https://speakerdeck.com/ytaka23/developers-summit-2020)の内容を参考に、PlusCal(TLA+)を使ったモデル走査を試してみました。

PlusCal の書き方は主に [Learn TLA+](https://learntla.com/) を見ました。

## IDEを準備する。

[[TLA+] TLA+と形式仕様言語 [目的と準備]](https://dev.classmethod.jp/planning/what-is-tlaplus/)のページを見て、以下をインストールしました。

- TLA+ IDE
- pdflatex

これで初めることができます。

私は普段で使っている IDE が Visual Studio Code なので、

- [TLA+ の vscode extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)

も入れてみました。インストール後に[こちら](https://github.com/alygin/vscode-tlaplus/wiki/Automatic-Module-Parsing)に書いてある設定をしておくと、ファイルを保存したときに PlusCal から TLA+ への変換を自動で実行してくれるようになり便利です。

## Hello World.

初めて PlusCal に挑戦するときには、[Learn TLA+ の Example](https://learntla.com/introduction/example/) をやってみるのがオススメです。

IDE ( TLA+ IDE でも vscode でも )で自分が書いたコードを実行するというだけでも、普段使っているプログラミング言語とは結構違うので、Example にある手順で、

- とても簡単な仕様でまずはモデル走査を成功させる。
- 仕様を少し変えてみて、矛盾（満たすべき条件を満たさない状態）が検出されることを確認する。
- 発生した矛盾を、修正して再びグリーンな状態にする。
- トランザクション、並列処理など、現実に起こりそうな仕様変更を加えてみる。

というのを試してみると「なるほど、仕様を変えたときにおきる、こういうパターンの矛盾が、モデル走査することで検出できるのか」という雰囲気がだんだん分かってくると思います。

```sh
/hello
```

hello フォルダ以下にあるファイルは、上記の Example のソースを TLA+ IDE または vscode で実際に動かしたときに使ったファイルです。

## 決済に２つのサービスを使っている分散システムの仕様を検証してみる。

```sh
/payment
```

[「厳密な共通言語」としての形式手法](https://speakerdeck.com/ytaka23/developers-summit-2020)に出てきた、１つの決済サービスがバックエンドで２つの支払いサービスを使っているというストーリー（簡易的なTCCパターン）に沿って、 PlusCal のコードを記述してみたものです。

### ソースコード

```
payment.tla
payment.cfg
```

を使ってモデル走査を実行すると Success します。このソースコードは、

1. 登場する３つのサービスを作る。
2. 支払いサービスが crash しない仕様でモデル走査が Success する。
3. 支払いサービスが crash するように仕様を変更し、モデル走査が Fail する。
4. 代替サーバーを作成する。
   1. 支払いサービスをコピーした仕様で作成。
   2. 支払いサービスの Crash を条件に、代わりに Confirm / Cancel を発行する。
5. モデル走査が Fail する。
6. 代替サーバーの仕様を修正し、モデル走査が Success する。

という一連のストーリーが完了した後のソースコードです。

### ハンズオン的にストーリーを進めるには。

```
payment.tla 
```
の各所にコメントで説明を記載していますので、それを見つつ以下のように進めてみてください。

#### 登場する３つのサービスを作る。
まずは、支払いサービス、カード決済サービス、ポイント決済サービスの３つを作成し、エラー無く動く状態を作ってみましょう。

```
---- MODULE payment ----
EXTENDS Naturals, TLC
(* --algorithm payment
variables
    paymentStatus = "try",
    cardStatus = "idling",
    pointStatus = "idling";

define 
    confirmable == cardStatus \in {"reserved"} /\ pointStatus \in {"reserved"}
    cancelable  == cardStatus \in {"canceled"} \/ pointStatus \in {"canceled"}
    consistency == ~ (
        ( cardStatus \in {"confirmed"} /\ pointStatus \in {"canceled"} )
     \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"confirmed"} )
    )  
    completed   == <>(
        ( cardStatus \in {"confirmed"} /\ pointStatus \in {"confirmed"} )
     \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"canceled"} )
    )           
fair process Payment = "Payment"
begin
    ConfirmOrCancel:
    either 
        await confirmable;
        paymentStatus := "confirm";
    or
        await cancelable;
        paymentStatus := "cancel";
    end either;
end process;

fair process Card = "Card"
begin
    IdleAndReserveAndConfirmed:
    while cardStatus \in {"idling", "reserved" } do 
        either
            await cardStatus = "idling";
            cardStatus := "reserved";
        or
            await cardStatus = "reserved" /\ paymentStatus = "confirm";
            cardStatus := "confirmed";
        or
            await cardStatus = "idling" \/ (cardStatus = "reserved" /\ paymentStatus = "cancel");
            cardStatus := "canceled";
        end either;
    end while;
end process;

\* ポイント決済サービスを、カード決済サービスと同様に作成。

end algorithm; *)
====
```

上記のコードを PlusCal から TLA+ に変換し、 `payment.cfg` の設定内容で実行すると、Success するはずです。
まずはこの状態を作り、PlusCal の条件やプロセスが各サービスのどの動作に対応しているのかを理解しましょう。

#### 支払いサーバーを Crash するように変更する。

支払いサービスに以下のように ServerCrash のセクションを追加します。
支払いサーバーは、 confirm か cancel を発行した後、どこかのタイミングで crash するようになります。

```
fair process Payment = "Payment"
begin
    ConfirmOrCancel:
    either 
        await confirmable;
        paymentStatus := "confirm";
    or
        await cancelable;
        paymentStatus := "cancel";
    end either;
    ServerCrash:
        paymentStatus := "crash";
end process;
```

この変更により、モデル走査時に成り立つべき条件として指定している、consistency と completed のどちらかにエラーが発生するようになります。

#### 支払いサービスの代替サービスを作成する。

今回のストーリーでは、支払いサービスの crash に対処するために、代替のサービスを作ります。まずは、

- Payment の process をそのままコピー。
- 名前を SubPayment に変える。
- ` /\ paymentStatus = "crash";` をつけてメインサーバーが落ちたときにだけ動作するようにする。
- 代替サービスは crash はしないようにする（簡単のため）

という、支払いサーバーと同じ動作をする代替サーバーを作ってみます。

```
fair process SubPayment = "SubPayment"
begin
    ConfirmOrCancel:
    either        
        await confirmable /\ paymentStatus = "crash";
        paymentStatus := "confirm";
    or
        await cancelable /\ paymentStatus = "crash";
        paymentStatus := "cancel";
    end either;
end process;
```

これを追加してモデル走査をすると、 Fail します。

メインサービスは、自分が try をして各決済サービスの reserved を確認して confirm を発行していました。メインサービスが confirm を発行した後に crash するパターンでは、代替サービスはその後に登場するため、一部の決済サービスが confirmed になっている可能性がありました。そのため代替サービスはメインサービスとは違い、各決済サービスが reserved になっているだけでなく、一部 confirmed になった状態でも confirm を発行しなければいけなかったのです。

#### 代替サービスの仕様を修正する。

支払いサービスが confirm を発行する条件として使っている confirmable の下に、代替サービス用に subConfirmable を追加してみましょう。

```
    subConfirmable == 
            cardStatus \in {"reserved", "confirmed"} 
        /\  pointStatus \in {"reserved", "confirmed"}
```

次に、代替サービスが confirm を発行する条件を confirmable から subConfirmable に修正してみましょう。

```
    await subConfirmable /\ paymentStatus = "crash"; 
    paymentStatus := "confirm";
```

モデル走査すると、今度は Success します。

## まとめ。

今回のストーリーでは、サービスは特定の障害しか起こさなかったり、落ちない前提のサービスがあったりと簡略化はされていましたが、モデル走査で何ができるのか、どんな場面で使うと有効なのかが、少し分かってきました。

複数のサービスを実装をした後にサービス間でのプロトコル仕様の矛盾が判明してしまったときの修正コスト等を考えると、今回のように仕様を記述してモデル走査を実施するというのは、なかなか有効な手法なのではないでしょうか。

#### 良さそうな点

- 非同期で動くサービス同士の状態遷移など、人間がパターンを列挙するのが難しい仕様をチェックできる。
- 発生しうるパターンをテストケース的に網羅することを人間がやらなくても、モデル走査で網羅的にチェックできる。
- PlusCal を使うと、TLA+ を直接使って論理式を記述するよりも、プログラミング言語的に記述することができる。
- 仕様の記述があれば、仕様の変更により矛盾がおきないか、というのを比較的簡単に検出できそう。

#### 厳しそうな点

- 普段のプログラミングで言う単体テストのレベルからこれを使うのは、かなり大変そう。
- より複雑な障害のパターンを考慮に入れていくには、分散システムで使われている既存の証明など、結構学習コストの高いエリアに踏み込んでいく必要がありそう。
