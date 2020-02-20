---- MODULE payment ----
EXTENDS Naturals, TLC
(* --algorithm payment
variables
    \* 支払いサービスの初期値
    paymentStatus = "try",
    \* カード決済サービス・ポイント決済サービスでの遷移１
    \* （ process 内部変数にすると define からうまく使えなかったためグローバルに…）
    cardStatus = "idling",
    pointStatus = "idling";

define 
    \* 支払いサービスが confirm をして良い状態なのかを判断するための値。
    \* すべての決済サービスが reserved になったら OK。
    confirmable == cardStatus \in {"reserved"} /\ pointStatus \in {"reserved"}

    \* 代替支払いサービスが confirm をして良いかを監視するための値。
    \* ここを支払いサービスと違う条件にしないといけない、というあたりが、PlusCal で見つけられる仕様バグの一例。
    subConfirmable == 
            cardStatus \in {"reserved", "confirmed"} 
        /\  pointStatus \in {"reserved", "confirmed"}
    
    \* 支払いサービス・代替支払いサービスが cancel をして良い状態なのかを判断するための値。
    \* 決済サービスのどれかが canceled になったら。
    cancelable  == cardStatus \in {"canceled"} \/ pointStatus \in {"canceled"}

    \* 常に満たしていないといけない条件（一貫性）
    \* 決済サービスの confirmed と canceled が混ざった状態は NG。
    \* payment.cfg の INVARIANT 項目で指定することで、これが常に満たされていないといけない、ということを指示している。
    consistency == ~ (
        ( cardStatus \in {"confirmed"} /\ pointStatus \in {"canceled"} )
     \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"confirmed"} )
    )  

    \* 支払いサービスの処理が完了したことを表す条件。
    \* 決済サービスの状態が、「すべて confirmed」または「すべて canceled」になったら完了。
    \* payment.cfg の PROPERTY 項目で指定することで、これがいつかは満たされる、ということを指示している。
    completed   == <>(
        ( cardStatus \in {"confirmed"} /\ pointStatus \in {"confirmed"} )
     \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"canceled"} )
    )       
end define;

\* 支払いサービス。このサービスが Card 決済と Point 決済の２つのサービスに対して try, confirm, cancel 等をおこなう。
\* fair と書かれているのは「勝手には落ちないプロセス」として定義している。
\* fair でないプロセスにすると、今回の Crash のように自分で定義しているエラー以外にも、予期せぬプロセス終了が発生するようになり、より複雑になる…。
fair process Payment = "Payment"
begin
    ConfirmOrCancel:
    either 
        \* try の状態から、各決済サービスの状態が confirm して良い状態になるまで待機する。
        await confirmable;
        paymentStatus := "confirm";
    or
        \* try の状態から、各決済サービスの状態が cancel して良い状態になるまで待機する。
        await cancelable;
        paymentStatus := "cancel";
    end either;
    \* 今回のシナリオでは支払いサーバーは「confirm か cancel をしたあと、いつか crash する」という設定。
    ServerCrash:
        paymentStatus := "crash";
end process;

\* 支払いサービスの代替サーバー。支払いサービスが crash になったときに使われるという設定のサーバー。
\* 「メイン支払いサーバーが落ちていたら」を paymentStatus = "crash" の条件で追加したもの。
fair process SubPayment = "SubPayment"
begin
    ConfirmOrCancel:
    either        
        (* 
            ここの条件を支払いサービスと同じ「 confirmable 」を使おうとすると、
                - メイン支払いサーバーが confirm した後に crash に遷移した
                - 一部の決済サービスは confirm 
                - 一部の決済サービスが reserved
            という状態のときに代替サーバーが confirm を発行できない（支払いが完了しない）という状態に陥る。
            単純に同じ支払いサーバーを増やすのではダメであるということが、モデル走査することで仕様のバグとして分かる。
        *)
        await subConfirmable /\ paymentStatus = "crash"; 
        \* await confirmable /\ paymentStatus = "crash";  <= デッドロックになる方の仕様
        paymentStatus := "confirm";
    or
        await cancelable /\ paymentStatus = "crash";
        paymentStatus := "cancel";
    end either;
    \* 今回の設定では、支払い代替サーバーは crash しない。
end process;

(*
カード決済サービス。
-   遷移１：idling が初期状態。
      意味：peyment が try をしたときにはカード決済サービスは最初 idling である。
-   遷移２：idling から、 reserved または canceled に遷移する。
      意味：カード決済サービスの状態は、payment からの try を受けて、仮登録 or 失敗になる。
-   遷移３：reserved 状態で、支払いサービスが confirm になったら、 confirmded に遷移する。
      意味：支払いサービスは、すべての決済サービスが reserved になったのを見て confirm を実行する。
            各決済サービスは、自分が reserved になった後は、支払いサービスからの confirm が来るまで待機する。
-   遷移４：reserved 状態で、支払いサービスが cancel になった場合は、 canceled に遷移する。
      意味：自分は reserved になったが、他の決済サービスが失敗し、支払いサービスから cancel が来た場合には、自分もキャンセルになる。
*)
fair process Card = "Card"
begin
    IdleAndReserveAndConfirmed:
    while cardStatus \in {"idling", "reserved" } do 
        either
            \* 遷移２（ のうち、 reserved に遷移するほう ）
            await cardStatus = "idling";
            cardStatus := "reserved";
        or
            \* 遷移３
            await cardStatus = "reserved" /\ paymentStatus = "confirm";
            cardStatus := "confirmed";
        or
            \* 遷移２ （ のうち、 canceled に遷移するほう ）
            \* 遷移４
            await cardStatus = "idling" \/ (cardStatus = "reserved" /\ paymentStatus = "cancel");
            cardStatus := "canceled";
        end either;
    end while;
end process;

\* ポイント決済サービス
\*   挙動はカード決済サービスとまったく同じ。
\*   PlusCal の配列をうまく扱うことができず、２つ作った。
fair process Point = "Point"
begin
    IdleAndReserveAndConfirmed:
    while pointStatus \in {"idling", "reserved" } do 
        either
            await pointStatus = "idling";
            pointStatus := "reserved";
        or
            await pointStatus = "reserved" /\ paymentStatus = "confirm";
            pointStatus := "confirmed";
        or
            await pointStatus = "idling" \/ (pointStatus = "reserved" /\ paymentStatus = "cancel");
            pointStatus := "canceled";
        end either;
    end while;
end process;
    
end algorithm; *)

\* これより下は、ここより上に algorithm で書いていた PlusCal のソースコードを、 TLA+ のコードに変換したもの。
\* 変換処理が同じファイル内の下部に追記されるという仕様であるため、こんな感じになっている。
 
\* BEGIN TRANSLATION
\* Label ConfirmOrCancel of process Payment at line 50 col 5 changed to ConfirmOrCancel_
\* Label IdleAndReserveAndConfirmed of process Card at line 103 col 5 changed to IdleAndReserveAndConfirmed_
VARIABLES paymentStatus, cardStatus, pointStatus, pc

(* define statement *)
confirmable == cardStatus \in {"reserved"} /\ pointStatus \in {"reserved"}



subConfirmable ==
        cardStatus \in {"reserved", "confirmed"}
    /\  pointStatus \in {"reserved", "confirmed"}



cancelable  == cardStatus \in {"canceled"} \/ pointStatus \in {"canceled"}




consistency == ~ (
    ( cardStatus \in {"confirmed"} /\ pointStatus \in {"canceled"} )
 \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"confirmed"} )
)




completed   == <>(
    ( cardStatus \in {"confirmed"} /\ pointStatus \in {"confirmed"} )
 \/ ( cardStatus \in {"canceled"} /\ pointStatus \in {"canceled"} )
)


vars == << paymentStatus, cardStatus, pointStatus, pc >>

ProcSet == {"Payment"} \cup {"SubPayment"} \cup {"Card"} \cup {"Point"}

Init == (* Global variables *)
        /\ paymentStatus = "try"
        /\ cardStatus = "idling"
        /\ pointStatus = "idling"
        /\ pc = [self \in ProcSet |-> CASE self = "Payment" -> "ConfirmOrCancel_"
                                        [] self = "SubPayment" -> "ConfirmOrCancel"
                                        [] self = "Card" -> "IdleAndReserveAndConfirmed_"
                                        [] self = "Point" -> "IdleAndReserveAndConfirmed"]

ConfirmOrCancel_ == /\ pc["Payment"] = "ConfirmOrCancel_"
                    /\ \/ /\ confirmable
                          /\ paymentStatus' = "confirm"
                       \/ /\ cancelable
                          /\ paymentStatus' = "cancel"
                    /\ pc' = [pc EXCEPT !["Payment"] = "ServerCrash"]
                    /\ UNCHANGED << cardStatus, pointStatus >>

ServerCrash == /\ pc["Payment"] = "ServerCrash"
               /\ paymentStatus' = "crash"
               /\ pc' = [pc EXCEPT !["Payment"] = "Done"]
               /\ UNCHANGED << cardStatus, pointStatus >>

Payment == ConfirmOrCancel_ \/ ServerCrash

ConfirmOrCancel == /\ pc["SubPayment"] = "ConfirmOrCancel"
                   /\ \/ /\ subConfirmable /\ paymentStatus = "crash"
                         /\ paymentStatus' = "confirm"
                      \/ /\ cancelable /\ paymentStatus = "crash"
                         /\ paymentStatus' = "cancel"
                   /\ pc' = [pc EXCEPT !["SubPayment"] = "Done"]
                   /\ UNCHANGED << cardStatus, pointStatus >>

SubPayment == ConfirmOrCancel

IdleAndReserveAndConfirmed_ == /\ pc["Card"] = "IdleAndReserveAndConfirmed_"
                               /\ IF cardStatus \in {"idling", "reserved" }
                                     THEN /\ \/ /\ cardStatus = "idling"
                                                /\ cardStatus' = "reserved"
                                             \/ /\ cardStatus = "reserved" /\ paymentStatus = "confirm"
                                                /\ cardStatus' = "confirmed"
                                             \/ /\ cardStatus = "idling" \/ (cardStatus = "reserved" /\ paymentStatus = "cancel")
                                                /\ cardStatus' = "canceled"
                                          /\ pc' = [pc EXCEPT !["Card"] = "IdleAndReserveAndConfirmed_"]
                                     ELSE /\ pc' = [pc EXCEPT !["Card"] = "Done"]
                                          /\ UNCHANGED cardStatus
                               /\ UNCHANGED << paymentStatus, pointStatus >>

Card == IdleAndReserveAndConfirmed_

IdleAndReserveAndConfirmed == /\ pc["Point"] = "IdleAndReserveAndConfirmed"
                              /\ IF pointStatus \in {"idling", "reserved" }
                                    THEN /\ \/ /\ pointStatus = "idling"
                                               /\ pointStatus' = "reserved"
                                            \/ /\ pointStatus = "reserved" /\ paymentStatus = "confirm"
                                               /\ pointStatus' = "confirmed"
                                            \/ /\ pointStatus = "idling" \/ (pointStatus = "reserved" /\ paymentStatus = "cancel")
                                               /\ pointStatus' = "canceled"
                                         /\ pc' = [pc EXCEPT !["Point"] = "IdleAndReserveAndConfirmed"]
                                    ELSE /\ pc' = [pc EXCEPT !["Point"] = "Done"]
                                         /\ UNCHANGED pointStatus
                              /\ UNCHANGED << paymentStatus, cardStatus >>

Point == IdleAndReserveAndConfirmed

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Payment \/ SubPayment \/ Card \/ Point
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Payment)
        /\ WF_vars(SubPayment)
        /\ WF_vars(Card)
        /\ WF_vars(Point)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
