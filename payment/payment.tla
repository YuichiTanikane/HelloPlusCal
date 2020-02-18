---- MODULE payment ----
EXTENDS Naturals, TLC
(* --algorithm payment
variables
    paymentStatus = "try",
    cardStatus = "idling",
    pointStatus = "idling";

define 
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
end define;

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

fair process SubPayment = "SubPayment"
begin
    ConfirmOrCancel:
    either        
        await subConfirmable /\ paymentStatus = "crash";
        paymentStatus := "confirm";
    or
        await cancelable /\ paymentStatus = "crash";
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
\* Label ConfirmOrCancel of process Payment at line 28 col 5 changed to ConfirmOrCancel_
\* Label IdleAndReserveAndConfirmed of process Card at line 54 col 5 changed to IdleAndReserveAndConfirmed_
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
