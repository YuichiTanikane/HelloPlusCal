---- MODULE Transfer ----
EXTENDS Naturals, TLC
(* https://learntla.com/introduction/example/ を一通りやったソース *)
(* --algorithm Transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account;

process Transfer = 1 (* ← ここを Transfer \in 1..2 にして複数プロセスにするとエラーが発生する *)
  variable money \in 1..20;
begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
end process

end algorithm *)

\* ここから下は自動生成されたもの。
\* BEGIN TRANSLATION
\* Label Transfer of process Transfer at line 12 col 3 changed to Transfer_
VARIABLES alice_account, bob_account, account_total, pc, money

vars == << alice_account, bob_account, account_total, pc, money >>

ProcSet == {1}

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ account_total = alice_account + bob_account
        (* Process Transfer *)
        /\ money \in 1..20
        /\ pc = [self \in ProcSet |-> "Transfer_"]

Transfer_ == /\ pc[1] = "Transfer_"
             /\ IF alice_account >= money
                   THEN /\ pc' = [pc EXCEPT ![1] = "A"]
                   ELSE /\ pc' = [pc EXCEPT ![1] = "C"]
             /\ UNCHANGED << alice_account, bob_account, account_total, money >>

A == /\ pc[1] = "A"
     /\ alice_account' = alice_account - money
     /\ bob_account' = bob_account + money
     /\ pc' = [pc EXCEPT ![1] = "C"]
     /\ UNCHANGED << account_total, money >>

C == /\ pc[1] = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 16, column 4.")
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << alice_account, bob_account, account_total, money >>

Transfer == Transfer_ \/ A \/ C

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Transfer
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

====
