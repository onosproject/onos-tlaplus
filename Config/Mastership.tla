----------------------------- MODULE Mastership -----------------------------

EXTENDS Southbound

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT LogMastership

ASSUME LogMastership \in BOOLEAN 

\* A record of target masterships
VARIABLE mastership

LOCAL CurrentState ==
   [nodes      |-> node,
    mastership |-> mastership]

LOCAL SuccessorState ==
   [nodes      |-> node',
    mastership |-> mastership']

LOCAL Log == INSTANCE Log WITH
   File           <- "Mastership.log",
   CurrentState   <- CurrentState,
   SuccessorState <- SuccessorState,
   Enabled        <- LogMastership

----

(*
This section models mastership reconciliation.
*)

ReconcileMastership(n) ==
   /\ \/ /\ node[n].connected
         /\ mastership.master = Nil
         /\ mastership' = [master |-> n, term |-> mastership.term + 1, conn |-> node[n].incarnation]
      \/ /\ ~node[n].connected
         /\ mastership.master = n
         /\ mastership' = [mastership EXCEPT !.master = Nil]
   /\ UNCHANGED <<node, target>>

----

(*
Formal specification, constraints, and theorems.
*)

InitMastership ==
   /\ Log!Init
   /\ mastership = [master |-> Nil, term |-> 0, conn |-> 0]

NextMastership == 
   \/ \E n \in Nodes :
         Log!Action(ReconcileMastership(n), [node |-> n])

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
