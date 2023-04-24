----------------------------- MODULE Mastership -----------------------------

EXTENDS Southbound

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT TraceMastership

\* A record of target masterships
VARIABLE mastership

LOCAL InitState ==
   [nodes       |-> node,
    masterships |-> mastership]

LOCAL NextState ==
   [nodes       |-> node',
    masterships |-> mastership']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Mastership",
   InitState <- InitState,
   NextState <- NextState,
   Enabled   <- TraceMastership

----

(*
This section models mastership reconciliation.
*)

ReconcileMastership(n) ==
   /\ \/ /\ node[n].connected
         /\ mastership.master = Nil
         /\ mastership' = [master |-> n, term |-> mastership.term + 1]
      \/ /\ ~node[n].connected
         /\ mastership.master = n
         /\ mastership' = [mastership EXCEPT !.master = Nil]
   /\ UNCHANGED <<node, target>>

----

(*
Formal specification, constraints, and theorems.
*)

InitMastership ==
   /\ mastership = [master |-> Nil, term |-> 0]

NextMastership == 
   \/ \E n \in Node :
         Trace!Step(ReconcileMastership(n), [node |-> n])

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
