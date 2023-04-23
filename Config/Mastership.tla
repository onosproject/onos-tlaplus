----------------------------- MODULE Mastership -----------------------------

EXTENDS Southbound

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* The set of all nodes
CONSTANT Node

\* A record of target masterships
VARIABLE mastership

LOCAL InitState ==
   [conn        |-> conn,
    masterships |-> mastership]

LOCAL NextState ==
   [conn        |-> conn',
    masterships |-> mastership']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Mastership",
   InitState <- InitState,
   NextState <- NextState

----

(*
This section models mastership reconciliation.
*)

ReconcileMastership(n) ==
   /\ \/ /\ conn.state = Connected
         /\ mastership.master # n
         /\ mastership' = [master |-> n, term |-> mastership.term + 1]
      \/ /\ conn.state = Disconnected
         /\ mastership.master # Nil
         /\ mastership' = [mastership EXCEPT !.master = Nil]
   /\ UNCHANGED <<conn, target>>

----

(*
Formal specification, constraints, and theorems.
*)

InitMastership ==
   /\ mastership = [master |-> Nil, term |-> 0]

NextMastership == 
   \/ \E n \in Node :
         Trace!Step(ReconcileMastership(n), [node |-> n])

----

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \in STRING

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
