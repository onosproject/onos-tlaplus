------------------------------- MODULE Mastership -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

----

CONSTANTS
   None,
   Node

VARIABLES
   conn,
   target

LOCAL Southbound == INSTANCE Southbound

----

VARIABLE mastership

----

(*
This section models mastership reconciliation.
*)

Reconcile(n) ==
   /\ \/ /\ conn[n].connected
         /\ mastership.master = None
         /\ mastership' = [master |-> n, term |-> mastership.term + 1, conn |-> conn[n].id]
      \/ /\ ~conn[n].connected
         /\ mastership.master = n
         /\ mastership' = [mastership EXCEPT !.master = None]
   /\ UNCHANGED <<conn, target>>

----

Init ==
   /\ mastership = [master |-> None, term |-> 0, conn |-> 0]
   /\ Southbound!Init

Next ==
   \/ \E n \in Node : Reconcile(n)
   \/ /\ Southbound!Next
      /\ UNCHANGED <<mastership>>

=============================================================================
