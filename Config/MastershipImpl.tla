------------------------------- MODULE MastershipImpl -------------------------------

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

CONSTANT LogEnabled

VARIABLE mastership

LOCAL Log == INSTANCE Log WITH
   File      <- "Mastership.log",
   CurrState <- [
      target        |-> target,
      mastership    |-> mastership,
      conns         |-> conn],
   SuccState <- [
      target        |-> target',
      mastership    |-> mastership',
      conns         |-> conn'],
   Enabled   <- LogEnabled

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
   \/ \E n \in Node : Log!Action(Reconcile(n), [node |-> n])
   \/ /\ Southbound!Next
      /\ UNCHANGED <<mastership>>

=============================================================================
