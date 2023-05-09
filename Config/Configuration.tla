------------------------------- MODULE Configuration -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

----

CONSTANTS
   None,
   Node

VARIABLES
   mastership,
   conn,
   target

LOCAL Mastership == INSTANCE Mastership

----

(*
This section specifies constant parameters for the model.
*)

CONSTANTS
   Synchronizing, 
   Synchronized

VARIABLE configuration

----

(*
This section models configuration reconciliation.
*)

Reconcile(n) ==
   /\ mastership.master = n
   /\ \/ /\ configuration.status = Synchronized
         /\ configuration.applied.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.status = Synchronizing]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.status = Synchronizing
         /\ configuration.applied.term < mastership.term
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.applied.values]
         /\ configuration' = [configuration EXCEPT !.applied.term   = mastership.term,
                                                   !.applied.target = target.id,
                                                   !.status         = Synchronized]
   /\ UNCHANGED <<mastership, conn>>

----

Init ==
   /\ configuration = [
         committed |-> [
            values |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         applied |-> [
            term   |-> 0,
            target |-> 0,
            values |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         status  |-> Synchronizing]
   /\ Mastership!Init

Next ==
   \/ \E n \in Node : Reconcile(n)
   \/ /\ Mastership!Next
      /\ UNCHANGED <<configuration>>

=============================================================================
