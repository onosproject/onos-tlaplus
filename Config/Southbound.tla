------------------------------- MODULE Southbound -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT None

ASSUME None \in STRING

CONSTANT Node

ASSUME \A n \in Node : n \in STRING

VARIABLE conn

VARIABLE target

----

(*
This section models configuration target.
*)

StartTarget ==
   /\ ~target.running
   /\ target' = [target EXCEPT !.id      = target.id + 1,
                               !.running = TRUE]
   /\ UNCHANGED <<conn>>

StopTarget ==
   /\ target.running
   /\ target' = [target EXCEPT !.running = FALSE,
                               !.values  = [p \in {} |-> [value |-> None]]]
   /\ conn' = [n \in Node |-> [conn[n] EXCEPT !.connected = FALSE]]

----

(*
This section models nodes connection to the configuration target.
*)

ConnectNode(n) ==
   /\ ~conn[n].connected
   /\ target.running
   /\ conn' = [conn EXCEPT ![n].id        = conn[n].id + 1,
                           ![n].connected = TRUE]
   /\ UNCHANGED <<target>>

DisconnectNode(n) ==
   /\ conn[n].connected
   /\ conn' = [conn EXCEPT ![n].connected = FALSE]
   /\ UNCHANGED <<target>>

----

Init ==
   /\ conn = [n \in Node |-> [id |-> 0, connected |-> FALSE]]
   /\ target = [
         id      |-> 0, 
         values  |-> [p \in {} |-> [index |-> 0, value |-> None]], 
         running |-> FALSE]

Next ==
   \/ \E n \in Node :
         \/ ConnectNode(n)
         \/ DisconnectNode(n)
   \/ StartTarget
   \/ StopTarget

=============================================================================
