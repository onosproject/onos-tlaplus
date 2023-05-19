------------------------------- MODULE Target -------------------------------

INSTANCE Naturals

----

\* An empty constant
CONSTANT Nil

\* The set of possible master nodes
CONSTANT Node

----

\* The target state
VARIABLE target

\* A record of connections between nodes and the target
VARIABLE conn

TypeOK ==
   /\ target.id \in Nat
   /\ \A p \in DOMAIN target.values :
         /\ target.values[p].index \in Nat
         /\ target.values[p].value \in STRING
   /\ target.running \in BOOLEAN 
   /\ \A n \in DOMAIN conn : 
         /\ n \in Node
         /\ conn[n].id \in Nat
         /\ conn[n].connected \in BOOLEAN 

----

(*
This section specifies the behavior of configuration targets.
*)

Start ==
   /\ ~target.running
   /\ target' = [target EXCEPT !.id      = target.id + 1,
                               !.running = TRUE]
   /\ UNCHANGED <<conn>>

Stop ==
   /\ target.running
   /\ target' = [target EXCEPT !.running = FALSE,
                               !.values  = [p \in {} |-> [index |-> 0, value |-> Nil]]]
   /\ conn' = [n \in Node |-> [conn[n] EXCEPT !.connected = FALSE]]

----

(*
This section specifies the behavior of connections to the target.
*)

Connect(n) ==
   /\ ~conn[n].connected
   /\ target.running
   /\ conn' = [conn EXCEPT ![n].id        = conn[n].id + 1,
                           ![n].connected = TRUE]
   /\ UNCHANGED <<target>>

Disconnect(n) ==
   /\ conn[n].connected
   /\ conn' = [conn EXCEPT ![n].connected = FALSE]
   /\ UNCHANGED <<target>>

=============================================================================
