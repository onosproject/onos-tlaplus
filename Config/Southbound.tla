----------------------------- MODULE Southbound -----------------------------

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* A record of target states
VARIABLE target

\* The set of all nodes
CONSTANT Nodes

\* The state of nodes
VARIABLE node

----

(*
This section models node and target states.
*)

Start ==
   /\ ~target.running
   /\ target' = [target EXCEPT !.incarnation = target.incarnation + 1,
                               !.running     = TRUE]
   /\ UNCHANGED <<node>>

Stop ==
   /\ target.running
   /\ target' = [target EXCEPT !.running  = FALSE,
                               !.values = [p \in {} |-> [value |-> Nil]]]
   /\ UNCHANGED <<node>>

Connect(n) ==
   /\ ~node[n].connected
   /\ target.running
   /\ node' = [node EXCEPT ![n].target      = target.incarnation,
                           ![n].incarnation = node[n].incarnation + 1,
                           ![n].connected   = TRUE]
   /\ UNCHANGED <<target>>

Disconnect(n) ==
   /\ node[n].connected
   /\ node' = [node EXCEPT ![n].connected = FALSE]
   /\ UNCHANGED <<target>>

----

InitSouthbound ==
   /\ target = [incarnation |-> 0, 
                running     |-> FALSE,
                values      |-> [p \in {} |-> [value |-> Nil]]]
   /\ node = [n \in Nodes |-> [target |-> 0, incarnation |-> 0, connected |-> FALSE]]

NextSouthbound ==
   \/ Start
   \/ Stop
   \/ \E n \in Nodes : Connect(n)
   \/ \E n \in Nodes : Disconnect(n)

----

ASSUME /\ IsFiniteSet(Nodes) 
       /\ \A n \in Nodes : 
             /\ n \in STRING

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
