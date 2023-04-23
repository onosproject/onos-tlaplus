----------------------------- MODULE Southbound -----------------------------

EXTENDS Target

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* The set of all nodes
CONSTANT Node

\* A connected state
CONSTANT Connected

\* A disconnected state
CONSTANT Disconnected

\* The state of the connection to the target
VARIABLE conn

----

(*
This section models target states.
*)

Connect(n) ==
   /\ conn[n].state # Connected
   /\ target.state = Alive
   /\ conn' = [conn EXCEPT ![n].id    = conn[n].id + 1,
                           ![n].state = Connected]
   /\ UNCHANGED <<target>>

Disconnect(n) ==
   /\ conn[n].state = Connected
   /\ conn' = [conn EXCEPT ![n].state = Disconnected]
   /\ UNCHANGED <<target>>

----

InitSouthbound ==
   /\ conn = [n \in Node |-> [id |-> 0, state |-> Disconnected]]

NextSouthbound ==
   \/ \E n \in Node : Connect(n)
   \/ \E n \in Node : Disconnect(n)

----

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \in STRING

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
