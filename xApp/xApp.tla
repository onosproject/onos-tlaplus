-------------------------------- MODULE xApp --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty value
CONSTANT Nil

\* Node states
CONSTANT Stopped, Started

\* A set of E2T node identifiers
CONSTANT E2TNodes

ASSUME /\ IsFiniteSet(E2TNodes)
       /\ \A n \in E2TNodes : n \in STRING

\* A mapping of node states
VARIABLE nodes

\* Connections to E2T nodes
VARIABLE conns

vars == <<nodes, conns>>

LOCAL E2T == INSTANCE E2TService

----

StartNode(n) ==
   /\ nodes[n] = Stopped
   /\ nodes' = [nodes EXCEPT ![n] = Started]
   /\ UNCHANGED <<conns>>

StopNode(n) ==
   /\ nodes[n] = Started
   /\ nodes' = [nodes EXCEPT ![n] = Stopped]
   /\ UNCHANGED <<conns>>

----

SendControlRequest(n, c) ==
   /\ UNCHANGED <<nodes>>

HandleControlResponse(n, c, r) ==
   /\ UNCHANGED <<nodes>>

SendSubscribeRequest(n, c) ==
   /\ UNCHANGED <<nodes>>

HandleSubscribeResponse(n, c, r) ==
   /\ UNCHANGED <<nodes>>

SendUnsubscribeRequest(n, c) ==
   /\ UNCHANGED <<nodes>>

HandleUnsubscribeResponse(n, c, r) ==
   /\ UNCHANGED <<nodes>>

HandleE2TResponse(n, c) ==
   /\ \/ E2T!Client!Handle!SubscribeResponse(c, LAMBDA m : HandleSubscribeResponse(n, c, m))
      \/ E2T!Client!Handle!UnsubscribeResponse(c, LAMBDA m : HandleUnsubscribeResponse(n, c, m))
      \/ E2T!Client!Handle!ControlResponse(c, LAMBDA m : HandleControlResponse(n, c, m))
   /\ UNCHANGED <<nodes>>

----

Init ==
   /\ E2T!Init
   /\ nodes = [n \in E2TNodes |-> Stopped]

Next ==
   \/ \E n \in E2TNodes : StartNode(n)
   \/ \E n \in E2TNodes : StopNode(n)
   \/ \E n \in E2TNodes, c \in E2T!Connections : SendSubscribeRequest(n, c)
   \/ \E n \in E2TNodes, c \in E2T!Connections : SendUnsubscribeRequest(n, c)
   \/ \E n \in E2TNodes, c \in E2T!Connections : SendControlRequest(n, c)
   \/ \E n \in E2TNodes, c \in E2T!Connections : HandleE2TResponse(n, c)

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 19:33:23 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 15:19:07 PDT 2021 by jordanhalterman
