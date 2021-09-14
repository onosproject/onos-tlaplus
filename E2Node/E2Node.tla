------------------------------- MODULE E2Node -------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty value
CONSTANT Nil

\* Node states
CONSTANT Stopped, Started

\* A set of E2 node identifiers
CONSTANT E2Nodes

ASSUME /\ IsFiniteSet(E2Nodes)
       /\ \A n \in E2Nodes : n \in STRING

\* A set of E2T node identifiers
CONSTANT E2TNodes

ASSUME /\ IsFiniteSet(E2TNodes)
       /\ \A n \in E2TNodes : n \in STRING

\* A mapping of node states
VARIABLE nodes

\* Connections to E2 nodes
VARIABLE conns

vars == <<nodes, conns>>

LOCAL E2AP == INSTANCE E2AP

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

SendE2SetupRequest(n, c) ==
   /\ UNCHANGED <<nodes>>

HandleE2SetupResponse(n, c, r) ==
   /\ UNCHANGED <<nodes>>

HandleRICSusbcriptionRequest(n, c, r) ==
   /\ UNCHANGED <<nodes>>

HandleRICSubscriptionDeleteRequest(n, c, r) ==
   /\ UNCHANGED <<nodes>>

HandleRICControlRequest(n, c, r) ==
   /\ E2AP!E2Node!Reply!RICControlResponse(c, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<nodes>>

HandleRequest(n, c) ==
   /\ \/ E2AP!E2Node!Handle!RICSusbcriptionRequest(c, LAMBDA m : HandleRICSusbcriptionRequest(n, c, m))
      \/ E2AP!E2Node!Handle!RICSubscriptionDeleteRequest(c, LAMBDA m : HandleRICSubscriptionDeleteRequest(n, c, m))
      \/ E2AP!E2Node!Handle!RICControlRequest(c, LAMBDA m : HandleRICControlRequest(n, c, m))
   /\ UNCHANGED <<nodes>>

----

Init ==
   /\ E2AP!Init

Next ==
   \/ \E n \in E2Nodes : StartNode(n)
   \/ \E n \in E2Nodes : StopNode(n)
   \/ \E n \in E2Nodes, t \in E2TNodes : E2AP!E2Node!Connect(n, t)
   \/ \E c \in E2AP!Connections : E2AP!E2Node!Disconnect(c)
   \/ \E n \in E2Nodes, c \in E2AP!Connections : SendE2SetupRequest(n, c)
   \/ \E n \in E2TNodes, c \in E2AP!Connections : HandleRequest(n, c)

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 19:43:18 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 15:18:28 PDT 2021 by jordanhalterman
