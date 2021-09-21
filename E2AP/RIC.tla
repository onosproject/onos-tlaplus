-------------------------------- MODULE RIC --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty value
CONSTANT Nil

\* Node states
CONSTANT Stopped, Started

\* A set of RIC node identifiers
CONSTANT RICNode

ASSUME /\ IsFiniteSet(RICNode)
       /\ \A n \in RICNode : n \in STRING

\* A mapping of node states
VARIABLE state

\* Network state
VARIABLE net

\* A store of E2 node states
VARIABLE nodes

vars == <<state, net, nodes>>

LOCAL E2AP == INSTANCE E2AP WITH conns <- net

----

StartNode(n) ==
   /\ state[n] = Stopped
   /\ state' = [nodes EXCEPT ![n] = Started]
   /\ UNCHANGED <<net, nodes>>

StopNode(n) ==
   /\ state[n] = Started
   /\ state' = [nodes EXCEPT ![n] = Stopped]
   /\ UNCHANGED <<net, nodes>>

----

HandleE2SetupRequest(node, conn, res) ==
   /\ E2AP!RIC(node)!Reply!E2SetupResponse(conn, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<state>>

HandleRICControlResponse(node, conn, res) ==
   /\ UNCHANGED <<state>>

HandleRICSubscriptionResponse(node, conn, res) ==
   /\ UNCHANGED <<state>>

HandleRICSubscriptionDeleteResponse(node, conn, res) ==
   /\ UNCHANGED <<state>>

HandleRICIndication(node, conn, res) ==
   /\ UNCHANGED <<state>>

HandleE2NodeConfigurationUpdate(node, conn, req) ==
   /\ UNCHANGED <<state>>

HandleRequest(node, conn) ==
   /\ \/ E2AP!RIC(node)!Handle!E2SetupRequest(conn, LAMBDA m : HandleE2SetupRequest(node, conn, m))
      \/ E2AP!RIC(node)!Handle!RICControlResponse(conn, LAMBDA m : HandleRICControlResponse(node, conn, m))
      \/ E2AP!RIC(node)!Handle!RICSubscriptionResponse(conn, LAMBDA m : HandleRICSubscriptionResponse(node, conn, m))
      \/ E2AP!RIC(node)!Handle!RICSubscriptionDeleteResponse(conn, LAMBDA m : HandleRICSubscriptionDeleteResponse(node, conn, m))
      \/ E2AP!RIC(node)!Handle!RICIndication(conn, LAMBDA m : HandleRICIndication(node, conn, m))
      \/ E2AP!RIC(node)!Handle!E2NodeConfigurationUpdate(conn, LAMBDA m : HandleE2NodeConfigurationUpdate(node, conn, m))
   /\ UNCHANGED <<nodes>>

----

Init ==
   /\ E2AP!Init
   /\ state = [n \in RICNode |-> Stopped]
   /\ nodes = [n \in {} |-> [id |-> Nil]]

Next ==
   \/ \E node \in RICNode : StartNode(node)
   \/ \E node \in RICNode : StopNode(node)
   \/ \E node \in RICNode : \E conn \in E2AP!RIC(node)!Connections : HandleRequest(node, conn)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 06:07:29 PDT 2021 by jordanhalterman
\* Created Tue Sep 21 02:14:49 PDT 2021 by jordanhalterman
