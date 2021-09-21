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
VARIABLE network

\* A global store of E2 node states
VARIABLE nodes

\* A set of E2 node management connections
VARIABLE mgmtConn

\* A transaction ID counter
VARIABLE txId

\* A set of E2 node data connections
VARIABLE dataConn

\* A request ID counter
VARIABLE reqId

vars == <<state, network, nodes, mgmtConn, txId, dataConn, reqId>>

LOCAL E2AP == INSTANCE E2AP WITH conns <- network

----

StartNode(node) ==
   /\ state[node] = Stopped
   /\ E2AP!Server(node)!Start
   /\ state' = [nodes EXCEPT ![node] = Started]
   /\ UNCHANGED <<nodes>>

StopNode(node) ==
   /\ state[node] = Started
   /\ E2AP!Server(node)!Stop
   /\ state' = [nodes EXCEPT ![node] = Stopped]
   /\ UNCHANGED <<network, nodes>>

----

HandleE2SetupRequest(node, conn, req) ==
   /\ E2AP!Server(node)!Receive!E2SetupRequest(conn, req)
   /\ \/ /\ conn.id \notin DOMAIN mgmtConn
         /\ mgmtConn' = mgmtConn @@ (conn.id :> conn)
      \/ /\ conn.id \in DOMAIN mgmtConn
         /\ UNCHANGED <<mgmtConn>>
   /\ \/ /\ req.e2NodeId \notin DOMAIN nodes
         /\ nodes' = nodes @@ (req.e2NodeId :> [e2NodeId |-> req.e2NodeId, 
                                                sms      |-> req.sms])
      \/ /\ req.e2NodeId \in DOMAIN nodes
         /\ nodes' = [nodes EXCEPT ![req.e2NodeId] = [
                         nodes[req.e2NodeId] EXCEPT !.sms = req.sms]]
   /\ E2AP!Server(node)!Reply!E2SetupResponse(conn, [txId |-> req.txId])
   /\ UNCHANGED <<state, txId, reqId>>

HandleRICControlResponse(node, conn, res) ==
   /\ E2AP!Server(node)!Receive!RICControlResponse(conn, res)
   /\ UNCHANGED <<state>>

HandleRICSubscriptionResponse(node, conn, res) ==
   /\ E2AP!Server(node)!Receive!RICSubscriptionResponse(conn, res)
   /\ UNCHANGED <<state>>

HandleRICSubscriptionDeleteResponse(node, conn, res) ==
   /\ E2AP!Server(node)!Receive!RICSubscriptionDeleteResponse(conn, res)
   /\ UNCHANGED <<state>>

HandleRICIndication(node, conn, res) ==
   /\ E2AP!Server(node)!Receive!RICIndication(conn, res)
   /\ UNCHANGED <<state>>

E2ConnectionUpdate(node) ==
   /\ node \in DOMAIN mgmtConn
   /\ E2AP!Server(node)!Send!E2ConnectionUpdate(mgmtConn[node], [txId |-> txId[node] + 1])
   /\ txId' = [txId EXCEPT ![node] = txId[node] + 1]
   /\ UNCHANGED <<state>>

HandleE2NodeConfigurationUpdate(node, conn, req) ==
   /\ E2AP!Server(node)!Receive!E2NodeConfigurationUpdate(conn, req)
   /\ E2AP!Server(node)!Reply!E2NodeConfigurationUpdateAcknowledge(conn, [txId |-> req.txId])
   /\ UNCHANGED <<state>>

----

Init ==
   /\ E2AP!Init
   /\ state = [n \in RICNode |-> Stopped]
   /\ nodes = [n \in {} |-> [id |-> Nil]]
   /\ mgmtConn = [n \in {} |-> Nil]
   /\ txId = [n \in RICNode |-> 0]
   /\ dataConn = [n \in {} |-> Nil]
   /\ reqId = [n \in RICNode |-> 0]

Next ==
   \/ \E node \in RICNode : StartNode(node)
   \/ \E node \in RICNode : StopNode(node)
   \/ \E node \in RICNode : E2ConnectionUpdate(node)
   \/ \E node \in RICNode : 
         \E conn \in E2AP!Server(node)!Connections : 
            \/ E2AP!Server(node)!Handle!E2SetupRequest(conn, LAMBDA c, m : HandleE2SetupRequest(node, conn, m))
            \/ E2AP!Server(node)!Handle!RICControlResponse(conn, LAMBDA c, m : HandleRICControlResponse(node, conn, m))
            \/ E2AP!Server(node)!Handle!RICSubscriptionResponse(conn, LAMBDA c, m : HandleRICSubscriptionResponse(node, conn, m))
            \/ E2AP!Server(node)!Handle!RICSubscriptionDeleteResponse(conn, LAMBDA c, m : HandleRICSubscriptionDeleteResponse(node, conn, m))
            \/ E2AP!Server(node)!Handle!RICIndication(conn, LAMBDA c, m : HandleRICIndication(node, conn, m))
            \/ E2AP!Server(node)!Handle!E2NodeConfigurationUpdate(conn, LAMBDA c, m : HandleE2NodeConfigurationUpdate(node, conn, m))

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 13:32:08 PDT 2021 by jordanhalterman
\* Created Tue Sep 21 13:26:28 PDT 2021 by jordanhalterman
