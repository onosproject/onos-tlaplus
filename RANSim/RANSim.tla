------------------------------- MODULE RANSim -------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty value
CONSTANT Nil

\* Node states
CONSTANT Stopped, Started

\* Connection states
CONSTANT Connecting, Connected, Configuring, Configured

\* The set of E2 node identifiers
CONSTANT E2Node

ASSUME /\ IsFiniteSet(E2Node)
       /\ \A n \in E2Node : n \in STRING

\* A set of RIC node identifiers
CONSTANT RICNode

ASSUME /\ IsFiniteSet(RICNode)
       /\ \A n \in RICNode : n \in STRING

\* The state of the E2 node
VARIABLE state

\* The state of the network
VARIABLE network

\* The primary management connection
VARIABLE mgmtConn

\* The state of E2AP connections
VARIABLE dataConn

\* The set of outstanding transactions
VARIABLE transactions

\* Subscriptions
VARIABLE subs

vars == <<state, network, mgmtConn, dataConn, subs>>

LOCAL E2AP == INSTANCE E2AP WITH conns <- network

----

StartNode(e2Node) ==
   /\ state[e2Node] = Stopped
   /\ state' = [state EXCEPT ![e2Node] = Started]
   /\ UNCHANGED <<network, mgmtConn, dataConn, subs>>

StopNode(e2Node) ==
   /\ state[e2Node] = Started
   /\ state' = [state EXCEPT ![e2Node] = Stopped]
   /\ UNCHANGED <<network, mgmtConn, dataConn, subs>>

----

ReconcileConnection(e2NodeId, ricNodeId) ==
   /\ ricNodeId \in dataConn[e2NodeId]
   /\ \/ /\ dataConn[e2NodeId].state = Connecting
         /\ E2AP!Client(e2NodeId)!Connect(ricNodeId)
         /\ LET newConnId == CHOOSE i \in {conn.id : conn \in network[e2NodeId]} : i \notin {conn.id : conn \in network'[e2NodeId]}
            IN
               /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = dataConn[e2NodeId] @@ (ricNodeId :> [state |-> Connected, conn |-> newConnId])]
               /\ UNCHANGED <<transactions>>
      \/ /\ dataConn[e2NodeId].state # Connecting
         /\ \/ /\ \E conn \in E2AP!Client(e2NodeId)!Connections : 
                     /\ conn.id = dataConn[e2NodeId].conn
                     /\ \/ /\ dataConn[e2NodeId].state = Connecting
                           /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = [
                                             dataConn[e2NodeId] EXCEPT ![ricNodeId].state = Connected]]
                           /\ UNCHANGED <<transactions>>
                        \/ /\ dataConn[e2NodeId].state = Connected
                           /\ Len(transactions[e2NodeId]) < 256
                           /\ LET txId == CHOOSE i \in 0..255 : i \notin DOMAIN transactions[e2NodeId]
                                  req == [txId |-> txId, e2NodeId |-> e2NodeId]
                              IN
                                 /\ E2AP!Client(e2NodeId)!Send!E2NodeConfigurationUpdate(conn, req)
                                 /\ transactions' = [transactions EXCEPT ![e2NodeId] = transactions[e2NodeId] @@ (txId :> req)]
                                 /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = [
                                             dataConn[e2NodeId] EXCEPT ![ricNodeId].state = Configuring]]
                        \/ /\ dataConn[e2NodeId].state = Configuring
                           /\ E2AP!Client(e2NodeId)!Ready(conn)
                           /\ LET res == E2AP!Client(e2NodeId)!Read(conn)
                              IN
                                 /\ E2AP!Client(e2NodeId)!Receive!E2NodeConfigurationUpdateAcknowledge(conn, res)
                                 /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = [
                                             dataConn[e2NodeId] EXCEPT ![ricNodeId].state = Configured]]
                           /\ UNCHANGED <<transactions>>
                        \/ /\ dataConn[e2NodeId].state = Configured
                           /\ UNCHANGED <<dataConn>>
            \/ /\ ~\E conn \in E2AP!Client(e2NodeId)!Connections : conn.id = dataConn[e2NodeId].conn
               /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = [
                                  dataConn[e2NodeId] EXCEPT ![ricNodeId] = [state |-> Connecting, conn |-> Nil]]]
   /\ UNCHANGED <<subs>>

----

Connect(e2NodeId, ricNodeId) ==
   /\ E2AP!Client(e2NodeId)!Connect(ricNodeId)
   /\ UNCHANGED <<state, dataConn, transactions>>

Disconnect(e2NodeId, conn) ==
   /\ E2AP!Client(e2NodeId)!Disconnect(conn)
   /\ UNCHANGED <<state, dataConn, transactions>>

E2Setup(e2NodeId, conn) ==
   /\ ~\E c \in E2AP!Client(e2NodeId)!Connections : c.id = mgmtConn[e2NodeId].connId
   /\ Len(transactions[e2NodeId]) < 256
   /\ LET txId == CHOOSE i \in 0..255 : i \notin DOMAIN transactions
          req == [txId |-> txId, e2NodeId |-> E2Node]
      IN 
         /\ transactions' = transactions @@ (txId :> req)
         /\ E2AP!Client(E2Node)!Send!E2SetupRequest(conn, req)
   /\ UNCHANGED <<mgmtConn, dataConn, subs>>

HandleE2SetupResponse(e2NodeId, conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2SetupResponse(conn, res)
   /\ \/ /\ res.txId \in DOMAIN transactions[e2NodeId]
         /\ mgmtConn' = [mgmtConn EXCEPT ![e2NodeId] = [connId |-> conn.id]]
         /\ transactions' = [transactions EXCEPT ![e2NodeId] = [
                                t \in DOMAIN transactions[e2NodeId] \ {res.txId} |-> transactions[e2NodeId][t]]]
      \/ /\ res.txId \notin transactions[e2NodeId]
         /\ UNCHANGED <<mgmtConn, transactions>>
   /\ UNCHANGED <<dataConn, subs>>

HandleRICSubscriptionRequest(e2NodeId, conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionRequest(conn, req)
   /\ UNCHANGED <<dataConn, subs>>

HandleRICSubscriptionDeleteRequest(e2NodeId, conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionDeleteRequest(conn, req)
   /\ UNCHANGED <<dataConn, subs>>

HandleRICControlRequest(e2NodeId, conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICControlRequest(conn, req)
   /\ E2AP!Client(E2Node)!Reply!RICControlAcknowledge(conn, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<dataConn, subs>>

HandleE2ConnectionUpdate(e2NodeId, conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!E2ConnectionUpdate(conn, req)
   /\ LET add == IF "add" \in DOMAIN req THEN req["add"] ELSE {}
          update == IF "update" \in DOMAIN req THEN req["update"] ELSE {}
          remove == IF "remove" \in DOMAIN req THEN req["remove"] ELSE {}
      IN
         /\ dataConn' = [dataConn EXCEPT ![e2NodeId] = [
                            n \in (DOMAIN dataConn[e2NodeId] \cup add) \ remove |-> 
                               IF n \notin update /\ n \in DOMAIN dataConn THEN
                                  dataConn[n]
                               ELSE
                                  [state |-> Connecting, conn |-> Nil]]]
   /\ UNCHANGED <<subs>>

HandleE2NodeConfigurationUpdateAcknowledge(e2NodeId, conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2NodeConfigurationUpdateAcknowledge(conn, res)
   /\ res.txId \in transactions
   /\ dataConn[conn.dst].state = Configuring
   /\ transactions' = [t \in DOMAIN transactions \ {res.txId} |-> transactions[t]]
   /\ dataConn' = [dataConn EXCEPT ![conn.dst].state = Configured]
   /\ UNCHANGED <<subs>>

HandleRequest(e2NodeId, conn) ==
   /\ \/ E2AP!Client(E2Node)!Handle!RICSubscriptionRequest(conn, LAMBDA c, m: HandleRICSubscriptionRequest(e2NodeId, c, m))
      \/ E2AP!Client(E2Node)!Handle!RICSubscriptionDeleteRequest(conn, LAMBDA c, m: HandleRICSubscriptionDeleteRequest(e2NodeId, c, m))
      \/ E2AP!Client(E2Node)!Handle!RICControlRequest(conn, LAMBDA c, m: HandleRICControlRequest(e2NodeId, c, m))
      \/ E2AP!Client(E2Node)!Handle!E2ConnectionUpdate(conn, LAMBDA c, m: HandleE2ConnectionUpdate(e2NodeId, c, m))
      \/ E2AP!Client(E2Node)!Handle!E2NodeConfigurationUpdateAcknowledge(conn, LAMBDA c, m: HandleE2NodeConfigurationUpdateAcknowledge(e2NodeId, c, m))
   /\ UNCHANGED <<state>>

----

Init ==
   /\ E2AP!Init
   /\ state = [n \in E2Node |-> Stopped]
   /\ mgmtConn = [n \in E2Node |-> [connId |-> Nil]]
   /\ dataConn = [n \in E2Node |-> [c \in {} |-> [connId |-> Nil]]]
   /\ transactions = [n \in E2Node |-> [t \in {} |-> [id |-> Nil]]]
   /\ subs = [n \in E2Node |-> [i \in {} |-> [id |-> Nil]]]

Next ==
   \/ \E e2NodeId \in E2Node : 
         StartNode(e2NodeId)
   \/ \E e2NodeId \in E2Node : 
         StopNode(e2NodeId)
   \/ \E e2NodeId \in E2Node, ricNodeId \in RICNode : 
         Connect(e2NodeId, ricNodeId)
   \/ \E e2NodeId \in E2Node, ricNodeId \in RICNode : 
         Disconnect(e2NodeId, ricNodeId)
   \/ \E e2NodeId \in E2Node :
         \E conn \in E2AP!Client(e2NodeId)!Connections :
            E2Setup(e2NodeId, conn)
   \/ \E e2NodeId \in E2Node :
         \E conn \in E2AP!Client(e2NodeId)!Connections :
            HandleRequest(e2NodeId, conn)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 15:04:44 PDT 2021 by jordanhalterman
\* Created Tue Sep 21 13:27:29 PDT 2021 by jordanhalterman
