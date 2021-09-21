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

\* Connection states
CONSTANT Connecting, Connected, Configuring, Configured

\* The E2 node identifier
CONSTANT E2Node

\* A set of RIC node identifiers
CONSTANT RIC

ASSUME /\ IsFiniteSet(RIC)
       /\ \A n \in RIC : n \in STRING
       
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

StartNode ==
   /\ state = Stopped
   /\ state' = Started
   /\ UNCHANGED <<network, mgmtConn, dataConn, subs>>

StopNode ==
   /\ state = Started
   /\ state' = Stopped
   /\ UNCHANGED <<network, mgmtConn, dataConn, subs>>

----

ConnectManagement(node) ==
   /\ ~\E conn \in E2AP!Client(E2Node)!Connections : conn.dst = node
   /\ E2AP!Client(E2Node)!Connect(node)
   /\ UNCHANGED <<state, mgmtConn, dataConn, subs>>

DisconnectManagement(conn) ==
   /\ E2AP!Client(E2Node)!Disconnect(conn)
   /\ UNCHANGED <<state, mgmtConn, dataConn, subs>>

ConnectDataConn(node) ==
   /\ dataConn[node].state = Connecting
   /\ E2AP!Client(E2Node)!Connect(node)
   /\ dataConn' = [dataConn EXCEPT ![node].state = Connected]
   /\ UNCHANGED <<state, mgmtConn, dataConn, subs>>

ConfigureDataConn(node) ==
   /\ dataConn[node].state = Connected
   /\ \E conn \in E2AP!Client(E2Node)!Connections : conn.dst = node
   /\ LET conn == CHOOSE c \in E2AP!Client(E2Node)!Connections : c.dst = node
          txId == CHOOSE i \in 0..255 : i \notin DOMAIN transactions
          req == [txId |-> txId, e2NodeId |-> E2Node]
      IN
         /\ transactions' = transactions @@ (txId :> req)
         /\ dataConn' = [dataConn EXCEPT ![node].state = Configuring]
         /\ E2AP!Client(E2Node)!Send!E2NodeConfigurationUpdate(conn, req)
   /\ UNCHANGED <<state, mgmtConn, subs>>

E2Setup(conn) ==
   /\ Len(transactions) < 256
   /\ LET txId == CHOOSE i \in 0..255 : i \notin DOMAIN transactions
          req == [txId |-> txId, e2NodeId |-> E2Node]
      IN 
         /\ transactions' = transactions @@ (txId :> req)
         /\ E2AP!Client(E2Node)!Send!E2SetupRequest(conn, req)
   /\ UNCHANGED <<mgmtConn, dataConn, subs>>

HandleE2SetupResponse(conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2SetupResponse(conn, res)
   /\ \/ /\ res.txId \in transactions
         /\ mgmtConn' = conn
         /\ transactions' = [t \in DOMAIN transactions \ {res.txId} |-> transactions[t]]
      \/ /\ res.txId \notin transactions
         /\ UNCHANGED <<transactions>>
   /\ UNCHANGED <<dataConn, subs>>

HandleRICSubscriptionRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionRequest(conn, req)
   /\ UNCHANGED <<dataConn, subs>>

HandleRICSubscriptionDeleteRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionDeleteRequest(conn, req)
   /\ UNCHANGED <<dataConn, subs>>

HandleRICControlRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICControlRequest(conn, req)
   /\ E2AP!Client(E2Node)!Reply!RICControlAcknowledge(conn, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<dataConn, subs>>

HandleE2ConnectionUpdate(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!E2ConnectionUpdate(conn, req)
   /\ LET add == IF "add" \in DOMAIN req THEN req["add"] ELSE {}
          update == IF "update" \in DOMAIN req THEN req["update"] ELSE {}
          remove == IF "remove" \in DOMAIN req THEN req["remove"] ELSE {}
      IN
         /\ dataConn' = [n \in (DOMAIN dataConn \cup add) \cap remove |-> 
                            IF n \in DOMAIN dataConn THEN
                               dataConn[n]
                            ELSE
                               [state |-> Connecting]]
   /\ UNCHANGED <<subs>>

HandleE2NodeConfigurationUpdateAcknowledge(conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2NodeConfigurationUpdateAcknowledge(conn, res)
   /\ res.txId \in transactions
   /\ dataConn[conn.dst].state = Configuring
   /\ transactions' = [t \in DOMAIN transactions \ {res.txId} |-> transactions[t]]
   /\ dataConn' = [dataConn EXCEPT ![conn.dst].state = Configured]
   /\ UNCHANGED <<subs>>

HandleRequest(c) ==
   /\ \/ E2AP!Client(E2Node)!Handle!RICSubscriptionRequest(c, HandleRICSubscriptionRequest)
      \/ E2AP!Client(E2Node)!Handle!RICSubscriptionDeleteRequest(c, HandleRICSubscriptionDeleteRequest)
      \/ E2AP!Client(E2Node)!Handle!RICControlRequest(c, HandleRICControlRequest)
      \/ E2AP!Client(E2Node)!Handle!E2ConnectionUpdate(c, HandleE2ConnectionUpdate)
      \/ E2AP!Client(E2Node)!Handle!E2NodeConfigurationUpdateAcknowledge(c, HandleE2NodeConfigurationUpdateAcknowledge)
   /\ UNCHANGED <<state>>

----

Init ==
   /\ E2AP!Init
   /\ state = Stopped
   /\ mgmtConn = [connId |-> Nil]
   /\ dataConn = [c \in {} |-> [connId |-> Nil]]
   /\ transactions = [t \in {} |-> [id |-> Nil]]
   /\ subs = [i \in {} |-> [id |-> Nil]]

Next ==
   \/ StartNode
   \/ StopNode
   \/ \E node \in RIC : E2AP!Client(E2Node)!Connect(node)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : E2AP!Client(E2Node)!Disconnect(conn)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : E2Setup(conn)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : HandleRequest(conn)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 13:36:09 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 15:18:28 PDT 2021 by jordanhalterman
