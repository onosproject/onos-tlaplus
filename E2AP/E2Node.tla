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

\* The state of E2AP connections
VARIABLE conns

\* Subscriptions
VARIABLE subs

vars == <<state, network, conns, subs>>

LOCAL E2AP == INSTANCE E2AP WITH conns <- network

----

StartNode ==
   /\ state = Stopped
   /\ state' = Started
   /\ UNCHANGED <<network, conns, subs>>

StopNode ==
   /\ state = Started
   /\ state' = Stopped
   /\ UNCHANGED <<network, conns, subs>>

----

SendE2SetupRequest(conn) ==
   /\ UNCHANGED <<conns, subs>>

HandleE2SetupResponse(conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2SetupResponse(conn, res)
   /\ UNCHANGED <<conns, subs>>

HandleRICSubscriptionRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionRequest(conn, req)
   /\ UNCHANGED <<conns, subs>>

HandleRICSubscriptionDeleteRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICSubscriptionDeleteRequest(conn, req)
   /\ UNCHANGED <<conns, subs>>

HandleRICControlRequest(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!RICControlRequest(conn, req)
   /\ E2AP!Client(E2Node)!Reply!RICControlAcknowledge(conn, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<conns, subs>>

HandleE2ConnectionUpdate(conn, req) ==
   /\ E2AP!Client(E2Node)!Receive!E2ConnectionUpdate(conn, req)
   /\ UNCHANGED <<subs>>

HandleE2NodeConfigurationUpdateAcknowledge(conn, res) ==
   /\ E2AP!Client(E2Node)!Receive!E2NodeConfigurationUpdateAcknowledge(conn, res)
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
   /\ conns = [c \in {} |-> Nil]
   /\ subs = [i \in {} |-> [id |-> Nil]]

Next ==
   \/ StartNode
   \/ StopNode
   \/ \E node \in RIC : E2AP!Client(E2Node)!Connect(node)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : E2AP!Client(E2Node)!Disconnect(conn)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : SendE2SetupRequest(conn)
   \/ \E conn \in E2AP!Client(E2Node)!Connections : HandleRequest(conn)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 09:35:51 PDT 2021 by jordanhalterman
\* Created Tue Sep 21 02:14:57 PDT 2021 by jordanhalterman
