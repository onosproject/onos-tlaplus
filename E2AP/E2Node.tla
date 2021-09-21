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

SendE2SetupRequest(c) ==
   /\ UNCHANGED <<conns, subs>>

HandleE2SetupResponse(c, r) ==
   /\ UNCHANGED <<conns, subs>>

HandleRICSusbcriptionRequest(c, r) ==
   /\ UNCHANGED <<conns, subs>>

HandleRICSubscriptionDeleteRequest(c, r) ==
   /\ UNCHANGED <<conns, subs>>

HandleRICControlRequest(c, r) ==
   /\ E2AP!Client(E2Node)!Reply!RICControlAcknowledge(c, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<conns, subs>>

HandleE2ConnectionUpdate(c, r) ==
   /\ UNCHANGED <<subs>>

HandleE2NodeConfigurationUpdateAcknowledge(c, r) ==
   /\ UNCHANGED <<subs>>

HandleRequest(c) ==
   /\ \/ E2AP!Client(E2Node)!Handle!RICSusbcriptionRequest(c, HandleRICSusbcriptionRequest)
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
   \/ \E t \in RIC : E2AP!Client(E2Node)!Connect(t)
   \/ \E c \in E2AP!Client(E2Node)!Connections : E2AP!Client(E2Node)!Disconnect(c)
   \/ \E c \in E2AP!Client(E2Node)!Connections : SendE2SetupRequest(c)
   \/ \E c \in E2AP!Client(E2Node)!Connections : HandleRequest(c)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 08:59:49 PDT 2021 by jordanhalterman
\* Created Tue Sep 21 02:14:57 PDT 2021 by jordanhalterman
