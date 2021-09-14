-------------------------------- MODULE E2T --------------------------------

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

\* A set of E2 node identifiers
CONSTANT E2Nodes

ASSUME /\ IsFiniteSet(E2Nodes)
       /\ \A n \in E2Nodes : n \in STRING

\* A mapping of node states
VARIABLE nodes

\* A global store of mastership for each E2 node
VARIABLE masterships

\* A global store of connections for each E2 node
VARIABLE conns

\* A store of streams for each node
VARIABLE streams

\* A global store of channel states
VARIABLE chans

\* A global store of subscription states
VARIABLE subs

vars == <<nodes, masterships, conns, streams, chans, subs>>

LOCAL API == INSTANCE E2TService

LOCAL E2AP == INSTANCE E2AP

----

StartNode(n) ==
   /\ nodes[n] = Stopped
   /\ nodes' = [nodes EXCEPT ![n] = Started]
   /\ UNCHANGED <<masterships, conns, streams, chans, subs>>

StopNode(n) ==
   /\ nodes[n] = Started
   /\ nodes' = [nodes EXCEPT ![n] = Stopped]
   /\ streams' = [streams EXCEPT ![n] = [id \in {} |-> [id |-> Nil]]]
   /\ UNCHANGED <<masterships, conns, chans, subs>>

----

HandleSubscribeRequest(n, c, r) ==
   /\ \/ /\ r.sub.id \notin streams[n]
         /\ streams' = [streams EXCEPT ![n] = streams[n] @@ (r.sub.id :> [id |-> r.sub.id])]
      \/ /\ r.sub.id \in streams[n]
         /\ UNCHANGED <<streams>>
   /\ UNCHANGED <<chans, subs>>

HandleUnsubscribeRequest(n, c, r) ==
   /\ \/ /\ r.sub.id \notin streams[n]
         /\ streams' = [streams EXCEPT ![n] = [i \in {subId \in DOMAIN streams[n] : subId # r.id} |-> streams[n][i]]]
      \/ /\ r.sub.id \in streams[n]
         /\ UNCHANGED <<streams>>
   /\ API!Server!Send!SubscribeResponse(c, [id |-> r.id])
   /\ UNCHANGED <<chans, subs>>

HandleControlRequest(n, c, r) ==
   /\ API!Server!Send!ControlResponse(c, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<chans, subs>>

HandleE2TRequest(n, c) ==
   /\ \/ API!Server!Handle!SubscribeRequest(c, LAMBDA m : HandleSubscribeRequest(n, c, m))
      \/ API!Server!Handle!UnsubscribeRequest(c, LAMBDA m : HandleUnsubscribeRequest(n, c, m))
      \/ API!Server!Handle!ControlRequest(c, LAMBDA m : HandleControlRequest(n, c, m))
   /\ UNCHANGED <<nodes>>

----

ReconcileMastership(n, e) ==
   /\ masterships[e].master \notin DOMAIN conns[e]
   /\ \E c \in DOMAIN conns[e] : c # masterships[e].master
   /\ masterships' = [masterships EXCEPT ![e] = [
                         term |-> masterships[e].term + 1,
                         conn |-> CHOOSE c \in DOMAIN conns[e] : c # masterships[e].master]]
   /\ UNCHANGED <<nodes, subs>>

ReconcileStream(n, s) ==
   /\ UNCHANGED <<nodes, subs>>

\* ReconcileChannel reconciles a channel's state
ReconcileChannel(n, c) ==
   /\ UNCHANGED <<nodes, streams>>

\* ReconcileSubscription reconciles a subscription's state
ReconcileSubscription(n, s) ==
   /\ UNCHANGED <<nodes, streams, chans>>

----

HandleE2SetupRequest(node, conn, res) ==
   /\ UNCHANGED <<chans, subs>>

HandleRICControlResponse(node, conn, res) ==
   /\ UNCHANGED <<chans, subs>>

HandleRICSubscriptionResponse(node, conn, res) ==
   /\ UNCHANGED <<chans, subs>>

HandleRICSubscriptionDeleteResponse(node, conn, res) ==
   /\ UNCHANGED <<chans, subs>>

HandleRICIndication(node, conn, res) ==
   /\ UNCHANGED <<chans, subs>>

HandleE2APRequest(node, conn) ==
   /\ \/ E2AP!RIC!Handle!E2SetupRequest(conn, LAMBDA m : HandleE2SetupRequest(node, conn, m))
      \/ E2AP!RIC!Handle!RICControlResponse(conn, LAMBDA m : HandleRICControlResponse(node, conn, m))
      \/ E2AP!RIC!Handle!RICSubscriptionResponse(conn, LAMBDA m : HandleRICSubscriptionResponse(node, conn, m))
      \/ E2AP!RIC!Handle!RICSubscriptionDeleteResponse(conn, LAMBDA m : HandleRICSubscriptionDeleteResponse(node, conn, m))
      \/ E2AP!RIC!Handle!RICIndication(conn, LAMBDA m : HandleRICIndication(node, conn, m))
   /\ UNCHANGED <<nodes>>

----

Init ==
   /\ nodes = [n \in E2TNodes |-> Stopped]
   /\ masterships = [e \in E2Nodes |-> [master |-> Nil, term |-> 0]]
   /\ conns = [e \in E2Nodes |-> [c \in {} |-> [id |-> c, e2node |-> Nil, e2t |-> Nil]]]
   /\ streams = [n \in E2TNodes |-> [x \in {} |-> [id |-> x]]]
   /\ chans = [x \in {} |-> [id |-> x]]
   /\ subs = [x \in {} |-> [id |-> x]]

Next ==
   \/ \E n \in E2TNodes : StartNode(n)
   \/ \E n \in E2TNodes : StopNode(n)
   \/ \E n \in E2TNodes, c \in API!Connections : HandleE2TRequest(n, c)
   \/ \E n \in E2TNodes, c \in E2AP!Connections : HandleE2APRequest(n, c)
   \/ \E n \in E2TNodes, e \in E2Nodes : ReconcileMastership(n, e)
   \/ \E n \in E2TNodes : \E s \in streams[n] : ReconcileStream(n, s)
   \/ \E n \in E2TNodes, c \in chans : ReconcileChannel(n, c)
   \/ \E n \in E2TNodes, s \in subs : ReconcileSubscription(n, s)

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 19:08:57 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 03:23:39 PDT 2021 by jordanhalterman
