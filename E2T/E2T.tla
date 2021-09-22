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
CONSTANT E2Term

ASSUME /\ IsFiniteSet(E2Term)
       /\ \A n \in E2Term : n \in STRING

\* A mapping of node states
VARIABLE state

\* gRPC connection states
VARIABLE grpc

\* SCTP connection states
VARIABLE sctp

\* A global store of mastership for each E2 node
VARIABLE masterships

\* A global store of configuration for each E2 node
VARIABLE nodes

\* A global store of connections for each E2 node
VARIABLE conns

\* A store of streams for each node
VARIABLE streams

\* A global store of channel states
VARIABLE chans

\* A global store of subscription states
VARIABLE subs

vars == <<state, masterships, grpc, sctp, streams, chans, subs>>

LOCAL API == INSTANCE E2TService WITH conns <- grpc

LOCAL E2AP == INSTANCE E2AP WITH conns <- sctp

----

StartNode(e2TermID) ==
   /\ state[e2TermID] = Stopped
   /\ state' = [state EXCEPT ![e2TermID] = Started]
   /\ E2AP!Server(e2TermID)!Start
   /\ UNCHANGED <<masterships, conns, streams, chans, subs>>

StopNode(e2TermID) ==
   /\ state[e2TermID] = Started
   /\ state' = [state EXCEPT ![e2TermID] = Stopped]
   /\ E2AP!Server(e2TermID)!Start
   /\ streams' = [streams EXCEPT ![e2TermID] = [id \in {} |-> [id |-> Nil]]]
   /\ UNCHANGED <<masterships, conns, chans, subs>>

----

HandleSubscribeRequest(e2TermID, apiConn, apiReq) ==
   /\ \/ /\ apiReq.sub.id \notin streams[e2TermID]
         /\ streams' = [streams EXCEPT ![e2TermID] = streams[e2TermID] @@ (apiReq.sub.id :> [id |-> apiReq.sub.id])]
      \/ /\ apiReq.sub.id \in streams[e2TermID]
         /\ UNCHANGED <<streams>>
   /\ UNCHANGED <<chans, subs>>

SendSubscribeResponse(e2TermID, apiConn, s) ==
   /\ Len(streams[e2TermID][s]) > 0
   /\ API!Server!Send!SubscribeResponse(apiConn, [indication |-> streams[e2TermID][s][1]])
   /\ streams' = [streams EXCEPT ![e2TermID] = [streams[e2TermID] EXCEPT ![s] = SubSeq(streams[e2TermID][s], 2, Len(streams[e2TermID][s]))]]
   /\ UNCHANGED <<chans, subs>>

HandleUnsubscribeRequest(e2TermID, apiConn, apiReq) ==
   /\ \/ /\ apiReq.sub.id \notin streams[e2TermID]
         /\ streams' = [streams EXCEPT ![e2TermID] = [i \in {subId \in DOMAIN streams[e2TermID] : subId # apiReq.id} |-> streams[e2TermID][i]]]
      \/ /\ apiReq.sub.id \in streams[e2TermID]
         /\ UNCHANGED <<streams>>
   /\ API!Server!Reply!UnsubscribeResponse(apiConn, [id |-> apiReq.id])
   /\ UNCHANGED <<chans, subs>>

HandleControlRequest(e2TermID, apiConn, apiReq) ==
   /\ API!Server!Reply!ControlResponse(apiConn, [foo |-> "bar", bar |-> "baz"])
   /\ UNCHANGED <<chans, subs>>

HandleE2TRequest(e2TermID, apiConn) ==
   /\ \/ API!Server!Handle!SubscribeRequest(apiConn, LAMBDA m : HandleSubscribeRequest(e2TermID, apiConn, m))
      \/ API!Server!Handle!UnsubscribeRequest(apiConn, LAMBDA m : HandleUnsubscribeRequest(e2TermID, apiConn, m))
      \/ API!Server!Handle!ControlRequest(apiConn, LAMBDA m : HandleControlRequest(e2TermID, apiConn, m))
   /\ UNCHANGED <<state>>

----

ReconcileMastership(e2TermID, e2NodeID) ==
   /\ masterships[e2NodeID].master \notin DOMAIN conns[e2NodeID]
   /\ \E c \in DOMAIN conns[e2NodeID] : c # masterships[e2NodeID].master
   /\ masterships' = [masterships EXCEPT ![e2NodeID] = [
                         term |-> masterships[e2NodeID].term + 1,
                         conn |-> CHOOSE c \in DOMAIN conns[e2NodeID] : c # masterships[e2NodeID].master]]
   /\ UNCHANGED <<state, subs>>

ReconcileStream(n, s) ==
   /\ UNCHANGED <<state, subs>>

\* ReconcileChannel reconciles a channel's state
ReconcileChannel(n, c) ==
   /\ UNCHANGED <<state, streams>>

\* ReconcileSubscription reconciles a subscription's state
ReconcileSubscription(n, s) ==
   /\ UNCHANGED <<state, streams, chans>>

----

HandleE2SetupRequest(node, conn, res) ==
   /\ E2AP!Server(node)!Reply!E2SetupResponse(conn, [foo |-> "bar", bar |-> "baz"])
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
   /\ \/ E2AP!Server(node)!Handle!E2SetupRequest(conn, LAMBDA c, m : HandleE2SetupRequest(node, conn, m))
      \/ E2AP!Server(node)!Handle!RICControlResponse(conn, LAMBDA c, m : HandleRICControlResponse(node, conn, m))
      \/ E2AP!Server(node)!Handle!RICSubscriptionResponse(conn, LAMBDA c, m : HandleRICSubscriptionResponse(node, conn, m))
      \/ E2AP!Server(node)!Handle!RICSubscriptionDeleteResponse(conn, LAMBDA c, m : HandleRICSubscriptionDeleteResponse(node, conn, m))
      \/ E2AP!Server(node)!Handle!RICIndication(conn, LAMBDA c, m : HandleRICIndication(node, conn, m))
   /\ UNCHANGED <<state>>

----

Init ==
   /\ state = [e2TermID \in E2Term |-> Stopped]
   /\ masterships = [e2TermID \in E2Term |-> [e \in {} |-> [master |-> Nil, term |-> 0]]]
   /\ nodes = [e \in {} |-> [version |-> 0, conns |-> {}]]
   /\ conns = [e \in {} |-> [id |-> Nil]]
   /\ streams = [n \in E2Term |-> [x \in {} |-> [id |-> x]]]
   /\ chans = [x \in {} |-> [id |-> x]]
   /\ subs = [x \in {} |-> [id |-> x]]

Next ==
   \/ \E n \in E2Term : 
         StartNode(n)
   \/ \E n \in E2Term : 
         StopNode(n)
   \/ \E n \in E2Term, c \in API!Connections : 
         HandleE2TRequest(n, c)
   \/ \E n \in E2Term, c \in API!Connections : 
         \E s \in DOMAIN streams[n] : 
            SendSubscribeResponse(n, c, s)
   \/ \E n \in E2Term : 
         \E c \in E2AP!Server(n)!Connections : 
            HandleE2APRequest(n, c)
   \/ \E n \in E2Term : 
         \E e \in DOMAIN nodes[n] : 
            ReconcileMastership(n, e)
   \/ \E n \in E2Term : 
         \E s \in DOMAIN streams[n] : 
            ReconcileStream(n, s)
   \/ \E n \in E2Term, c \in chans : 
         ReconcileChannel(n, c)
   \/ \E n \in E2Term, s \in subs : 
         ReconcileSubscription(n, s)

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 18:16:38 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 03:23:39 PDT 2021 by jordanhalterman
