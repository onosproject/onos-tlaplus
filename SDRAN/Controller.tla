----------------------------- MODULE Controller -----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

VARIABLE time

Clock == INSTANCE Clock

\* A queue of requests to reconcile
VARIABLE requests

----

Enqueue(id) ==
   /\ requests' = Append(requests, [id |-> id, time |-> 0])

Retry(request) ==
   /\ requests' = <<[id |-> request.id, time |-> 0]>> \o requests'

Requeue(request) ==
   /\ requests' = Append(requests', [id |-> request.id, time |-> 0])

RequeueAfter(request, duration) ==
   /\ LET t == Clock!Time + duration
      IN
         /\ requests' = Append(requests', [id |-> request.id, time |-> t])

LOCAL ReconcileRequest(R(_)) ==
   /\ \E r \in DOMAIN requests :
         LET request == requests[r]
         IN
            /\ request.time = 0
            /\ \A x \in DOMAIN requests : 
                  \/ requests[x].time # 0
                  \/ r <= x
            /\ requests' = SubSeq(requests, 0, r) \o SubSeq(requests, r+1, Len(requests))
            /\ R(request)

LOCAL ReconcileDelayed(R(_)) ==
   /\ \E r \in DOMAIN requests :
         LET request == requests[r]
         IN
            /\ request.time # 0
            /\ request.time <= Clock!Time
            /\ \A x \in DOMAIN requests : 
                  \/ request.time < requests[x].time 
                  \/ /\ request.time = requests[x].time
                     /\ r <= x
            /\ requests' = SubSeq(requests, 0, r) \o SubSeq(requests, r+1, Len(requests))
            /\ R(request)

Reconcile(R(_)) ==
   \/ ReconcileRequest(R)
   \/ ReconcileDelayed(R)

----

Init ==
   /\ requests = <<>>

Next ==
   \/ FALSE

=============================================================================
\* Modification History
\* Last modified Fri Aug 20 02:30:56 PDT 2021 by jordanhalterman
\* Created Fri Aug 20 02:17:50 PDT 2021 by jordanhalterman
