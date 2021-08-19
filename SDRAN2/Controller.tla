----------------------------- MODULE Controller -----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

CONSTANT Nil

VARIABLE time

Clock == INSTANCE Clock

\* A queue of request to reconcile
VARIABLE queue

----

Enqueue(id) ==
   /\ queue' = Append(queue, [id |-> id, time |-> Nil])

Retry(request) ==
   /\ queue' = <<[id |-> request.id, time |-> Nil]>> \o queue'

Requeue(request) ==
   /\ queue' = Append(queue', [id |-> request.id, time |-> Nil])

RequeueAfter(request, duration) ==
   /\ LET t == Clock!Time + duration
      IN
         /\ queue' = Append(queue', [id |-> request.id, time |-> t])

LOCAL ReconcileRequest(R(_)) == 
   /\ \E r \in queue : r.time = Nil
   /\ LET r == CHOOSE x \in DOMAIN queue : 
         /\ queue[x].time = Nil 
         /\ \A y \in {z \in DOMAIN queue : queue[z].time = Nil} : x <= y
         request == queue[r]
      IN
         /\ R(request)
         /\ queue' = SubSeq(queue, 0, r) \o SubSeq(queue, r+1, Len(queue))

LOCAL ReconcileDelayed(R(_)) ==
   /\ \E r \in queue : r.time <= Clock!Time
   /\ LET r == CHOOSE x \in DOMAIN queue : 
         /\ queue[x].time <= Clock!Time 
         /\ \A y \in {z \in DOMAIN queue : queue[z].time <= Clock!Time} : queue[x].time <= queue[y].time
         request == queue[r]
      IN
         /\ R(request)
         /\ queue' = SubSeq(queue, 0, r) \o SubSeq(queue, r+1, Len(queue))

Reconcile(R(_)) ==
   \/ ReconcileRequest(R)
   \/ ReconcileDelayed(R)

----

Init ==
   /\ queue = <<>>

Next ==
   \/ FALSE

=============================================================================
\* Modification History
\* Last modified Thu Aug 19 12:07:02 PDT 2021 by jordanhalterman
\* Created Thu Aug 19 00:53:05 PDT 2021 by jordanhalterman
