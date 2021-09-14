---------------------------- MODULE CRDTCounter ----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE TLC

CONSTANT Nodes

CONSTANT IncrementRequest,
         IncrementResponse,
         GetRequest,
         GetResponse,
         LookupRequest,
         LookupResponse

VARIABLE messages

VARIABLE requests

VARIABLE count

LOCAL Messaging == INSTANCE Messaging

----

SendIncrementRequest(n) ==
   /\ Messaging!Send([type |-> IncrementRequest, dst |-> n])
   /\ UNCHANGED <<requests, count>>

HandleIncrementRequest(n, m) ==
   /\ Messaging!Receive(m)
   /\ count' = [count EXCEPT ![n] = count[n] + 1]
   /\ Messaging!Reply([type |-> IncrementResponse, count |-> count'[n]])
   /\ UNCHANGED <<requests>>

HandleIncrementResponse(m) ==
   /\ Messaging!Receive(m)
   /\ UNCHANGED <<count>>

HandleGetRequest(n, m) ==
   /\ Messaging!Receive(m)
   /\ \A o \in Nodes : Messaging!Reply([type |-> LookupRequest, src |-> n, dst |-> o, req |-> m])
   /\ requests' = requests @@ (m :> {})
   /\ UNCHANGED <<count>>

HandleGetResponse(m) ==
   /\ Messaging!Receive(m)
   /\ UNCHANGED <<count>>

HandleLookupRequest(n, m) ==
   /\ Messaging!Receive(m)
   /\ Messaging!Reply([type |-> LookupResponse, count |-> count[n], src |-> n, dst |-> m.src, req |-> m.req])
   /\ UNCHANGED <<requests, count>>

HandleLookupResponse(n, m) ==
   /\ Messaging!Receive(m)
   /\ \/ /\ m.req \in requests
         /\ requests' = [requests EXCEPT ![m.req] = requests[m.req] \cup {m}]
      \/ /\ m.req \notin requests
         /\ UNCHANGED <<requests>>
   /\ UNCHANGED <<count>>

HandleMessage(m) ==
   \/ /\ m.type = IncrementRequest
      /\ HandleIncrementRequest(m.dst, m)
   \/ /\ m.type = IncrementResponse
      /\ HandleIncrementResponse(m)
   \/ /\ m.type = GetRequest
      /\ HandleGetRequest(m.dst, m)
   \/ /\ m.type = GetResponse
      /\ HandleGetResponse(m)
   \/ /\ m.type = LookupRequest
      /\ HandleLookupRequest(m.dst, m)
   \/ /\ m.type = LookupResponse
      /\ HandleLookupResponse(m.dst, m)

----

Init ==
   /\ messages = [m \in {} |-> 0]
   /\ requests = [m \in {} |-> {}]
   /\ count = [n \in Nodes |-> 0]

Next ==
   \/ Messaging!Handle(HandleMessage)

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 16:40:46 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 16:40:43 PDT 2021 by jordanhalterman
