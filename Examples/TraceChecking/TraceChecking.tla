--------------------------- MODULE TraceChecking ---------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

VARIABLE messages

VARIABLE requests

VARIABLE count

LOCAL Counter == INSTANCE CRDTCounter WITH
   Nodes <- {"a", "b", "c"},
   IncrementRequest <- "IncrementRequest",
   IncrementResponse <- "IncrementResponse",
   GetRequest <- "GetRequest",
   GetResponse <- "GetResponse",
   LookupRequest <- "LookupRequest",
   LookupResponse <- "LookupResponse"
   
   ---------------------------- MODULE SingleStep --------------------------
   
   VARIABLE index
   
   VARIABLE ready
   
   vars == <<messages, requests, count, index, ready>>
   
   Traces == <<[node |-> "a",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [a |-> 0],
                next |-> [a |-> 1]],
               [node |-> "a",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [a |-> 1],
                next |-> [a |-> 2]],
               [node |-> "b",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [b |-> 2],
                next |-> [b |-> 1]],
               [node |-> "b",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [b |-> 1],
                next |-> [b |-> 2]],
               [node |-> "c",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [c |-> 2],
                next |-> [c |-> 3]],
               [node |-> "c",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [c |-> 1],
                next |-> [c |-> 2]],
               [node |-> "a",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [a |-> 2],
                next |-> [a |-> 3]],
               [node |-> "c",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [c |-> 3],
                next |-> [c |-> 4]],
               [node |-> "a",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [a |-> 4],
                next |-> [a |-> 3]],
               [node |-> "b",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [b |-> 3],
                next |-> [b |-> 5]],
               [node |-> "b",
                step |-> "HandleIncrementRequest",
                msg  |-> [type |-> "IncrementRequest"],
                init |-> [b |-> 4],
                next |-> [b |-> 10]]>>
   
   Prepare ==
      /\ ~ready
      /\ \/ /\ Len(Traces) > index
            /\ index' = index + 1
            /\ ready' = TRUE
            /\ LET trace == Traces[index']
               IN
                  /\ count' = trace.init
         \/ /\ Len(Traces) = index
            /\ UNCHANGED <<count, index, ready>>
   
   Run ==
      /\ ready
      /\ LET trace == Traces[index]
         IN
            /\ \/ /\ trace.step = "HandleIncrementRequest"
                  /\ Counter!HandleIncrementRequest(trace.node, trace.msg)
            /\ Assert(count' = trace.next, "next state does not match")
      /\ ready' = FALSE
      /\ UNCHANGED <<index>>
   
   Init ==
      /\ Counter!Init
      /\ index = 0
      /\ ready = FALSE
   
   Next ==
      \/ Prepare
      \/ Run
      
   Spec == Init /\ [][Next]_vars
   
   ==========================================================================
   
   ----------------------------- MODULE MultiStep ---------------------------
   
   VARIABLE index
   
   VARIABLE ready
   
   vars == <<messages, requests, count, index, ready>>
   
   Traces == <<<<[node |-> "a",
                  step |-> "HandleGetRequest",
                  msg  |-> [type |-> "GetRequest"],
                  init |-> [count |-> [a |-> 0]],
                  next |-> [messages |-> [type |-> "GetResponse", count |-> 0]]]>>,
                <<[node |-> "a",
                  step |-> "HandleLookupResponse",
                  msg  |-> [type |-> "GetRequest"],
                  init |-> [count |-> [a |-> 0]],
                  next |-> [responses |-> {}]]>>,
                <<[node |-> "a",
                  step |-> "HandleLookupResponse",
                  msg  |-> [type |-> "GetRequest"],
                  init |-> [count |-> [a |-> 0]],
                  next |-> [messages |-> [type |-> "GetResponse", count |-> 0]]]>>,
                <<[node |-> "a",
                  step |-> "HandleLookupResponse",
                  msg  |-> [type |-> "GetRequest"],
                  init |-> [count |-> [a |-> 0]],
                  next |-> [messages |-> [type |-> "GetResponse", count |-> 0]]]>>>>
   
   Prepare ==
      /\ ~ready
      /\ \/ /\ Len(Traces) > index
            /\ index' = index + 1
            /\ ready' = TRUE
            /\ LET trace == Traces[index']
               IN
                  /\ count' = trace.init
         \/ /\ Len(Traces) = index
            /\ UNCHANGED <<count, index, ready>>
   
   Run ==
      /\ ready
      /\ LET trace == Traces[index]
         IN
            /\ \/ /\ trace.step = "HandleGetRequest"
                  /\ Counter!HandleGetRequest(trace.node, trace.msg)
      /\ ready' = FALSE
      /\ UNCHANGED <<index>>
   
   Init ==
      /\ Counter!Init
      /\ index = 0
      /\ ready = FALSE
   
   Next ==
      \/ Prepare
      \/ Run
      
   Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
   
   ==========================================================================
   
=============================================================================
\* Modification History
\* Last modified Mon Sep 13 17:22:00 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 16:40:23 PDT 2021 by jordanhalterman
