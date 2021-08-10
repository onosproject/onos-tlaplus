------------------------------- MODULE E2Node -------------------------------

EXTENDS E2T

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

CONSTANT E2Node

----

E2NodeSendE2SetupRequest(c) ==
    /\ E2TSB!Send(c, [type |-> E2Setup])
    /\ UNCHANGED <<>>

E2NodeHandleE2SetupResponse(c, m) ==
    /\ E2TSB!Receive(c)
    /\ UNCHANGED <<>>

E2NodeHandleMessage(c, m) ==
   /\ \/ /\ m.type = E2SetupResponse
         /\ E2NodeHandleE2SetupResponse(c, m)
   /\ UNCHANGED <<>>

----

E2NodeInit == TRUE

E2NodeNext ==
    \/ \E s \in E2Node, d \in E2TNode : E2TSB!Connect(s, d)
    \/ \E c \in E2TSB!Connections : E2TSB!Handle(c, E2NodeHandleMessage)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:31:58 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:53 PDT 2021 by jordanhalterman
