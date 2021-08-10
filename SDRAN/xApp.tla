-------------------------------- MODULE xApp --------------------------------

EXTENDS E2T

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

CONSTANT AppNode

----

AppSendSubscribeRequest(c) ==
    /\ E2TNB!Send(c, [type |-> SubscribeRequest])
    /\ UNCHANGED <<>>

AppHandleSubscribeResponse(c, m) ==
    /\ E2TNB!Receive(c)
    /\ UNCHANGED <<>>

AppSendUnsubscribeRequest(c) ==
    /\ E2TNB!Send(c, [type |-> UnsubscribeRequest])
    /\ UNCHANGED <<>>

AppHandleUnsubscribeResponse(c, m) ==
    /\ E2TNB!Receive(c)
    /\ UNCHANGED <<>>

AppHandleMessage(c, m) ==
   /\ \/ /\ m.type = SubscribeResponse
         /\ AppHandleSubscribeResponse(c, m)
      \/ /\ m.type = UnsubscribeResponse
         /\ AppHandleUnsubscribeResponse(c, m)
   /\ UNCHANGED <<>>

----

AppInit == TRUE

AppNext ==
    \/ \E s \in AppNode, d \in E2TNode : E2TNB!Connect(s, d)
    \/ \E c \in E2TNB!Connections : E2TNB!Handle(c, AppHandleMessage)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:36:57 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:35 PDT 2021 by jordanhalterman
