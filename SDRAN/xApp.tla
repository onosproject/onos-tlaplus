-------------------------------- MODULE xApp --------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

CONSTANT Nodes

   ------------------------------- MODULE SB ------------------------------
   
   SendSubscribeRequest(c) ==
       /\ API!E2T!Client!Send(c, [type |-> API!E2T!Protocol.SubscribeRequest])
       /\ UNCHANGED <<>>
   
   HandleSubscribeResponse(c, m) ==
       /\ API!E2T!Client!Receive(c)
       /\ UNCHANGED <<>>
   
   SendUnsubscribeRequest(c) ==
       /\ API!E2T!Client!Send(c, [type |-> API!E2T!Protocol.UnsubscribeRequest])
       /\ UNCHANGED <<>>
   
   HandleUnsubscribeResponse(c, m) ==
       /\ API!E2T!Client!Receive(c)
       /\ UNCHANGED <<>>
   
   HandleMessage(c, m) ==
      /\ \/ /\ m.type = API!E2T!Protocol.SubscribeResponse
            /\ HandleSubscribeResponse(c, m)
         \/ /\ m.type = API!E2T!Protocol.UnsubscribeResponse
            /\ HandleUnsubscribeResponse(c, m)
      /\ UNCHANGED <<>>
   
   Handle(c) == API!E2T!Client!Handle(c, HandleMessage)
   
   Servers == API!E2T!Servers
   
   Connections == API!E2T!Connections
    
   Connect(s, d) == API!E2T!Client!Connect(s, d)

   Init == TRUE
   
   Next ==
       \/ \E s \in Nodes, d \in Servers : Connect(s, d)
       \/ \E c \in Connections : Handle(c)
      
   ==========================================================================

LOCAL SB == INSTANCE SB

----

Init ==
   /\ SB!Init

Next ==
   \/ SB!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 04:57:31 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:35 PDT 2021 by jordanhalterman
