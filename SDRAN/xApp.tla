-------------------------------- MODULE xApp --------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

CONSTANT App

ASSUME App \in STRING

CONSTANT Nodes

ASSUME /\ IsFiniteSet(Nodes) 
       /\ \A n \in Nodes : n \in STRING

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

Init == TRUE

Next ==
    \/ \E s \in Nodes, d \in SB!Servers : SB!Connect(s, d)
    \/ \E c \in SB!Connections : SB!Handle(c)
   
=============================================================================
\* Modification History
\* Last modified Fri Aug 13 06:00:31 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:35 PDT 2021 by jordanhalterman
