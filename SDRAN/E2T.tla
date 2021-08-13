-------------------------------- MODULE E2T --------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

CONSTANT Nodes

----

   ------------------------------- MODULE NB ------------------------------
   
   HandleSubscribeRequest(c, m) ==
       /\ API!E2T!Server!Receive(c)
       /\ API!E2T!Server!Reply(c, [type |-> API!E2T!Protocol.SubscribeResponse])
       /\ UNCHANGED <<>>
   
   HandleUnsubscribeRequest(c, m) ==
       /\ API!E2T!Server!Receive(c)
       /\ API!E2T!Server!Reply(c, [type |-> API!E2T!Protocol.UnsubscribeResponse])
       /\ UNCHANGED <<>>
   
   HandleMessage(c, m) ==
      /\ \/ /\ m.type = API!E2T!Protocol.SubscribeRequest
            /\ HandleSubscribeRequest(c, m)
      /\ \/ /\ m.type = API!E2T!Protocol.UnsubscribeRequest
            /\ HandleUnsubscribeRequest(c, m)
      /\ UNCHANGED <<>>
      
   Handle(c) == API!E2T!Server!Handle(c, HandleMessage)
   
   Servers == API!E2T!Servers
   
   Connections == API!E2T!Connections
    
   Serve(s) == API!E2T!Server!Start(s)
    
   Stop(s) == API!E2T!Server!Stop(s)
   
   Init == TRUE
   
   Next ==
       \/ \E s \in Nodes : Serve(s)
       \/ \E s \in Servers : Stop(s)
       \/ \E c \in Connections : Handle(c)
      
   ==========================================================================

LOCAL NB == INSTANCE NB

   ------------------------------- MODULE SB ------------------------------
   
   HandleE2Setup(c, m) ==
       /\ API!E2AP!Server!Receive(c)
       /\ API!E2AP!Server!Reply(c, [type |-> API!E2AP!Protocol.E2SetupResponse])
       /\ UNCHANGED <<>>
   
   HandleMessage(c, m) ==
      /\ \/ /\ m.type = API!E2AP!Protocol.E2Setup
            /\ HandleE2Setup(c, m)
      /\ UNCHANGED <<>>
   
   Handle(c) == API!E2AP!Server!Handle(c, HandleMessage)
   
   Servers == API!E2AP!Servers
   
   Connections == API!E2AP!Connections
    
   Serve(s) == API!E2AP!Server!Start(s)
    
   Stop(s) == API!E2AP!Server!Stop(s)
   
   Init == TRUE
      
   Next ==
       \/ \E s \in Nodes : Serve(s)
       \/ \E s \in Servers : Stop(s)
       \/ \E c \in Connections : Handle(c)
      
   ==========================================================================

LOCAL SB == INSTANCE SB

----

Init ==
   /\ SB!Init
   /\ NB!Init

Next ==
   \/ SB!Next
   \/ NB!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 04:56:41 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:45 PDT 2021 by jordanhalterman
