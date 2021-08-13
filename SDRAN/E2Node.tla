------------------------------- MODULE E2Node -------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

CONSTANT Nodes

   ------------------------------- MODULE NB ------------------------------
   
   SendE2SetupRequest(c) ==
       /\ API!E2AP!Client!Send(c, [type |-> API!E2AP!Protocol.E2Setup])
       /\ UNCHANGED <<>>
   
   HandleE2SetupResponse(c, m) ==
       /\ API!E2AP!Client!Receive(c)
       /\ UNCHANGED <<>>
   
   HandleMessage(c, m) ==
      /\ \/ /\ m.type = API!E2AP!Protocol.E2SetupResponse
            /\ HandleE2SetupResponse(c, m)
      /\ UNCHANGED <<>>
   
   Handle(c) == API!E2AP!Client!Handle(c, HandleMessage)
   
   Servers == API!E2AP!Servers
   
   Connections == API!E2AP!Connections
    
   Connect(s, d) == API!E2AP!Client!Connect(s, d)
      
   Init == TRUE
   
   Next ==
       \/ \E s \in Nodes, d \in Servers : Connect(s, d)
       \/ \E c \in Connections : Handle(c)
         
   ==========================================================================

LOCAL NB == INSTANCE NB

----

Init ==
   /\ NB!Init

Next ==
   \/ NB!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 04:57:05 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:53 PDT 2021 by jordanhalterman
