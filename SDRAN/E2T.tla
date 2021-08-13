-------------------------------- MODULE E2T --------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

CONSTANT Nodes

CONSTANT OK, Error

ASSUME /\ IsFiniteSet(Nodes) 
       /\ \A n \in Nodes : n \in STRING

   ------------------------------ MODULE Store -----------------------------
   
   CreateSubscription(s) == [status |-> OK]
   
   DeleteSubscription(s) == [status |-> OK]
   
   Init == TRUE
   
   Next == FALSE

   ========================================================================
   
LOCAL Store == INSTANCE Store
   
   ------------------------------- MODULE NB ------------------------------
   
   HandleSubscribeRequest(c, m) ==
       /\ LET r == Store!CreateSubscription(m)
          IN API!E2T!Server!Send!SubscribeResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleUnsubscribeRequest(c, m) ==
       /\ LET r == Store!DeleteSubscription(m)
          IN API!E2T!Server!Send!UnsubscribeResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleMessage(c, m) ==
      /\ \/ API!E2T!Server!Receive!SubscribeRequest(c, HandleSubscribeRequest)
         \/ API!E2T!Server!Receive!UnsubscribeRequest(c, HandleUnsubscribeRequest)
      /\ UNCHANGED <<>>
   
   Init ==
      /\ TRUE
   
   Next ==
      \/ \E s \in Nodes : API!E2T!Server!Serve(s)
      \/ \E s \in API!E2T!Servers : API!E2T!Server!Stop(s)
      \/ \E c \in API!E2T!Connections :
            \/ API!E2T!Server!Receive!SubscribeRequest(c, HandleSubscribeRequest)
            \/ API!E2T!Server!Receive!UnsubscribeRequest(c, HandleUnsubscribeRequest)
         
   ==========================================================================

LOCAL NB == INSTANCE NB

   ------------------------------- MODULE SB ------------------------------
   
   HandleE2SetupRequest(c, m) ==
       /\ API!E2AP!Server!Send!E2SetupResponse(c, [status |-> OK])
       /\ UNCHANGED <<>>
   
   Init ==
      /\ TRUE
   
   Next ==
      \/ \E s \in Nodes : API!E2AP!Server!Serve(s)
      \/ \E s \in API!E2AP!Servers : API!E2AP!Server!Stop(s)
      \/ \E c \in API!E2AP!Connections :
            \/ API!E2AP!Server!Receive!E2SetupRequest(c, HandleE2SetupRequest)
         
   ==========================================================================

LOCAL SB == INSTANCE SB

----

Init ==
   /\ SB!Init
   /\ NB!Init
   /\ Store!Init

Next ==
   \/ SB!Next
   \/ NB!Next
   \/ Store!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 15:49:45 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:45 PDT 2021 by jordanhalterman
