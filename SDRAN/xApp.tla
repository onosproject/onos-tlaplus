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

vars == <<>>

   ------------------------------ MODULE Store -----------------------------
   
   Init == TRUE
   
   Next == FALSE

   ========================================================================
   
LOCAL Store == INSTANCE Store
   
   ------------------------------- MODULE SB ------------------------------
   
   subscriptionDetails == [
      actions |-> [i \in Nat |-> [actionID |-> {n \in Nat : n > 0 /\ n < 256}]]]
   
   SendSubscribeRequest(c) ==
      /\ API!E2T!Client!Send!SubscribeRequest(c, [foo |-> "bar"])
      /\ UNCHANGED <<e2apApiVars, topoApiVars>>
   
   HandleSubscribeResponse(c, m) ==
      /\ UNCHANGED <<e2apApiVars, topoApiVars>>
   
   SendUnsubscribeRequest(c) ==
      /\ API!E2T!Client!Send!UnsubscribeRequest(c, [foo |-> "bar"])
      /\ UNCHANGED <<e2apApiVars, topoApiVars>>
   
   HandleUnsubscribeResponse(c, m) ==
      /\ UNCHANGED <<e2apApiVars, topoApiVars>>
   
   Init ==
      /\ TRUE
   
   Next ==
      \/ \E n \in Nodes, s \in API!E2T!Servers : API!E2T!Client!Connect(n, s)
      \/ \E c \in API!E2T!Connections : API!E2T!Client!Disconnect(c)
      \/ \E c \in API!E2T!Connections : SendSubscribeRequest(c)
      \/ \E c \in API!E2T!Connections : SendUnsubscribeRequest(c)
      \/ \E c \in API!E2T!Connections :
            \/ API!E2T!Client!Receive!SubscribeResponse(c, HandleSubscribeResponse)
            \/ API!E2T!Client!Receive!UnsubscribeResponse(c, HandleUnsubscribeResponse)
         
   ==========================================================================

LOCAL SB == INSTANCE SB

----

Init ==
   /\ SB!Init
   /\ Store!Init

Next ==
   \/ SB!Next
   \/ Store!Next

=============================================================================
\* Modification History
\* Last modified Sat Aug 14 12:43:39 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:35 PDT 2021 by jordanhalterman
