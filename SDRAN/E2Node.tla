------------------------------- MODULE E2Node -------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

CONSTANT Nodes

ASSUME /\ IsFiniteSet(Nodes) 
       /\ \A n \in Nodes : n \in STRING

vars == <<>>

   ------------------------------ MODULE Store -----------------------------
   
   Init == TRUE
   
   Next == FALSE

   ========================================================================
   
LOCAL Store == INSTANCE Store
   
   ------------------------------- MODULE NB ------------------------------
   
   SendE2SetupRequest(c) ==
      /\ API!E2AP!Client!Send!E2SetupRequest(c, [foo |-> "bar"])
   
   HandleE2SetupResponse(c, m) ==
      /\ UNCHANGED <<>>
   
   Init ==
      /\ TRUE
   
   Next ==
      \/ \E n \in Nodes, s \in API!E2AP!Servers : API!E2AP!Client!Connect(n, s)
      \/ \E c \in API!E2AP!Connections : API!E2AP!Client!Disconnect(c)
      \/ \E c \in API!E2AP!Connections :
            \/ SendE2SetupRequest(c)
            \/ API!E2AP!Client!Receive!E2SetupResponse(c, HandleE2SetupResponse)
         
   ==========================================================================

LOCAL NB == INSTANCE NB

----

Init ==
   /\ NB!Init
   /\ Store!Init

Next ==
   \/ NB!Next
   \/ Store!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 16:36:37 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:53 PDT 2021 by jordanhalterman
