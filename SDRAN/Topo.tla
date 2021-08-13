-------------------------------- MODULE Topo --------------------------------

EXTENDS API

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

CONSTANT Nodes

CONSTANT OK, Error

ASSUME /\ IsFiniteSet(Nodes) 
       /\ \A n \in Nodes : n \in STRING

   ------------------------------ MODULE Store -----------------------------
   
   Create(m) == [status |-> OK]
   
   Update(m) == [status |-> OK]
   
   Delete(m) == [status |-> OK]
   
   Get(m) == [status |-> OK]
   
   List(m) == [status |-> OK]
   
   Watch(m) == [status |-> OK]
      
   Init == TRUE
   
   Next == FALSE
   
   ========================================================================
   
LOCAL Store == INSTANCE Store
   
   ------------------------------- MODULE NB ------------------------------
   
   HandleCreateRequest(c, m) ==
       /\ LET r == Store!Create(m)
          IN API!Topo!Server!Send!CreateResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleUpdateRequest(c, m) ==
       /\ LET r == Store!Update(m)
          IN API!Topo!Server!Send!UpdateResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleDeleteRequest(c, m) ==
       /\ LET r == Store!Delete(m)
          IN API!Topo!Server!Send!DeleteResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleGetRequest(c, m) ==
       /\ LET r == Store!Get(m)
          IN API!Topo!Server!Send!GetResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleListRequest(c, m) ==
       /\ LET r == Store!List(m)
          IN API!Topo!Server!Send!ListResponse(c, r)
       /\ UNCHANGED <<>>
   
   HandleWatchRequest(c, m) ==
       /\ LET r == Store!Watch(m)
          IN API!Topo!Server!Send!WatchResponse(c, r)
       /\ UNCHANGED <<>>
   
   Init ==
      /\ TRUE
   
   Next ==
      \/ \E s \in Nodes : API!Topo!Server!Serve(s)
      \/ \E s \in API!Topo!Servers : API!Topo!Server!Stop(s)
      \/ \E c \in API!Topo!Connections :
            \/ API!Topo!Server!Receive!CreateRequest(c, HandleCreateRequest)
            \/ API!Topo!Server!Receive!UpdateRequest(c, HandleUpdateRequest)
            \/ API!Topo!Server!Receive!DeleteRequest(c, HandleDeleteRequest)
            \/ API!Topo!Server!Receive!GetRequest(c, HandleGetRequest)
            \/ API!Topo!Server!Receive!ListRequest(c, HandleListRequest)
            \/ API!Topo!Server!Receive!WatchRequest(c, HandleWatchRequest)
         
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
\* Last modified Fri Aug 13 15:49:50 PDT 2021 by jordanhalterman
\* Created Fri Aug 13 09:50:50 PDT 2021 by jordanhalterman
