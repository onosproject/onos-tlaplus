-------------------------------- MODULE E2T --------------------------------

EXTENDS Protocol

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL NB == INSTANCE NB

\* The set of all E2T nodes
CONSTANT E2TNode

VARIABLE sbConnId, sbConn

LOCAL SB == INSTANCE SB WITH Nil <- "", connId <- sbConnId, conn <- sbConn

----

InitE2TVars == 
    /\ SB!Init
    /\ NB!Init

----

LOCAL E2THandleE2SetupRequest(n, c, m) ==
    /\ SB!Reply(c, [type |-> E2SetupResponse])
    /\ UNCHANGED <<>>

LOCAL E2THandleMessage(c) ==
    /\ Len(SB!conn[c].messages) > 0
    /\ LET m == SB!conn[c].messages[1] IN
           /\ \/ /\ m.type = SB!E2Setup
                 /\ E2THandleE2SetupRequest(SB!conn[c].ricnode, c, m)
           /\ UNCHANGED <<>>

----

E2TNext ==
    \/ SB!Next
    \/ \E c \in DOMAIN SB!conn : 
          E2THandleMessage(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 04:51:39 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:56:24 PDT 2021 by jordanhalterman
