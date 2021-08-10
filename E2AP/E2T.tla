-------------------------------- MODULE E2T --------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, NB, SB

\* The set of all E2T nodes
CONSTANT E2TNode

----

InitE2TVars == TRUE

----

E2THandleE2SetupRequest(n, c, m) ==
    /\ SBReply(c, [type |-> E2SetupResponse])
    /\ UNCHANGED <<>>

E2THandleMessage(c) ==
    /\ Len(sbConn[c].messages) > 0
    /\ LET m == sbConn[c].messages[1] IN
           /\ \/ /\ m.type = E2Setup
                 /\ E2THandleE2SetupRequest(sbConn[c].ricnode, c, m)
           /\ UNCHANGED <<>>

----

E2TNext ==
    \/ \E c \in DOMAIN sbConn : 
          E2THandleMessage(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 03:51:50 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:56:24 PDT 2021 by jordanhalterman
