-------------------------------- MODULE RIC --------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, NB, SB

\* The set of all RIC nodes
CONSTANT RICNode

----

InitRICVars == TRUE

----

RICHandleE2SetupRequest(n, c, m) ==
    /\ SBReply(c, [type |-> E2SetupResponse])
    /\ UNCHANGED <<>>

RICHandleMessage(c) ==
    /\ Len(sbConn[c].messages) > 0
    /\ LET m == sbConn[c].messages[1] IN
           /\ \/ /\ m.type = E2Setup
                 /\ RICHandleE2SetupRequest(sbConn[c].ricnode, c, m)
           /\ UNCHANGED <<>>

----

RICNext ==
    \/ \E c \in DOMAIN sbConn : 
          RICHandleMessage(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:56:14 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:56:24 PDT 2021 by jordanhalterman
