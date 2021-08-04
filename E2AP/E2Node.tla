------------------------------- MODULE E2Node -------------------------------

EXTENDS RIC, SB

\* The set of all E2 nodes
CONSTANT E2Node

----

InitE2NodeVars == TRUE

----

E2NodeSendE2SetupRequest(n, c) ==
    /\ SBSend(c, [type |-> E2Setup])
    /\ UNCHANGED <<>>

E2NodeHandleE2SetupResponse(n, c, m) ==
    /\ SBReceive(c)
    /\ UNCHANGED <<>>

E2NodeHandleMessage(c) ==
    /\ Len(sbConn[c].messages) > 0
    /\ LET m == sbConn[c].messages[1] IN
           /\ \/ /\ m.type = E2SetupResponse
                 /\ E2NodeHandleE2SetupResponse(sbConn[c].e2node, c, m)
           /\ UNCHANGED <<>>

----

E2NodeNext ==
    \/ \E n \in E2Node, r \in RICNode : 
          SBConnect(n, r)
    \/ \E c \in DOMAIN sbConn : 
          E2NodeHandleMessage(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:55:15 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:00:09 PDT 2021 by jordanhalterman
