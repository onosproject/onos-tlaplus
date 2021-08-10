------------------------------- MODULE App -------------------------------

EXTENDS E2T, NB

\* The domain of all apps and their nodes
CONSTANT App

----

InitAppVars == TRUE

----

AppNodeSendSubscribeRequest(n, c) ==
    /\ NBSend(c, [type |-> SubscribeRequest])
    /\ UNCHANGED <<>>

AppNodeHandleSubscribeResponse(a, n, c, m) ==
    /\ NBReceive(c)
    /\ UNCHANGED <<>>

AppNodeHandleMessage(c) ==
    /\ Len(nbConn[c].messages) > 0
    /\ LET m == nbConn[c].messages[1] IN
           /\ \/ /\ m.type = SubscribeResponse
                 /\ AppNodeHandleSubscribeResponse(nbConn[c].app, nbConn[c].appnode, c, m)
           /\ UNCHANGED <<>>

----

AppNext ==
    \/ \E a \in DOMAIN App : 
          \E n \in App[a], r \in E2TNode : 
             NBConnect(a, n, r)
    \/ \E c \in DOMAIN nbConn : 
          AppNodeHandleMessage(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 03:52:05 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:00:09 PDT 2021 by jordanhalterman
