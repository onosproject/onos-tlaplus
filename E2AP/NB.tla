------------------------------ MODULE NB ------------------------------

EXTENDS Naturals, Sequences, TLC, Messages

\* Message type constants
CONSTANT 
    SubscribeRequest,
    SubscribeResponse

VARIABLE nbConn

VARIABLE nbConnId

----

InitNBVars ==
    /\ nbConn = [c \in {} |-> [app |-> Nil, appnode |-> Nil, ricnode |-> Nil, messages |-> <<>>]]

----

NBSend(c, m) == nbConn' = [nbConn EXCEPT ![c] = [nbConn[c] EXCEPT !.messages = Append(nbConn[c].messages, m)]]

NBReceive(c) == nbConn' = [nbConn EXCEPT ![c] = [nbConn[c] EXCEPT !.messages = SubSeq(nbConn[c].messages, 2, Len(nbConn[c].messages))]]

NBReply(c, m) == nbConn' = [nbConn EXCEPT ![c] = [nbConn[c] EXCEPT !.messages = Append(SubSeq(nbConn[c].messages, 2, Len(nbConn[c].messages)), m)]]

----

NBConnect(app, appnode, ricnode) ==
    /\ nbConnId' = nbConnId + 1
    /\ nbConn' = nbConn @@ (nbConnId' :> [app |-> app, appnode |-> appnode, ricnode |-> ricnode, messages |-> <<>>])

NBDisconnect(id) ==
    /\ nbConn' = [c \in {v \in DOMAIN nbConn : v # id} |-> nbConn[c]]

----

NBNext ==
    \/ \E c \in DOMAIN nbConn : NBDisconnect(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:57:18 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:01:02 PDT 2021 by jordanhalterman
