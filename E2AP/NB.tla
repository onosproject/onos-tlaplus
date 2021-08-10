------------------------------ MODULE NB ------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

CONSTANT Nil

\* Message type constants
CONSTANT 
    SubscribeRequest,
    SubscribeResponse

VARIABLE conn

VARIABLE connId

----

Init ==
    /\ conn = [c \in {} |-> [app |-> Nil, appnode |-> Nil, ricnode |-> Nil, messages |-> <<>>]]

----

Send(c, m) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = Append(conn[c].messages, m)]]

Receive(c) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = SubSeq(conn[c].messages, 2, Len(conn[c].messages))]]

Reply(c, m) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = Append(SubSeq(conn[c].messages, 2, Len(conn[c].messages)), m)]]

----

Connect(app, appnode, ricnode) ==
    /\ connId' = connId + 1
    /\ conn' = conn @@ (connId' :> [app |-> app, appnode |-> appnode, ricnode |-> ricnode, messages |-> <<>>])

Disconnect(id) ==
    /\ conn' = [c \in {v \in DOMAIN conn : v # id} |-> conn[c]]

----

Next ==
    \/ \E c \in DOMAIN conn : Disconnect(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 04:33:16 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:01:02 PDT 2021 by jordanhalterman
