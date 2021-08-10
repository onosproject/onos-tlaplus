------------------------------ MODULE SB ------------------------------

EXTENDS Protocol

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

CONSTANT Nil

VARIABLE conn

VARIABLE connId

----

Init ==
    /\ conn = [c \in {} |-> [e2node |-> Nil, ricnode |-> Nil, messages |-> <<>>]]

----

Send(c, m) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = Append(conn[c].messages, m)]]

Receive(c) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = SubSeq(conn[c].messages, 2, Len(conn[c].messages))]]

Reply(c, m) == conn' = [conn EXCEPT ![c] = [conn[c] EXCEPT !.messages = Append(SubSeq(conn[c].messages, 2, Len(conn[c].messages)), m)]]

----

Connect(e2node, ricnode) ==
    /\ connId' = connId + 1
    /\ conn' = conn @@ (connId' :> [e2node |-> e2node, ricnode |-> ricnode, messages |-> <<>>])

Disconnect(id) ==
    /\ conn' = [c \in {v \in DOMAIN conn : v # id} |-> conn[c]]

----

Next ==
    \/ \E c \in DOMAIN conn : Disconnect(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 04:49:43 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:01:02 PDT 2021 by jordanhalterman
