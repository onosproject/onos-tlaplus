----------------------------- MODULE Messaging -----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT Nil

VARIABLES conn, connId

----

Connections == {conn[c] : c \in DOMAIN conn}

Connect(n, m) ==
   /\ connId' = connId + 1
   /\ conn' = conn @@ (connId' :> [id |-> connId', src |-> n, dst |-> m, msgs |-> <<>>])

Disconnect(c) ==
   /\ conn' = [x \in {y \in DOMAIN conn : y # c.id} |-> conn[x]]
   /\ UNCHANGED <<connId>>

Send(c, m) == 
   /\ conn' = [conn EXCEPT ![c.id] = [conn[c.id] EXCEPT !.msgs = Append(conn[c.id].msgs, m)]]
   /\ UNCHANGED <<connId>>

Receive(c) == 
   /\ conn' = [conn EXCEPT ![c.id] = [conn[c.id] EXCEPT !.msgs = SubSeq(conn[c.id].msgs, 2, Len(conn[c.id].msgs))]]
   /\ UNCHANGED <<connId>>

Reply(c, m) == 
   /\ conn' = [conn EXCEPT ![c.id] = [conn[c.id] EXCEPT !.msgs = Append(SubSeq(conn[c.id].msgs, 2, Len(conn[c.id].msgs)), m)]]
   /\ UNCHANGED <<connId>>

Handle(c, f(_, _)) == Len(c.msgs) > 0 /\ f(c, c.msgs[1])

----

Init ==
    /\ connId = 0
    /\ conn = [c \in {} |-> [e2n |-> Nil, e2t |-> Nil, msgs |-> <<>>]]

Next == \E c \in DOMAIN conn : Disconnect(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:31:18 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 05:35:32 PDT 2021 by jordanhalterman
