-------------------------------- MODULE SCTP --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT Nil

LOCAL Min(s) == CHOOSE x \in s : \A y \in s : x >= y

LOCAL Max(s) == CHOOSE x \in s : \A y \in s : x <= y

VARIABLE conns

vars == <<conns>>

   ----------------------------- MODULE Client --------------------------

   CONSTANT ID

   Connect(dst) ==
      LET maxId == Max(DOMAIN conns)
          connId == Min({i \in 1..(maxId+1) : i \notin DOMAIN conns})
      IN conns' = conns @@ (connId :> [id |-> connId, src |-> ID, dst |-> dst, req |-> <<>>, res |-> <<>>])

   Disconnect(c) ==
      conns' = [x \in DOMAIN conns \ {c.id} |-> conns[x]]

   Send(c, m) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.req = Append(conns[c.id].req, m)]]

   Receive(c) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.res = SubSeq(conns[c.id].res, 2, Len(conns[c.id].res))]]

   Reply(c, m) ==
      conns' = [conns' EXCEPT ![c.id] = [conns'[c.id] EXCEPT !.req = Append(conns'[c.id].req, m)]]

   Handle(c, f(_, _)) == Len(c.res) > 0 /\ f(c, c.res[1])

   Connections == {c \in conns : c.src = ID}

   ======================================================================

Client(ID) == INSTANCE Client

   ----------------------------- MODULE Server --------------------------

   CONSTANT ID

   Send(c, m) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.res = Append(conns[c.id].res, m)]]

   Receive(c) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.req = SubSeq(conns[c.id].req, 2, Len(conns[c.id].req))]]

   Reply(c, m) ==
      conns' = [conns' EXCEPT ![c.id] = [conns'[c.id] EXCEPT !.res = Append(conns'[c.id].res, m)]]

   Handle(c, f(_, _)) == Len(c.req) > 0 /\ f(c, c.req[1])

   Connections == {c \in conns : c.dst = ID}

   ======================================================================

Server(ID) == INSTANCE Server

Init ==
   /\ conns = [c \in {} |-> [e2n |-> Nil, e2t |-> Nil, req |-> <<>>, res |-> <<>>]]

Next ==
   \/ UNCHANGED <<conns>>

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 05:40:27 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 12:21:16 PDT 2021 by jordanhalterman
