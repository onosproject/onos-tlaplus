-------------------------------- MODULE gRPC --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT Nil

CONSTANT OK

CONSTANT Error

CONSTANT
   Unknown,
   Canceled,
   NotFound,
   AlreadyExists,
   Unauthorized,
   Forbidden,
   Conflict,
   Invalid,
   Unavailable,
   NotSupported,
   Timeout,
   Internal

----

LOCAL Min(s) == CHOOSE x \in s : \A y \in s : x >= y

LOCAL Max(s) == CHOOSE x \in s : \A y \in s : x <= y

VARIABLE conns

vars == <<conns>>

   ------------------------------ MODULE Client -------------------------

   Connect(src, dst) ==
      LET maxId == Max(DOMAIN conns)
          connId == Min({i \in 1..(maxId+1) : i \notin DOMAIN conns})
      IN conns' = conns @@ (connId :> [id |-> connId, src |-> src, dst |-> dst, req |-> <<>>, res |-> <<>>])

   Disconnect(c) ==
      conns' = [x \in DOMAIN conns \ {c.id} |-> conns[x]]

   Send(c, m) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.req = Append(conns[c.id].req, m)]]

   Receive(c) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.res = SubSeq(conns[c.id].res, 2, Len(conns[c.id].res))]]

   Reply(c, m) ==
      conns' = [conns' EXCEPT ![c.id] = [conns'[c.id] EXCEPT !.req = Append(conns'[c.id].req, m)]]

   Handle(c, f(_, _)) == Len(c.res) > 0 /\ f(c, c.res[1])

   ======================================================================

Client == INSTANCE Client

Connections == {conns[c] : c \in DOMAIN conns}

   ----------------------------- MODULE Server --------------------------

   Send(c, m) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.res = Append(conns[c.id].res, m)]]

   Receive(c) ==
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.req = SubSeq(conns[c.id].req, 2, Len(conns[c.id].req))]]

   Reply(c, m) ==
      conns' = [conns' EXCEPT ![c.id] = [conns'[c.id] EXCEPT !.res = Append(conns'[c.id].res, m)]]

   Handle(c, f(_, _)) == Len(c.req) > 0 /\ f(c, c.req[1])

   ======================================================================

Server == INSTANCE Server

Init ==
   /\ conns = [c \in {} |-> [src |-> Nil, dst |-> Nil, req |-> <<>>, res |-> <<>>]]

Next ==
   \/ UNCHANGED <<conns>>

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 15:12:09 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 12:23:50 PDT 2021 by jordanhalterman
