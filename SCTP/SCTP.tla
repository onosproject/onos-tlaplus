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

   Disconnect(conn) ==
      conns' = [x \in DOMAIN conns \ {conn.id} |-> conns[x]]

   Send(conn, msg) ==
      conns' = [conns EXCEPT ![conn.id] = [conns[conn.id] EXCEPT !.req = Append(conns[conn.id].req, msg)]]

   Receive(conn) ==
      conns' = [conns EXCEPT ![conn.id] = [conns[conn.id] EXCEPT !.res = SubSeq(conns[conn.id].res, 2, Len(conns[conn.id].res))]]

   Reply(conn, msg) ==
      conns' = [conns' EXCEPT ![conn.id] = [conns'[conn.id] EXCEPT !.req = Append(conns'[conn.id].req, msg)]]

   Handle(conn, handler(_, _)) == Len(conn.res) > 0 /\ handler(conn, conn.res[1])

   Connections == {conn \in conns : conn.src = ID}

   ======================================================================

Client(ID) == INSTANCE Client

   ----------------------------- MODULE Server --------------------------

   CONSTANT ID

   Send(conn, msg) ==
      conns' = [conns EXCEPT ![conn.id] = [conns[conn.id] EXCEPT !.res = Append(conns[conn.id].res, msg)]]

   Receive(conn) ==
      conns' = [conns EXCEPT ![conn.id] = [conns[conn.id] EXCEPT !.req = SubSeq(conns[conn.id].req, 2, Len(conns[conn.id].req))]]

   Reply(conn, msg) ==
      conns' = [conns' EXCEPT ![conn.id] = [conns'[conn.id] EXCEPT !.res = Append(conns'[conn.id].res, msg)]]

   Handle(conn, handler(_, _)) == Len(conn.req) > 0 /\ handler(conn, conn.req[1])

   Connections == {conn \in conns : conn.dst = ID}

   ======================================================================

Server(ID) == INSTANCE Server

Init ==
   /\ conns = [connId \in {} |-> [connId |-> connId, 
                                  src    |-> Nil, 
                                  dst    |-> Nil, 
                                  req    |-> <<>>, 
                                  res    |-> <<>>]]

Next ==
   \/ UNCHANGED <<conns>>

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 08:27:33 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 12:21:16 PDT 2021 by jordanhalterman
