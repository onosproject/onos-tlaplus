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

   Connect(tgt) ==
      /\ tgt \in DOMAIN conns
      /\ LET maxId == Max({conns[tgt][i].connId : i \in conns[tgt]})
             connId == Min({i \in 1..(maxId+1) : i \notin DOMAIN conns[tgt]})
             conn == [id  |-> connId, 
                      src |-> ID, 
                      tgt |-> tgt, 
                      req |-> <<>>, 
                      res |-> <<>>]
         IN conns' = [conns EXCEPT ![tgt] = conns[tgt] @@ (connId :> conn)]

   Disconnect(conn) ==
      conns' = [conns EXCEPT ![conn.tgt] = [x \in DOMAIN conns[conn.tgt] \ {conn.id} |-> conns[conn.tgt][x]]]

   Send(conn, msg) ==
      conns' = [conns EXCEPT ![conn.tgt] = [
                   conns[conn.tgt] EXCEPT ![conn.id] = [
                      conns[conn.tgt][conn.id] EXCEPT !.req = Append(conns[conn.tgt][conn.id].req, msg)]]]

   Receive(conn) ==
      conns' = [conns EXCEPT ![conn.tgt] = [
                   conns[conn.tgt] EXCEPT ![conn.id] = [
                      conns[conn.tgt][conn.id] EXCEPT !.res = SubSeq(conns[conn.tgt][conn.id].res, 2, Len(conns[conn.tgt][conn.id].res))]]]

   Reply(conn, msg) ==
      conns' = [conns' EXCEPT ![conn.tgt] = [
                   conns'[conn.tgt] EXCEPT ![conn.id] = [
                      conns'[conn.tgt][conn.id] EXCEPT !.req = Append(conns'[conn.tgt][conn.id].req, msg)]]]

   Connections == {conn \in UNION {{conns[s][c] : c \in DOMAIN s} : s \in conns} : conn.src = ID}
   
   Connected(connId) == \E s \in conns : \E c \in s : c.id = connId
   
   Ready(conn) == Len(conn.res) > 0
   
   Read(conn) == conn.res[1]

   ======================================================================

Client(ID) == INSTANCE Client

   ----------------------------- MODULE Server --------------------------

   CONSTANT ID
   
   Start ==
      /\ ID \notin DOMAIN conns
      /\ conns' = conns @@ (ID :> [connId \in {} |-> [connId |-> connId]])

   Stop ==
      /\ ID \in DOMAIN conns
      /\ conns' = [c \in {c \in DOMAIN conns : c # ID} |-> conns[c]]

   Send(conn, msg) ==
      /\ Assert(conn.tgt = ID, "Send on invalid connection")
      /\ conns' = [conns EXCEPT ![conn.tgt] = [
                      conns[conn.tgt] EXCEPT ![conn.id] = [
                         conns[conn.tgt][conn.id] EXCEPT !.res = Append(conns[conn.tgt][conn.id].res, msg)]]]

   Receive(conn) ==
      /\ Assert(conn.tgt = ID, "Receive on invalid connection")
      /\ conns' = [conns EXCEPT ![conn.tgt] = [
                      conns[conn.tgt] EXCEPT ![conn.id] = [
                         conns[conn.tgt][conn.id] EXCEPT !.res = SubSeq(conns[conn.tgt][conn.id].req, 2, Len(conns[conn.tgt][conn.id].req))]]]

   Reply(conn, msg) ==
      /\ Assert(conn.tgt = ID, "Reply on invalid connection")
      /\ conns' = [conns' EXCEPT ![conn.tgt] = [
                   conns'[conn.tgt] EXCEPT ![conn.id] = [
                      conns'[conn.tgt][conn.id] EXCEPT !.req = Append(conns'[conn.tgt][conn.id].res, msg)]]]

   Connections == {conn \in UNION {{conns[s][c] : c \in DOMAIN s} : s \in conns} : conn.tgt = ID}

   Connected(connId) == \E s \in conns : \E c \in s : c.id = connId
   
   Ready(conn) == Len(conn.req) > 0
   
   Read(conn) == conn.req[1]

   ======================================================================

Server(ID) == INSTANCE Server

Init ==
   /\ conns = [id \in {} |-> [
                  connId \in {} |-> [connId |-> connId, 
                                     src    |-> Nil, 
                                     tgt    |-> Nil, 
                                     req    |-> <<>>, 
                                     res    |-> <<>>]]]

Next ==
   \/ UNCHANGED <<conns>>

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 14:35:07 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 12:21:16 PDT 2021 by jordanhalterman
