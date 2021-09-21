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
      /\ dst \in DOMAIN conns
      /\ LET maxId == Max({conns[dst][i].connId : i \in conns[dst]})
             connId == Min({i \in 1..(maxId+1) : i \notin DOMAIN conns[dst]})
             conn == [id  |-> connId, 
                      src |-> ID, 
                      dst |-> dst, 
                      req |-> <<>>, 
                      res |-> <<>>]
         IN conns' = [conns EXCEPT ![dst] = conns[dst] @@ (connId :> conn)]

   Disconnect(conn) ==
      conns' = [conns EXCEPT ![conn.dst] = [x \in DOMAIN conns[conn.dst] \ {conn.id} |-> conns[conn.dst][x]]]

   Send(conn, msg) ==
      conns' = [conns EXCEPT ![conn.dst] = [
                   conns[conn.dst] EXCEPT ![conn.id] = [
                      conns[conn.dst][conn.id] EXCEPT !.req = Append(conns[conn.dst][conn.id].req, msg)]]]

   Receive(conn) ==
      conns' = [conns EXCEPT ![conn.dst] = [
                   conns[conn.dst] EXCEPT ![conn.id] = [
                      conns[conn.dst][conn.id] EXCEPT !.res = SubSeq(conns[conn.dst][conn.id].res, 2, Len(conns[conn.dst][conn.id].res))]]]

   Reply(conn, msg) ==
      conns' = [conns' EXCEPT ![conn.dst] = [
                   conns'[conn.dst] EXCEPT ![conn.id] = [
                      conns'[conn.dst][conn.id] EXCEPT !.req = Append(conns'[conn.dst][conn.id].req, msg)]]]

   Connections == {conn \in UNION {{conns[s][c] : c \in DOMAIN s} : s \in conns} : conn.src = ID}
   
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
      /\ Assert(conn.dst = ID, "Send on invalid connection")
      /\ conns' = [conns EXCEPT ![conn.dst] = [
                      conns[conn.dst] EXCEPT ![conn.id] = [
                         conns[conn.dst][conn.id] EXCEPT !.res = Append(conns[conn.dst][conn.id].res, msg)]]]

   Receive(conn) ==
      /\ Assert(conn.dst = ID, "Receive on invalid connection")
      /\ conns' = [conns EXCEPT ![conn.dst] = [
                      conns[conn.dst] EXCEPT ![conn.id] = [
                         conns[conn.dst][conn.id] EXCEPT !.res = SubSeq(conns[conn.dst][conn.id].req, 2, Len(conns[conn.dst][conn.id].req))]]]

   Reply(conn, msg) ==
      /\ Assert(conn.dst = ID, "Reply on invalid connection")
      /\ conns' = [conns' EXCEPT ![conn.dst] = [
                   conns'[conn.dst] EXCEPT ![conn.id] = [
                      conns'[conn.dst][conn.id] EXCEPT !.req = Append(conns'[conn.dst][conn.id].res, msg)]]]

   Connections == {conn \in UNION {{conns[s][c] : c \in DOMAIN s} : s \in conns} : conn.dst = ID}

   Ready(conn) == Len(conn.req) > 0
   
   Read(conn) == conn.req[1]

   ======================================================================

Server(ID) == INSTANCE Server

Init ==
   /\ conns = [id \in {} |-> [
                  connId \in {} |-> [connId |-> connId, 
                                     src    |-> Nil, 
                                     dst    |-> Nil, 
                                     req    |-> <<>>, 
                                     res    |-> <<>>]]]

Next ==
   \/ UNCHANGED <<conns>>

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 09:25:14 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 12:21:16 PDT 2021 by jordanhalterman
