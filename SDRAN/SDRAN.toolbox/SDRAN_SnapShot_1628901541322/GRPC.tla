-------------------------------- MODULE GRPC --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT Nil

----

LOCAL Min(s) == CHOOSE x \in s : \A y \in s : x >= y

LOCAL Max(s) == CHOOSE x \in s : \A y \in s : x <= y

VARIABLE servers

VARIABLE conns

vars == <<servers, conns>>
   
   ------------------------------ MODULE Client -------------------------
   
   Connect(c, s) ==
      LET maxId == Max(DOMAIN conns)
          connId == Min({i \in 1..(maxId+1) : i \notin DOMAIN conns})
      IN conns' = conns @@ (connId :> [id |-> connId, src |-> c, dst |-> s, req |-> <<>>, res |-> <<>>])
   
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
   
   Start(s) ==
      /\ servers' = servers \cup {s}
      /\ UNCHANGED <<conns>>
   
   Stop(s) == 
      /\ servers' = servers \ {s}
      /\ conns' = [c \in DOMAIN conns \ {c \in conns : conns[c].dst # s} |-> conns[c]]
   
   Send(c, m) == 
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.res = Append(conns[c.id].res, m)]]
   
   Receive(c) == 
      conns' = [conns EXCEPT ![c.id] = [conns[c.id] EXCEPT !.req = SubSeq(conns[c.id].req, 2, Len(conns[c.id].req))]]
   
   Reply(c, m) == 
      conns' = [conns' EXCEPT ![c.id] = [conns'[c.id] EXCEPT !.res = Append(conns'[c.id].res, m)]]
   
   Handle(c, f(_, _)) == Len(c.req) > 0 /\ f(c, c.req[1])
   
   ======================================================================

Servers == servers
   
Server == INSTANCE Server
      
Init == 
   /\ servers = {}
   /\ conns = [c \in {} |-> [e2n |-> Nil, e2t |-> Nil, req |-> <<>>, res |-> <<>>]]

Next == 
   \/ TRUE
       
=============================================================================
\* Modification History
\* Last modified Fri Aug 13 16:27:39 PDT 2021 by jordanhalterman
\* Created Fri Aug 13 14:42:38 PDT 2021 by jordanhalterman
