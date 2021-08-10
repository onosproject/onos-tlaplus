-------------------------------- MODULE Topo --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT Nil

CONSTANT CreateRequest,
         CreateResponse,
         UpdateRequest,
         UpdateResponse,
         DeleteRequest,
         DeleteResponse,
         GetRequest,
         GetResponse,
         ListRequest,
         ListResponse,
         WatchRequest,
         WatchResponse

CONSTANT Kind,
         Entity,
         Relation

VARIABLES topoSbConn, topoSbConnId

TopoSB == INSTANCE Messaging WITH Nil <- "<nil>", conn <- topoSbConn, connId <- topoSbConnId

----

TopoHandleCreateRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleUpdateRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleDeleteRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleGetRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleListRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleWatchRequest(c, m) ==
    /\ TopoSB!Receive(c)
    /\ UNCHANGED <<>>

TopoHandleMessage(c, m) ==
   /\ \/ /\ m.type = CreateRequest
         /\ TopoHandleCreateRequest(c, m)
      \/ /\ m.type = UpdateRequest
         /\ TopoHandleUpdateRequest(c, m)
      \/ /\ m.type = DeleteRequest
         /\ TopoHandleDeleteRequest(c, m)
      \/ /\ m.type = GetRequest
         /\ TopoHandleGetRequest(c, m)
      \/ /\ m.type = ListRequest
         /\ TopoHandleListRequest(c, m)
      \/ /\ m.type = WatchRequest
         /\ TopoHandleWatchRequest(c, m)
   /\ UNCHANGED <<topoSbConnId>>

----

TopoInit ==
   /\ TopoSB!Init

TopoNext ==
   \/ \E c \in TopoSB!Connections : TopoSB!Disconnect(c)
   \/ \E c \in TopoSB!Connections : TopoSB!Handle(c, TopoHandleMessage)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:37:13 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:19 PDT 2021 by jordanhalterman
