--------------------------------- MODULE Topo --------------------------------

(*
The Topo module provides a formal specification of the µONOS topology 
service. The spec defines the client and server interfaces for µONOS Topo
and provides helpers for managing and operating on connections.
*)

CONSTANT Nil

VARIABLE conns

gRPC == INSTANCE gRPC WITH
   OK <- "OK",
   Error <- "Error"

LOCAL INSTANCE TLC

vars == <<conns>>

   ----------------------------- MODULE Messages ----------------------------
   
   (*
   The Messages module defines predicates for receiving, sending, and
   verifying all the messages supported by µONOS Topo.
   *)
   
   \* Message type constants
   CONSTANT 
      CreateRequest,
      CreateResponse
   CONSTANTS
      UpdateRequest,
      UpdateResponse
   CONSTANTS
      DeleteRequest,
      DeleteResponse
   CONSTANT 
      GetRequest,
      GetResponse
   CONSTANT 
      ListRequest,
      ListResponse
   CONSTANT 
      WatchRequest,
      WatchResponse
   
   LOCAL messageTypes == 
      {CreateRequest,
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
       WatchResponse}
   
   \* Message types should be defined as strings to simplify debugging
   ASSUME \A m \in messageTypes : m \in STRING
      
   ----
   
   (*
   This section defines predicates for identifying µONOS Topo message 
   types on the network.
   *)
   
   IsCreateRequest(m) == m.type = CreateRequest
   
   IsCreateResponse(m) == m.type = CreateResponse
   
   IsUpdateRequest(m) == m.type = UpdateRequest
   
   IsUpdateResponse(m) == m.type = UpdateResponse
   
   IsDeleteRequest(m) == m.type = DeleteRequest
   
   IsDeleteResponse(m) == m.type = DeleteResponse
   
   IsGetRequest(m) == m.type = GetRequest
   
   IsGetResponse(m) == m.type = GetResponse
   
   IsListRequest(m) == m.type = ListRequest
   
   IsListResponse(m) == m.type = ListResponse
   
   IsWatchRequest(m) == m.type = WatchRequest
   
   IsWatchResponse(m) == m.type = WatchResponse
   
   ----
      
   (*
   This section defines predicates for validating µONOS Topo message contents.
   The predicates provide precise documentation on the E2AP message format 
   and are used within the spec to verify that steps adhere to the E2AP 
   protocol specification.
   *)
   
   LOCAL ValidCreateRequest(m) == TRUE
   
   LOCAL ValidCreateResponse(m) == TRUE
   
   LOCAL ValidUpdateRequest(m) == TRUE
   
   LOCAL ValidUpdateResponse(m) == TRUE
   
   LOCAL ValidDeleteRequest(m) == TRUE
   
   LOCAL ValidDeleteResponse(m) == TRUE
   
   LOCAL ValidGetRequest(m) == TRUE
   
   LOCAL ValidGetResponse(m) == TRUE
   
   LOCAL ValidListRequest(m) == TRUE
   
   LOCAL ValidListResponse(m) == TRUE
   
   LOCAL ValidWatchRequest(m) == TRUE
   
   LOCAL ValidWatchResponse(m) == TRUE
   
   ----
   
   (*
   This section defines operators for constructing µONOS Topo messages.
   *)
   
   LOCAL SetType(m, t) == [m EXCEPT !.type = t]
   
   WithCreateRequest(m) == 
      IF Assert(ValidCreateRequest(m), "Invalid CreateRequest") 
      THEN SetType(m, CreateRequest) 
      ELSE Nil
   
   WithCreateResponse(m) == 
      IF Assert(ValidCreateResponse(m), "Invalid CreateResponse") 
      THEN SetType(m, CreateResponse) 
      ELSE Nil
   
   WithUpdateRequest(m) == 
      IF Assert(ValidUpdateRequest(m), "Invalid UpdateRequest") 
      THEN SetType(m, UpdateRequest) 
      ELSE Nil
   
   WithUpdateResponse(m) == 
      IF Assert(ValidUpdateResponse(m), "Invalid UpdateResponse") 
      THEN SetType(m, UpdateResponse) 
      ELSE Nil
   
   WithDeleteRequest(m) == 
      IF Assert(ValidDeleteRequest(m), "Invalid DeleteRequest") 
      THEN SetType(m, DeleteRequest) 
      ELSE Nil
   
   WithDeleteResponse(m) == 
      IF Assert(ValidDeleteResponse(m), "Invalid DeleteResponse") 
      THEN SetType(m, DeleteResponse) 
      ELSE Nil
   
   WithGetRequest(m) == 
      IF Assert(ValidGetRequest(m), "Invalid GetRequest") 
      THEN SetType(m, GetRequest) 
      ELSE Nil
   
   WithGetResponse(m) == 
      IF Assert(ValidGetResponse(m), "Invalid GetResponse") 
      THEN SetType(m, GetResponse) 
      ELSE Nil
   
   WithListRequest(m) == 
      IF Assert(ValidListRequest(m), "Invalid ListRequest") 
      THEN SetType(m, ListRequest) 
      ELSE Nil
   
   WithListResponse(m) == 
      IF Assert(ValidListResponse(m), "Invalid ListResponse") 
      THEN SetType(m, ListResponse) 
      ELSE Nil
   
   WithWatchRequest(m) == 
      IF Assert(ValidWatchRequest(m), "Invalid WatchRequest") 
      THEN SetType(m, WatchRequest) 
      ELSE Nil
   
   WithWatchResponse(m) == 
      IF Assert(ValidWatchResponse(m), "Invalid WatchResponse") 
      THEN SetType(m, WatchResponse) 
      ELSE Nil
   
   ======================================================================

\* The Messages module is instantiated locally to avoid access from outside
\* the module.
LOCAL Messages == INSTANCE Messages WITH
   CreateRequest <- "CreateRequest",
   CreateResponse <- "CreateResponse",
   UpdateRequest <- "UpdateRequest",
   UpdateResponse <- "UpdateResponse",
   DeleteRequest <- "DeleteRequest",
   DeleteResponse <- "DeleteResponse",
   GetRequest <- "GetRequest",
   GetResponse <- "GetResponse",
   ListRequest <- "ListRequest",
   ListResponse <- "ListResponse",
   WatchRequest <- "WatchRequest",
   WatchResponse <- "WatchResponse"

   ------------------------------ MODULE Client -----------------------------
   
   (*
   The Client module provides operators for managing and operating on Topo
   client connections and specifies the message types supported for the
   client.
   *)
   
      ---------------------------- MODULE Requests --------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the Topo client.
      *)
      
      CreateRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WithCreateRequest(m))
      
      UpdateRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!WithUpdateRequest(m))
      
      DeleteRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!WithDeleteRequest(m))
      
      GetRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WithGetRequest(m))
      
      ListRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WithListRequest(m))
      
      WatchRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WithWatchRequest(m))
      
      =======================================================================
   
   \* Instantiate the Topo!Client!Send module
   Send == INSTANCE Requests
   
      --------------------------- MODULE Responses --------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an Topo client.
      *)
      
      CreateResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsCreateResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      UpdateResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsUpdateResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      DeleteResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsDeleteResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      GetResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsGetResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      ListResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsListResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      WatchResponse(c, h(_, _)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsWatchResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(c, m))
      
      =======================================================================
   
   \* Instantiate the Topo!Client!Receive module
   Receive == INSTANCE Responses
   
   Connect(s, d) == gRPC!Client!Connect(s, d)
   
   Disconnect(c) == gRPC!Client!Disconnect(c)
   
   ==========================================================================

\* Provides operators for the Topo client
Client == INSTANCE Client
      
   ------------------------------ MODULE Server -----------------------------
   
   (*
   The Server module provides operators for managing and operating on Topo
   servers and specifies the message types supported for the server.
   *)
   
      --------------------------- MODULE Responses --------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the Topo server.
      *)
      
      CreateResponse(c, m) == 
         /\ gRPC!Server!Reply(c, Messages!WithCreateResponse(m))
      
      UpdateResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithUpdateResponse(m))
      
      DeleteResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithDeleteResponse(m))
      
      GetResponse(c, m) == 
         /\ gRPC!Server!Reply(c, Messages!WithGetResponse(m))
      
      ListResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithListResponse(m))
      
      WatchResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithWatchResponse(m))
      
      =======================================================================
   
   \* Instantiate the Topo!Server!Send module
   Send == INSTANCE Responses
   
      --------------------------- MODULE Requests ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an Topo server.
      *)
      
      CreateRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsCreateRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      UpdateRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsUpdateRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      DeleteRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsDeleteRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      GetRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsGetRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      ListRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsListRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      WatchRequest(c, h(_, _)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsWatchRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(c, m))
      
      =======================================================================
   
   \* Instantiate the Topo!Server!Receive module
   Receive == INSTANCE Requests
   
   ==========================================================================

\* Provides operators for the Topo server
Server == INSTANCE Server

\* The set of all open Topo connections
Connections == gRPC!Connections

Init ==
   /\ gRPC!Init

Next ==
   /\ gRPC!Next

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 15:38:22 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 15:07:05 PDT 2021 by jordanhalterman
