--------------------------------- MODULE Topo --------------------------------

(*
The Topo module provides a formal specification of the µONOS topology 
service. The spec defines the client and server interfaces for µONOS Topo
and provides helpers for managing and operating on connections.
*)

CONSTANT Nil

\* Message type constants
CONSTANT 
   CreateRequestType,
   CreateResponseType
CONSTANTS
   UpdateRequestType,
   UpdateResponseType
CONSTANTS
   DeleteRequestType,
   DeleteResponseType
CONSTANT 
   GetRequestType,
   GetResponseType
CONSTANT 
   ListRequestType,
   ListResponseType
CONSTANT 
   WatchRequestType,
   WatchResponseType

LOCAL messageTypes == 
   {CreateRequestType,
    CreateResponseType,
    UpdateRequestType,
    UpdateResponseType,
    DeleteRequestType,
    DeleteResponseType,
    GetRequestType,
    GetResponseType,
    ListRequestType,
    ListResponseType,
    WatchRequestType,
    WatchResponseType}

\* Message types should be defined as strings to simplify debugging
ASSUME \A m \in messageTypes : m \in STRING

VARIABLE conns

LOCAL INSTANCE API

LOCAL INSTANCE TLC

vars == <<conns>>

   ----------------------------- MODULE Messages ----------------------------
   
   (*
   The Messages module defines predicates for receiving, sending, and
   verifying all the messages supported by µONOS Topo.
   *)
   
   ----
   
   (*
   This section defines predicates for identifying µONOS Topo message 
   types on the network.
   *)
   
   IsCreateRequest(m) == m.type = CreateRequestType
   
   IsCreateResponse(m) == m.type = CreateResponseType
   
   IsUpdateRequest(m) == m.type = UpdateRequestType
   
   IsUpdateResponse(m) == m.type = UpdateResponseType
   
   IsDeleteRequest(m) == m.type = DeleteRequestType
   
   IsDeleteResponse(m) == m.type = DeleteResponseType
   
   IsGetRequest(m) == m.type = GetRequestType
   
   IsGetResponse(m) == m.type = GetResponseType
   
   IsListRequest(m) == m.type = ListRequestType
   
   IsListResponse(m) == m.type = ListResponseType
   
   IsWatchRequest(m) == m.type = WatchRequestType
   
   IsWatchResponse(m) == m.type = WatchResponseType
   
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
   
   CreateRequest(m) == 
      IF Assert(ValidCreateRequest(m), "Invalid CreateRequest") 
      THEN SetType(m, CreateRequestType) 
      ELSE Nil
   
   CreateResponse(m) == 
      IF Assert(ValidCreateResponse(m), "Invalid CreateResponse") 
      THEN SetType(m, CreateResponseType) 
      ELSE Nil
   
   UpdateRequest(m) == 
      IF Assert(ValidUpdateRequest(m), "Invalid UpdateRequest") 
      THEN SetType(m, UpdateRequestType) 
      ELSE Nil
   
   UpdateResponse(m) == 
      IF Assert(ValidUpdateResponse(m), "Invalid UpdateResponse") 
      THEN SetType(m, UpdateResponseType) 
      ELSE Nil
   
   DeleteRequest(m) == 
      IF Assert(ValidDeleteRequest(m), "Invalid DeleteRequest") 
      THEN SetType(m, DeleteRequestType) 
      ELSE Nil
   
   DeleteResponse(m) == 
      IF Assert(ValidDeleteResponse(m), "Invalid DeleteResponse") 
      THEN SetType(m, DeleteResponseType) 
      ELSE Nil
   
   GetRequest(m) == 
      IF Assert(ValidGetRequest(m), "Invalid GetRequest") 
      THEN SetType(m, GetRequestType) 
      ELSE Nil
   
   GetResponse(m) == 
      IF Assert(ValidGetResponse(m), "Invalid GetResponse") 
      THEN SetType(m, GetResponseType) 
      ELSE Nil
   
   ListRequest(m) == 
      IF Assert(ValidListRequest(m), "Invalid ListRequest") 
      THEN SetType(m, ListRequestType) 
      ELSE Nil
   
   ListResponse(m) == 
      IF Assert(ValidListResponse(m), "Invalid ListResponse") 
      THEN SetType(m, ListResponseType) 
      ELSE Nil
   
   WatchRequest(m) == 
      IF Assert(ValidWatchRequest(m), "Invalid WatchRequest") 
      THEN SetType(m, WatchRequestType) 
      ELSE Nil
   
   WatchResponse(m) == 
      IF Assert(ValidWatchResponse(m), "Invalid WatchResponse") 
      THEN SetType(m, WatchResponseType) 
      ELSE Nil
   
   ======================================================================

\* The Messages module is instantiated locally to avoid access from outside
\* the module.
LOCAL Messages == INSTANCE Messages

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
         /\ gRPC!Client!Send(c, Messages!CreateRequest(m))
      
      UpdateRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!UpdateRequest(m))
      
      DeleteRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!DeleteRequest(m))
      
      GetRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!GetRequest(m))
      
      ListRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!ListRequest(m))
      
      WatchRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WatchRequest(m))
      
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
         /\ gRPC!Server!Reply(c, Messages!CreateResponse(m))
      
      UpdateResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!UpdateResponse(m))
      
      DeleteResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!DeleteResponse(m))
      
      GetResponse(c, m) == 
         /\ gRPC!Server!Reply(c, Messages!GetResponse(m))
      
      ListResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!ListResponse(m))
      
      WatchResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WatchResponse(m))
      
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

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 15:16:04 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 15:07:05 PDT 2021 by jordanhalterman
