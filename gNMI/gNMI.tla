-------------------------------- MODULE gNMI --------------------------------


LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

CONSTANT Nil

CONSTANT OK, Error

VARIABLE conns

gRPC == INSTANCE gRPC WITH
   OK <- "OK",
   Error <- "Error"

vars == <<conns>>

   ----------------------------- MODULE Messages ----------------------------
   
   (*
   The Messages module defines predicates for receiving, sending, and
   verifying all the messages supported by gNMI.
   *)
   
   \* Message type constants
   CONSTANT 
      CapabilityRequest,
      CapabilityResponse
   CONSTANTS
      GetRequest,
      GetResponse
   CONSTANTS
      SetRequest,
      SetResponse
   CONSTANTS
      SubscribeRequest,
      SubscribeResponse
   
   CONSTANTS
      Invalid,
      Delete,
      Replace,
      Update
      
   LOCAL messageTypes == 
      {CapabilityRequest, 
       CapabilityResponse,
       GetRequest,
       GetResponse,
       SetRequest,
       SetResponse,
       SubscribeRequest,
       SubscribeResponse}
   
   \* Message types should be defined as strings to simplify debugging
   ASSUME \A m \in messageTypes : m \in STRING
   
   LOCAL opTypes == 
      {Invalid,
       Delete,
       Replace,
       Update}
   
   \* Operation types should be defined as strings to simplify debugging
   ASSUME \A m \in opTypes : m \in STRING
         
   ----
   
   (*
   This section defines predicates for identifying gNMI message types on
   the network.
   *)
   
   IsCapabilityRequest(m) == m.type = CapabilityRequest
  
   IsCapabilityResponse(m) == m.type = CapabilityResponse
   
   IsGetRequest(m) == m.type = GetRequest
   
   IsGetResponse(m) == m.type = GetResponse
   
   IsSetRequest(m) == m.type = SetRequest
   
   IsSetResponse(m) == m.type = SetResponse
   
   IsSubscribeRequest(m) == m.type = SubscribeRequest
   
   IsSubscribeResponse(m) == m.type = SubscribeResponse
   
   ----
      
   (*
   This section defines predicates for validating gNMI message contents. The predicates
   provide precise documentation on the gNMI message format and are used within the spec
   to verify that steps adhere to the gNMI protocol specification.
   *)
   
   LOCAL ValidFields(m, fs) ==
      /\ {f : f \in DOMAIN m} \o fs # {}
   
   LOCAL ValidUpdate(m) ==
      /\ ValidFields(m, {"path", "value"})
   
   LOCAL ValidUpdates(ms) ==
      /\ \A m \in ms : ValidUpdate(m)
      
   LOCAL ValidDelete(m) ==
      /\ ValidFields(m, {"path"})
      
   LOCAL ValidDeletes(ms) ==
      /\ \A m \in ms : ValidDelete(m)
   
   LOCAL ValidNotification(m) ==
      /\ ValidFields(m, {"prefix"})
      /\ "update" \in DOMAIN m => ValidUpdates(m["update"])
      /\ "delete" \in DOMAIN m => ValidDeletes(m["delete"])
   
   LOCAL ValidCapabilityRequest(m) == TRUE
   
   LOCAL ValidCapabilityResponse(m) == TRUE
   
   LOCAL ValidGetRequest(m) == 
      /\ ValidFields(m, {"path"})
   
   LOCAL ValidGetResponse(m) == 
      /\ ValidFields(m, {"notification"})
      /\ ValidNotification(m["notification"])
   
   LOCAL ValidSetRequest(m) == 
      /\ ValidFields(m, {"prefix"})
      /\ "update" \in DOMAIN m => ValidUpdates(m["update"])
      /\ "replace" \in DOMAIN m => ValidUpdates(m["replace"])
      /\ "delete" \in DOMAIN m => ValidDeletes(m["delete"])
   
   LOCAL ValidOperation(op) ==
      /\ op \in {Invalid, Delete, Replace, Update}
      
   LOCAL ValidResult(m) ==
      /\ ValidFields(m, {"path", "op"})
      /\ ValidOperation(m["op"])
   
   LOCAL ValidSetResponse(m) == 
      /\ ValidFields(m, {"prefix", "response"})
      /\ ValidResult(m["response"])
      
   LOCAL ValidSubscription(m) ==
      /\ ValidFields(m, {"path", "mode"})
   
   LOCAL ValidSubscribeRequest(m) ==
      \/ /\ "subscribe" \in DOMAIN m
         /\ ValidFields(m["subscribe"], {"prefix", "subscription"})
         /\ ValidSubscription(m["subscribe"]["subscription"])
      \/ /\ "poll" \in DOMAIN m
      \/ /\ "aliases" \in DOMAIN m
         /\ \A a \in m["aliases"] : ValidFields(a, {"path", "alias"})
      
   LOCAL ValidSubscribeResponse(m) == 
      \/ /\ "update" \in DOMAIN m
         /\ ValidNotification(m["update"])
   
   ----
   
   (*
   This section defines operators for constructing gNMI messages.
   *)
   
   LOCAL SetType(m, t) == [m EXCEPT !.type = t]
   
   WithCapabilityRequest(m) ==
      IF Assert(ValidCapabilityRequest(m), "Invalid CapabilityRequest") 
      THEN SetType(m, CapabilityRequest) 
      ELSE Nil
   
   WithCapabilityResponse(m) ==
      IF Assert(ValidCapabilityResponse(m), "Invalid CapabilityResponse") 
      THEN SetType(m, CapabilityResponse) 
      ELSE Nil
   
   WithGetRequest(m) == 
      IF Assert(ValidGetRequest(m), "Invalid GetRequest") 
      THEN SetType(m, GetRequest) 
      ELSE Nil
   
   WithGetResponse(m) == 
      IF Assert(ValidGetResponse(m), "Invalid GetResponse") 
      THEN SetType(m, GetResponse) 
      ELSE Nil
   
   WithSetRequest(m) == 
      IF Assert(ValidSetRequest(m), "Invalid SetRequest") 
      THEN SetType(m, SetRequest) 
      ELSE Nil
   
   WithSetResponse(m) == 
      IF Assert(ValidSetResponse(m), "Invalid SetResponse") 
      THEN SetType(m, SetResponse) 
      ELSE Nil
   
   WithSubscribeRequest(m) == 
      IF Assert(ValidSubscribeRequest(m), "Invalid SubscribeRequest") 
      THEN SetType(m, SubscribeRequest) 
      ELSE Nil
   
   WithSubscribeResponse(m) == 
      IF Assert(ValidSubscribeResponse(m), "Invalid SubscribeResponse") 
      THEN SetType(m, SubscribeResponse) 
      ELSE Nil
      
   ==========================================================================

\* The Messages module is instantiated locally to avoid access from outside
\* the module.
LOCAL Messages == INSTANCE Messages WITH
   CapabilityRequest <- "CapabilityRequest", 
   CapabilityResponse <- "CapabilityResponse",
   GetRequest <- "GetRequest",
   GetResponse <- "GetResponse",
   SetRequest <- "SetRequest",
   SetResponse <- "SetResponse",
   SubscribeRequest <- "SubscribeRequest",
   SubscribeResponse <- "SubscribeResponse",
   Invalid <- "Invalid",
   Delete <- "Delete",
   Replace <- "Replace",
   Update <- "Update"

   ------------------------------ MODULE Client -----------------------------
   
   (*
   The Client module provides operators for managing and operating on gNMI
   client connections and specifies the message types supported for the
   client.
   *)
   
      ------------------------------ MODULE Send ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the gNMI client.
      *)
      
      CapabilityRequest(c, m) == 
         /\ gRPC!Client!Send(c, Messages!WithCapabilityRequest(m))
      
      GetRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!WithGetRequest(m))
      
      SetRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!WithSetRequest(m))
      
      SubscribeRequest(c, m) ==
         /\ gRPC!Client!Send(c, Messages!WithSubscribeRequest(m))
      
      =======================================================================
   
   \* Instantiate the gNMI!Client!Requests module
   Send == INSTANCE Send
   
      ----------------------------- MODULE Receive --------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an gNMI client.
      *)
      
      CapabilityResponse(c, h(_)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsCapabilityResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(m))
      
      GetResponse(c, h(_)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsGetResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(m))
      
      SetResponse(c, h(_)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsSetResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(m))
      
      SubscribeResponse(c, h(_)) == 
         gRPC!Client!Handle(c, LAMBDA x, m : 
            /\ Messages!IsSubscribeResponse(m) 
            /\ gRPC!Client!Receive(c)
            /\ h(m))
      
      =======================================================================
   
   \* Instantiate the gNMI!Client!Responses module
   Handle == INSTANCE Receive
   
   Connect(s, d) == gRPC!Client!Connect(s, d)
   
   Disconnect(c) == gRPC!Client!Disconnect(c)
   
   ==========================================================================

\* Provides operators for the gNMI client
Client == INSTANCE Client
      
   ------------------------------ MODULE Server -----------------------------
   
   (*
   The Server module provides operators for managing and operating on gNMI
   servers and specifies the message types supported for the server.
   *)
   
      ------------------------------- MODULE Send ---------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the gNMI server.
      *)
      
      CapabilityResponse(c, m) == 
         /\ gRPC!Server!Send(c, Messages!WithCapabilityResponse(m))
      
      GetResponse(c, m) ==
         /\ gRPC!Server!Send(c, Messages!WithGetResponse(m))
      
      SetResponse(c, m) ==
         /\ gRPC!Server!Send(c, Messages!WithSetResponse(m))
      
      SubscribeResponse(c, m) ==
         /\ gRPC!Server!Send(c, Messages!WithSubscribeResponse(m))
      
      =======================================================================
   
   \* Instantiate the gNMI!Server!Responses module
   Send == INSTANCE Send
   
      ------------------------------ MODULE Reply ---------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the gNMI server.
      *)
      
      CapabilityResponse(c, m) == 
         /\ gRPC!Server!Reply(c, Messages!WithCapabilityResponse(m))
      
      GetResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithGetResponse(m))
      
      SetResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithSetResponse(m))
      
      SubscribeResponse(c, m) ==
         /\ gRPC!Server!Reply(c, Messages!WithSubscribeResponse(m))
      
      =======================================================================
   
   \* Instantiate the gNMI!Server!Reply module
   Reply == INSTANCE Reply
   
      ---------------------------- MODULE Receive ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an gNMI server.
      *)
      
      CapabilityRequest(c, h(_)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsCapabilityRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(m))
      
      GetRequest(c, h(_)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsGetRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(m))
      
      SetRequest(c, h(_)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsSetRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(m))
      
      SubscribeRequest(c, h(_)) == 
         gRPC!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsSubscribeRequest(m) 
            /\ gRPC!Server!Receive(c)
            /\ h(m))
      
      =======================================================================
   
   \* Instantiate the gNMI!Server!Requests module
   Handle == INSTANCE Receive
   
   ==========================================================================

\* Provides operators for the gNMI server
Server == INSTANCE Server

\* The set of all open gNMI connections
Connections == gRPC!Connections

Init ==
   /\ gRPC!Init

Next ==
   /\ gRPC!Next

=============================================================================
\* Modification History
\* Last modified Wed Jan 12 00:36:00 PST 2022 by jordanhalterman
\* Created Tue Jan 11 23:46:02 PST 2022 by jordanhalterman
