-------------------------------- MODULE E2AP --------------------------------

(*
The E2AP module provides a formal specification of the E2AP protocol. The
spec defines the client and server interfaces for E2AP and provides helpers
for managing and operating on connections.
*)

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

CONSTANT Nil

VARIABLE conns

\* The E2AP protocol is implemented on SCTP
LOCAL SCTP == INSTANCE SCTP

vars == <<conns>>
      
   ----------------------------- MODULE Messages ----------------------------
   
   (*
   The Messages module defines predicates for receiving, sending, and
   verifying all the messages supported by E2AP.
   *)
   
   \* Message type constants
   CONSTANTS
      E2SetupRequest,
      E2SetupResponse,
      E2SetupFailure
   CONSTANTS
      ResetRequest,
      ResetResponse
   CONSTANTS
      RICSubscriptionRequest,
      RICSubscriptionResponse,
      RICSubscriptionFailure
   CONSTANTS
      RICSubscriptionDeleteRequest,
      RICSubscriptionDeleteResponse,
      RICSubscriptionDeleteFailure
   CONSTANTS
      RICControlRequest,
      RICControlResponse,
      RICControlFailure,
      RICServiceUpdate
   CONSTANTS
      E2ConnectionUpdate,
      E2ConnectionUpdateAcknowledge,
      E2ConnectionUpdateFailure
   CONSTANTS
      E2NodeConfigurationUpdate,
      E2NodeConfigurationUpdateAcknowledge,
      E2NodeConfigurationUpdateFailure
   
   LOCAL messageTypes == 
      {E2SetupRequest, 
       E2SetupResponse,
       E2SetupFailure,
       ResetRequest,
       ResetResponse,
       RICSubscriptionRequest,
       RICSubscriptionResponse,
       RICSubscriptionFailure,
       RICSubscriptionDeleteRequest,
       RICSubscriptionDeleteResponse,
       RICSubscriptionDeleteFailure,
       RICControlRequest,
       RICControlResponse,
       RICControlFailure,
       RICServiceUpdate,
       E2ConnectionUpdate,
       E2ConnectionUpdateAcknowledge,
       E2ConnectionUpdateFailure,
       E2NodeConfigurationUpdate,
       E2NodeConfigurationUpdateAcknowledge,
       E2NodeConfigurationUpdateFailure}
   
   \* Message types should be defined as strings to simplify debugging
   ASSUME \A m \in messageTypes : m \in STRING
      
   ----
   
   (*
   This section defines predicates for identifying E2AP message types on
   the network.
   *)
   
   IsE2SetupRequest(m) == m.type = E2SetupRequest
   
   IsE2SetupResponse(m) == m.type = E2SetupResponse
   
   IsE2SetupFailure(m) == m.type = E2SetupFailure
   
   IsResetRequest(m) == m.type = ResetRequest
   
   IsResetResponse(m) == m.type = ResetResponse
   
   IsRICSubscriptionRequest(m) == m.type = RICSubscriptionRequest
   
   IsRICSubscriptionResponse(m) == m.type = RICSubscriptionResponse
   
   IsRICSubscriptionFailure(m) == m.type = RICSubscriptionFailure
   
   IsRICSubscriptionDeleteRequest(m) == m.type = RICSubscriptionDeleteRequest
   
   IsRICSubscriptionDeleteResponse(m) == m.type = RICSubscriptionDeleteResponse
   
   IsRICSubscriptionDeleteFailure(m) == m.type = RICSubscriptionDeleteFailure
   
   IsRICControlRequest(m) == m.type = RICControlRequest
   
   IsRICControlResponse(m) == m.type = RICControlResponse
   
   IsRICControlFailure(m) == m.type = RICControlFailure
   
   IsRICServiceUpdate(m) == m.type = RICServiceUpdate
   
   IsE2ConnectionUpdate(m) == m.type = E2ConnectionUpdate
   
   IsE2ConnectionUpdateAcknowledge(m) == m.type = E2ConnectionUpdateAcknowledge
   
   IsE2ConnectionUpdateFailure(m) == m.type = E2ConnectionUpdateFailure
   
   IsE2NodeConfigurationUpdate(m) == m.type = E2NodeConfigurationUpdate
   
   IsE2NodeConfigurationUpdateAcknowledge(m) == m.type = E2NodeConfigurationUpdateAcknowledge
   
   IsE2NodeConfigurationUpdateFailure(m) == m.type = E2NodeConfigurationUpdateFailure
      
   ----
      
   (*
   This section defines predicates for validating E2AP message contents. The predicates
   provide precise documentation on the E2AP message format and are used within the spec
   to verify that steps adhere to the E2AP protocol specification.
   *)
   
   LOCAL ValidE2SetupRequest(m) == TRUE
   
   LOCAL ValidE2SetupResponse(m) == TRUE
   
   LOCAL ValidE2SetupFailure(m) == TRUE
   
   LOCAL ValidResetRequest(m) == TRUE
   
   LOCAL ValidResetResponse(m) == TRUE
   
   LOCAL ValidRICSubscriptionRequest(m) == TRUE
   
   LOCAL ValidRICSubscriptionResponse(m) == TRUE
   
   LOCAL ValidRICSubscriptionFailure(m) == TRUE
   
   LOCAL ValidRICSubscriptionDeleteRequest(m) == TRUE
   
   LOCAL ValidRICSubscriptionDeleteResponse(m) == TRUE
   
   LOCAL ValidRICSubscriptionDeleteFailure(m) == TRUE
   
   LOCAL ValidRICControlRequest(m) == TRUE
   
   LOCAL ValidRICControlResponse(m) == TRUE
   
   LOCAL ValidRICControlFailure(m) == TRUE
   
   LOCAL ValidRICServiceUpdate(m) == TRUE
   
   LOCAL ValidE2ConnectionUpdate(m) == TRUE
   
   LOCAL ValidE2ConnectionUpdateAcknowledge(m) == TRUE
   
   LOCAL ValidE2ConnectionUpdateFailure(m) == TRUE
   
   LOCAL ValidE2NodeConfigurationUpdate(m) == TRUE
   
   LOCAL ValidE2NodeConfigurationUpdateAcknowledge(m) == TRUE
   
   LOCAL ValidE2NodeConfigurationUpdateFailure(m) == TRUE
   
   ----
   
   (*
   This section defines operators for constructing E2AP messages.
   *)
   
   LOCAL SetType(m, t) == [m EXCEPT !.type = t]
   
   LOCAL SetFailureCause(m, c) == [m EXCEPT !.cause = c]
   
   WithE2SetupRequest(m) ==
      IF Assert(ValidE2SetupRequest(m), "Invalid E2SetupRequest") 
      THEN SetType(m, E2SetupRequest)
      ELSE Nil
   
   WithE2SetupResponse(m) ==
      IF Assert(ValidE2SetupResponse(m), "Invalid E2SetupResponse") 
      THEN SetType(m, E2SetupResponse) 
      ELSE Nil
   
   WithE2SetupFailure(m, c) == 
      IF Assert(ValidE2SetupFailure(m), "Invalid E2SetupFailure") 
      THEN SetType(m, SetFailureCause(E2SetupFailure, c))
      ELSE Nil
   
   WithResetRequest(m) == 
      IF Assert(ValidResetRequest(m), "Invalid ResetRequest") 
      THEN SetType(m, ResetRequest) 
      ELSE Nil
   
   WithResetResponse(m) == 
      IF Assert(ValidResetResponse(m), "Invalid ResetResponse") 
      THEN SetType(m, ResetResponse) 
      ELSE Nil
   
   WithRICSubscriptionRequest(m) == 
      IF Assert(ValidRICSubscriptionRequest(m), "Invalid RICSubscriptionRequest") 
      THEN SetType(m, RICSubscriptionRequest) 
      ELSE Nil
   
   WithRICSubscriptionResponse(m) == 
      IF Assert(ValidRICSubscriptionResponse(m), "Invalid RICSubscriptionResponse") 
      THEN SetType(m, RICSubscriptionResponse) 
      ELSE Nil
   
   WithRICSubscriptionFailure(m, c) == 
      IF Assert(ValidRICSubscriptionFailure(m), "Invalid RICSubscriptionFailure") 
      THEN SetType(m, SetFailureCause(RICSubscriptionFailure, c)) 
      ELSE Nil
   
   WithRICSubscriptionDeleteRequest(m) == 
      IF Assert(ValidRICSubscriptionDeleteRequest(m), "Invalid RICSubscriptionDeleteRequest") 
      THEN SetType(m, RICSubscriptionDeleteRequest) 
      ELSE Nil
   
   WithRICSubscriptionDeleteResponse(m) == 
      IF Assert(ValidRICSubscriptionDeleteResponse(m), "Invalid RICSubscriptionDeleteResponse") 
      THEN SetType(m, RICSubscriptionDeleteResponse) 
      ELSE Nil
   
   WithRICSubscriptionDeleteFailure(m, c) == 
      IF Assert(ValidRICSubscriptionDeleteFailure(m), "Invalid RICSubscriptionDeleteFailure") 
      THEN SetType(m, SetFailureCause(RICSubscriptionDeleteFailure, c)) 
      ELSE Nil
   
   WithRICControlRequest(m) == 
      IF Assert(ValidRICControlRequest(m), "Invalid RICControlRequest") 
      THEN SetType(m, RICControlRequest) 
      ELSE Nil
   
   WithRICControlResponse(m) == 
      IF Assert(ValidRICControlResponse(m), "Invalid RICControlResponse") 
      THEN SetType(m, RICControlResponse) 
      ELSE Nil
   
   WithRICControlFailure(m, c) == 
      IF Assert(ValidRICControlFailure(m), "Invalid RICControlFailure") 
      THEN SetType(m, SetFailureCause(RICControlFailure, c)) 
      ELSE Nil
   
   WithRICServiceUpdate(m) == 
      IF Assert(ValidRICServiceUpdate(m), "Invalid RICServiceUpdate") 
      THEN SetType(m, RICServiceUpdate) 
      ELSE Nil
   
   WithE2ConnectionUpdate(m) == 
      IF Assert(ValidE2ConnectionUpdate(m), "Invalid E2ConnectionUpdate") 
      THEN SetType(m, E2ConnectionUpdate) 
      ELSE Nil
   
   WithE2ConnectionUpdateAcknowledge(m) == 
      IF Assert(ValidE2ConnectionUpdateAcknowledge(m), "Invalid E2ConnectionUpdateAcknowledge") 
      THEN SetType(m, E2ConnectionUpdateAcknowledge) 
      ELSE Nil
   
   WithE2ConnectionUpdateFailure(m, c) == 
      IF Assert(ValidE2ConnectionUpdateFailure(m), "Invalid E2ConnectionUpdateFailure") 
      THEN SetType(m, SetFailureCause(E2ConnectionUpdateFailure, c)) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdate(m) == 
      IF Assert(ValidE2NodeConfigurationUpdate(m), "Invalid E2NodeConfigurationUpdate") 
      THEN SetType(m, E2NodeConfigurationUpdate) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdateAcknowledge(m) == 
      IF Assert(ValidE2NodeConfigurationUpdateAcknowledge(m), "Invalid E2NodeConfigurationUpdateAcknowledge") 
      THEN SetType(m, E2NodeConfigurationUpdateAcknowledge) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdateFailure(m, c) == 
      IF Assert(ValidE2NodeConfigurationUpdateFailure(m), "Invalid E2NodeConfigurationUpdateFailure") 
      THEN SetType(m, SetFailureCause(E2NodeConfigurationUpdateFailure, c)) 
      ELSE Nil
      
   ==========================================================================

\* The Messages module is instantiated locally to avoid access from outside
\* the module.
LOCAL Messages == INSTANCE Messages WITH
   E2SetupRequest <- "E2SetupRequest",
   E2SetupResponse <- "E2SetupResponse",
   E2SetupFailure <- "E2SetupFailure",
   ResetRequest <- "ResetRequest",
   ResetResponse <- "ResetResponse",
   RICSubscriptionRequest <- "RICSubscriptionRequest",
   RICSubscriptionResponse <- "RICSubscriptionResponse",
   RICSubscriptionFailure <- "RICSubscriptionFailure",
   RICSubscriptionDeleteRequest <- "RICSubscriptionDeleteRequest",
   RICSubscriptionDeleteResponse <- "RICSubscriptionDeleteResponse",
   RICSubscriptionDeleteFailure <- "RICSubscriptionDeleteFailure",
   RICControlRequest <- "RICControlRequest",
   RICControlResponse <- "RICControlResponse",
   RICControlFailure <- "RICControlFailure",
   RICServiceUpdate <- "RICServiceUpdate",
   E2ConnectionUpdate <- "E2ConnectionUpdate",
   E2ConnectionUpdateAcknowledge <- "E2ConnectionUpdateAcknowledge",
   E2ConnectionUpdateFailure <- "E2ConnectionUpdateFailure",
   E2NodeConfigurationUpdate <- "E2NodeConfigurationUpdate",
   E2NodeConfigurationUpdateAcknowledge <- "E2NodeConfigurationUpdateAcknowledge",
   E2NodeConfigurationUpdateFailure <- "E2NodeConfigurationUpdateFailure"

   ------------------------------ MODULE Cause ------------------------------
   
   (*
   The Messages module defines predicates for receiving, sending, and
   verifying all the messages supported by E2AP.
   *)
   
      ------------------------------ MODULE Misc ----------------------------

      CONSTANTS
         Unspecified,
         ControlProcessingOverload,
         HardwareFailure,
         OMIntervention
         
      LOCAL failureCauses ==
         {Unspecified,
          ControlProcessingOverload,
          HardwareFailure,
          OMIntervention}
      
      ASSUME \A c \in failureCauses : c \in STRING
            
      IsUnspecified(m) == m.cause = Unspecified
      IsControlProcessingOverload(m) == m.cause = ControlProcessingOverload
      IsHardwareFailure(m) == m.cause = HardwareFailure
      IsOMIntervention(m) == m.cause = OMIntervention
      
      =======================================================================
   
   Misc == INSTANCE Misc WITH
      Unspecified <- "Unspecified",
      ControlProcessingOverload <- "ControlProcessingOverload",
      HardwareFailure <- "HardwareFailure",
      OMIntervention <- "OMIntervention"
   
      ---------------------------- MODULE Protocol --------------------------

      CONSTANTS
         Unspecified,
         TransferSyntaxError,
         AbstractSyntaxErrorReject,
         AbstractSyntaxErrorIgnoreAndNotify,
         MessageNotCompatibleWithReceiverState,
         SemanticError,
         AbstractSyntaxErrorFalselyConstructedMessage
         
      LOCAL failureCauses ==
         {Unspecified,
          TransferSyntaxError,
          AbstractSyntaxErrorReject,
          AbstractSyntaxErrorIgnoreAndNotify,
          MessageNotCompatibleWithReceiverState,
          SemanticError,
          AbstractSyntaxErrorFalselyConstructedMessage}
      
      ASSUME \A c \in failureCauses : c \in STRING
            
      IsUnspecified(m) == m.cause = Unspecified
      IsTransferSyntaxError(m) == m.cause = TransferSyntaxError
      IsAbstractSyntaxErrorReject(m) == m.cause = AbstractSyntaxErrorReject
      IsAbstractSyntaxErrorIgnoreAndNotify(m) == m.cause = AbstractSyntaxErrorIgnoreAndNotify
      IsMessageNotCompatibleWithReceiverState(m) == m.cause = MessageNotCompatibleWithReceiverState
      IsSemanticError(m) == m.cause = SemanticError
      IsAbstractSyntaxErrorFalselyConstructedMessage(m) == m.cause = AbstractSyntaxErrorFalselyConstructedMessage
      
      =======================================================================
   
   Protocol == INSTANCE Protocol WITH
      Unspecified <- "Unspecified",
      TransferSyntaxError <- "TransferSyntaxError",
      AbstractSyntaxErrorReject <- "AbstractSyntaxErrorReject",
      AbstractSyntaxErrorIgnoreAndNotify <- "AbstractSyntaxErrorIgnoreAndNotify",
      MessageNotCompatibleWithReceiverState <- "MessageNotCompatibleWithReceiverState",
      SemanticError <- "SemanticError",
      AbstractSyntaxErrorFalselyConstructedMessage <- "AbstractSyntaxErrorFalselyConstructedMessage"
   
      ------------------------------ MODULE RIC -----------------------------

      CONSTANTS
         Unspecified,
         RANFunctionIDInvalid,
         ActionNotSupported,
         ExcessiveActions,
         DuplicateAction,
         DuplicateEvent,
         FunctionResourceLimit,
         RequestIDUnknown,
         InconsistentActionSubsequentActionSequence,
         ControlMessageInvalid,
         CallProcessIDInvalid
         
      LOCAL failureCauses ==
         {Unspecified,
          RANFunctionIDInvalid,
          ActionNotSupported,
          ExcessiveActions,
          DuplicateAction,
          DuplicateEvent,
          FunctionResourceLimit,
          RequestIDUnknown,
          InconsistentActionSubsequentActionSequence,
          ControlMessageInvalid,
          CallProcessIDInvalid}
      
      ASSUME \A c \in failureCauses : c \in STRING
            
      IsUnspecified(m) == m.cause = Unspecified
      IsRANFunctionIDInvalid(m) == m.cause = RANFunctionIDInvalid
      IsActionNotSupported(m) == m.cause = ActionNotSupported
      IsExcessiveActions(m) == m.cause = ExcessiveActions
      IsDuplicateAction(m) == m.cause = DuplicateAction
      IsDuplicateEvent(m) == m.cause = DuplicateEvent
      IsFunctionResourceLimit(m) == m.cause = FunctionResourceLimit
      IsRequestIDUnknown(m) == m.cause = RequestIDUnknown
      IsInconsistentActionSubsequentActionSequence(m) == m.cause = InconsistentActionSubsequentActionSequence
      IsControlMessageInvalid(m) == m.cause = ControlMessageInvalid
      IsCallProcessIDInvalid(m) == m.cause = CallProcessIDInvalid
      
      =======================================================================
   
   RIC == INSTANCE RIC WITH
      Unspecified <- "Unspecified",
      RANFunctionIDInvalid <- "RANFunctionIDInvalid",
      ActionNotSupported <- "ActionNotSupported",
      ExcessiveActions <- "ExcessiveActions",
      DuplicateAction <- "DuplicateAction",
      DuplicateEvent <- "DuplicateEvent",
      FunctionResourceLimit <- "FunctionResourceLimit",
      RequestIDUnknown <- "RequestIDUnknown",
      InconsistentActionSubsequentActionSequence <- "InconsistentActionSubsequentActionSequence",
      ControlMessageInvalid <- "ControlMessageInvalid",
      CallProcessIDInvalid <- "CallProcessIDInvalid"
   
      --------------------------- MODULE RICService -------------------------

      CONSTANTS
         Unspecified,
         FunctionNotRequired,
         ExcessiveFunctions,
         RICResourceLimit
         
      LOCAL failureCauses ==
         {Unspecified,
          FunctionNotRequired,
          ExcessiveFunctions,
          RICResourceLimit}
      
      ASSUME \A c \in failureCauses : c \in STRING
      
      IsUnspecified(m) == m.cause = Unspecified
      IsFunctionNotRequired(m) == m.cause = FunctionNotRequired
      IsExcessiveFunctions(m) == m.cause = ExcessiveFunctions
      IsRICResourceLimit(m) == m.cause = RICResourceLimit
            
      =======================================================================
   
   RICService == INSTANCE RICService WITH
      Unspecified <- "Unspecified",
      FunctionNotRequired <- "FunctionNotRequired",
      ExcessiveFunctions <- "ExcessiveFunctions",
      RICResourceLimit <- "RICResourceLimit"
   
      --------------------------- MODULE Transport --------------------------

      CONSTANTS
         Unspecified,
         TransportResourceUnavailable
         
      LOCAL failureCauses ==
         {Unspecified,
          TransportResourceUnavailable}
      
      ASSUME \A c \in failureCauses : c \in STRING
            
      IsUnspecified(m) == m.cause = Unspecified
      IsTransportResourceUnavailable(m) == m.cause = TransportResourceUnavailable
      
      =======================================================================
   
   Transport == INSTANCE Transport WITH
         Unspecified <- "Unspecified",
         TransportResourceUnavailable <- "TransportResourceUnavailable"
      
   (*
   This section defines predicates for identifying E2AP message types on
   the network.
   *)
   
   ==========================================================================

\* The Cause module provides failure causes
Cause == INSTANCE Cause

   ------------------------------ MODULE Client -----------------------------
   
   (*
   The Client module provides operators for managing and operating on E2AP
   client connections and specifies the message types supported for the
   client.
   *)
   
      ---------------------------- MODULE Requests --------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP client.
      *)
      
      E2SetupRequest(c, m) == 
         /\ SCTP!Client!Send(c, Messages!WithE2SetupResponse(m))
      
      ResetRequest(c, m) ==
         /\ SCTP!Client!Send(c, Messages!WithResetRequest(m))
      
      ResetResponse(c, m) ==
         /\ SCTP!Client!Reply(c, Messages!WithResetResponse(m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Send module
   Send == INSTANCE Requests
   
      --------------------------- MODULE Responses --------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP client.
      *)
      
      E2SetupResponse(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsE2SetupResponse(m) 
            /\ SCTP!Client!Receive(c)
            /\ h(c, m))
      
      ResetRequest(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsResetRequest(m) 
            /\ SCTP!Client!Receive(c)
            /\ h(c, m))
      
      ResetResponse(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsResetResponse(m) 
            /\ SCTP!Client!Receive(c)
            /\ h(c, m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Receive module
   Receive == INSTANCE Responses
   
   Connect(s, d) == SCTP!Client!Connect(s, d)
   
   Disconnect(c) == SCTP!Client!Disconnect(c)
   
   ==========================================================================

\* Provides operators for the E2AP client
Client == INSTANCE Client
      
   ------------------------------ MODULE Server -----------------------------
   
   (*
   The Server module provides operators for managing and operating on E2AP
   servers and specifies the message types supported for the server.
   *)
   
      --------------------------- MODULE Responses --------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP server.
      *)
      
      E2SetupResponse(c, m) == 
         /\ SCTP!Server!Reply(c, Messages!WithE2SetupResponse(m))
      
      ResetRequest(c, m) ==
         /\ SCTP!Server!Send(c, Messages!WithResetRequest(m))
      
      ResetResponse(c, m) ==
         /\ SCTP!Server!Reply(c, Messages!WithResetResponse(m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Send module
   Send == INSTANCE Responses
   
      ---------------------------- MODULE Requests --------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP server.
      *)
      
      E2SetupRequest(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsE2SetupRequest(m) 
            /\ SCTP!Server!Receive(c)
            /\ h(c, m))
      
      ResetRequest(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsResetRequest(m) 
            /\ SCTP!Server!Receive(c)
            /\ h(c, m))
      
      ResetResponse(c, h(_, _)) == 
         SCTP!Server!Handle(c, LAMBDA x, m : 
            /\ Messages!IsResetResponse(m) 
            /\ SCTP!Server!Receive(c)
            /\ h(c, m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Receive module
   Receive == INSTANCE Requests
   
   ==========================================================================

\* Provides operators for the E2AP server
Server == INSTANCE Server

\* The set of all open E2AP connections
Connections == SCTP!Connections

Init == SCTP!Init

Next == SCTP!Next

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 16:15:39 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 10:53:17 PDT 2021 by jordanhalterman
