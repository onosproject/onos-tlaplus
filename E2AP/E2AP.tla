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
         
      All ==
         {Unspecified,
          ControlProcessingOverload,
          HardwareFailure,
          OMIntervention}
      
      ASSUME \A c \in All : c \in STRING
            
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
         
      All ==
         {Unspecified,
          TransferSyntaxError,
          AbstractSyntaxErrorReject,
          AbstractSyntaxErrorIgnoreAndNotify,
          MessageNotCompatibleWithReceiverState,
          SemanticError,
          AbstractSyntaxErrorFalselyConstructedMessage}
      
      ASSUME \A c \in All : c \in STRING
            
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
         
      All ==
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
      
      ASSUME \A c \in All : c \in STRING
            
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
         
      All ==
         {Unspecified,
          FunctionNotRequired,
          ExcessiveFunctions,
          RICResourceLimit}
      
      ASSUME \A c \in All : c \in STRING
      
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
         
      All ==
         {Unspecified,
          TransportResourceUnavailable}
      
      ASSUME \A c \in All : c \in STRING
            
      IsUnspecified(m) == m.cause = Unspecified
      IsTransportResourceUnavailable(m) == m.cause = TransportResourceUnavailable
      
      =======================================================================
   
   Transport == INSTANCE Transport WITH
         Unspecified <- "Unspecified",
         TransportResourceUnavailable <- "TransportResourceUnavailable"
      
   All == Misc!All \cup Protocol!All \cup RIC!All \cup RICService!All \cup Transport!All
   
   IsCause(c) == c \in All
      
   (*
   This section defines predicates for identifying E2AP message types on
   the network.
   *)
   
   ==========================================================================

\* The Cause module provides failure causes
Cause == INSTANCE Cause

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
      RICServiceUpdate,
      RICServiceUpdateAcknowledge,
      RICServiceUpdateFailure
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
      RICIndication
   CONSTANTS
      RICControlRequest,
      RICControlResponse,
      RICControlFailure
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
       RICServiceUpdate,
       RICServiceUpdateAcknowledge,
       RICServiceUpdateFailure,
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
   
   IsRICServiceUpdate(m) == m.type = RICServiceUpdate
   
   IsRICServiceUpdateAcknowledge(m) == m.type = RICServiceUpdateAcknowledge
   
   IsRICServiceUpdateFailure(m) == m.type = RICServiceUpdateFailure
   
   IsResetRequest(m) == m.type = ResetRequest
   
   IsResetResponse(m) == m.type = ResetResponse
   
   IsRICSubscriptionRequest(m) == m.type = RICSubscriptionRequest
   
   IsRICSubscriptionResponse(m) == m.type = RICSubscriptionResponse
   
   IsRICSubscriptionFailure(m) == m.type = RICSubscriptionFailure
   
   IsRICSubscriptionDeleteRequest(m) == m.type = RICSubscriptionDeleteRequest
   
   IsRICSubscriptionDeleteResponse(m) == m.type = RICSubscriptionDeleteResponse
   
   IsRICSubscriptionDeleteFailure(m) == m.type = RICSubscriptionDeleteFailure
   
   IsRICIndication(m) == m.type = RICIndication
   
   IsRICControlRequest(m) == m.type = RICControlRequest
   
   IsRICControlResponse(m) == m.type = RICControlResponse
   
   IsRICControlFailure(m) == m.type = RICControlFailure
   
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
   
   LOCAL ValidE2SetupRequest(m) == 
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "globalE2NodeId" \in DOMAIN m 
         /\ m["globalE2NodeId"] \in Nat
   
   LOCAL ValidE2SetupResponse(m) == 
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "globalRicId" \in DOMAIN m    
         /\ m["globalRicId"] \in Nat
   
   LOCAL ValidE2SetupFailure(m) == 
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidRICServiceUpdate(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
   
   LOCAL ValidRICServiceUpdateAcknowledge(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
   
   LOCAL ValidRICServiceUpdateFailure(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidResetRequest(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
   
   LOCAL ValidResetResponse(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
   
   LOCAL ValidE2ConnectionUpdate(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "add" \in DOMAIN m => 
            /\ IsFiniteSet(m["add"])
            /\ \A a \in m["add"] : a \in STRING
         /\ "update" \in DOMAIN m =>
            /\ IsFiniteSet(m["update"])
            /\ \A a \in m["update"] : a \in STRING
         /\ "remove" \in DOMAIN m =>
            /\ IsFiniteSet(m["remove"])
            /\ \A a \in m["remove"] : a \in STRING
   
   LOCAL ValidE2ConnectionUpdateAcknowledge(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "succeeded" \in DOMAIN m =>
            /\ IsFiniteSet(m["succeeded"])
            /\ \A a \in m["succeeded"] : a \in STRING
         /\ "failed" \in DOMAIN m =>
            /\ IsFiniteSet(m["failed"])
            /\ \A a \in m["failed"] : a \in STRING
   
   LOCAL ValidE2ConnectionUpdateFailure(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidE2NodeConfigurationUpdate(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "globalE2NodeId" \in DOMAIN m 
         /\ m["globalE2NodeId"] \in Nat
      /\ /\ "add" \in DOMAIN m => 
            /\ IsFiniteSet(m["add"])
         /\ "update" \in DOMAIN m => 
            /\ IsFiniteSet(m["update"])
         /\ "remove" \in DOMAIN m => 
            /\ IsFiniteSet(m["remove"])
   
   LOCAL ValidE2NodeConfigurationUpdateAcknowledge(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "add" \in DOMAIN m => 
            /\ IsFiniteSet(m["add"])
         /\ "update" \in DOMAIN m => 
            /\ IsFiniteSet(m["update"])
         /\ "remove" \in DOMAIN m => 
            /\ IsFiniteSet(m["remove"])
   
   LOCAL ValidE2NodeConfigurationUpdateFailure(m) ==  
      /\ /\ "transactionId" \in DOMAIN m 
         /\ m["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidRICSubscriptionRequest(m) ==  
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionResponse(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionFailure(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidRICSubscriptionDeleteRequest(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionDeleteResponse(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionDeleteFailure(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
   LOCAL ValidRICIndication(m) ==
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICControlRequest(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICControlAcknowledge(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
   
   LOCAL ValidRICControlFailure(m) == 
      /\ /\ "requestId" \in DOMAIN m 
         /\ m["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN m
         /\ m["cause"] \in Cause!All
   
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
   
   WithRICServiceUpdate(m) ==
      IF Assert(ValidRICServiceUpdate(m), "Invalid RICServiceUpdate") 
      THEN SetType(m, RICServiceUpdate)
      ELSE Nil
   
   WithRICServiceUpdateAcknowledge(m) ==
      IF Assert(ValidRICServiceUpdateAcknowledge(m), "Invalid RICServiceUpdateAcknowledge") 
      THEN SetType(m, RICServiceUpdateAcknowledge) 
      ELSE Nil
   
   WithRICServiceUpdateFailure(m, c) == 
      IF Assert(ValidRICServiceUpdateFailure(m), "Invalid RICServiceUpdateFailure") 
      THEN SetType(m, SetFailureCause(RICServiceUpdateFailure, c))
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
   
   WithRICIndication(m) == 
      IF Assert(ValidRICIndication(m), "Invalid RICIndication") 
      THEN SetType(m, RICIndication) 
      ELSE Nil
   
   WithRICControlRequest(m) == 
      IF Assert(ValidRICControlRequest(m), "Invalid RICControlRequest") 
      THEN SetType(m, RICControlRequest) 
      ELSE Nil
   
   WithRICControlAcknowledge(m) == 
      IF Assert(ValidRICControlAcknowledge(m), "Invalid RICControlAcknowledge") 
      THEN SetType(m, RICControlResponse) 
      ELSE Nil
   
   WithRICControlFailure(m, c) == 
      IF Assert(ValidRICControlFailure(m), "Invalid RICControlFailure") 
      THEN SetType(m, SetFailureCause(RICControlFailure, c)) 
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
   RICIndication <- "RICIndication",
   RICControlRequest <- "RICControlRequest",
   RICControlResponse <- "RICControlResponse",
   RICControlFailure <- "RICControlFailure",
   RICServiceUpdate <- "RICServiceUpdate",
   RICServiceUpdateAcknowledge <- "RICServiceUpdateAcknowledge",
   RICServiceUpdateFailure <- "RICServiceUpdateFailure",
   E2ConnectionUpdate <- "E2ConnectionUpdate",
   E2ConnectionUpdateAcknowledge <- "E2ConnectionUpdateAcknowledge",
   E2ConnectionUpdateFailure <- "E2ConnectionUpdateFailure",
   E2NodeConfigurationUpdate <- "E2NodeConfigurationUpdate",
   E2NodeConfigurationUpdateAcknowledge <- "E2NodeConfigurationUpdateAcknowledge",
   E2NodeConfigurationUpdateFailure <- "E2NodeConfigurationUpdateFailure"

   ------------------------------ MODULE E2Node -----------------------------
   
   (*
   The Client module provides operators for managing and operating on E2AP
   client connections and specifies the message types supported for the
   client.
   *)
   
      ------------------------------ MODULE Send ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP client.
      *)
      
      E2SetupRequest(conn, msg) == 
         /\ SCTP!Client!Send(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdate(conn, msg) == 
         /\ SCTP!Client!Send(conn, Messages!WithRICServiceUpdate(msg))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithResetResponse(msg))
      
      RICSubscriptionResponse(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICSubscriptionResponse(msg))
      
      RICSubscriptionFailure(conn, msg, cause) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICSubscriptionFailure(msg, cause))
      
      RICSubscriptionDeleteResponse(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICSubscriptionDeleteResponse(msg))
      
      RICSubscriptionDeleteFailure(conn, msg, cause) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICSubscriptionDeleteFailure(msg, cause))
      
      RICIndication(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICIndication(msg))
      
      RICControlAcknowledge(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICControlAcknowledge(msg))
      
      RICControlFailure(conn, msg, cause) ==
         /\ SCTP!Client!Send(conn, Messages!WithRICControlFailure(msg, cause))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client!Send(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Requests module
   Send == INSTANCE Send
   
      ------------------------------ MODULE Reply ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP client.
      *)
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithResetResponse(msg))
      
      RICSubscriptionResponse(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICSubscriptionResponse(msg))
      
      RICSubscriptionFailure(conn, msg, cause) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICSubscriptionFailure(msg, cause))
      
      RICSubscriptionDeleteResponse(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICSubscriptionDeleteResponse(msg))
      
      RICSubscriptionDeleteFailure(conn, msg, cause) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICSubscriptionDeleteFailure(msg, cause))
      
      RICIndication(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICIndication(msg))
      
      RICControlAcknowledge(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICControlAcknowledge(msg))
      
      RICControlFailure(conn, msg, cause) ==
         /\ SCTP!Client!Reply(conn, Messages!WithRICControlFailure(msg, cause))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client!Reply(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Reply module
   Reply == INSTANCE Reply
   
      ---------------------------- MODULE Receive ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP client.
      *)
      
      E2SetupResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2SetupResponse(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      RICServiceUpdateAcknowledge(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICServiceUpdateAcknowledge(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      RICServiceUpdateFailure(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICServiceUpdateFailure(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      ResetRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsResetRequest(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      ResetResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsResetResponse(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      RICSusbcriptionRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICSubscriptionRequest(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      RICSubscriptionDeleteRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICSubscriptionDeleteRequest(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      RICControlRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICControlRequest(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2ConnectionUpdate(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2ConnectionUpdate(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2ConnectionUpdateAcknowledge(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2ConnectionUpdateAcknowledge(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2NodeConfigurationUpdate(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2NodeConfigurationUpdate(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2NodeConfigurationUpdateAcknowledge(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2NodeConfigurationUpdateAcknowledge(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Responses module
   Handle == INSTANCE Receive
   
   Connect(s, d) == SCTP!Client!Connect(s, d)
   
   Disconnect(c) == SCTP!Client!Disconnect(c)
   
   ==========================================================================

\* Provides operators for the E2AP client
E2Node == INSTANCE E2Node
      
   ------------------------------- MODULE RIC -------------------------------
   
   (*
   The Server module provides operators for managing and operating on E2AP
   servers and specifies the message types supported for the server.
   *)
   
      ----------------------------- MODULE Send -----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP server.
      *)
      
      E2SetupResponse(conn, msg) == 
         /\ SCTP!Server!Send(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdateAcknowledge(conn, msg) == 
         /\ SCTP!Server!Send(conn, Messages!WithRICServiceUpdateAcknowledge(msg))
      
      RICServiceUpdateFailure(conn, msg, cause) == 
         /\ SCTP!Server!Send(conn, Messages!WithRICServiceUpdateFailure(msg, cause))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithResetResponse(msg))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server!Send(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Send module
   Send == INSTANCE Send
   
      ----------------------------- MODULE Reply ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP server.
      *)
      
      E2SetupResponse(conn, msg) == 
         /\ SCTP!Server!Reply(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdateAcknowledge(conn, msg) == 
         /\ SCTP!Server!Reply(conn, Messages!WithRICServiceUpdateAcknowledge(msg))
      
      RICServiceUpdateFailure(conn, msg, cause) == 
         /\ SCTP!Server!Reply(conn, Messages!WithRICServiceUpdateFailure(msg, cause))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithResetResponse(msg))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server!Reply(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Reply module
   Reply == INSTANCE Reply
   
      ---------------------------- MODULE Receive ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP server.
      *)
      
      E2SetupRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2SetupRequest(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      RICServiceUpdate(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICServiceUpdate(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      ResetRequest(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsResetRequest(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      ResetResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsResetResponse(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      RICSubscriptionResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICSubscriptionResponse(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      RICSubscriptionDeleteResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICSubscriptionDeleteResponse(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      RICControlResponse(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICControlResponse(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      RICIndication(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsRICIndication(m) 
            /\ SCTP!Server!Receive(conn)
            /\ handler(m))
      
      E2ConnectionUpdate(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2ConnectionUpdate(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2ConnectionUpdateAcknowledge(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2ConnectionUpdateAcknowledge(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2NodeConfigurationUpdate(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2NodeConfigurationUpdate(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      E2NodeConfigurationUpdateAcknowledge(conn, handler(_)) == 
         SCTP!Server!Handle(conn, LAMBDA x, m : 
            /\ Messages!IsE2NodeConfigurationUpdateAcknowledge(m) 
            /\ SCTP!Client!Receive(conn)
            /\ handler(m))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Requests module
   Handle == INSTANCE Receive
   
   ==========================================================================

\* Provides operators for the E2AP server
RIC == INSTANCE RIC

\* The set of all open E2AP connections
Connections == SCTP!Connections

Init == SCTP!Init

Next == SCTP!Next

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 00:39:05 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 10:53:17 PDT 2021 by jordanhalterman
