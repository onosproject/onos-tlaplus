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
   
   IsE2SetupRequest(msg) == msg.type = E2SetupRequest
   
   IsE2SetupResponse(msg) == msg.type = E2SetupResponse
   
   IsE2SetupFailure(msg) == msg.type = E2SetupFailure
   
   IsRICServiceUpdate(msg) == msg.type = RICServiceUpdate
   
   IsRICServiceUpdateAcknowledge(msg) == msg.type = RICServiceUpdateAcknowledge
   
   IsRICServiceUpdateFailure(msg) == msg.type = RICServiceUpdateFailure
   
   IsResetRequest(msg) == msg.type = ResetRequest
   
   IsResetResponse(msg) == msg.type = ResetResponse
   
   IsRICSubscriptionRequest(msg) == msg.type = RICSubscriptionRequest
   
   IsRICSubscriptionResponse(msg) == msg.type = RICSubscriptionResponse
   
   IsRICSubscriptionFailure(msg) == msg.type = RICSubscriptionFailure
   
   IsRICSubscriptionDeleteRequest(msg) == msg.type = RICSubscriptionDeleteRequest
   
   IsRICSubscriptionDeleteResponse(msg) == msg.type = RICSubscriptionDeleteResponse
   
   IsRICSubscriptionDeleteFailure(msg) == msg.type = RICSubscriptionDeleteFailure
   
   IsRICIndication(msg) == msg.type = RICIndication
   
   IsRICControlRequest(msg) == msg.type = RICControlRequest
   
   IsRICControlResponse(msg) == msg.type = RICControlResponse
   
   IsRICControlFailure(msg) == msg.type = RICControlFailure
   
   IsE2ConnectionUpdate(msg) == msg.type = E2ConnectionUpdate
   
   IsE2ConnectionUpdateAcknowledge(msg) == msg.type = E2ConnectionUpdateAcknowledge
   
   IsE2ConnectionUpdateFailure(msg) == msg.type = E2ConnectionUpdateFailure
   
   IsE2NodeConfigurationUpdate(msg) == msg.type = E2NodeConfigurationUpdate
   
   IsE2NodeConfigurationUpdateAcknowledge(msg) == msg.type = E2NodeConfigurationUpdateAcknowledge
   
   IsE2NodeConfigurationUpdateFailure(msg) == msg.type = E2NodeConfigurationUpdateFailure
      
   ----
      
   (*
   This section defines predicates for validating E2AP message contents. The predicates
   provide precise documentation on the E2AP message format and are used within the spec
   to verify that steps adhere to the E2AP protocol specification.
   *)
   
   LOCAL ValidE2SetupRequest(msg) == 
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "globalE2NodeId" \in DOMAIN msg 
         /\ msg["globalE2NodeId"] \in Nat
   
   LOCAL ValidE2SetupResponse(msg) == 
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "globalRicId" \in DOMAIN msg    
         /\ msg["globalRicId"] \in Nat
   
   LOCAL ValidE2SetupFailure(msg) == 
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidRICServiceUpdate(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
   
   LOCAL ValidRICServiceUpdateAcknowledge(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
   
   LOCAL ValidRICServiceUpdateFailure(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidResetRequest(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
   
   LOCAL ValidResetResponse(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
   
   LOCAL ValidE2ConnectionUpdate(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "add" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["add"])
            /\ \A a \in msg["add"] : a \in STRING
         /\ "update" \in DOMAIN msg =>
            /\ IsFiniteSet(msg["update"])
            /\ \A a \in msg["update"] : a \in STRING
         /\ "remove" \in DOMAIN msg =>
            /\ IsFiniteSet(msg["remsgove"])
            /\ \A a \in msg["remove"] : a \in STRING
   
   LOCAL ValidE2ConnectionUpdateAcknowledge(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "succeeded" \in DOMAIN msg =>
            /\ IsFiniteSet(msg["succeeded"])
            /\ \A a \in msg["succeeded"] : a \in STRING
         /\ "failed" \in DOMAIN msg =>
            /\ IsFiniteSet(msg["failed"])
            /\ \A a \in msg["failed"] : a \in STRING
   
   LOCAL ValidE2ConnectionUpdateFailure(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidE2NodeConfigurationUpdate(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "globalE2NodeId" \in DOMAIN msg 
         /\ msg["globalE2NodeId"] \in Nat
      /\ /\ "add" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["add"])
         /\ "update" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["update"])
         /\ "remove" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["remove"])
   
   LOCAL ValidE2NodeConfigurationUpdateAcknowledge(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "add" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["add"])
         /\ "update" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["update"])
         /\ "remove" \in DOMAIN msg => 
            /\ IsFiniteSet(msg["remove"])
   
   LOCAL ValidE2NodeConfigurationUpdateFailure(msg) ==  
      /\ /\ "transactionId" \in DOMAIN msg 
         /\ msg["transactionId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidRICSubscriptionRequest(msg) ==  
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionResponse(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionFailure(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidRICSubscriptionDeleteRequest(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionDeleteResponse(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICSubscriptionDeleteFailure(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   LOCAL ValidRICIndication(msg) ==
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICControlRequest(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICControlAcknowledge(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
   
   LOCAL ValidRICControlFailure(msg) == 
      /\ /\ "requestId" \in DOMAIN msg 
         /\ msg["requestId"] \in Nat
      /\ /\ "cause" \in DOMAIN msg
         /\ msg["cause"] \in Cause!All
   
   ----
   
   (*
   This section defines operators for constructing E2AP messages.
   *)
   
   LOCAL SetType(msg, type) == [msg EXCEPT !.type = type]
   
   LOCAL SetFailureCause(msg, cause) == [msg EXCEPT !.cause = cause]
   
   WithE2SetupRequest(msg) ==
      IF Assert(ValidE2SetupRequest(msg), "Invalid E2SetupRequest") 
      THEN SetType(msg, E2SetupRequest)
      ELSE Nil
   
   WithE2SetupResponse(msg) ==
      IF Assert(ValidE2SetupResponse(msg), "Invalid E2SetupResponse") 
      THEN SetType(msg, E2SetupResponse) 
      ELSE Nil
   
   WithE2SetupFailure(msg, cause) == 
      IF Assert(ValidE2SetupFailure(msg), "Invalid E2SetupFailure") 
      THEN SetType(msg, SetFailureCause(E2SetupFailure, cause))
      ELSE Nil
   
   WithRICServiceUpdate(msg) ==
      IF Assert(ValidRICServiceUpdate(msg), "Invalid RICServiceUpdate") 
      THEN SetType(msg, RICServiceUpdate)
      ELSE Nil
   
   WithRICServiceUpdateAcknowledge(msg) ==
      IF Assert(ValidRICServiceUpdateAcknowledge(msg), "Invalid RICServiceUpdateAcknowledge") 
      THEN SetType(msg, RICServiceUpdateAcknowledge) 
      ELSE Nil
   
   WithRICServiceUpdateFailure(msg, cause) == 
      IF Assert(ValidRICServiceUpdateFailure(msg), "Invalid RICServiceUpdateFailure") 
      THEN SetType(msg, SetFailureCause(RICServiceUpdateFailure, cause))
      ELSE Nil
   
   WithResetRequest(msg) == 
      IF Assert(ValidResetRequest(msg), "Invalid ResetRequest") 
      THEN SetType(msg, ResetRequest) 
      ELSE Nil
   
   WithResetResponse(msg) == 
      IF Assert(ValidResetResponse(msg), "Invalid ResetResponse") 
      THEN SetType(msg, ResetResponse) 
      ELSE Nil
   
   WithRICSubscriptionRequest(msg) == 
      IF Assert(ValidRICSubscriptionRequest(msg), "Invalid RICSubscriptionRequest") 
      THEN SetType(msg, RICSubscriptionRequest) 
      ELSE Nil
   
   WithRICSubscriptionResponse(msg) == 
      IF Assert(ValidRICSubscriptionResponse(msg), "Invalid RICSubscriptionResponse") 
      THEN SetType(msg, RICSubscriptionResponse) 
      ELSE Nil
   
   WithRICSubscriptionFailure(msg, cause) == 
      IF Assert(ValidRICSubscriptionFailure(msg), "Invalid RICSubscriptionFailure") 
      THEN SetType(msg, SetFailureCause(RICSubscriptionFailure, cause)) 
      ELSE Nil
   
   WithRICSubscriptionDeleteRequest(msg) == 
      IF Assert(ValidRICSubscriptionDeleteRequest(msg), "Invalid RICSubscriptionDeleteRequest") 
      THEN SetType(msg, RICSubscriptionDeleteRequest) 
      ELSE Nil
   
   WithRICSubscriptionDeleteResponse(msg) == 
      IF Assert(ValidRICSubscriptionDeleteResponse(msg), "Invalid RICSubscriptionDeleteResponse") 
      THEN SetType(msg, RICSubscriptionDeleteResponse) 
      ELSE Nil
   
   WithRICSubscriptionDeleteFailure(msg, cause) == 
      IF Assert(ValidRICSubscriptionDeleteFailure(msg), "Invalid RICSubscriptionDeleteFailure") 
      THEN SetType(msg, SetFailureCause(RICSubscriptionDeleteFailure, cause)) 
      ELSE Nil
   
   WithRICIndication(msg) == 
      IF Assert(ValidRICIndication(msg), "Invalid RICIndication") 
      THEN SetType(msg, RICIndication) 
      ELSE Nil
   
   WithRICControlRequest(msg) == 
      IF Assert(ValidRICControlRequest(msg), "Invalid RICControlRequest") 
      THEN SetType(msg, RICControlRequest) 
      ELSE Nil
   
   WithRICControlAcknowledge(msg) == 
      IF Assert(ValidRICControlAcknowledge(msg), "Invalid RICControlAcknowledge") 
      THEN SetType(msg, RICControlResponse) 
      ELSE Nil
   
   WithRICControlFailure(msg, cause) == 
      IF Assert(ValidRICControlFailure(msg), "Invalid RICControlFailure") 
      THEN SetType(msg, SetFailureCause(RICControlFailure, cause)) 
      ELSE Nil
   
   WithE2ConnectionUpdate(msg) == 
      IF Assert(ValidE2ConnectionUpdate(msg), "Invalid E2ConnectionUpdate") 
      THEN SetType(msg, E2ConnectionUpdate) 
      ELSE Nil
   
   WithE2ConnectionUpdateAcknowledge(msg) == 
      IF Assert(ValidE2ConnectionUpdateAcknowledge(msg), "Invalid E2ConnectionUpdateAcknowledge") 
      THEN SetType(msg, E2ConnectionUpdateAcknowledge) 
      ELSE Nil
   
   WithE2ConnectionUpdateFailure(msg, cause) == 
      IF Assert(ValidE2ConnectionUpdateFailure(msg), "Invalid E2ConnectionUpdateFailure") 
      THEN SetType(msg, SetFailureCause(E2ConnectionUpdateFailure, cause)) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdate(msg) == 
      IF Assert(ValidE2NodeConfigurationUpdate(msg), "Invalid E2NodeConfigurationUpdate") 
      THEN SetType(msg, E2NodeConfigurationUpdate) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdateAcknowledge(msg) == 
      IF Assert(ValidE2NodeConfigurationUpdateAcknowledge(msg), "Invalid E2NodeConfigurationUpdateAcknowledge") 
      THEN SetType(msg, E2NodeConfigurationUpdateAcknowledge) 
      ELSE Nil
   
   WithE2NodeConfigurationUpdateFailure(msg, cause) == 
      IF Assert(ValidE2NodeConfigurationUpdateFailure(msg), "Invalid E2NodeConfigurationUpdateFailure") 
      THEN SetType(msg, SetFailureCause(E2NodeConfigurationUpdateFailure, cause)) 
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

   ------------------------------ MODULE Client -----------------------------
   
   (*
   The Client module provides operators for managing and operating on E2AP
   client connections and specifies the message types supported for the
   client.
   *)
   
   CONSTANT ID
   
      ------------------------------ MODULE Send ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP client.
      *)
      
      E2SetupRequest(conn, msg) == 
         /\ SCTP!Client(ID)!Send(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdate(conn, msg) == 
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICServiceUpdate(msg))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithResetResponse(msg))
      
      RICSubscriptionResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICSubscriptionResponse(msg))
      
      RICSubscriptionFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICSubscriptionFailure(msg, cause))
      
      RICSubscriptionDeleteResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICSubscriptionDeleteResponse(msg))
      
      RICSubscriptionDeleteFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICSubscriptionDeleteFailure(msg, cause))
      
      RICIndication(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICIndication(msg))
      
      RICControlAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICControlAcknowledge(msg))
      
      RICControlFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithRICControlFailure(msg, cause))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Send(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Requests module
   Send == INSTANCE Send
   
      ------------------------------ MODULE Reply ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP client.
      *)
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithResetResponse(msg))
      
      RICSubscriptionResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICSubscriptionResponse(msg))
      
      RICSubscriptionFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICSubscriptionFailure(msg, cause))
      
      RICSubscriptionDeleteResponse(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICSubscriptionDeleteResponse(msg))
      
      RICSubscriptionDeleteFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICSubscriptionDeleteFailure(msg, cause))
      
      RICIndication(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICIndication(msg))
      
      RICControlAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICControlAcknowledge(msg))
      
      RICControlFailure(conn, msg, cause) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithRICControlFailure(msg, cause))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Client(ID)!Reply(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Reply module
   Reply == INSTANCE Reply
   
      ---------------------------- MODULE Receive ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP client.
      *)
      
      E2SetupResponse(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      RICServiceUpdateAcknowledge(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      RICServiceUpdateFailure(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      ResetRequest(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      ResetResponse(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      RICSubscriptionRequest(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      RICSubscriptionDeleteRequest(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      RICControlRequest(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      E2ConnectionUpdate(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      E2ConnectionUpdateAcknowledge(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      E2NodeConfigurationUpdate(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) == 
         SCTP!Client(ID)!Receive(conn)
      
      =======================================================================
   
   \* Instantiate the E2AP!Client!Responses module
   Receive == INSTANCE Receive
   
      ---------------------------- MODULE Handle ----------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP client.
      *)
      
      E2SetupResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2SetupResponse(msg)
               /\ handler(conn, msg)
      
      RICServiceUpdateAcknowledge(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICServiceUpdateAcknowledge(msg)
               /\ handler(conn, msg)
      
      RICServiceUpdateFailure(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICServiceUpdateFailure(msg)
               /\ handler(conn, msg)
      
      ResetRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsResetRequest(msg)
               /\ handler(conn, msg)
      
      ResetResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsResetResponse(msg)
               /\ handler(conn, msg)
      
      RICSubscriptionRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICSubscriptionRequest(msg)
               /\ handler(conn, msg)
      
      RICSubscriptionDeleteRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICSubscriptionDeleteRequest(msg)
               /\ handler(conn, msg)
      
      RICControlRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICControlRequest(msg)
               /\ handler(conn, msg)
      
      E2ConnectionUpdate(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2ConnectionUpdate(msg)
               /\ handler(conn, msg)
      
      E2ConnectionUpdateAcknowledge(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2ConnectionUpdateAcknowledge(msg)
               /\ handler(conn, msg)
      
      E2NodeConfigurationUpdate(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2NodeConfigurationUpdate(msg)
               /\ handler(conn, msg)
      
      E2NodeConfigurationUpdateAcknowledge(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2NodeConfigurationUpdateAcknowledge(msg)
               /\ handler(conn, msg)
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Handle module
   Handle == INSTANCE Handle
   
   Connect(dst) == SCTP!Client(ID)!Connect(dst)
   
   Disconnect(conn) == SCTP!Client(ID)!Disconnect(conn)
   
   \* The set of all open E2AP connections
   Connections == SCTP!Client(ID)!Connections
      
   ==========================================================================

\* Provides operators for the E2AP client
Client(ID) == INSTANCE Client
      
   ----------------------------- MODULE Server ------------------------------
   
   (*
   The Server module provides operators for managing and operating on E2AP
   servers and specifies the message types supported for the server.
   *)
   
   CONSTANT ID
   
      ----------------------------- MODULE Send -----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP server.
      *)
      
      E2SetupResponse(conn, msg) == 
         /\ SCTP!Server(ID)!Send(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdateAcknowledge(conn, msg) == 
         /\ SCTP!Server(ID)!Send(conn, Messages!WithRICServiceUpdateAcknowledge(msg))
      
      RICServiceUpdateFailure(conn, msg, cause) == 
         /\ SCTP!Server(ID)!Send(conn, Messages!WithRICServiceUpdateFailure(msg, cause))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithResetResponse(msg))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server(ID)!Send(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Send module
   Send == INSTANCE Send
   
      ----------------------------- MODULE Reply ----------------------------
      
      (*
      This module provides message type operators for the message types that
      can be send by the E2AP server.
      *)
      
      E2SetupResponse(conn, msg) == 
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithE2SetupResponse(msg))
      
      RICServiceUpdateAcknowledge(conn, msg) == 
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithRICServiceUpdateAcknowledge(msg))
      
      RICServiceUpdateFailure(conn, msg, cause) == 
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithRICServiceUpdateFailure(msg, cause))
      
      ResetRequest(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithResetRequest(msg))
      
      ResetResponse(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithResetResponse(msg))
      
      E2ConnectionUpdate(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithE2ConnectionUpdate(msg))
      
      E2ConnectionUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithE2ConnectionUpdateAcknowledge(msg))
      
      E2NodeConfigurationUpdate(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithE2NodeConfigurationUpdate(msg))
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) ==
         /\ SCTP!Server(ID)!Reply(conn, Messages!WithE2NodeConfigurationUpdateAcknowledge(msg))
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Reply module
   Reply == INSTANCE Reply
   
      ---------------------------- MODULE Receive ---------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP server.
      *)
      
      E2SetupRequest(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      RICServiceUpdate(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      ResetRequest(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      ResetResponse(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      RICSubscriptionResponse(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      RICSubscriptionDeleteResponse(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      RICControlResponse(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      RICIndication(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      E2ConnectionUpdate(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      E2ConnectionUpdateAcknowledge(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      E2NodeConfigurationUpdate(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      E2NodeConfigurationUpdateAcknowledge(conn, msg) == 
         SCTP!Server(ID)!Receive(conn)
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Requests module
   Receive == INSTANCE Receive
   
      ---------------------------- MODULE Handle ----------------------------
      
      (* 
      This module provides predicates for the types of messages that can be 
      received by an E2AP server.
      *)
      
      E2SetupRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2SetupRequest(msg)
               /\ handler(conn, msg)
      
      RICServiceUpdate(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICServiceUpdate(msg)
               /\ handler(conn, msg)
      
      ResetRequest(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsResetRequest(msg)
               /\ handler(conn, msg)
      
      ResetResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsResetResponse(msg)
               /\ handler(conn, msg)
      
      RICSubscriptionResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICSubscriptionResponse(msg)
               /\ handler(conn, msg)
      
      RICSubscriptionDeleteResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICSubscriptionDeleteResponse(msg)
               /\ handler(conn, msg)
      
      RICControlResponse(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICControlResponse(msg)
               /\ handler(conn, msg)
      
      RICIndication(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsRICIndication(msg)
               /\ handler(conn, msg)
      
      E2ConnectionUpdate(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2ConnectionUpdate(msg)
               /\ handler(conn, msg)
      
      E2ConnectionUpdateAcknowledge(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2ConnectionUpdateAcknowledge(msg)
               /\ handler(conn, msg)
      
      E2NodeConfigurationUpdate(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2NodeConfigurationUpdate(msg)
               /\ handler(conn, msg)
      
      E2NodeConfigurationUpdateAcknowledge(conn, handler(_, _)) == 
         /\ SCTP!Server(ID)!Ready(conn)
         /\ LET msg == SCTP!Server(ID)!Read(conn)
            IN
               /\ Messages!IsE2NodeConfigurationUpdateAcknowledge(msg)
               /\ handler(conn, msg)
      
      =======================================================================
   
   \* Instantiate the E2AP!Server!Handle module
   Handle == INSTANCE Handle
   
   \* The set of all open E2AP connections
   Connections == SCTP!Server(ID)!Connections
   
   ==========================================================================

\* Provides operators for the E2AP server
Server(ID) == INSTANCE Server

Init == SCTP!Init

Next == SCTP!Next

=============================================================================
\* Modification History
\* Last modified Tue Sep 21 09:36:09 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 10:53:17 PDT 2021 by jordanhalterman
