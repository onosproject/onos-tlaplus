----------------------------- MODULE Protocols -----------------------------

EXTENDS TLC

   ------------------------------- MODULE E2AP ------------------------------
      
   \* Message type constants
   CONSTANTS
      E2Setup,
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
      {E2Setup, 
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

   ASSUME \A m \in messageTypes : m \in STRING

   \* Failure cause constants
   CONSTANTS
      MiscFailureUnspecified,
      MiscFailureControlProcessingOverload,
      MiscFailureHardwareFailure,
      MiscFailureOMIntervention
   CONSTANTS
      ProtocolFailureUnspecified,
      ProtocolFailureTransferSyntaxError,
      ProtocolFailureAbstractSyntaxErrorReject,
      ProtocolFailureAbstractSyntaxErrorIgnoreAndNotify,
      ProtocolFailureMessageNotCompatibleWithReceiverState,
      ProtocolFailureSemanticError,
      ProtocolFailureAbstractSyntaxErrorFalselyConstructedMessage
   CONSTANTS
      RICFailureUnspecified,
      RICFailureRANFunctionIDInvalid,
      RICFailureActionNotSupported,
      RICFailureExcessiveActions,
      RICFailureDuplicateAction,
      RICFailureDuplicateEvent,
      RICFailureFunctionResourceLimit,
      RICFailureRequestIDUnknown,
      RICFailureInconsistentActionSubsequentActionSequence,
      RICFailureControlMessageInvalid,
      RICFailureCallProcessIDInvalid
   CONSTANTS
      RICServiceFailureUnspecified,
      RICServiceFailureFunctionNotRequired,
      RICServiceFailureExcessiveFunctions,
      RICServiceFailureRICResourceLimit
   CONSTANTS
      TransportFailureUnspecified,
      TransportFailureTransportResourceUnavailable
   
   LOCAL failureCauses ==
      {MiscFailureUnspecified,
       MiscFailureControlProcessingOverload,
       MiscFailureHardwareFailure,
       MiscFailureOMIntervention,
       ProtocolFailureUnspecified,
       ProtocolFailureTransferSyntaxError,
       ProtocolFailureAbstractSyntaxErrorReject,
       ProtocolFailureAbstractSyntaxErrorIgnoreAndNotify,
       ProtocolFailureMessageNotCompatibleWithReceiverState,
       ProtocolFailureSemanticError,
       ProtocolFailureAbstractSyntaxErrorFalselyConstructedMessage,
       RICFailureUnspecified,
       RICFailureRANFunctionIDInvalid,
       RICFailureActionNotSupported,
       RICFailureExcessiveActions,
       RICFailureDuplicateAction,
       RICFailureDuplicateEvent,
       RICFailureFunctionResourceLimit,
       RICFailureRequestIDUnknown,
       RICFailureInconsistentActionSubsequentActionSequence,
       RICFailureControlMessageInvalid,
       RICFailureCallProcessIDInvalid,
       RICServiceFailureUnspecified,
       RICServiceFailureFunctionNotRequired,
       RICServiceFailureExcessiveFunctions,
       RICServiceFailureRICResourceLimit,
       TransportFailureUnspecified,
       TransportFailureTransportResourceUnavailable}
   
   ASSUME \A c \in failureCauses : c \in STRING
   
   Protocol == [t \in messageTypes |-> t]
   
   Cause == [c \in failureCauses |-> c]

   ----
   
   LOCAL IsValidE2Setup(m) == TRUE
   
   LOCAL IsValidE2SetupResponse(m) == TRUE
   
   LOCAL IsValidE2SetupFailure(m) == TRUE
   
   LOCAL IsValidResetRequest(m) == TRUE
   
   LOCAL IsValidResetResponse(m) == TRUE
   
   LOCAL IsValidRICSubscriptionRequest(m) == TRUE
   
   LOCAL IsValidRICSubscriptionResponse(m) == TRUE
   
   LOCAL IsValidRICSubscriptionFailure(m) == TRUE
   
   LOCAL IsValidRICSubscriptionDeleteRequest(m) == TRUE
   
   LOCAL IsValidRICSubscriptionDeleteResponse(m) == TRUE
   
   LOCAL IsValidRICSubscriptionDeleteFailure(m) == TRUE
   
   LOCAL IsValidRICControlRequest(m) == TRUE
   
   LOCAL IsValidRICControlResponse(m) == TRUE
   
   LOCAL IsValidRICControlFailure(m) == TRUE
   
   LOCAL IsValidRICServiceUpdate(m) == TRUE
   
   LOCAL IsValidE2ConnectionUpdate(m) == TRUE
   
   LOCAL IsValidE2ConnectionUpdateAcknowledge(m) == TRUE
   
   LOCAL IsValidE2ConnectionUpdateFailure(m) == TRUE
   
   LOCAL IsValidE2NodeConfigurationUpdate(m) == TRUE
   
   LOCAL IsValidE2NodeConfigurationUpdateAcknowledge(m) == TRUE
   
   LOCAL IsValidE2NodeConfigurationUpdateFailure(m) == TRUE
   
   ----
   
   LOCAL IsValidMessage(m) ==
      \/ /\ m.type = E2Setup
         /\ IsValidE2Setup(m)
      \/ /\ m.type = E2SetupResponse
         /\ IsValidE2SetupResponse(m)
      \/ /\ m.type = E2SetupFailure
         /\ IsValidE2SetupFailure(m)
      \/ /\ m.type = ResetRequest
         /\ IsValidResetRequest(m)
      \/ /\ m.type = ResetResponse
         /\ IsValidResetResponse(m)
      \/ /\ m.type = RICSubscriptionRequest
         /\ IsValidRICSubscriptionRequest(m)
      \/ /\ m.type = RICSubscriptionResponse
         /\ IsValidRICSubscriptionResponse(m)
      \/ /\ m.type = RICSubscriptionFailure
         /\ IsValidRICSubscriptionFailure(m)
      \/ /\ m.type = RICSubscriptionDeleteRequest
         /\ IsValidRICSubscriptionDeleteRequest(m)
      \/ /\ m.type = RICSubscriptionDeleteResponse
         /\ IsValidRICSubscriptionDeleteResponse(m)
      \/ /\ m.type = RICSubscriptionDeleteFailure
         /\ IsValidRICSubscriptionDeleteFailure(m)
      \/ /\ m.type = RICControlRequest
         /\ IsValidRICControlRequest(m)
      \/ /\ m.type = RICControlResponse
         /\ IsValidRICControlResponse(m)
      \/ /\ m.type = RICControlFailure
         /\ IsValidRICControlFailure(m)
      \/ /\ m.type = RICServiceUpdate
         /\ IsValidRICServiceUpdate(m)
      \/ /\ m.type = E2ConnectionUpdate
         /\ IsValidE2ConnectionUpdate(m)
      \/ /\ m.type = E2ConnectionUpdateAcknowledge
         /\ IsValidE2ConnectionUpdateAcknowledge(m)
      \/ /\ m.type = E2ConnectionUpdateFailure
         /\ IsValidE2ConnectionUpdateFailure(m)
      \/ /\ m.type = E2NodeConfigurationUpdate
         /\ IsValidE2NodeConfigurationUpdate(m)
      \/ /\ m.type = E2NodeConfigurationUpdateAcknowledge
         /\ IsValidE2NodeConfigurationUpdateAcknowledge(m)
      \/ /\ m.type = E2NodeConfigurationUpdateFailure
         /\ IsValidE2NodeConfigurationUpdateFailure(m)
   
   VARIABLE servers, conns
      
   INSTANCE Messaging WITH Nil <- "<nil>", IsValid <- IsValidMessage
   
   ==========================================================================

VARIABLE e2apServers, e2apConns

E2AP == INSTANCE E2AP WITH
   servers <- e2apServers,
   conns <- e2apConns,
   E2Setup <- "E2Setup",
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
   E2NodeConfigurationUpdateFailure <- "E2NodeConfigurationUpdateFailure",
   MiscFailureUnspecified <- "MiscFailureUnspecified",
   MiscFailureControlProcessingOverload <- "MiscFailureControlProcessingOverload",
   MiscFailureHardwareFailure <- "MiscFailureHardwareFailure",
   MiscFailureOMIntervention <- "MiscFailureOMIntervention",
   ProtocolFailureUnspecified <- "ProtocolFailureUnspecified",
   ProtocolFailureTransferSyntaxError <- "ProtocolFailureTransferSyntaxError",
   ProtocolFailureAbstractSyntaxErrorReject <- "ProtocolFailureAbstractSyntaxErrorReject",
   ProtocolFailureAbstractSyntaxErrorIgnoreAndNotify <- "ProtocolFailureAbstractSyntaxErrorIgnoreAndNotify",
   ProtocolFailureMessageNotCompatibleWithReceiverState <- "ProtocolFailureMessageNotCompatibleWithReceiverState",
   ProtocolFailureSemanticError <- "ProtocolFailureSemanticError",
   ProtocolFailureAbstractSyntaxErrorFalselyConstructedMessage <- "ProtocolFailureAbstractSyntaxErrorFalselyConstructedMessage",
   RICFailureUnspecified <- "RICFailureUnspecified",
   RICFailureRANFunctionIDInvalid <- "RICFailureRANFunctionIDInvalid",
   RICFailureActionNotSupported <- "RICFailureActionNotSupported",
   RICFailureExcessiveActions <- "RICFailureExcessiveActions",
   RICFailureDuplicateAction <- "RICFailureDuplicateAction",
   RICFailureDuplicateEvent <- "RICFailureDuplicateEvent",
   RICFailureFunctionResourceLimit <- "RICFailureFunctionResourceLimit",
   RICFailureRequestIDUnknown <- "RICFailureRequestIDUnknown",
   RICFailureInconsistentActionSubsequentActionSequence <- "RICFailureInconsistentActionSubsequentActionSequence",
   RICFailureControlMessageInvalid <- "RICFailureControlMessageInvalid",
   RICFailureCallProcessIDInvalid <- "RICFailureCallProcessIDInvalid",
   RICServiceFailureUnspecified <- "RICServiceFailureUnspecified",
   RICServiceFailureFunctionNotRequired <- "RICServiceFailureFunctionNotRequired",
   RICServiceFailureExcessiveFunctions <- "RICServiceFailureExcessiveFunctions",
   RICServiceFailureRICResourceLimit <- "RICServiceFailureRICResourceLimit",
   TransportFailureUnspecified <- "TransportFailureUnspecified",
   TransportFailureTransportResourceUnavailable <- "TransportFailureTransportResourceUnavailable"

   ------------------------------- MODULE E2T ------------------------------

   \* Message type constants
   CONSTANT 
      SubscribeRequest,
      SubscribeResponse
   CONSTANTS
      UnsubscribeRequest,
      UnsubscribeResponse
   CONSTANTS
      ControlRequest,
      ControlResponse
      
   LOCAL messageTypes == 
      {SubscribeRequest, 
       SubscribeResponse,
       UnsubscribeRequest,
       UnsubscribeResponse,
       ControlRequest,
       ControlResponse}
   
   ASSUME \A m \in messageTypes : m \in STRING
   
   Protocol == [t \in messageTypes |-> t]
   
   ----
   
   LOCAL IsValidSubscribeRequest(m) == TRUE
   
   LOCAL IsValidSubscribeResponse(m) == TRUE
   
   LOCAL IsValidUnsubscribeRequest(m) == TRUE
   
   LOCAL IsValidUnsubscribeResponse(m) == TRUE
   
   ----
   
   LOCAL IsValidMessage(m) ==
      \/ /\ m.type = SubscribeRequest
         /\ IsValidSubscribeRequest(m)
      \/ /\ m.type = SubscribeResponse
         /\ IsValidSubscribeResponse(m)
      \/ /\ m.type = UnsubscribeRequest
         /\ IsValidUnsubscribeRequest(m)
      \/ /\ m.type = UnsubscribeResponse
         /\ IsValidUnsubscribeResponse(m)

   VARIABLE servers, conns
      
   INSTANCE Messaging WITH Nil <- "<nil>", IsValid <- IsValidMessage
   
   ==========================================================================

VARIABLES e2tServers, e2tConns

E2T == INSTANCE E2T WITH 
   servers <- e2tServers,
   conns <- e2tConns,
   SubscribeRequest <- "SubscribeRequest", 
   SubscribeResponse <- "SubscribeResponse", 
   UnsubscribeRequest <- "UnsubscribeRequest", 
   UnsubscribeResponse <- "UnsubscribeResponse", 
   ControlRequest <- "ControlRequest", 
   ControlResponse <- "ControlResponse"

Init == 
   /\ E2AP!Init
   /\ E2T!Init

Next ==
   \/ E2AP!Next
   \/ E2T!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 06:03:48 PDT 2021 by jordanhalterman
\* Created Fri Aug 13 04:37:35 PDT 2021 by jordanhalterman
