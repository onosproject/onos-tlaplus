-------------------------------- MODULE E2AP --------------------------------

\* Message type constants
CONSTANT 
    E2Setup,
    E2SetupResponse,
    E2SetupFailure
CONSTANT
    ResetRequest,
    ResetResponse
CONSTANT
    RICSubscriptionRequest,
    RICSubscriptionResponse,
    RICSubscriptionFailure
CONSTANT
    RICSubscriptionDeleteRequest,
    RICSubscriptionDeleteResponse,
    RICSubscriptionDeleteFailure
CONSTANT
    RICControlRequest,
    RICControlResponse,
    RICControlFailure,
    RICServiceUpdate
CONSTANT
    E2ConnectionUpdate,
    E2ConnectionUpdateAcknowledge,
    E2ConnectionUpdateFailure
CONSTANT
    E2NodeConfigurationUpdate,
    E2NodeConfigurationUpdateAcknowledge,
    E2NodeConfigurationUpdateFailure

\* Failure cause constants
CONSTANT
    MiscFailureUnspecified,
    MiscFailureControlProcessingOverload,
    MiscFailureHardwareFailure,
    MiscFailureOMIntervention
CONSTANT
    ProtocolFailureUnspecified,
    ProtocolFailureTransferSyntaxError,
    ProtocolFailureAbstractSyntaxErrorReject,
    ProtocolFailureAbstractSyntaxErrorIgnoreAndNotify,
    ProtocolFailureMessageNotCompatibleWithReceiverState,
    ProtocolFailureSemanticError,
    ProtocolFailureAbstractSyntaxErrorFalselyConstructedMessage
CONSTANT
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
CONSTANT
    RICServiceFailureUnspecified,
    RICServiceFailureFunctionNotRequired,
    RICServiceFailureExcessiveFunctions,
    RICServiceFailureRICResourceLimit
CONSTANT
    TransportFailureUnspecified,
    TransportFailureTransportResourceUnavailable

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 04:51:58 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:32:11 PDT 2021 by jordanhalterman
