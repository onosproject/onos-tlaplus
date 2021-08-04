------------------------------ MODULE Messages ------------------------------

EXTENDS Naturals, Sequences, TLC

\* A reserved value.
CONSTANTS Nil

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

VARIABLE connections

VARIABLE connectionId

VARIABLE messages

----

InitMessageVars ==
    /\ connections = [c \in {} |-> [e2node |-> Nil, e2tnode |-> Nil]]
    /\ messages = [m \in {} |-> <<>>]

----

Send(c, m) == messages' = [messages EXCEPT ![c] = Append(messages[c], m)]

Receive(c) == messages' = [messages EXCEPT ![c] = SubSeq(messages[c], 2, Len(messages[c]))]

Reply(c, m) == messages' = [messages EXCEPT ![c] = Append(SubSeq(messages[c], 2, Len(messages[c])), m)]

----

Connect(ricnode, e2node) ==
    /\ connectionId' = connectionId + 1
    /\ connections' = connections @@ (connectionId :> [ricnode |-> ricnode, e2node |-> e2node])
    /\ UNCHANGED <<messages>>

Disconnect(id) ==
    /\ connections' = [c \in {v \in DOMAIN connections : v # id} |-> connections[c]]
    /\ UNCHANGED <<connectionId, messages>>


=============================================================================
\* Modification History
\* Last modified Tue Aug 03 17:09:12 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:01:02 PDT 2021 by jordanhalterman
