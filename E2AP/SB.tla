------------------------------ MODULE SB ------------------------------

EXTENDS Naturals, Sequences, TLC, Messages

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

VARIABLE sbConn

VARIABLE sbConnId

----

InitSBVars ==
    /\ sbConn = [c \in {} |-> [e2node |-> Nil, ricnode |-> Nil, messages |-> <<>>]]

----

SBSend(c, m) == sbConn' = [sbConn EXCEPT ![c] = [sbConn[c] EXCEPT !.messages = Append(sbConn[c].messages, m)]]

SBReceive(c) == sbConn' = [sbConn EXCEPT ![c] = [sbConn[c] EXCEPT !.messages = SubSeq(sbConn[c].messages, 2, Len(sbConn[c].messages))]]

SBReply(c, m) == sbConn' = [sbConn EXCEPT ![c] = [sbConn[c] EXCEPT !.messages = Append(SubSeq(sbConn[c].messages, 2, Len(sbConn[c].messages)), m)]]

----

SBConnect(e2node, ricnode) ==
    /\ sbConnId' = sbConnId + 1
    /\ sbConn' = sbConn @@ (sbConnId' :> [e2node |-> e2node, ricnode |-> ricnode, messages |-> <<>>])

SBDisconnect(id) ==
    /\ sbConn' = [c \in {v \in DOMAIN sbConn : v # id} |-> sbConn[c]]

----

SBNext ==
    \/ \E c \in DOMAIN sbConn : SBDisconnect(c)

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:57:12 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:01:02 PDT 2021 by jordanhalterman
