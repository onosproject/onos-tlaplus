-------------------------------- MODULE E2T --------------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE TLC

CONSTANT E2TNode

----

\* Message type constants
CONSTANT 
   SubscribeRequest,
   SubscribeResponse
CONSTANTS
   UnsubscribeRequest,
   UnsubscribeResponse
   
VARIABLES e2tNbConn, e2tNbConnId

E2TNB == INSTANCE Messaging WITH Nil <- "<nil>", conn <- e2tNbConn, connId <- e2tNbConnId

----

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

VARIABLES e2tSbConn, e2tSbConnId

E2TSB == INSTANCE Messaging WITH Nil <- "<nil>", conn <- e2tSbConn, connId <- e2tSbConnId

----

E2TNBHandleSubscribe(c, m) ==
    /\ E2TNB!Reply(c, [type |-> SubscribeResponse])
    /\ UNCHANGED <<>>

E2TNBHandleUnsubscribe(c, m) ==
    /\ E2TNB!Reply(c, [type |-> UnsubscribeResponse])
    /\ UNCHANGED <<>>

E2TNBHandleMessage(c, m) ==
   /\ \/ /\ m.type = SubscribeRequest
         /\ E2TNBHandleSubscribe(c, m)
   /\ \/ /\ m.type = UnsubscribeRequest
         /\ E2TNBHandleSubscribe(c, m)
   /\ UNCHANGED <<>>

----

E2TSBHandleE2Setup(c, m) ==
    /\ E2TSB!Reply(c, [type |-> E2SetupResponse])
    /\ UNCHANGED <<>>

E2TSBHandleMessage(c, m) ==
   /\ \/ /\ m.type = E2Setup
         /\ E2TSBHandleE2Setup(c, m)
   /\ UNCHANGED <<>>

----

E2TInit ==
   /\ E2TNB!Init
   /\ E2TSB!Init

E2TNext ==
   \/ \E c \in E2TNB!Connections : E2TNB!Disconnect(c)
   \/ \E c \in E2TSB!Connections : E2TSB!Disconnect(c)
   \/ \E c \in E2TNB!Connections : E2TNB!Handle(c, E2TNBHandleMessage)
   \/ \E c \in E2TSB!Connections : E2TSB!Handle(c, E2TSBHandleMessage)

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:31:08 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:55:45 PDT 2021 by jordanhalterman
