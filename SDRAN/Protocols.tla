----------------------------- MODULE Protocols -----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

   ---------------------------- MODULE E2AP --------------------------------
   
   (*
   The E2AP module provides a formal specification of the E2AP protocol. The
   spec defines the client and server interfaces for E2AP and provides helpers
   for managing and operating on connections.
   *)
   
   CONSTANT Nil

   VARIABLE servers, conns
   
   vars == <<servers, conns>>
   
   \* The E2AP protocol is implemented on SCTP
   LOCAL SCTP == INSTANCE SCTP
   
   \* Message type constants
   CONSTANTS
      E2SetupRequestType,
      E2SetupResponseType,
      E2SetupFailureType
   CONSTANTS
      ResetRequestType,
      ResetResponseType
   CONSTANTS
      RICSubscriptionRequestType,
      RICSubscriptionResponseType,
      RICSubscriptionFailureType
   CONSTANTS
      RICSubscriptionDeleteRequestType,
      RICSubscriptionDeleteResponseType,
      RICSubscriptionDeleteFailureType
   CONSTANTS
      RICControlRequestType,
      RICControlResponseType,
      RICControlFailureType,
      RICServiceUpdateType
   CONSTANTS
      E2ConnectionUpdateType,
      E2ConnectionUpdateAcknowledgeType,
      E2ConnectionUpdateFailureType
   CONSTANTS
      E2NodeConfigurationUpdateType,
      E2NodeConfigurationUpdateAcknowledgeType,
      E2NodeConfigurationUpdateFailureType

   LOCAL messageTypes == 
      {E2SetupRequestType, 
       E2SetupResponseType,
       E2SetupFailureType,
       ResetRequestType,
       ResetResponseType,
       RICSubscriptionRequestType,
       RICSubscriptionResponseType,
       RICSubscriptionFailureType,
       RICSubscriptionDeleteRequestType,
       RICSubscriptionDeleteResponseType,
       RICSubscriptionDeleteFailureType,
       RICControlRequestType,
       RICControlResponseType,
       RICControlFailureType,
       RICServiceUpdateType,
       E2ConnectionUpdateType,
       E2ConnectionUpdateAcknowledgeType,
       E2ConnectionUpdateFailureType,
       E2NodeConfigurationUpdateType,
       E2NodeConfigurationUpdateAcknowledgeType,
       E2NodeConfigurationUpdateFailureType}

   \* Message types should be defined as strings to simplify debugging
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
       
       
   CONSTANTS
      Report,
      Insert,
      Policy
      
   CONSTANTS
      ricService,
      supportFunction,
      both   
 
   LOCAL actionTypes == {
         Report,
         Insert, 
         Policy}
         
   LOCAL tnlAssociationUsage == {
      ricService,
      supportFunction,
      both}    
   
   \* Failure causes should be defined as strings to simplify debugging
   ASSUME \A c \in failureCauses : c \in STRING
   
   Cause == [c \in failureCauses |-> c]
   
   ActionType == [a \in actionTypes |-> a]
   
   TnlAssociationUsage == [u \in tnlAssociationUsage |-> u]
   
      --------------------------- MODULE Messages --------------------------
      
      (*
      The Messages module defines predicates for receiving, sending, and
      verifying all the messages supported by E2AP.
      *)
      
      ----
      
      (*
      This section defines predicates for identifying E2AP message types on
      the network.
      *)
      
      IsE2SetupRequest(m) == m.type = E2SetupRequestType
      
      IsE2SetupResponse(m) == m.type = E2SetupResponseType
      
      IsE2SetupFailure(m) == m.type = E2SetupFailureType
      
      IsResetRequest(m) == m.type = ResetRequestType
      
      IsResetResponse(m) == m.type = ResetResponseType
      
      IsRICSubscriptionRequest(m) == m.type = RICSubscriptionRequestType
      
      IsRICSubscriptionResponse(m) == m.type = RICSubscriptionResponseType
      
      IsRICSubscriptionFailure(m) == m.type = RICSubscriptionFailureType
      
      IsRICSubscriptionDeleteRequest(m) == m.type = RICSubscriptionDeleteRequestType
      
      IsRICSubscriptionDeleteResponse(m) == m.type = RICSubscriptionDeleteResponseType
      
      IsRICSubscriptionDeleteFailure(m) == m.type = RICSubscriptionDeleteFailureType
      
      IsRICControlRequest(m) == m.type = RICControlRequestType
      
      IsRICControlResponse(m) == m.type = RICControlResponseType
      
      IsRICControlFailure(m) == m.type = RICControlFailureType
      
      IsRICServiceUpdate(m) == m.type = RICServiceUpdateType
      
      IsE2ConnectionUpdate(m) == m.type = E2ConnectionUpdateType
      
      IsE2ConnectionUpdateAcknowledge(m) == m.type = E2ConnectionUpdateAcknowledgeType
      
      IsE2ConnectionUpdateFailure(m) == m.type = E2ConnectionUpdateFailureType
      
      IsE2NodeConfigurationUpdate(m) == m.type = E2NodeConfigurationUpdateType
      
      IsE2NodeConfigurationUpdateAcknowledge(m) == m.type = E2NodeConfigurationUpdateAcknowledgeType
      
      IsE2NodeConfigurationUpdateFailure(m) == m.type = E2NodeConfigurationUpdateFailureType
         
      ----
         
      (*
      This section defines predicates for validating E2AP message contents. The predicates
      provide precise documentation on the E2AP message format and are used within the spec
      to verify that steps adhere to the E2AP protocol specification.
      *)
      
      LOCAL ContainValidTransactionID(m) == 
                /\ "transactionID" \in DOMAIN m 
                /\ m.trasnactionID \in Nat 
                /\ m.transactionID < 256
   
   
      LOCAL ContainValidRANFunctionID(m) == 
                 /\ "ranFunctionID" \in DOMAIN m 
                 /\ m.ranFunctionID \in Nat 
                 /\ m.ranFunctionID > 0 
                 /\ m.ranFunctionID < 4096
  
      LOCAL ContainValidRANFunctionOID(m) == 
                 /\ "ranFunctionOID" \in DOMAIN m
                 /\  m.ranFunctionOID \in STRING
                 
   
      LOCAL IsValidRANFunctionItem(ranFunctionItem) == 
                 /\ ContainValidRANFunctionID(ranFunctionItem)
                 /\ ContainValidRANFunctionOID(ranFunctionItem)
   
      LOCAL ContainValidRANFunctionList(m) == 
                 /\  "ranFunctionList" \in DOMAIN m 
                 /\ \A ranFunctionItem \in m.ranFunctionList : IsValidRANFunctionItem(ranFunctionItem)
   
   
   
      LOCAL ContainValidRICRequestID(m) == 
         /\ "ricRequestID" \in DOMAIN m
         /\ m.ricRequestID.requesterID \in Nat /\ m.ricRequestID.requesterID < 65536
         /\ m.ricRequestID.instanceID \in Nat /\ m.ricRequestID.instanceID < 65536
   
   
   
      LOCAL ContainValidFailureCause(m) == 
         /\ "cause" \in DOMAIN m  
         /\  m.cause \in DOMAIN Cause  
 
 
      LOCAL ContainValidActionID(m) == 
         /\ "actionID" \in DOMAIN m
         /\ m.actionID \in DOMAIN Nat 
         /\ m.actionID < 256    
          
      LOCAL ContainValidActionType(m) == 
         /\ "actionType" \in DOMAIN m
         /\  m.actionType \in DOMAIN ActionType                    
 
 
      LOCAL IsValidAction(m) == 
         /\ ContainValidActionID(m)
         /\ ContainValidActionType(m)  
     
     
      LOCAL ContainValidTranportLayerInfo(m) == 
         /\ "transportLayerInformation" \in DOMAIN m
         /\ m.address \in DOMAIN STRING
         /\ m.port \in DOMAIN Nat
           
     
      LOCAL ContainValidTnlAssociationUsage(m) == 
         /\ "tnlAssociationUsage" \in DOMAIN m
         /\ m.tnlAssociationUsage \in DOMAIN TnlAssociationUsage
             
     
      LOCAL IsValidConnectionToAddItem(m) == 
         /\ ContainValidTranportLayerInfo(m)
         /\ ContainValidTnlAssociationUsage(m)
     
           
        
      LOCAL ContainValidConnectionToAddList(m) == 
         /\ "connectionAddToList" \in DOMAIN m
         /\ \A connectionToAddItem \in m.connectionToAddList : IsValidConnectionToAddItem(connectionToAddItem) 
      
      
      LOCAL ValidE2SetupRequest(m) == 
         /\ IsE2SetupRequest(m)
         /\ "globalE2NodeID" \in DOMAIN m /\ m.globalE2NodeID \in STRING
         /\ "plmnID" \in DOMAIN m /\ m.plmnID \in Nat
         /\ ContainValidRANFunctionList(m)
         /\ ContainValidTransactionID(m)
      
      LOCAL ValidE2SetupResponse(m) == 
         /\ IsE2SetupResponse(m)
         /\ ContainValidTransactionID(m)
      
      LOCAL ValidE2SetupFailure(m) == 
         /\ IsE2SetupFailure(m)
         /\ ContainValidTransactionID(m)
         /\ ContainValidFailureCause(m)
      
      LOCAL ValidResetRequest(m) == 
         /\ IsResetRequest(m)
         /\ ContainValidTransactionID(m)
      
      
      LOCAL ValidResetResponse(m) == 
         /\ IsResetResponse(m)
         /\ ContainValidTransactionID(m)
      
      LOCAL ValidRICSubscriptionRequest(m) == 
         /\ IsRICSubscriptionRequest(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
         /\ "subscriptionDetails" \in DOMAIN m
         /\ \A action \in m.subscriptionDetails.actions : IsValidAction(action)
      
      LOCAL ValidRICSubscriptionResponse(m) == 
         /\ IsRICSubscriptionResponse(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
      
      LOCAL ValidRICSubscriptionFailure(m) == 
         /\ IsRICSubscriptionFailure(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
         /\ ContainValidFailureCause(m)
      
      LOCAL ValidRICSubscriptionDeleteRequest(m) == 
         /\ IsRICSubscriptionDeleteRequest(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
      
      LOCAL ValidRICSubscriptionDeleteResponse(m) == 
         /\ IsRICSubscriptionDeleteResponse(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
      
      LOCAL ValidRICSubscriptionDeleteFailure(m) == 
         /\ IsRICSubscriptionDeleteFailure(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
         /\ ContainValidFailureCause(m)
      
      LOCAL ValidRICControlRequest(m) == 
         /\ IsRICControlRequest(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
         /\ "controlHeader" \in DOMAIN m
         /\ "controlMessage" \in DOMAIN m
      
      LOCAL ValidRICControlResponse(m) == 
         /\ IsRICControlResponse(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
      
      LOCAL ValidRICControlFailure(m) == 
         /\ IsRICControlFailure(m)
         /\ ContainValidRANFunctionID(m)
         /\ ContainValidRICRequestID(m)
         /\ ContainValidFailureCause(m)
      
      LOCAL ValidRICServiceUpdate(m) == 
         /\ IsRICServiceUpdate(m)
         /\ ContainValidTransactionID(m)
      
      LOCAL ValidE2ConnectionUpdate(m) == 
         /\ IsE2ConnectionUpdate(m)  
         /\ ContainValidTransactionID(m)
         /\ ContainValidConnectionToAddList(m)
       \*/\ ContainValidConnectionToRemoveList(m)
       \*/\ ContainValidConnectionTomModifyList(m)
      
      LOCAL ValidE2ConnectionUpdateAcknowledge(m) == 
         /\ IsE2ConnectionUpdateAcknowledge(m)
         /\ ContainValidTransactionID(m)
      
      LOCAL ValidE2ConnectionUpdateFailure(m) == 
         /\ IsE2ConnectionUpdateFailure(m)
         /\ ContainValidTransactionID(m) 
         /\ ContainValidFailureCause(m)
      
      LOCAL ValidE2NodeConfigurationUpdate(m) == 
         /\ IsE2NodeConfigurationUpdate(m)
         /\ ContainValidTransactionID(m) 
      
      LOCAL ValidE2NodeConfigurationUpdateAcknowledge(m) == 
         /\ IsE2NodeConfigurationUpdateAcknowledge(m)
         /\ ContainValidTransactionID(m) 
      
      LOCAL ValidE2NodeConfigurationUpdateFailure(m) == 
         /\ IsE2NodeConfigurationUpdateFailure(m)
         /\ ContainValidTransactionID(m)
         /\ ContainValidFailureCause(m)
      
      ----
      
      (*
      This section defines operators for constructing E2AP messages.
      *)
      
      LOCAL SetType(m, t) == [m EXCEPT !.type = t]
      
      E2SetupRequest(m) ==
         IF Assert(ValidE2SetupRequest(m), "Invalid E2SetupRequest") 
         THEN SetType(m, E2SetupRequestType) 
         ELSE Nil
      
      E2SetupResponse(m) ==
         IF Assert(ValidE2SetupResponse(m), "Invalid E2SetupResponse") 
         THEN SetType(m, E2SetupResponseType) 
         ELSE Nil
      
      E2SetupFailure(m) == 
         IF Assert(ValidE2SetupFailure(m), "Invalid E2SetupFailure") 
         THEN SetType(m, E2SetupFailureType) 
         ELSE Nil
      
      ResetRequest(m) == 
         IF Assert(ValidResetRequest(m), "Invalid ResetRequest") 
         THEN SetType(m, ResetRequestType) 
         ELSE Nil
      
      ResetResponse(m) == 
         IF Assert(ValidResetResponse(m), "Invalid ResetResponse") 
         THEN SetType(m, ResetResponseType) 
         ELSE Nil
      
      RICSubscriptionRequest(m) == 
         IF Assert(ValidRICSubscriptionRequest(m), "Invalid RICSubscriptionRequest") 
         THEN SetType(m, RICSubscriptionRequestType) 
         ELSE Nil
      
      RICSubscriptionResponse(m) == 
         IF Assert(ValidRICSubscriptionResponse(m), "Invalid RICSubscriptionResponse") 
         THEN SetType(m, RICSubscriptionResponseType) 
         ELSE Nil
      
      RICSubscriptionFailure(m) == 
         IF Assert(ValidRICSubscriptionFailure(m), "Invalid RICSubscriptionFailure") 
         THEN SetType(m, RICSubscriptionFailureType) 
         ELSE Nil
      
      RICSubscriptionDeleteRequest(m) == 
         IF Assert(ValidRICSubscriptionDeleteRequest(m), "Invalid RICSubscriptionDeleteRequest") 
         THEN SetType(m, RICSubscriptionDeleteRequestType) 
         ELSE Nil
      
      RICSubscriptionDeleteResponse(m) == 
         IF Assert(ValidRICSubscriptionDeleteResponse(m), "Invalid RICSubscriptionDeleteResponse") 
         THEN SetType(m, RICSubscriptionDeleteResponseType) 
         ELSE Nil
      
      RICSubscriptionDeleteFailure(m) == 
         IF Assert(ValidRICSubscriptionDeleteFailure(m), "Invalid RICSubscriptionDeleteFailure") 
         THEN SetType(m, RICSubscriptionDeleteFailureType) 
         ELSE Nil
      
      RICControlRequest(m) == 
         IF Assert(ValidRICControlRequest(m), "Invalid RICControlRequest") 
         THEN SetType(m, RICControlRequestType) 
         ELSE Nil
      
      RICControlResponse(m) == 
         IF Assert(ValidRICControlResponse(m), "Invalid RICControlResponse") 
         THEN SetType(m, RICControlResponseType) 
         ELSE Nil
      
      RICControlFailure(m) == 
         IF Assert(ValidRICControlFailure(m), "Invalid RICControlFailure") 
         THEN SetType(m, RICControlFailureType) 
         ELSE Nil
      
      RICServiceUpdate(m) == 
         IF Assert(ValidRICServiceUpdate(m), "Invalid RICServiceUpdate") 
         THEN SetType(m, RICServiceUpdateType) 
         ELSE Nil
      
      E2ConnectionUpdate(m) == 
         IF Assert(ValidE2ConnectionUpdate(m), "Invalid E2ConnectionUpdate") 
         THEN SetType(m, E2ConnectionUpdateType) 
         ELSE Nil
      
      E2ConnectionUpdateAcknowledge(m) == 
         IF Assert(ValidE2ConnectionUpdateAcknowledge(m), "Invalid E2ConnectionUpdateAcknowledge") 
         THEN SetType(m, E2ConnectionUpdateAcknowledgeType) 
         ELSE Nil
      
      E2ConnectionUpdateFailure(m) == 
         IF Assert(ValidE2ConnectionUpdateFailure(m), "Invalid E2ConnectionUpdateFailure") 
         THEN SetType(m, E2ConnectionUpdateFailureType) 
         ELSE Nil
      
      E2NodeConfigurationUpdate(m) == 
         IF Assert(ValidE2NodeConfigurationUpdate(m), "Invalid E2NodeConfigurationUpdate") 
         THEN SetType(m, E2NodeConfigurationUpdateType) 
         ELSE Nil
      
      E2NodeConfigurationUpdateAcknowledge(m) == 
         IF Assert(ValidE2NodeConfigurationUpdateAcknowledge(m), "Invalid E2NodeConfigurationUpdateAcknowledge") 
         THEN SetType(m, E2NodeConfigurationUpdateAcknowledgeType) 
         ELSE Nil
      
      E2NodeConfigurationUpdateFailure(m) == 
         IF Assert(ValidE2NodeConfigurationUpdateFailure(m), "Invalid E2NodeConfigurationUpdateFailure") 
         THEN SetType(m, E2NodeConfigurationUpdateFailureType) 
         ELSE Nil
         
      ======================================================================
   
   \* The Messages module is instantiated locally to avoid access from outside
   \* the module.
   LOCAL Messages == INSTANCE Messages

      ---------------------------- MODULE Client ---------------------------
      
      (*
      The Client module provides operators for managing and operating on E2AP
      client connections and specifies the message types supported for the
      client.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the E2AP client.
         *)
         
         E2SetupRequest(c, m) == 
            /\ SCTP!Client!Send(c, Messages!E2SetupResponse(m))
         
         ResetRequest(c, m) ==
            /\ SCTP!Client!Send(c, Messages!ResetRequest(m))
         
         ResetResponse(c, m) ==
            /\ SCTP!Client!Reply(c, Messages!ResetResponse(m))
         
         ===================================================================
      
      \* Instantiate the E2AP!Client!Send module
      Send == INSTANCE Send
      
         ---------------------------- MODULE Receive --------------------------
         
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
         
         ===================================================================
      
      \* Instantiate the E2AP!Client!Receive module
      Receive == INSTANCE Receive
      
      Connect(s, d) == SCTP!Client!Connect(s, d)
      
      Disconnect(c) == SCTP!Client!Disconnect(c)
      
      ======================================================================

   \* Provides operators for the E2AP client
   Client == INSTANCE Client
         
      ---------------------------- MODULE Server ---------------------------
      
      (*
      The Server module provides operators for managing and operating on E2AP
      servers and specifies the message types supported for the server.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the E2AP server.
         *)
         
         E2SetupResponse(c, m) == 
            /\ SCTP!Server!Reply(c, Messages!E2SetupResponse(m))
         
         ResetRequest(c, m) ==
            /\ SCTP!Server!Send(c, Messages!ResetRequest(m))
         
         ResetResponse(c, m) ==
            /\ SCTP!Server!Reply(c, Messages!ResetResponse(m))
         
         ===================================================================
      
      \* Instantiate the E2AP!Server!Send module
      Send == INSTANCE Send
      
         ---------------------------- MODULE Receive --------------------------
         
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
         
         ===================================================================
      
      \* Instantiate the E2AP!Server!Receive module
      Receive == INSTANCE Receive
      
      \* Starts a new E2AP server
      Serve(s) == SCTP!Server!Start(s)
      
      \* Stops the given E2AP server
      Stop(s) == SCTP!Server!Stop(s)
      
      ======================================================================

   \* Provides operators for the E2AP server
   Server == INSTANCE Server
   
   \* The set of all running E2AP servers
   Servers == SCTP!Servers
   
   \* The set of all open E2AP connections
   Connections == SCTP!Connections
   
   Init == SCTP!Init
   
   Next == SCTP!Next

   =========================================================================

VARIABLES e2apServers, e2apConns

E2AP == INSTANCE E2AP WITH
   servers <- e2apServers,
   conns <- e2apConns,
   Nil <- [type |-> ""],
   E2SetupRequestType <- "E2SetupRequest",
   E2SetupResponseType <- "E2SetupResponse",
   E2SetupFailureType <- "E2SetupFailure",
   ResetRequestType <- "ResetRequest",
   ResetResponseType <- "ResetResponse",
   RICSubscriptionRequestType <- "RICSubscriptionRequest",
   RICSubscriptionResponseType <- "RICSubscriptionResponse",
   RICSubscriptionFailureType <- "RICSubscriptionFailure",
   RICSubscriptionDeleteRequestType <- "RICSubscriptionDeleteRequest",
   RICSubscriptionDeleteResponseType <- "RICSubscriptionDeleteResponse",
   RICSubscriptionDeleteFailureType <- "RICSubscriptionDeleteFailure",
   RICControlRequestType <- "RICControlRequest",
   RICControlResponseType <- "RICControlResponse",
   RICControlFailureType <- "RICControlFailure",
   RICServiceUpdateType <- "RICServiceUpdate",
   E2ConnectionUpdateType <- "E2ConnectionUpdate",
   E2ConnectionUpdateAcknowledgeType <- "E2ConnectionUpdateAcknowledge",
   E2ConnectionUpdateFailureType <- "E2ConnectionUpdateFailure",
   E2NodeConfigurationUpdateType <- "E2NodeConfigurationUpdate",
   E2NodeConfigurationUpdateAcknowledgeType <- "E2NodeConfigurationUpdateAcknowledge",
   E2NodeConfigurationUpdateFailureType <- "E2NodeConfigurationUpdateFailure",
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
   TransportFailureTransportResourceUnavailable <- "TransportFailureTransportResourceUnavailable",
   Report <- "Report",
   Insert <- "Insert",
   Policy <- "Policy",
   ricService <- "RicService",
   supportFunction <- "SupportFunction",
   both <- "Both"

   --------------------------- MODULE E2TService ---------------------------
   
   (*
   The E2AP module provides a formal specification of the E2T service. The
   spec defines the client and server interfaces for E2T and provides helpers
   for managing and operating on connections.
   *)
   
   CONSTANT Nil

   VARIABLE servers, conns
      
   vars == <<servers, conns>>
      
   \* The E2T API is implemented as a gRPC service
   LOCAL GRPC == INSTANCE GRPC
         
   \* Message type constants
   CONSTANT 
      SubscribeRequestType,
      SubscribeResponseType
   CONSTANTS
      UnsubscribeRequestType,
      UnsubscribeResponseType
   CONSTANTS
      ControlRequestType,
      ControlResponseType

   LOCAL messageTypes == 
      {SubscribeRequestType, 
       SubscribeResponseType,
       UnsubscribeRequestType,
       UnsubscribeResponseType,
       ControlRequestType,
       ControlResponseType}
   
   \* Message types should be defined as strings to simplify debugging
   ASSUME \A m \in messageTypes : m \in STRING

      --------------------------- MODULE Messages --------------------------
      
      (*
      The Messages module defines predicates for receiving, sending, and
      verifying all the messages supported by E2T.
      *)
      
      ----
      
      (*
      This section defines predicates for identifying E2T message types on
      the network.
      *)
      
      IsSubscribeRequest(m) == m.type = SubscribeRequestType
      
      IsSubscribeResponse(m) == m.type = SubscribeResponseType
      
      IsUnsubscribeRequest(m) == m.type = UnsubscribeRequestType
      
      IsUnsubscribeResponse(m) == m.type = UnsubscribeResponseType
      
      IsControlRequest(m) == m.type = ControlRequestType
      
      IsControlResponse(m) == m.type = ControlResponseType
      
      ----
         
      (*
      This section defines predicates for validating E2T message contents. The predicates
      provide precise documentation on the E2T message format and are used within the spec
      to verify that steps adhere to the E2T protocol specification.
      *)
      
      LOCAL ValidSubscribeRequest(m) == TRUE
      
      LOCAL ValidSubscribeResponse(m) == TRUE
      
      LOCAL ValidUnsubscribeRequest(m) == TRUE
      
      LOCAL ValidUnsubscribeResponse(m) == TRUE
      
      LOCAL ValidControlRequest(m) == TRUE
      
      LOCAL ValidControlResponse(m) == TRUE
      
      ----
      
      (*
      This section defines operators for constructing E2T messages.
      *)
      
      LOCAL SetType(m, t) == [m EXCEPT !.type = t]
      
      SubscribeRequest(m) ==
         IF Assert(ValidSubscribeRequest(m), "Invalid SubscribeRequest") 
         THEN SetType(m, SubscribeRequestType) 
         ELSE Nil
      
      SubscribeResponse(m) ==
         IF Assert(ValidSubscribeResponse(m), "Invalid SubscribeResponse") 
         THEN SetType(m, SubscribeResponseType) 
         ELSE Nil
      
      UnsubscribeRequest(m) == 
         IF Assert(ValidUnsubscribeRequest(m), "Invalid UnsubscribeRequest") 
         THEN SetType(m, UnsubscribeRequestType) 
         ELSE Nil
      
      UnsubscribeResponse(m) == 
         IF Assert(ValidUnsubscribeResponse(m), "Invalid UnsubscribeResponse") 
         THEN SetType(m, UnsubscribeResponseType) 
         ELSE Nil
      
      ControlRequest(m) == 
         IF Assert(ValidControlRequest(m), "Invalid ControlRequest") 
         THEN SetType(m, ControlRequestType) 
         ELSE Nil
      
      ControlResponse(m) == 
         IF Assert(ValidControlResponse(m), "Invalid ControlResponse") 
         THEN SetType(m, ControlResponseType) 
         ELSE Nil
         
      ======================================================================
   
   \* The Messages module is instantiated locally to avoid access from outside
   \* the module.
   LOCAL Messages == INSTANCE Messages

      ---------------------------- MODULE Client ---------------------------
      
      (*
      The Client module provides operators for managing and operating on E2T
      client connections and specifies the message types supported for the
      client.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the E2T client.
         *)
         
         SubscribeRequest(c, m) == 
            /\ GRPC!Client!Send(c, Messages!SubscribeRequest(m))
         
         UnsubscribeRequest(c, m) ==
            /\ GRPC!Client!Send(c, Messages!UnsubscribeRequest(m))
         
         ControlRequest(c, m) ==
            /\ GRPC!Client!Send(c, Messages!ControlRequest(m))
         
         ===================================================================
      
      \* Instantiate the E2T!Client!Send module
      Send == INSTANCE Send
      
         ---------------------------- MODULE Receive --------------------------
         
         (* 
         This module provides predicates for the types of messages that can be 
         received by an E2T client.
         *)
         
         SubscribeResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsSubscribeResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         UnsubscribeResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsUnsubscribeResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         ControlResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsControlResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         ===================================================================
      
      \* Instantiate the E2T!Client!Receive module
      Receive == INSTANCE Receive
      
      Connect(s, d) == GRPC!Client!Connect(s, d)
      
      Disconnect(c) == GRPC!Client!Disconnect(c)
      
      ======================================================================

   \* Provides operators for the E2T client
   Client == INSTANCE Client
         
      ---------------------------- MODULE Server ---------------------------
      
      (*
      The Server module provides operators for managing and operating on E2T
      servers and specifies the message types supported for the server.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the E2T server.
         *)
         
         SubscribeResponse(c, m) == 
            /\ GRPC!Server!Reply(c, Messages!SubscribeResponse(m))
         
         UnsubscribeResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!UnsubscribeResponse(m))
         
         ControlResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!ControlResponse(m))
         
         ===================================================================
      
      \* Instantiate the E2T!Server!Send module
      Send == INSTANCE Send
      
         ---------------------------- MODULE Receive --------------------------
         
         (* 
         This module provides predicates for the types of messages that can be 
         received by an E2T server.
         *)
         
         SubscribeRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsSubscribeRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         UnsubscribeRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsUnsubscribeRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         ControlRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsControlRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         ===================================================================
      
      \* Instantiate the E2T!Server!Receive module
      Receive == INSTANCE Receive
      
      \* Starts a new E2T server
      Serve(s) == GRPC!Server!Start(s)
      
      \* Stops the given E2T server
      Stop(s) == GRPC!Server!Stop(s)
      
      ======================================================================

   \* Provides operators for the E2T server
   Server == INSTANCE Server
   
   \* The set of all running E2T servers
   Servers == GRPC!Servers
   
   \* The set of all open E2T connections
   Connections == GRPC!Connections
   
   Init == GRPC!Init
   
   Next == GRPC!Next

   =========================================================================

VARIABLES e2tServers, e2tConns

E2T == INSTANCE E2TService WITH
   servers <- e2tServers,
   conns <- e2tConns,
   Nil <- [type |-> ""],
   SubscribeRequestType <- "SubscribeRequest", 
   SubscribeResponseType <- "SubscribeResponse", 
   UnsubscribeRequestType <- "UnsubscribeRequest", 
   UnsubscribeResponseType <- "UnsubscribeResponse", 
   ControlRequestType <- "ControlRequest", 
   ControlResponseType <- "ControlResponse"

   --------------------------- MODULE TopoService --------------------------
   
   (*
   The Topo module provides a formal specification of the µONOS topology 
   service. The spec defines the client and server interfaces for µONOS Topo
   and provides helpers for managing and operating on connections.
   *)
   
   CONSTANT Nil
   
   VARIABLES servers, conns
      
   vars == <<servers, conns>>
      
   \* The Topo API is implemented as a gRPC service
   LOCAL GRPC == INSTANCE GRPC
         
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

      --------------------------- MODULE Messages --------------------------
      
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

      ---------------------------- MODULE Client ---------------------------
      
      (*
      The Client module provides operators for managing and operating on Topo
      client connections and specifies the message types supported for the
      client.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the Topo client.
         *)
         
         CreateRequest(c, m) == 
            /\ GRPC!Client!Send(c, Messages!CreateRequest(m))
         
         UpdateRequest(c, m) ==
            /\ GRPC!Client!Send(c, Messages!UpdateRequest(m))
         
         DeleteRequest(c, m) ==
            /\ GRPC!Client!Send(c, Messages!DeleteRequest(m))
         
         GetRequest(c, m) == 
            /\ GRPC!Client!Send(c, Messages!GetRequest(m))
         
         ListRequest(c, m) == 
            /\ GRPC!Client!Send(c, Messages!ListRequest(m))
         
         WatchRequest(c, m) == 
            /\ GRPC!Client!Send(c, Messages!WatchRequest(m))
         
         ===================================================================
      
      \* Instantiate the Topo!Client!Send module
      Send == INSTANCE Send
      
         ---------------------------- MODULE Receive --------------------------
         
         (* 
         This module provides predicates for the types of messages that can be 
         received by an Topo client.
         *)
         
         CreateResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsCreateResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         UpdateResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsUpdateResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         DeleteResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsDeleteResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         GetResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsGetResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         ListResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsListResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         WatchResponse(c, h(_, _)) == 
            GRPC!Client!Handle(c, LAMBDA x, m : 
               /\ Messages!IsWatchResponse(m) 
               /\ GRPC!Client!Receive(c)
               /\ h(c, m))
         
         ===================================================================
      
      \* Instantiate the Topo!Client!Receive module
      Receive == INSTANCE Receive
      
      Connect(s, d) == GRPC!Client!Connect(s, d)
      
      Disconnect(c) == GRPC!Client!Disconnect(c)
      
      ======================================================================

   \* Provides operators for the Topo client
   Client == INSTANCE Client
         
      ---------------------------- MODULE Server ---------------------------
      
      (*
      The Server module provides operators for managing and operating on Topo
      servers and specifies the message types supported for the server.
      *)
      
         ---------------------------- MODULE Send --------------------------
         
         (*
         This module provides message type operators for the message types that
         can be send by the Topo server.
         *)
         
         CreateResponse(c, m) == 
            /\ GRPC!Server!Reply(c, Messages!CreateResponse(m))
         
         UpdateResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!UpdateResponse(m))
         
         DeleteResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!DeleteResponse(m))
         
         GetResponse(c, m) == 
            /\ GRPC!Server!Reply(c, Messages!GetResponse(m))
         
         ListResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!ListResponse(m))
         
         WatchResponse(c, m) ==
            /\ GRPC!Server!Reply(c, Messages!WatchResponse(m))
         
         ===================================================================
      
      \* Instantiate the Topo!Server!Send module
      Send == INSTANCE Send
      
         -------------------------- MODULE Receive -------------------------
         
         (* 
         This module provides predicates for the types of messages that can be 
         received by an Topo server.
         *)
         
         CreateRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsCreateRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         UpdateRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsUpdateRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         DeleteRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsDeleteRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         GetRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsGetRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         ListRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsListRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         WatchRequest(c, h(_, _)) == 
            GRPC!Server!Handle(c, LAMBDA x, m : 
               /\ Messages!IsWatchRequest(m) 
               /\ GRPC!Server!Receive(c)
               /\ h(c, m))
         
         ===================================================================
      
      \* Instantiate the Topo!Server!Receive module
      Receive == INSTANCE Receive
      
      \* Starts a new Topo server
      Serve(s) == GRPC!Server!Start(s)
      
      \* Stops the given Topo server
      Stop(s) == GRPC!Server!Stop(s)
      
      ======================================================================

   \* Provides operators for the Topo server
   Server == INSTANCE Server
   
   \* The set of all running Topo servers
   Servers == GRPC!Servers
   
   \* The set of all open Topo connections
   Connections == GRPC!Connections
   
   Init == GRPC!Init
   
   Next == GRPC!Next
   
   =========================================================================

VARIABLE topoServers, topoConns

Topo == INSTANCE TopoService WITH
   servers <- topoServers,
   conns <- topoConns,
   Nil <- [type |-> ""],
   CreateRequestType <- "CreateRequest",
   CreateResponseType <- "CreateResponse",
   UpdateRequestType <- "UpdateRequest",
   UpdateResponseType <- "UpdateResponse",
   DeleteRequestType <- "DeleteRequest",
   DeleteResponseType <- "DeleteResponse",
   GetRequestType <- "GetRequest",
   GetResponseType <- "GetResponse",
   ListRequestType <- "ListRequest",
   ListResponseType <- "ListResponse",
   WatchRequestType <- "WatchRequest",
   WatchResponseType <- "WatchResponse"

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 18:00:43 PDT 2021 by adibrastegarnia
\* Last modified Fri Aug 13 17:42:40 PDT 2021 by jordanhalterman
\* Last modified Fri Aug 13 15:56:13 PDT 2021 by jordanhalterman
\* Created Fri Aug 13 15:34:11 PDT 2021 by jordanhalterman
