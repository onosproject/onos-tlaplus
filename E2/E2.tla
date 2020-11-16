--------------------------------- MODULE E2 ---------------------------------

(*
The E2 module provides the specification for the entire E2 protocol within
the µONOS RIC.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

----

CONSTANTS
   NetworkNil

VARIABLES
   networkChannels,
   networkChannelId

Network == INSTANCE Network WITH
   Nil       <- NetworkNil,
   channels  <- networkChannels,
   channelId <- networkChannelId

----

CONSTANTS
   TopoNodes,
   TopoNil

VARIABLES
   topoEntities,
   topoRelations

Topo == INSTANCE Topo WITH
   Nodes     <- TopoNodes,
   Nil       <- TopoNil,
   entities  <- topoEntities,
   relations <- topoRelations

----

CONSTANTS 
   E2SubNodes, 
   E2SubPhaseCreate, 
   E2SubPhaseDelete, 
   E2SubStatusPending, 
   E2SubStatusComplete, 
   E2SubNil

VARIABLES 
   e2SubSubscriptions, 
   e2SubSubscriptionTasks

E2Sub == INSTANCE E2Sub WITH
   Nodes             <- E2SubNodes,
   PhaseCreate       <- E2SubPhaseCreate,
   PhaseDelete       <- E2SubPhaseDelete,
   StatusPending     <- E2SubStatusPending,
   StatusComplete    <- E2SubStatusComplete,
   Nil               <- E2SubNil,
   subscriptions     <- e2SubSubscriptions,
   subscriptionTasks <- e2SubSubscriptionTasks

----

CONSTANTS
   E2TNodes

E2T == INSTANCE E2T WITH
   Nodes <- E2TNodes

----

CONSTANTS
   E2NodeNodes

E2Node == INSTANCE E2Node WITH
   Nodes <- E2NodeNodes

----

CONSTANTS
   E2AppNodes

E2App == INSTANCE E2App WITH
   Nodes <- E2AppNodes

----

Init ==
   /\ Network!Init
   /\ Topo!Init
   /\ E2Sub!Init
   /\ E2T!Init
   /\ E2Node!Init
   /\ E2App!Init

Next ==
   \/ Network!Next
   \/ Topo!Next
   \/ E2Sub!Next
   \/ E2T!Next
   \/ E2Node!Next
   \/ E2App!Next

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:16:57 PST 2020 by jordanhalterman
\* Created Sun Nov 15 10:26:47 PST 2020 by jordanhalterman
