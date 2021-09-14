------------------------------- MODULE SDRAN -------------------------------

CONSTANT xApps

CONSTANT E2TNodes

CONSTANT E2Nodes

LOCAL INSTANCE xApp

LOCAL INSTANCE E2T

LOCAL INSTANCE E2Node

Init == 
   /\ E2T!Init
   /\ E2Node!Init
   /\ xApp!Init

Next ==
   \/ E2T!Next
   \/ E2Node!Next
   \/ xApp!Next

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 19:57:31 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
