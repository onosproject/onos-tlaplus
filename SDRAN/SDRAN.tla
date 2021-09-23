------------------------------- MODULE SDRAN -------------------------------

CONSTANT xApps

CONSTANT E2TNodes

CONSTANT E2Nodes

LOCAL INSTANCE xApp

LOCAL INSTANCE E2T

LOCAL INSTANCE RANSim

Init == 
   /\ E2T!Init
   /\ RANSim!Init
   /\ xApp!Init

Next ==
   \/ E2T!Next
   \/ RANSim!Next
   \/ xApp!Next

=============================================================================
\* Modification History
\* Last modified Wed Sep 22 18:29:29 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
