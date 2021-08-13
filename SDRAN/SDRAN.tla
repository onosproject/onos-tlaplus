------------------------------- MODULE SDRAN -------------------------------

EXTENDS API

CONSTANT E2TNodes

E2T == INSTANCE E2T WITH Nodes <- E2TNodes

CONSTANT E2Nodes

E2Node == INSTANCE E2Node WITH Nodes <- E2Nodes

CONSTANT xAppNodes

xApp == INSTANCE xApp WITH Nodes <- xAppNodes

Init ==
   /\ API!Init
   /\ E2T!Init
   /\ E2Node!Init
   /\ xApp!Init

Next ==
   \/ API!Next
   \/ E2T!Next
   \/ E2Node!Next
   \/ xApp!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 04:58:21 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
