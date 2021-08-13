------------------------------- MODULE SDRAN -------------------------------

EXTENDS API

CONSTANT E2TNodes

E2T == INSTANCE E2T WITH Nodes <- E2TNodes

CONSTANT E2Nodes

E2Node == INSTANCE E2Node WITH Nodes <- E2Nodes

CONSTANT xApps

LOCAL xApp(app, nodes) == INSTANCE xApp WITH App <- app, Nodes <- nodes

Init ==
   /\ API!Init
   /\ E2T!Init
   /\ E2Node!Init
   /\ \A app \in DOMAIN xApps : xApp(app, xApps[app])!Init

Next ==
   \/ API!Next
   \/ E2T!Next
   \/ E2Node!Next
   \/ \E app \in DOMAIN xApps : xApp(app, xApps[app])!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 06:01:47 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
