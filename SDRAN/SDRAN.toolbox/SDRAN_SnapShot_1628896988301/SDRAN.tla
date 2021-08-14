------------------------------- MODULE SDRAN -------------------------------

EXTENDS API

CONSTANT TopoNodes

LOCAL Topo == INSTANCE Topo WITH Nodes <- TopoNodes

CONSTANT E2TNodes

LOCAL E2T == INSTANCE E2T WITH Nodes <- E2TNodes

CONSTANT E2Nodes

LOCAL E2Node == INSTANCE E2Node WITH Nodes <- E2Nodes

CONSTANT xApps

LOCAL xApp(app, nodes) == INSTANCE xApp WITH App <- app, Nodes <- nodes

Init == 
   /\ API!E2AP!Init
   /\ API!E2T!Init
   /\ API!Topo!Init
   /\ Topo!Init
   /\ E2T!Init
   /\ E2Node!Init
   /\ \A app \in DOMAIN xApps : xApp(app, xApps[app])!Init

Next ==
   \/ API!E2AP!Next
   \/ API!E2T!Next
   \/ API!Topo!Next
   \/ Topo!Next
   \/ E2T!Next
   \/ E2Node!Next
   \/ \E app \in DOMAIN xApps : xApp(app, xApps[app])!Next

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 16:20:58 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
