------------------------------- MODULE SDRAN -------------------------------

EXTENDS API

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

CONSTANT TopoNodes

LOCAL Topo == INSTANCE Topo WITH Nodes <- TopoNodes

CONSTANT E2TNodes

LOCAL E2T == INSTANCE E2T WITH Nodes <- E2TNodes

CONSTANT E2Nodes

LOCAL E2Node == INSTANCE E2Node WITH Nodes <- E2Nodes

CONSTANT xApps

LOCAL xApp(app, nodes) == INSTANCE xApp WITH App <- app, Nodes <- nodes

RECURSIVE SetToSeq(_)
LOCAL SetToSeq(S) == 
   IF Cardinality(S) = 0 THEN <<>>
   ELSE
      LET
         x == CHOOSE x \in S : TRUE
      IN
         <<x>> \o SetToSeq(S \ {x})

LOCAL xAppVars == SetToSeq({app \in DOMAIN xApps : xApp(app, xApps[app])!vars})

Init == 
   \*/\ API!E2AP!Init
   /\ API!E2T!Init
   /\ API!Topo!Init
   /\ Topo!Init
   /\ E2T!Init
   /\ E2Node!Init
   /\ \A app \in DOMAIN xApps : xApp(app, xApps[app])!Init

Next ==
   \*\/ /\ API!E2AP!Next
   \*   /\ UNCHANGED <<API!E2T!vars, API!Topo!vars, Topo!vars, E2T!vars, E2Node!vars, xAppVars>>
   \/ /\ API!E2T!Next
      /\ UNCHANGED <<API!E2AP!vars, API!Topo!vars, Topo!vars, E2T!vars, E2Node!vars, xAppVars>>
   \/ /\ API!Topo!Next
      /\ UNCHANGED <<API!E2AP!vars, API!E2T!vars, Topo!vars, E2T!vars, E2Node!vars, xAppVars>>
   \/ /\ Topo!Next
      /\ UNCHANGED <<API!E2AP!vars, API!E2T!vars, API!Topo!vars, E2T!vars, E2Node!vars, xAppVars>>
   \/ /\ E2T!Next
      /\ UNCHANGED <<API!E2AP!vars, API!E2T!vars, API!Topo!vars, Topo!vars, E2Node!vars, xAppVars>>
   \/ /\ E2Node!Next
      /\ UNCHANGED <<API!E2AP!vars, API!E2T!vars, API!Topo!vars, Topo!vars, E2T!vars, xAppVars>>
   \/ /\ \E app \in DOMAIN xApps : xApp(app, xApps[app])!Next
      /\ UNCHANGED <<API!E2AP!vars, API!E2T!vars, API!Topo!vars, Topo!vars, E2T!vars, E2Node!vars>>

=============================================================================
\* Modification History
\* Last modified Fri Aug 13 17:43:03 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
