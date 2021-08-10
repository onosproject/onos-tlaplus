------------------------------- MODULE SDRAN -------------------------------

EXTENDS Topo, E2T, E2Node, xApp

Init ==
   /\ TopoInit
   /\ E2TInit
   /\ E2NodeInit
   /\ AppInit

Next ==
   \/ TopoNext
   \/ E2TNext
   \/ E2NodeNext
   \/ AppNext

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 06:37:29 PDT 2021 by jordanhalterman
\* Created Tue Aug 10 04:53:48 PDT 2021 by jordanhalterman
