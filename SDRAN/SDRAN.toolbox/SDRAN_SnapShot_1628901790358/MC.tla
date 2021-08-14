---- MODULE MC ----
EXTENDS SDRAN, TLC

\* CONSTANT definitions @modelParameterConstants:0E2TNodes
const_162890178642568000 == 
{"e2t-1", "e2t-2"}
----

\* CONSTANT definitions @modelParameterConstants:1E2Nodes
const_162890178642569000 == 
{"e2node-1", "e2node-2"}
----

\* CONSTANT definitions @modelParameterConstants:2TopoNodes
const_162890178642570000 == 
{"topo-1"}
----

\* CONSTANT definitions @modelParameterConstants:3xApps
const_162890178642571000 == 
[app1 |-> {"instance1", "instance2"}, app2 |-> {"instance1", "instance2"}]
----

\* CONSTANT definitions @modelParameterConstants:4Error
const_162890178642572000 == 
"Error"
----

\* CONSTANT definitions @modelParameterConstants:5OK
const_162890178642573000 == 
"OK"
----

=============================================================================
\* Modification History
\* Created Fri Aug 13 17:43:06 PDT 2021 by jordanhalterman
