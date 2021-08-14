---- MODULE MC ----
EXTENDS SDRAN, TLC

\* CONSTANT definitions @modelParameterConstants:0E2TNodes
const_162889684724238000 == 
{"e2t-1", "e2t-2"}
----

\* CONSTANT definitions @modelParameterConstants:1E2Nodes
const_162889684724239000 == 
{"e2node-1", "e2node-2"}
----

\* CONSTANT definitions @modelParameterConstants:2TopoNodes
const_162889684724240000 == 
{"topo-1"}
----

\* CONSTANT definitions @modelParameterConstants:3xApps
const_162889684724241000 == 
[app1 |-> {"instance1", "instance2"}, app2 |-> {"instance1", "instance2"}]
----

\* CONSTANT definitions @modelParameterConstants:4Error
const_162889684724242000 == 
"Error"
----

\* CONSTANT definitions @modelParameterConstants:5OK
const_162889684724243000 == 
"OK"
----

=============================================================================
\* Modification History
\* Created Fri Aug 13 16:20:47 PDT 2021 by jordanhalterman
