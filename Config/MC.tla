---- MODULE MC ----
EXTENDS Config, TLC

target_log_constraint ==
    /\ \A t \in DOMAIN proposal : Len(proposal[t]) <= 2
    /\ \A t \in DOMAIN mastership : mastership[t].term <= 2

\* CONSTANT definitions @modelParameterConstants:1ConfigurationInProgress
const_1682129771341599000 == 
"InProgress"
----

\* CONSTANT definitions @modelParameterConstants:2ConfigurationFailed
const_1682129771341600000 == 
"Failed"
----

\* CONSTANT definitions @modelParameterConstants:3ProposalValidate
const_1682129771341601000 == 
"Validate"
----

\* CONSTANT definitions @modelParameterConstants:5ProposalComplete
const_1682129771341603000 == 
"Complete"
----

\* CONSTANT definitions @modelParameterConstants:6ConfigurationComplete
const_1682129771341604000 == 
"Complete"
----

\* CONSTANT definitions @modelParameterConstants:7ProposalAbort
const_1682129771341605000 == 
"Abort"
----

\* CONSTANT definitions @modelParameterConstants:8ProposalApply
const_1682129771341606000 == 
"Apply"
----

\* CONSTANT definitions @modelParameterConstants:9Nil
const_1682129771341607000 == 
"<nil>"
----

\* CONSTANT definitions @modelParameterConstants:10ProposalChange
const_1682129771341608000 == 
"Change"
----

\* CONSTANT definitions @modelParameterConstants:11ProposalFailure
const_1682129771341609000 == 
"Failure"
----

\* CONSTANT definitions @modelParameterConstants:12ProposalCommit
const_1682129771341610000 == 
"Commit"
----

\* CONSTANT definitions @modelParameterConstants:13ProposalInProgress
const_1682129771341611000 == 
"InProgress"
----

\* CONSTANT definitions @modelParameterConstants:14ProposalRollback
const_1682129771341612000 == 
"Rollback"
----

\* CONSTANT definitions @modelParameterConstants:15ProposalFailed
const_1682129771341613000 == 
"Failed"
----

\* CONSTANT definitions @modelParameterConstants:16Target
const_1682129771341614000 == 
[target1 |-> 
   [persistent |-> FALSE,
    values |-> [
      path1 |-> {"value1", "value2"},
      path2 |-> {"value3"}]],
target2 |-> 
   [persistent |-> TRUE,
    values |-> [
      path2 |-> {"value3", "value4"},
      path3 |-> {"value5"}]]]
----

\* CONSTANT definitions @modelParameterConstants:17ProposalSuccess
const_1682129771341615000 == 
"Success"
----

\* CONSTANT definitions @modelParameterConstants:18Node
const_1682129771341616000 == 
{"node1", "node2"}
----

\* CONSTANT definitions @modelParameterConstants:19ProposalInitialize
const_1682129771341617000 == 
"Initialize"
----

=============================================================================
\* Modification History
\* Created Fri Apr 21 19:16:11 PDT 2023 by jhalterm
