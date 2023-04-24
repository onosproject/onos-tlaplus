---- MODULE MC ----
EXTENDS Config, TLC

constraint_proposal == Len(proposal) <= 2

constraint_mastership == mastership.term <= 1

constraint_conn == \A n \in DOMAIN node : node[n].incarnation <= 1

constraint_target == target.incarnation <= 1

const_TraceEnabled == FALSE

const_Nil == "<nil>"

const_ConfigurationInProgress == "InProgress"

const_ConfigurationComplete == "Complete"

const_ConfigurationFailed == "Failed"

const_ProposalChange == "Change"

const_ProposalRollback == "Rollback"

const_ProposalValidate == "Validate"

const_ProposalInProgress == "InProgress"

const_ProposalCommit == "Commit"

const_ProposalApply == "Apply"

const_ProposalAbort == "Abort"

const_ProposalComplete == "Complete"

const_ProposalFailed == "Failed"

const_Target == [
   values |-> [
      path1 |-> {"value1", "value2"},
      path2 |-> {"value3"}]]

const_Node == {"node1", "node2"}

=============================================================================
\* Modification History
\* Created Fri Apr 21 19:16:11 PDT 2023 by jhalterm
