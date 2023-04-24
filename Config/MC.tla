---- MODULE MC ----
EXTENDS Config, TLC

constraint_proposal == Len(proposal) <= 2

constraint_mastership ==
   CASE mastership.term < 2 -> TRUE
     [] mastership.term = 2 -> mastership.master # Nil
     [] OTHER -> FALSE

constraint_node == 
   \A n \in DOMAIN node : 
      CASE node[n].incarnation < 2 -> TRUE
        [] node[n].incarnation = 2 -> node[n].connected
        [] OTHER -> FALSE

constraint_target == 
   CASE target.incarnation < 2 -> TRUE
     [] target.incarnation = 2 -> target.running
     [] OTHER -> FALSE

const_TraceEnabled == FALSE

const_Nil == "<nil>"

const_ConfigurationInProgress == "InProgress"

const_ConfigurationComplete == "Complete"

const_ConfigurationFailed == "Failed"

const_ProposalChange == "Change"

const_ProposalRollback == "Rollback"

const_ProposalCommit == "Commit"

const_ProposalApply == "Apply"

const_ProposalInProgress == "InProgress"

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
