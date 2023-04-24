---- MODULE MC ----
EXTENDS Config, TLC

const_Changes == 
   {[path1 |-> "value1"],
    [path1 |-> "value2"],
    [path1 |-> Nil]}

\*const_Changes == 
\*   {[path1 |-> "value1"],
\*    [path1 |-> "value2"],
\*    [path1 |-> Nil],
\*    [path2 |-> "value1"],
\*    [path2 |-> Nil],
\*    [path1 |-> "value1",
\*     path2 |-> Nil]}

const_Nodes == 
   {"node1", "node2"}

\*const_Nodes == 
\*   {"node1"}

constraint_proposal == 
   Len(proposal) <= 3

constraint_mastership == 
   mastership.term <= 2

\*constraint_mastership == 
\*   CASE mastership.term < 2 -> TRUE
\*     [] mastership.term = 2 -> mastership.master # Nil
\*     [] OTHER -> FALSE

constraint_node == 
   \A n \in DOMAIN node : node[n].incarnation <= 2

\*constraint_node == 
\*   \A n \in DOMAIN node : 
\*      CASE node[n].incarnation < 2 -> TRUE
\*        [] node[n].incarnation = 2 -> node[n].connected
\*        [] OTHER -> FALSE

constraint_target == 
   target.incarnation <= 2

\*constraint_target == 
\*   CASE target.incarnation < 2 -> TRUE
\*     [] target.incarnation = 2 -> target.running
\*     [] OTHER -> FALSE

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

=============================================================================
\* Modification History
\* Created Fri Apr 21 19:16:11 PDT 2023 by jhalterm
