------------------------------- MODULE ConfigImpl -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

----

LogEnabled == FALSE

NumProposals == 3

None == "<none>"

Synchronizing == "Synchronizing"
Synchronized == "Synchronized"

Change == "Change"
Rollback == "Rollback"

Commit == "Commit"
Apply == "Apply"

Pending == "Pending"
InProgress == "InProgress"
Complete == "Complete"
Aborted == "Aborted"
Failed == "Failed"

Node == {"node1"}

Path == {"path1"}

Value == {"value1", "value2"}

VARIABLES
   proposal,
   configuration,
   mastership,
   conn,
   target,
   history,
   mapping

INSTANCE ProposalImpl

=============================================================================
