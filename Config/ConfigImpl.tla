------------------------------- MODULE ConfigImpl -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

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
   history

vars == <<proposal, configuration, mastership, conn, target, history>>

LOCAL Proposal == INSTANCE ProposalImpl

LOCAL Configuration == INSTANCE ConfigurationImpl

LOCAL Mastership == INSTANCE MastershipImpl

LOCAL Southbound == INSTANCE Southbound

----

(*
Formal specification, constraints, and theorems.
*)

Init == 
   /\ Proposal!Init

Next == 
   \/ Proposal!Next

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ \A i \in 1..NumProposals : WF_vars(Proposal!ProposeChange(i) \/ Proposal!ProposeRollback(i))
   /\ \A n \in Node, i \in 1..NumProposals : WF_vars(Proposal!Reconcile(n, i))
   /\ \A n \in Node : WF_<<configuration, mastership, conn, target>>(Configuration!Reconcile(n))
   /\ \A n \in Node : WF_<<mastership, conn, target>>(Mastership!Reconcile(n))
   /\ \A n \in Node : WF_<<conn, target>>(Southbound!ConnectNode(n) \/ Southbound!DisconnectNode(n))
   /\ WF_<<target>>(Southbound!StartTarget)
   /\ WF_<<target>>(Southbound!StopTarget)

Mapping == INSTANCE Config WITH 
   proposal <- [i \in DOMAIN proposal |-> [
      phase    |-> proposal[i].phase,
      values   |-> [p \in DOMAIN proposal[i].change.values |-> proposal[i].change.values[p].value],
      change   |-> [
         commit |-> IF /\ proposal[i].change.commit = InProgress 
                       /\ configuration.committed.changeIndex >= i
                    THEN Complete
                    ELSE proposal[i].change.commit,
         apply  |-> IF /\ proposal[i].change.apply = InProgress 
                       /\ configuration.applied.changeIndex >= i
                    THEN Complete
                    ELSE proposal[i].change.apply],
      rollback |-> [
         commit |-> IF /\ proposal[i].rollback.commit = InProgress 
                       /\ configuration.committed.index # i
                    THEN Complete
                    ELSE proposal[i].rollback.commit,
         apply  |-> IF /\ proposal[i].rollback.apply = InProgress 
                       /\ configuration.applied.index # i
                    THEN Complete
                    ELSE proposal[i].rollback.apply]]],
   configuration <- [
      committed |-> [
         values |-> configuration.committed.values],
      applied |-> [
         term   |-> configuration.applied.term,
         target |-> configuration.applied.target,
         values |-> configuration.applied.values],
      status |-> configuration.status]

Refinement == Mapping!Spec

Constraint == Mapping!Constraint

Order == Mapping!Order

Consistency == Mapping!Consistency

Liveness == Mapping!Liveness

=============================================================================
