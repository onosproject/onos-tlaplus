------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

GenerateTestCases == FALSE

Nil == "<nil>"

Change == "Change"
Rollback == "Rollback"

Initialize == "Initialize"
Validate == "Validate"
Abort == "Abort"
Commit == "Commit"
Apply == "Apply"

InProgress == "InProgress"
Complete == "Complete"
Failed == "Failed"

Pending == "Pending"
Validated == "Validated"
Committed == "Committed"
Applied == "Applied"
Aborted == "Aborted"

Valid == TRUE
Invalid == FALSE

Success == "Success"
Failure == "Failure"

Node == {"node1"}

NumTransactions == 3

Path == {"path1"}
Value == {"value1", "value2"}

----

\* A transaction log. Transactions may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE transaction

\* A record of per-target proposals
VARIABLE proposal

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masterships
VARIABLE mastership

vars == <<transaction, proposal, configuration, mastership, target>>

----

LOCAL Transaction == INSTANCE Transaction

LOCAL Proposal == INSTANCE Proposal

LOCAL Configuration == INSTANCE Configuration

LOCAL Mastership == INSTANCE Mastership

----

RequestChange(p, v) ==
   /\ Transaction!RequestChange(p, v)

RequestRollback(i) ==
   /\ Transaction!RequestRollback(i)

SetMaster(n) ==
   /\ Mastership!SetMaster(n)
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

UnsetMaster ==
   /\ Mastership!UnsetMaster
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
   /\ Transaction!ReconcileTransaction(n, i)
   /\ GenerateTestCases => Transaction!Test!Log([node |-> n, index |-> i])

ReconcileProposal(n, i) ==
   /\ i \in DOMAIN proposal
   /\ Proposal!ReconcileProposal(n, i)
   /\ UNCHANGED <<transaction>>
   /\ GenerateTestCases => Proposal!Test!Log([node |-> n, index |-> i])

ReconcileConfiguration(n) ==
   /\ Configuration!ReconcileConfiguration(n)
   /\ UNCHANGED <<transaction, proposal>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [
         i \in {} |-> [
            type   |-> Change,
            phase  |-> Initialize,
            state  |-> InProgress]]
   /\ proposal = [
         i \in {} |-> [
            phase |-> Initialize,
            state |-> InProgress]]
   /\ configuration = [
         state  |-> InProgress,
         config |-> [
            index  |-> 0,
            term   |-> 0,
            values |-> [
               path \in {} |-> [
                  path    |-> path,
                  value   |-> Nil,
                  index   |-> 0,
                  deleted |-> FALSE]]],
         proposal  |-> [index |-> 0],
         commit    |-> [index |-> 0],
         target    |-> [
            index  |-> 0,
            term   |-> 0,
            values |-> [
               path \in {} |-> [
                  path    |-> path,
                  value   |-> Nil,
                  index   |-> 0,
                  deleted |-> FALSE]]]]
   /\ target = [path \in {} |-> [value |-> Nil]]
   /\ mastership = [master |-> Nil, term |-> 0]

Next ==
   \/ \E p \in Path, v \in Value :
         RequestChange(p, v)
   \/ \E i \in DOMAIN transaction :
         RequestRollback(i)
   \/ \E n \in Node :
         SetMaster(n)
   \*\/ \E t \in DOMAIN Target :
   \*      UnsetMaster(t)
   \/ \E n \in Node :
         \E i \in DOMAIN transaction :
            ReconcileTransaction(n, i)
   \/ \E n \in Node :
         \E i \in DOMAIN proposal :
            ReconcileProposal(n, i)
   \/ \E n \in Node :
         ReconcileConfiguration(n)

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ \A p \in Path, v \in Value :
         WF_<<transaction, proposal, configuration, mastership, target>>(Transaction!RequestChange(p, v))
   /\ \A i \in 1..NumTransactions : i \in DOMAIN transaction =>
         WF_<<transaction, proposal, configuration, mastership, target>>(Transaction!RequestRollback(i))
   /\ \A n \in Node :
         WF_<<mastership>>(Mastership!SetMaster(n))
   \*/\ \E t \in DOMAIN Target :
   \*      WF_<<mastership>>(Mastership!UnsetMaster(t))
   /\ \A n \in Node, i \in 1..NumTransactions :
         WF_<<transaction, proposal, configuration, mastership, target>>(Transaction!ReconcileTransaction(n, i))
   /\ \A n \in Node, i \in 1..NumTransactions :
         WF_<<proposal, configuration, mastership, target>>(Proposal!ReconcileProposal(n, i))
   /\ \A n \in Node :
         WF_<<configuration, mastership, target>>(Configuration!ReconcileConfiguration(n))

----

LimitTransactions == Len(transaction) <= NumTransactions

----

Order ==
   \A i \in DOMAIN proposal :
      /\ /\ proposal[i].phase = Commit
         /\ proposal[i].state = InProgress
         => ~\E j \in DOMAIN proposal :
               /\ j > i
               /\ proposal[j].phase = Commit
               /\ proposal[j].state = Complete
      /\ /\ proposal[i].phase = Apply
         /\ proposal[i].state = InProgress
         => ~\E j \in DOMAIN proposal :
               /\ j > i
               /\ proposal[j].phase = Apply
               /\ proposal[j].state = Complete

Consistency == 
   LET 
      \* Compute the transaction indexes that have been applied to the target
      targetIndexes == {i \in DOMAIN transaction : 
                           /\ i \in DOMAIN proposal
                           /\ proposal[i].phase = Apply
                           /\ proposal[i].state = Complete
                           /\ ~\E j \in DOMAIN transaction :
                                 /\ j > i
                                 /\ transaction[j].type = Rollback
                                 /\ transaction[j].rollback = i
                                 /\ transaction[j].phase = Apply
                                 /\ transaction[j].state = Complete}
      \* Compute the set of paths in the target that have been updated by transactions
      appliedPaths == UNION {DOMAIN proposal[i].change.values : i \in targetIndexes}
      \* Compute the highest index applied to the target for each path
      pathIndexes == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                        \A j \in targetIndexes :
                           /\ i >= j 
                           /\ p \in DOMAIN proposal[i].change.values]
      \* Compute the expected target configuration based on the last indexes applied
      \* to the target for each path.
      expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[pathIndexes[p]].change.values[p]]
   IN 
      target = expectedConfig

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN transaction
   /\ \/ /\ transaction[i].phase = Apply
         /\ transaction[i].state = Complete
      \/ transaction[i].state = Failed

Termination ==
   \A i \in 1..NumTransactions : <>Terminated(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
