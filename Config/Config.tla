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

Commit == "Commit"
Apply == "Apply"

Pending == "Pending"
InProgress == "InProgress"
Complete == "Complete"
Aborted == "Aborted"
Failed == "Failed"
Done == {Complete, Aborted, Failed}

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

\* A sequence of state changes used for model checking.
VARIABLE history

vars == <<transaction, proposal, configuration, mastership, target, history>>

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
   /\ UNCHANGED <<transaction, proposal, configuration, target, history>>

UnsetMaster ==
   /\ Mastership!UnsetMaster
   /\ UNCHANGED <<transaction, proposal, configuration, target, history>>

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
   /\ UNCHANGED <<transaction, proposal, history>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [
         i \in {} |-> [
            type   |-> Change,
            index  |-> 0,
            values |-> [p \in {} |-> Nil],
            commit |-> Pending,
            apply  |-> Pending]]
   /\ proposal = [
         i \in {} |-> [
            change |-> [
               phase  |-> Nil,
               state  |-> Nil,
               values |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]],
            rollback |-> [
               phase  |-> Nil,
               state  |-> Nil,
               values |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]]]]
   /\ configuration = [
         state  |-> InProgress,
         term   |-> 0,
         committed |-> [
            index    |-> 0,
            revision |-> 0,
            values   |-> [
               p \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]],
         applied |-> [
            index    |-> 0,
            revision |-> 0,
            values   |-> [
               p \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]]]
   /\ target = [
         values |-> [
            p \in {} |-> [
               index |-> 0, 
               value |-> Nil]]]
   /\ mastership = [
         master |-> Nil, 
         term   |-> 0]
   /\ history = <<>>

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
         WF_<<proposal, configuration, mastership, target, history>>(Proposal!ReconcileProposal(n, i))
   /\ \A n \in Node :
         WF_<<configuration, mastership, target>>(Configuration!ReconcileConfiguration(n))

----

LimitTransactions == Len(transaction) <= NumTransactions

----

TypeOK ==
   /\ Transaction!TypeOK
   /\ Proposal!TypeOK
   /\ Configuration!TypeOK
   /\ Mastership!TypeOK

LOCAL IsOrderedChange(p, i) ==
   /\ history[i].type = Change
   /\ history[i].phase = p
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].index >= history[i].index

LOCAL IsOrderedRollback(p, i) ==
   /\ history[i].type = Rollback
   /\ history[i].phase = p
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].index > history[i].index
         /\ ~\E k \in DOMAIN history :
               /\ k > j
               /\ k < i
               /\ history[k].type = Rollback
               /\ history[k].phase = p
               /\ history[k].index = history[j].index

Order ==
   /\ \A i \in DOMAIN history :
      \/ IsOrderedChange(Commit, i)
      \/ IsOrderedChange(Apply, i)
      \/ IsOrderedRollback(Commit, i)
      \/ IsOrderedRollback(Apply, i)
   /\ \A i \in DOMAIN proposal :
         /\ proposal[i].change.phase = Apply
         /\ proposal[i].change.state = Failed
         /\ proposal[i].rollback.phase = Apply => proposal[i].rollback.state # Complete
         => \A j \in DOMAIN proposal : (j > i => 
               (proposal[j].change.phase = Apply => 
                  proposal[j].change.state \in {Nil, Pending, Aborted}))

Consistency ==
   /\ \A i \in DOMAIN proposal :
         \/ configuration.committed.index < i
         \/ configuration.committed.revision < i
         => ~\E p \in DOMAIN configuration.committed.values : 
               configuration.committed.values[p].index = i
   /\ \A i \in DOMAIN proposal :
         \/ configuration.applied.index < i
         \/ configuration.applied.revision < i
         => /\ ~\E p \in DOMAIN configuration.applied.values : 
                  configuration.applied.values[p].index = i
            /\ ~\E p \in DOMAIN target.values :
                  target.values[p].index = i
   /\ configuration.state = Complete => 
         \A i \in DOMAIN proposal :
            /\ configuration.applied.index >= i
            /\ configuration.applied.revision >= i
            => \A p \in DOMAIN proposal[i].change.values :
                  /\ ~\E j \in DOMAIN proposal : 
                        /\ j > i 
                        /\ configuration.applied.index >= j
                        /\ configuration.applied.revision >= j
                  => /\ p \in DOMAIN target.values 
                     /\ target.values[p].value = proposal[i].change.values[p].value
                     /\ target.values[p].index = proposal[i].change.values[p].index

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminates(i) ==
   /\ i \in DOMAIN transaction
   /\ transaction[i].commit \in Done
   /\ transaction[i].apply \in Done

Termination ==
   \A i \in 1..NumTransactions : <>Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
