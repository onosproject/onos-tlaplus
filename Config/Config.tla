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
Canceled == "Canceled"
Failed == "Failed"

Node == {"node1"}

NumTransactions == 3
NumTerms == 1
NumConns == 1
NumStarts == 1

Path == {"path1"}
Value == {"value1", "value2"}

----

\* A transaction log.
VARIABLE transactions

\* A record of per-target configurations
VARIABLE configuration

\* A record of target masterships
VARIABLE mastership

\* A record of node connections to the target
VARIABLE conn

\* The target state
VARIABLE target

\* A sequence of state changes used for model checking.
VARIABLE history

vars == <<transactions, configuration, mastership, conn, target, history>>

----

LOCAL Transaction == INSTANCE Transaction

LOCAL Configuration == INSTANCE Configuration

LOCAL Mastership == INSTANCE Mastership

LOCAL Target == INSTANCE Target

----

AppendChange(i) ==
   /\ Transaction!AppendChange(i)

RollbackChange(i) ==
   /\ Transaction!RollbackChange(i)

ReconcileTransaction(n, i) ==
   /\ Transaction!ReconcileTransaction(n, i)
   /\ GenerateTestCases => Transaction!Test!Log([node |-> n, index |-> i])

ReconcileConfiguration(n) ==
   /\ Configuration!ReconcileConfiguration(n)
   /\ UNCHANGED <<transactions, history>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

ReconcileMastership(n) ==
   /\ Mastership!ReconcileMastership(n)
   /\ UNCHANGED <<transactions, configuration, target, history>>
   /\ GenerateTestCases => Mastership!Test!Log([node |-> n])

ConnectNode(n) ==
   /\ Target!Connect(n)
   /\ UNCHANGED <<transactions, configuration, mastership, history>>

DisconnectNode(n) ==
   /\ Target!Disconnect(n)
   /\ UNCHANGED <<transactions, configuration, mastership, history>>

StartTarget ==
   /\ Target!Start
   /\ UNCHANGED <<transactions, configuration, mastership, history>>

StopTarget ==
   /\ Target!Stop
   /\ UNCHANGED <<transactions, configuration, mastership, history>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transactions = [
         i \in {} |-> [
            phase    |-> Nil,
            values |-> [
               p \in {} |-> Nil],
            change   |-> [
               commit |-> Nil,
               apply  |-> Nil],
            rollback |-> [
               commit |-> Nil,
               apply  |-> Nil]]]
   /\ configuration = [
         state  |-> Pending,
         term   |-> 0,
         committed |-> [
            index       |-> 0,
            maxIndex    |-> 0,
            target      |-> 0,
            seqnum      |-> 0,
            transaction |-> 0,
            revision    |-> 0,
            values      |-> [
               p \in {} |-> Nil]],
         applied |-> [
            index       |-> 0,
            target      |-> 0,
            seqnum      |-> 0,
            transaction |-> 0,
            revision    |-> 0,
            values      |-> [
               p \in {} |-> Nil]]]
   /\ target = [
         id      |-> 1,
         running |-> TRUE,
         values  |-> [
            p \in {} |-> [
               index |-> 0, 
               value |-> Nil]]]
   /\ mastership = [
         master |-> CHOOSE n \in Node : TRUE, 
         term   |-> 1,
         conn   |-> 1]
   /\ conn = [
         n \in Node |-> [
            id        |-> 1,
            connected |-> TRUE]]
   /\ history = <<>>

Next ==
   \/ \E i \in 1..NumTransactions :
         \/ AppendChange(i)
         \/ RollbackChange(i)
   \/ \E n \in Node, i \in DOMAIN transactions :
         ReconcileTransaction(n, i)
   \/ \E n \in Node :
         ReconcileConfiguration(n)
   \/ \E n \in Node :
         ReconcileMastership(n)
   \/ \E n \in Node :
         \/ ConnectNode(n)
         \/ DisconnectNode(n)
   \/ StartTarget
   \/ StopTarget

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ \A i \in 1..NumTransactions :
         WF_<<transactions>>(Transaction!RollbackChange(i))
   /\ \A n \in Node, i \in 1..NumTransactions :
         WF_<<transactions, configuration, mastership, conn, target, history>>(Transaction!ReconcileTransaction(n, i))
   /\ \A n \in Node :
         WF_<<configuration, mastership, conn, target>>(Configuration!ReconcileConfiguration(n))
   /\ \A n \in Node :
         WF_<<mastership, conn>>(Mastership!ReconcileMastership(n))
   /\ \A n \in Node :
         WF_<<conn, target>>(Target!Connect(n) \/ Target!Disconnect(n))
   /\ WF_<<conn, target>>(Target!Start \/ Target!Stop)

----

LimitTerms == 
   \/ mastership.term < NumTerms
   \/ /\ mastership.term = NumTerms
      /\ mastership.master # Nil

LimitConns ==
   \A n \in DOMAIN conn :
      \/ conn[n].id < NumConns
      \/ /\ conn[n].id = NumConns 
         /\ conn[n].connected

LimitStarts ==
   \/ target.id < 2
   \/ /\ target.id = 2
      /\ target.running

----

TypeOK ==
   /\ Transaction!TypeOK
   /\ Configuration!TypeOK
   /\ Mastership!TypeOK

StatusCommitted(i) ==
   \/ /\ transactions'[i].change.commit \notin {Pending, Canceled}
      /\ transactions[i].change.commit # transactions'[i].change.commit
   \/ /\ transactions'[i].rollback.commit \notin {Pending, Canceled}
      /\ transactions[i].rollback.commit # transactions'[i].rollback.commit

StatusApplied(i) ==
   \/ /\ transactions'[i].change.apply \notin {Pending, Canceled}
      /\ transactions[i].change.apply # transactions'[i].change.apply
   \/ /\ transactions'[i].rollback.apply \notin {Pending, Canceled}
      /\ transactions[i].rollback.apply # transactions'[i].rollback.apply

ValidStatus(t, i, j) ==
   /\ j \in DOMAIN history
   /\ history[j].index = i
   /\ \/ /\ history[j].type = Change
         /\ history[j].phase = Commit
         /\ t[i].change.commit = history[j].status
      \/ /\ history[j].type = Change
         /\ history[j].phase = Apply
         /\ t[i].change.apply = history[j].status
      \/ /\ history[j].type = Rollback
         /\ history[j].phase = Commit
         /\ t[i].rollback.commit = history[j].status
      \/ /\ history[j].type = Rollback
         /\ history[j].phase = Apply
         /\ t[i].rollback.apply = history[j].status

ValidCommit(t, i) ==
   LET j == CHOOSE j \in DOMAIN history :
               /\ history[j].phase = Commit
               /\ ~\E k \in DOMAIN history :
                     /\ history[k].phase = Commit
                     /\ k > j
   IN ValidStatus(t, i, j)

ValidApply(t, i) ==
   LET j == CHOOSE j \in DOMAIN history :
               /\ history[j].phase = Apply
               /\ ~\E k \in DOMAIN history :
                     /\ history[k].phase = Apply
                     /\ k > j
   IN ValidStatus(t, i, j)

ConfigurationCommitted ==
   /\ configuration'.committed # configuration.committed
   /\ \E i \in DOMAIN history : history[i].phase = Commit
   => LET i == CHOOSE i \in DOMAIN history : 
                  /\ history[i].phase = Commit 
                  /\ ~\E j \in DOMAIN history : 
                        /\ history[j].phase = Commit
                        /\ j > i 
      IN ValidStatus(transactions, history[i].index, i)

ConfigurationApplied ==
   /\ configuration'.applied # configuration.applied
   /\ \E i \in DOMAIN history : history[i].phase = Apply
   => LET i == CHOOSE i \in DOMAIN history : 
                  /\ history[i].phase = Apply 
                  /\ ~\E j \in DOMAIN history : 
                        /\ history[j].phase = Apply
                        /\ j > i 
      IN ValidStatus(transactions, history[i].index, i)

StatusChanged ==
   \A i \in 1..NumTransactions :
      /\ i \in DOMAIN transactions =>
            /\ StatusCommitted(i) => ValidCommit(transactions', i)
            /\ StatusApplied(i) => ValidApply(transactions', i)

Transition == [][ConfigurationCommitted /\ ConfigurationApplied /\ StatusChanged]_<<transactions, history>>

LOCAL IsOrderedChange(p, i) ==
   /\ history[i].type = Change
   /\ history[i].phase = p
   /\ history[i].status = Complete
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].status = Complete
         /\ history[j].index >= history[i].index

LOCAL IsOrderedRollback(p, i) ==
   /\ history[i].type = Rollback
   /\ history[i].phase = p
   /\ history[i].status = Complete
   /\ \E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].status = Complete
         /\ history[j].index = history[i].index
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].status = Complete
         /\ history[j].index > history[i].index
         /\ ~\E k \in DOMAIN history :
               /\ k > j
               /\ k < i
               /\ history[k].type = Rollback
               /\ history[k].phase = p
               /\ history[j].status = Complete
               /\ history[k].index = history[j].index

Order ==
   /\ \A i \in DOMAIN history :
         history[i].status = Complete => 
            \/ IsOrderedChange(Commit, i)
            \/ IsOrderedChange(Apply, i)
            \/ IsOrderedRollback(Commit, i)
            \/ IsOrderedRollback(Apply, i)
   /\ \A i \in DOMAIN transactions :
         /\ transactions[i].change.apply = Failed
         /\ transactions[i].rollback.apply # Complete
         => ~\E j \in DOMAIN transactions : 
               /\ j > i
               /\ transactions[i].change.apply \in {InProgress, Complete}

LOCAL IsChangeCommitted(i) ==
   /\ configuration.committed.revision = i

LOCAL IsChangeApplied(i) ==
   /\ configuration.applied.revision = i

Consistency ==
   /\ \A i \in DOMAIN transactions :
         /\ IsChangeCommitted(i)
         /\ ~\E j \in DOMAIN transactions :
               /\ j > i
               /\ IsChangeCommitted(j)
         => \A p \in DOMAIN transactions[i].change.values :
               /\ configuration.committed.values[p] = transactions[i].change.values[p]
   /\ \A i \in DOMAIN transactions :
         /\ IsChangeApplied(i)
         /\ ~\E j \in DOMAIN transactions :
               /\ j > i
               /\ IsChangeApplied(j)
         => \A p \in DOMAIN transactions[i].change.values :
               /\ configuration.applied.values[p] = transactions[i].change.values[p]
               /\ /\ target.running
                  /\ configuration.applied.target = target.id
                  /\ configuration.state = Complete
                  => target.values[p] = transactions[i].change.values[p]

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

LOCAL IsChanging(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].phase = Change

LOCAL IsChanged(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].change.commit \in {Complete, Failed}
   /\ transactions[i].change.apply \in {Complete, Aborted, Failed}

LOCAL IsRollingBack(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].phase = Rollback

LOCAL IsRolledBack(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].rollback.commit \in {Complete, Failed}
   /\ transactions[i].rollback.apply \in {Complete, Aborted, Failed}

Terminates(i) ==
   /\ IsChanging(i) ~> IsChanged(i)
   /\ IsRollingBack(i) ~> IsRolledBack(i)

Termination ==
   \A i \in 1..NumTransactions : Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
