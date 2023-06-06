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
Complete == "Complete"
Aborted == "Aborted"
Failed == "Failed"

Node == {"node1"}

NumTransactions == 3
NumTerms == 2
NumConns == 2
NumStarts == 2

Path == {"path1"}
Value == {"value1", "value2"}

----

\* A transaction log of changes and rollbacks.
VARIABLE transaction

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

vars == <<transaction, configuration, mastership, conn, target, history>>

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
   /\ UNCHANGED <<transaction, history>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

ReconcileMastership(n) ==
   /\ Mastership!ReconcileMastership(n)
   /\ UNCHANGED <<transaction, configuration, target, history>>
   /\ GenerateTestCases => Mastership!Test!Log([node |-> n])

ConnectNode(n) ==
   /\ Target!Connect(n)
   /\ UNCHANGED <<transaction, configuration, mastership, history>>

DisconnectNode(n) ==
   /\ Target!Disconnect(n)
   /\ UNCHANGED <<transaction, configuration, mastership, history>>

StartTarget ==
   /\ Target!Start
   /\ UNCHANGED <<transaction, configuration, mastership, history>>

StopTarget ==
   /\ Target!Stop
   /\ UNCHANGED <<transaction, configuration, mastership, history>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [
         i \in {} |-> [
            type     |-> Nil,
            index    |-> 0,
            revision |-> 0,
            commit   |-> Nil,
            apply    |-> Nil,
            change   |-> [
               index    |-> 0,
               revision |-> 0,
               values   |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]],
            rollback |-> [
               index    |-> 0,
               revision |-> 0,
               values   |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]]]]
   /\ configuration = [
         state  |-> Pending,
         term   |-> 0,
         committed |-> [
            index    |-> 0,
            revision |-> 0,
            values   |-> [
               p \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]],
         applied |-> [
            target   |-> 0,
            index    |-> 0,
            revision |-> 0,
            values   |-> [
               p \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]]]
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
   \/ \E n \in Node :
         \E i \in DOMAIN transaction :
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
         WF_<<transaction>>(Transaction!RollbackChange(i))
   /\ \A n \in Node :
         WF_vars(\E i \in DOMAIN transaction : Transaction!ReconcileTransaction(n, i))
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

LOCAL IsOrderedChange(p, i) ==
   /\ history[i].type = Change
   /\ history[i].phase = p
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].revision >= history[i].revision

LOCAL IsOrderedRollback(p, i) ==
   /\ history[i].type = Rollback
   /\ history[i].phase = p
   /\ \E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].revision = history[i].revision
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].revision > history[i].revision
         /\ ~\E k \in DOMAIN history :
               /\ k > j
               /\ k < i
               /\ history[k].type = Rollback
               /\ history[k].phase = p
               /\ history[k].revision = history[j].revision

Order ==
   /\ \A i \in DOMAIN history :
      \/ IsOrderedChange(Commit, i)
      \/ IsOrderedChange(Apply, i)
      \/ IsOrderedRollback(Commit, i)
      \/ IsOrderedRollback(Apply, i)
   /\ \A i \in DOMAIN transaction :
         /\ transaction[i].type = Change
         /\ transaction[i].apply = Failed
         /\ ~\E j \in DOMAIN transaction : 
               /\ transaction[j].type = Rollback
               /\ transaction[j].rollback.revision = transaction[i].change.revision
               /\ transaction[j].apply = Complete
         => \A j \in DOMAIN transaction : (j > i =>
               (transaction[j].type = Change => transaction[j].apply # Complete))

Consistency ==
   /\ \A i \in DOMAIN transaction :
         /\ transaction[i].commit = Complete
         /\ ~\E j \in DOMAIN transaction :
               /\ j > i
               /\ transaction[j].commit = Complete
         => \A p \in DOMAIN transaction[i].change.values :
               /\ configuration.committed.values[p] = transaction[i].change.values[p]
   /\ \A i \in DOMAIN transaction :
         /\ transaction[i].apply = Complete
         /\ ~\E j \in DOMAIN transaction :
               /\ j > i
               /\ transaction[j].apply = Complete
         => \A p \in DOMAIN transaction[i].change.values :
               /\ configuration.applied.values[p] = transaction[i].change.values[p]
               /\ /\ target.running
                  /\ configuration.applied.target = target.id
                  /\ configuration.state = Complete
                  => target.values[p] = transaction[i].change.values[p]

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

LOCAL IsChanging(i) ==
   \E j \in DOMAIN transaction : 
      /\ transaction[j].type = Change 
      /\ transaction[j].change.revision = i

LOCAL IsChanged(i) ==
   \E j \in DOMAIN transaction : 
      /\ transaction[j].type = Change 
      /\ transaction[j].change.revision = i
      /\ transaction[j].commit # Pending
      /\ transaction[j].apply # Pending

LOCAL IsRollingBack(i) ==
   \E j \in DOMAIN transaction : 
      /\ transaction[j].type = Rollback 
      /\ transaction[j].rollback.revision = i

LOCAL IsRolledBack(i) ==
   \E j \in DOMAIN transaction : 
      /\ transaction[j].type = Rollback 
      /\ transaction[j].rollback.revision = i
      /\ transaction[j].commit # Pending
      /\ transaction[j].apply # Pending

Terminates(i) ==
   /\ IsChanging(i) ~> IsChanged(i)
   /\ IsRollingBack(i) ~> IsRolledBack(i)

Termination ==
   \A i \in 1..NumTransactions : Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
