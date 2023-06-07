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
NumTerms == 1
NumConns == 1
NumStarts == 1

Path == {"path1"}
Value == {"value1", "value2"}

----

\* A transaction log.
VARIABLE transactions

\* A proposal log of changes and rollbacks.
VARIABLE proposals

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

vars == <<transactions, proposals, configuration, mastership, conn, target, history>>

----

LOCAL Transaction == INSTANCE Transaction

LOCAL Proposal == INSTANCE Proposal

LOCAL Configuration == INSTANCE Configuration

LOCAL Mastership == INSTANCE Mastership

LOCAL Target == INSTANCE Target

----

AppendChange(i) ==
   /\ Transaction!AppendChange(i)
   /\ UNCHANGED <<mastership, conn, target, history>>

RollbackChange(i) ==
   /\ Transaction!RollbackChange(i)
   /\ UNCHANGED <<mastership, conn, target, history>>

ReconcileTransaction(n, i) ==
   /\ Transaction!ReconcileTransaction(n, i)
   /\ GenerateTestCases => Transaction!Test!Log([node |-> n, index |-> i])
   /\ UNCHANGED <<mastership, conn, target, history>>

ReconcileProposal(n, i) ==
   /\ Proposal!ReconcileProposal(n, i)
   /\ GenerateTestCases => Proposal!Test!Log([node |-> n, index |-> i])
   /\ UNCHANGED <<transactions>>

ReconcileConfiguration(n) ==
   /\ Configuration!ReconcileConfiguration(n)
   /\ UNCHANGED <<transactions, proposals, history>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

ReconcileMastership(n) ==
   /\ Mastership!ReconcileMastership(n)
   /\ UNCHANGED <<transactions, proposals, configuration, target, history>>
   /\ GenerateTestCases => Mastership!Test!Log([node |-> n])

ConnectNode(n) ==
   /\ Target!Connect(n)
   /\ UNCHANGED <<transactions, proposals, configuration, mastership, history>>

DisconnectNode(n) ==
   /\ Target!Disconnect(n)
   /\ UNCHANGED <<transactions, proposals, configuration, mastership, history>>

StartTarget ==
   /\ Target!Start
   /\ UNCHANGED <<transactions, proposals, configuration, mastership, history>>

StopTarget ==
   /\ Target!Stop
   /\ UNCHANGED <<transactions, proposals, configuration, mastership, history>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transactions = [
         i \in {} |-> [
            phase    |-> Nil,
            change   |-> 0,
            rollback |-> 0]]
   /\ proposals = [
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
   \/ \E n \in Node, i \in DOMAIN transactions :
         ReconcileTransaction(n, i)
   \/ \E n \in Node, i \in DOMAIN proposals :
         ReconcileProposal(n, i)
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
         WF_<<transactions, proposals, configuration>>(Transaction!ReconcileTransaction(n, i))
   /\ \A n \in Node :
         WF_<<proposals, configuration, mastership, conn, target, history>>(
            \E i \in DOMAIN proposals : Proposal!ReconcileProposal(n, i))
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
   /\ \A i \in DOMAIN transactions :
         /\ transactions[i].change # 0
         /\ proposals[transactions[i].change].apply = Failed
         /\ transactions[i].rollback # 0 => 
               proposals[transactions[i].rollback].apply # Complete
         => \A j \in DOMAIN transactions : (j > i => 
               (transactions[j].change # 0 => 
                  proposals[transactions[j].change].apply # Complete))

LOCAL IsChangeCommitted(i) ==
   /\ transactions[i].change # 0
   /\ proposals[transactions[i].change].commit = Complete
   /\ transactions[i].rollback # 0 =>
         proposals[transactions[i].rollback].commit # Complete

LOCAL IsChangeApplied(i) ==
   /\ transactions[i].change # 0
   /\ proposals[transactions[i].change].apply = Complete
   /\ transactions[i].rollback # 0 =>
         proposals[transactions[i].rollback].apply # Complete

Consistency ==
   /\ \A i \in DOMAIN transactions :
         /\ IsChangeCommitted(i)
         /\ ~\E j \in DOMAIN transactions :
               /\ j > i
               /\ IsChangeCommitted(j)
         => \A p \in DOMAIN transactions[i].values :
               /\ configuration.committed.values[p] = transactions[i].values[p]
   /\ \A i \in DOMAIN transactions :
         /\ IsChangeApplied(i)
         /\ ~\E j \in DOMAIN transactions :
               /\ j > i
               /\ IsChangeApplied(j)
         => \A p \in DOMAIN transactions[i].values :
               /\ configuration.applied.values[p] = transactions[i].values[p]
               /\ /\ target.running
                  /\ configuration.applied.target = target.id
                  /\ configuration.state = Complete
                  => target.values[p] = transactions[i].values[p]

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

LOCAL IsChanging(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].phase = Change

LOCAL IsChanged(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].change \in DOMAIN proposals
   /\ proposals[transactions[i].change].commit # Pending
   /\ proposals[transactions[i].change].apply # Pending

LOCAL IsRollingBack(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].phase = Rollback

LOCAL IsRolledBack(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].rollback \in DOMAIN proposals
   /\ proposals[transactions[i].rollback].commit # Pending
   /\ proposals[transactions[i].rollback].apply # Pending

Terminates(i) ==
   /\ IsChanging(i) ~> IsChanged(i)
   /\ IsRollingBack(i) ~> IsRolledBack(i)

Termination ==
   \A i \in 1..NumTransactions : Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
