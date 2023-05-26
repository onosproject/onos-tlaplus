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
Done == {Complete, Aborted, Failed}

Node == {"node1"}

NumTransactions == 3
NumTerms == 2
NumConns == 2
NumStarts == 2

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

\* A record of target masterships
VARIABLE mastership

\* A record of node connections to the target
VARIABLE conn

\* The target state
VARIABLE target

\* A sequence of state changes used for model checking.
VARIABLE history

vars == <<transaction, proposal, configuration, mastership, conn, target, history>>

----

LOCAL Transaction == INSTANCE Transaction

LOCAL Configuration == INSTANCE Configuration

LOCAL Mastership == INSTANCE Mastership

LOCAL Target == INSTANCE Target

----

AppendChange(p, v) ==
   /\ Transaction!AppendChange(p, v)

RollbackChange(i) ==
   /\ Transaction!RollbackChange(i)

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
   /\ Transaction!ReconcileTransaction(n, i)
   /\ GenerateTestCases => 
         LET context == [node |-> n, index |-> i]
         IN Transaction!Test!Log(context)

ReconcileConfiguration(n) ==
   /\ Configuration!ReconcileConfiguration(n)
   /\ UNCHANGED <<transaction, proposal, history>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n])

ReconcileMastership(n) ==
   /\ Mastership!ReconcileMastership(n)
   /\ UNCHANGED <<transaction, proposal, configuration, target, history>>
   /\ GenerateTestCases => Mastership!Test!Log([node |-> n])

ConnectNode(n) ==
   /\ Target!Connect(n)
   /\ UNCHANGED <<transaction, proposal, configuration, mastership, history>>

DisconnectNode(n) ==
   /\ Target!Disconnect(n)
   /\ UNCHANGED <<transaction, proposal, configuration, mastership, history>>

StartTarget ==
   /\ Target!Start
   /\ UNCHANGED <<transaction, proposal, configuration, mastership, history>>

StopTarget ==
   /\ Target!Stop
   /\ UNCHANGED <<transaction, proposal, configuration, mastership, history>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [
         i \in {} |-> [
            phase  |-> Nil,
            change |-> [
               proposal |-> 0,
               revision |-> 0,
               values   |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]],
            rollback |-> [
               proposal |-> 0,
               revision |-> 0,
               values   |-> [
                  p \in {} |-> [
                     index |-> 0,
                     value |-> Nil]]]]]
   /\ proposal = [
         i \in {} |-> [
            transaction |-> 0,
            commit      |-> Nil,
            apply       |-> Nil]]
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
   \/ \E p \in Path, v \in Value :
         AppendChange(p, v)
   \/ \E i \in DOMAIN transaction :
         RollbackChange(i)
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
   /\ \A p \in Path, v \in Value :
         WF_<<transaction, proposal, configuration, mastership, conn, target, history>>(Transaction!AppendChange(p, v))
   /\ \A i \in 1..NumTransactions :
         WF_<<transaction, proposal, configuration, mastership, conn, target, history>>(Transaction!RollbackChange(i))
   /\ \A n \in Node, i \in 1..NumTransactions :
         WF_<<transaction, proposal, configuration, mastership, conn, target, history>>(Transaction!ReconcileTransaction(n, i))
   /\ \A n \in Node :
         WF_<<configuration, mastership, conn, target>>(Configuration!ReconcileConfiguration(n))
   /\ \A n \in Node :
         WF_<<mastership, conn>>(Mastership!ReconcileMastership(n))
   /\ \A n \in Node :
         WF_<<conn, target>>(Target!Connect(n) \/ Target!Disconnect(n))
   /\ WF_<<conn, target>>(Target!Start \/ Target!Stop)

Alias == [
   log |-> [
      i \in DOMAIN transaction |-> [
         change |-> 
            IF transaction[i].change.proposal # 0 THEN 
               [commit |-> proposal[transaction[i].change.proposal].commit,
                apply  |-> proposal[transaction[i].change.proposal].apply,
                values |-> transaction[i].change.values] 
            ELSE 
               [commit |-> Nil, 
                apply  |-> Nil,
                values |-> transaction[i].change.values],
         rollback |-> 
            IF transaction[i].rollback.proposal # 0 THEN 
               [commit |-> proposal[transaction[i].rollback.proposal].commit,
                apply  |-> proposal[transaction[i].rollback.proposal].apply,
                values |-> transaction[i].rollback.values] 
            ELSE 
               [commit |-> Nil, 
                apply  |-> Nil,
                values |-> transaction[i].rollback.values]] @@ 
         transaction[i]],
   transaction   |-> transaction,
   proposal      |-> proposal,
   configuration |-> configuration,
   mastership    |-> mastership,
   conn          |-> conn,
   target        |-> target,
   history       |-> history]

----

LimitTransactions == Len(transaction) <= NumTransactions

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
         /\ history[j].index >= history[i].index

LOCAL IsOrderedRollback(p, i) ==
   /\ history[i].type = Rollback
   /\ history[i].phase = p
   /\ \E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].index = history[i].index
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
   /\ \A i \in DOMAIN transaction :
         /\ transaction[i].change.proposal # 0
         /\ proposal[transaction[i].change.proposal].apply = Failed
         /\ transaction[i].rollback.proposal # 0 => 
               proposal[transaction[i].rollback.proposal].apply # Complete
         => \A j \in DOMAIN transaction : (j > i => 
               (transaction[j].change.proposal # 0 => 
                  proposal[transaction[j].change.proposal].apply # Complete))

LOCAL IsChangeCommitted(i) ==
   /\ transaction[i].change.proposal # 0
   /\ proposal[transaction[i].change.proposal].commit = Complete
   /\ transaction[i].rollback.proposal # 0 =>
         proposal[transaction[i].rollback.proposal].commit # Complete

LOCAL IsChangeApplied(i) ==
   /\ transaction[i].change.proposal # 0
   /\ proposal[transaction[i].change.proposal].apply = Complete
   /\ transaction[i].rollback.proposal # 0 =>
         proposal[transaction[i].rollback.proposal].apply # Complete

Consistency ==
   /\ \A i \in DOMAIN transaction :
         /\ IsChangeCommitted(i)
         /\ ~\E j \in DOMAIN transaction :
               /\ j > i
               /\ IsChangeCommitted(j)
         => \A p \in DOMAIN transaction[i].change.values :
               /\ configuration.committed.values[p] = transaction[i].change.values[p]
   /\ \A i \in DOMAIN transaction :
         /\ IsChangeApplied(i)
         /\ ~\E j \in DOMAIN transaction :
               /\ j > i
               /\ IsChangeApplied(j)
         => \A p \in DOMAIN transaction[i].change.values :
               /\ configuration.applied.values[p] = transaction[i].change.values[p]
               /\ /\ target.running
                  /\ configuration.applied.target = target.id
                  /\ configuration.state = Complete
                  => target.values[p] = transaction[i].change.values[p]

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminates(i) ==
   /\ i \in DOMAIN transaction /\ transaction[i].phase = Change ~>
         /\ i \in DOMAIN transaction
         /\ transaction[i].change.proposal # 0
         /\ proposal[transaction[i].change.proposal].commit \in Done
         /\ proposal[transaction[i].change.proposal].apply \in Done
   /\ i \in DOMAIN transaction /\ transaction[i].phase = Rollback ~>
         /\ i \in DOMAIN transaction
         /\ transaction[i].rollback.proposal # 0
         /\ proposal[transaction[i].rollback.proposal].commit \in Done
         /\ proposal[transaction[i].rollback.proposal].apply \in Done

Termination ==
   \A i \in 1..NumTransactions : <>Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
