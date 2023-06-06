------------------------------- MODULE Transaction -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Transaction phase constants
CONSTANTS
   Change,
   Rollback

\* Proposal phase constants
CONSTANTS 
   Commit,
   Apply

\* Status constants
CONSTANTS
   Pending,
   Complete,
   Aborted,
   Failed

Status == {Pending, Complete, Aborted, Failed}

\* The set of all nodes
CONSTANT Node

\* The set of possible paths and values
CONSTANT Path, Value

Empty == [p \in {} |-> Nil]

----

\* Variables defined by other modules.
VARIABLES 
   configuration,
   mastership,
   conn,
   target

\* A transaction log. Transactions may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE transaction

\* A sequence of configuration changes used for model checking.
VARIABLE history

TypeOK == 
   \A i \in DOMAIN transaction :
      /\ transaction[i].type \in {Change, Rollback}
      /\ transaction[i].index \in Nat
      /\ transaction[i].revision \in Nat
      /\ transaction[i].change.index \in Nat
      /\ transaction[i].change.revision \in Nat
      /\ \A p \in DOMAIN transaction[i].change.values :
            transaction[i].change.values[p] # Nil => 
               transaction[i].change.values[p] \in STRING
      /\ transaction[i].rollback.index \in Nat
      /\ transaction[i].rollback.revision \in Nat
      /\ \A p \in DOMAIN transaction[i].rollback.values :
            transaction[i].rollback.values[p] # Nil => 
               transaction[i].rollback.values[p] \in STRING
      /\ transaction[i].commit \in Status
      /\ transaction[i].apply \in Status

LOCAL State == [
   transactions  |-> [i \in DOMAIN transaction |-> transaction[i] @@ [index |-> i]],
   configuration |-> configuration]

LOCAL Transitions ==
   LET
      transactions == {i \in DOMAIN transaction' : 
                           i \in DOMAIN transaction => transaction'[i] # transaction[i]}
   IN 
     [transactions |-> [i \in transactions |-> transaction'[i] @@ [index |-> i]]]

Test == INSTANCE Test WITH 
   File <- "Transaction.log"

----

(*
This section models configuration changes and rollbacks. Changes
are appended to the transaction log and processed asynchronously.
*)

LOCAL Transaction(i) ==
   IF i \in DOMAIN transaction THEN
      transaction[i]
   ELSE [
      index    |-> i, 
      revision |-> 0,
      change   |-> [
         index    |-> 0,
         revision |-> 0],
      rollback |-> [
         index    |-> 0,
         revision |-> 0],
      commit   |-> Nil,
      apply    |-> Nil]

LOCAL LastTransaction == Transaction(Len(transaction))

(*

  CHANGE [index=1, revision=1,  change=(index=1, revision=1), rollback=(index=0, revision=0)] <-- Change revision 1
  CHANGE [index=2, revision=2,  change=(index=2, revision=2), rollback=(index=1, revision=1)]
  CHANGE [index=3, revision=3,  change=(index=3, revision=3), rollback=(index=2, revision=2)]
ROLLBACK [index=4, revision=3,  change=(index=2, revision=2), rollback=(index=3, revision=3)] <-- Roll back revision 3 at index 3, leading to revision 2
ROLLBACK [index=5, revision=3,  change=(index=1, revision=1), rollback=(index=2, revision=2)]
  CHANGE [index=6, revision=4,  change=(index=6, revision=4), rollback=(index=1, revision=1)]
  CHANGE [index=7, revision=5,  change=(index=7, revision=5), rollback=(index=6, revision=4)]
ROLLBACK [index=8, revision=5,  change=(index=6, revision=4), rollback=(index=7, revision=5)] <-- Roll back revision 5 at index 7, leading to revision 4
ROLLBACK [index=9, revision=5,  change=(index=1, revision=1), rollback=(index=6, revision=4)] <-- Roll back revision 4 at index 6, leading to revision 1
  CHANGE [index=10, revision=6, change=(index=10, revision=6), rollback=(index=1, revision=1)]

*)

\* Add a change for revision 'i' to the transaction log
AppendChange(i) ==
   /\ LastTransaction.revision = i-1
   /\ Len(transaction) > 0 => transaction[Len(transaction)].commit = Complete
   /\ \E p \in Path, v \in Value :
         /\ transaction' = Append(transaction, [
                              type |-> Change,
                              index |-> Len(transaction)+1,
                              revision |-> i,
                              change   |-> [
                                 index    |-> Len(transaction)+1,
                                 revision |-> i,
                                 values   |-> (p :> v)],
                              rollback |-> [
                                 index    |-> LastTransaction.change.index,
                                 revision |-> LastTransaction.change.revision,
                                 values   |-> IF p \in DOMAIN configuration.committed.values THEN 
                                                 (p :> configuration.committed.values[p])
                                              ELSE 
                                                 (p :> Nil)],
                                 commit   |-> Pending,
                                 apply    |-> Pending])
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

\* Add a rollback of revision 'i' to the transaction log
RollbackChange(i) ==
   /\ LastTransaction.change.revision = i
   /\ Len(transaction) > 0 => transaction[Len(transaction)].commit = Complete
   /\ transaction' = Append(transaction, [
                        type     |-> Rollback,
                        index    |-> Len(transaction)+1,
                        revision |-> LastTransaction.revision,
                        change   |-> [
                           index    |-> transaction[LastTransaction.change.index].rollback.index,
                           revision |-> transaction[LastTransaction.change.index].rollback.revision,
                           values   |-> transaction[LastTransaction.change.index].rollback.values],
                        rollback |-> [
                           index    |-> LastTransaction.change.index,
                           revision |-> i,
                           values   |-> Empty],
                        commit   |-> Pending,
                        apply    |-> Pending])
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

----

CommitChange(n, i) ==
   /\ transaction[i].commit = Pending
   /\ i-1 \in DOMAIN transaction =>
         transaction[i-1].commit # Pending
   /\ configuration' = [configuration EXCEPT !.committed.index    = transaction[i].change.index,
                                             !.committed.revision = transaction[i].change.revision,
                                             !.committed.values   = transaction[i].change.values @@ 
                                                                        configuration.committed.values]
   /\ transaction' = [transaction EXCEPT ![i].commit = Complete]
   /\ history' = Append(history, [
                     type     |-> Change, 
                     phase    |-> Commit, 
                     revision |-> transaction[i].change.revision])
   /\ UNCHANGED <<target>>

ApplyChange(n, i) ==
   /\ transaction[i].apply = Pending
   /\ transaction[i].commit = Complete
   /\ i-1 \in DOMAIN transaction =>
         transaction[i-1].apply # Pending
   /\ \/ /\ i-1 \in DOMAIN transaction =>
               transaction[i-1].apply = Complete
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
            \* Apply to the target successfully.
         /\ \/ /\ target' = [target EXCEPT !.values = transaction[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index    = transaction[i].change.index,
                                                         !.applied.revision = transaction[i].change.revision,
                                                         !.applied.values   = transaction[i].change.values @@
                                                                                 configuration.applied.values]
               /\ transaction' = [transaction EXCEPT ![i].apply = Complete]
               /\ history' = Append(history, [
                                 type     |-> Change, 
                                 phase    |-> Apply, 
                                 revision |-> transaction[i].change.revision])
            \* Apply to the target failed.
            \/ /\ transaction' = [transaction EXCEPT ![i].apply = Failed]
               /\ UNCHANGED <<configuration, target, history>>
      \/ /\ i-1 \in DOMAIN transaction
         /\ transaction[i-1].apply \in {Aborted, Failed}
         /\ transaction' = [transaction EXCEPT ![i].apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>

ReconcileChange(n, i) ==
   /\ transaction[i].type = Change
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)

CommitRollback(n, i) ==
   /\ transaction[i].commit = Pending
   /\ i-1 \in DOMAIN transaction =>
         transaction[i-1].commit # Pending
   /\ configuration' = [configuration EXCEPT !.committed.index    = transaction[i].change.index,
                                             !.committed.revision = transaction[i].change.revision,
                                             !.committed.values   = transaction[i].change.values @@ 
                                                                        configuration.committed.values]
   /\ transaction' = [transaction EXCEPT ![i].commit = Complete]
   /\ history' = Append(history, [
                     type     |-> Rollback, 
                     phase    |-> Commit, 
                     revision |-> transaction[i].rollback.revision])
   /\ UNCHANGED <<target>>

ApplyRollback(n, i) ==
   /\ transaction[i].apply = Pending
   /\ transaction[i].commit = Complete
   /\ i-1 \in DOMAIN transaction =>
         transaction[i-1].apply # Pending
   /\ \/ /\ transaction[transaction[i].rollback.index].apply \in {Complete, Failed}
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = transaction[i].change.values @@ target.values]
         /\ configuration' = [configuration EXCEPT !.applied.index    = transaction[i].change.index,
                                                   !.applied.revision = transaction[i].change.revision,
                                                   !.applied.values   = transaction[i].change.values @@
                                                                           configuration.applied.values]
         /\ transaction' = [transaction EXCEPT ![i].apply = Complete]
         /\ history' = Append(history, [
                           type     |-> Rollback, 
                           phase    |-> Apply, 
                           revision |-> transaction[i].rollback.revision])
      \/ /\ transaction[transaction[i].rollback.index].apply = Aborted
         /\ transaction' = [transaction EXCEPT ![i].apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>

ReconcileRollback(n, i) ==
   /\ transaction[i].type = Rollback
   /\ \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)
   /\ UNCHANGED <<mastership, conn>>

=============================================================================
