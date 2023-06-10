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
   InProgress,
   Complete,
   Aborted,
   Canceled,
   Failed

Status == {Pending, InProgress, Complete, Aborted, Canceled, Failed}

Done == {Complete, Aborted, Canceled, Failed}

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
VARIABLE transactions

\* A history of transaction change/rollback commit/apply events used for model checking.
VARIABLE history

TypeOK == 
   \A i \in DOMAIN transactions :
      /\ transactions[i].index \in Nat
      /\ transactions[i].phase \in {Change, Rollback}
      /\ transactions[i].change.commit \in Status
      /\ transactions[i].change.apply \in Status
      /\ \A p \in DOMAIN transactions[i].change.values :
            transactions[i].change.values[p] # Nil =>
               transactions[i].change.values[p] \in STRING
      /\ transactions[i].rollback.commit # Nil => 
            transactions[i].rollback.commit \in Status
      /\ transactions[i].rollback.apply # Nil => 
            transactions[i].rollback.apply \in Status
      /\ \A p \in DOMAIN transactions[i].rollback.values :
            transactions[i].rollback.values[p] # Nil =>
               transactions[i].rollback.values[p] \in STRING

LOCAL State == [
   transactions  |-> transactions,
   configuration |-> configuration,
   mastership    |-> mastership,
   conn          |-> conn,
   target        |-> target]

LOCAL Transitions ==
   LET
      indexes   == {i \in DOMAIN transactions' : 
                           i \in DOMAIN transactions => transactions'[i] # transactions[i]}
   IN [transactions |-> [i \in indexes |-> transactions'[i]]] @@
         (IF configuration' # configuration THEN [configuration |-> configuration'] ELSE Empty) @@
         (IF target' # target THEN [target |-> target'] ELSE Empty)

Test == INSTANCE Test WITH 
   File <- "Transaction.log"

----

\* Add a change for revision 'i' to the transaction log
AppendChange(i) ==
   /\ Len(transactions) = i-1
   /\ \E p \in Path, v \in Value :
         LET transaction == [
               index    |-> Len(transactions)+1,
               phase    |-> Change,
               change   |-> [
                  index  |-> Len(transactions)+1,
                  seqnum |-> 0,
                  values |-> (p :> v),
                  commit |-> Pending,
                  apply  |-> Pending],
               rollback |-> [
                  index  |-> 0,
                  seqnum |-> 0,
                  values |-> Empty,
                  commit |-> Nil, 
                  apply  |-> Nil]]
         IN /\ transactions' = Append(transactions, transaction)
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

\* Add a rollback of revision 'i' to the transaction log
RollbackChange(i) ==
   /\ i \in DOMAIN transactions
   /\ transactions[i].phase = Change
   /\ transactions[i].change.commit = Complete
   /\ transactions' = [transactions EXCEPT ![i].phase           = Rollback,
                                           ![i].rollback.commit = Pending,
                                           ![i].rollback.apply  = Pending]
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

----

(*
- configuration
   - committed
      - transaction: the index of the last committed transaction
      - seqnum: the sequence number for the last successfully completed transaction
      - target: the current target transaction
      - index: the highest committed index
      - revision: the current committed index

* If target = transaction then the current transaction is being changed
* If target < transaction then the current transaction is being rolled back

*)

CommitChange(n, i) ==
   /\ \/ /\ transactions[i].change.commit = Pending
         /\ configuration.committed.index = i-1
         /\ \/ /\ configuration.committed.target # i
               /\ configuration.committed.transaction \in DOMAIN transactions =>
                     \/ /\ configuration.committed.target = configuration.committed.transaction
                        /\ transactions[configuration.committed.transaction].change.commit \in Done
                     \/ /\ configuration.committed.target < configuration.committed.transaction
                        /\ transactions[configuration.committed.transaction].rollback.commit \in Done
               /\ configuration' = [configuration EXCEPT !.committed.target = i]
               /\ history' = Append(history, [
                                 type   |-> Change, 
                                 phase  |-> Commit, 
                                 index  |-> i,
                                 status |-> InProgress])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.committed.target = i
               /\ transactions' = [transactions EXCEPT ![i].change.commit   = InProgress,
                                                       ![i].rollback.index  = configuration.committed.revision,
                                                       ![i].rollback.values = [
                                                          p \in DOMAIN transactions[i].change.values |-> 
                                                             IF p \in DOMAIN configuration.committed.values THEN
                                                                configuration.committed.values[p]
                                                             ELSE Nil]]
               /\ UNCHANGED <<configuration, history>>
      \/ /\ transactions[i].change.commit = InProgress
         /\ \/ /\ configuration.committed.index # i
               /\ \/ /\ configuration' = [configuration EXCEPT !.committed.transaction = i,
                                                               !.committed.index       = i,
                                                               !.committed.revision    = i,
                                                               !.committed.seqnum      = configuration.committed.seqnum+1,
                                                               !.committed.values      = transactions[i].change.values @@
                                                                                            configuration.committed.values]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Commit, 
                                       index  |-> i,
                                       status |-> Complete])
                  \/ /\ configuration' = [configuration EXCEPT !.committed.transaction = i,
                                                               !.committed.index       = i]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Commit, 
                                       index  |-> i,
                                       status |-> Failed])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.committed.index = i
               /\ \/ /\ configuration.committed.revision = i
                     /\ transactions' = [transactions EXCEPT ![i].change.commit = Complete,
                                                             ![i].change.seqnum = configuration.committed.seqnum]
                  \/ /\ configuration.committed.revision # i
                     /\ transactions' = [transactions EXCEPT ![i].change.commit = Failed,
                                                             ![i].change.apply  = Canceled]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

CommitRollback(n, i) ==
   /\ \/ /\ transactions[i].rollback.commit = Pending
         /\ configuration.committed.revision = i
         /\ \/ /\ configuration.committed.target = i
               /\ \/ /\ configuration.committed.transaction = i
                     /\ transactions[configuration.committed.transaction].change.commit = Complete
                  \/ /\ configuration.committed.transaction > i
                     /\ transactions[configuration.committed.transaction].rollback.commit = Complete
               /\ configuration' = [configuration EXCEPT !.committed.target = transactions[i].rollback.index]
               /\ history' = Append(history, [
                                 type   |-> Rollback, 
                                 phase  |-> Commit, 
                                 index  |-> i,
                                 status |-> InProgress])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.committed.revision = i
               /\ configuration.committed.target = transactions[i].rollback.index
               /\ transactions' = [transactions EXCEPT ![i].rollback.commit = InProgress]
               /\ UNCHANGED <<configuration, history>>
      \/ /\ transactions[i].rollback.commit = InProgress
         /\ \/ /\ configuration.committed.revision = i
               /\ configuration' = [configuration EXCEPT !.committed.transaction = i,
                                                         !.committed.seqnum      = configuration.committed.seqnum+1,
                                                         !.committed.revision    = transactions[i].rollback.index,
                                                         !.committed.values      = transactions[i].rollback.values @@
                                                                                      configuration.committed.values]
               /\ history' = Append(history, [
                                 type   |-> Rollback, 
                                 phase  |-> Commit, 
                                 index  |-> i,
                                 status |-> Complete])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.committed.revision = transactions[i].rollback.index
               /\ transactions' = [transactions EXCEPT ![i].rollback.commit = Complete,
                                                       ![i].rollback.seqnum = configuration.committed.seqnum]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

(*
- configuration
   - applied
      - transaction: the index of the last applied transaction
      - seqnum: the last applied sequence number
      - target: the current target revision (index)
      - revision: the last successfully applied revision

* If target = transaction then the current transaction is being changed
* If target < transaction then the current transaction is being rolled back

*)

ApplyChange(n, i) ==
   /\ transactions[i].change.commit = Complete
   /\ \/ /\ transactions[i].change.apply = Pending
         /\ configuration.applied.seqnum = transactions[i].change.seqnum - 1
         /\ \/ /\ configuration.applied.target # i
               /\ configuration.applied.transaction \in DOMAIN transactions =>
                     \/ /\ configuration.applied.target = configuration.applied.transaction
                        /\ transactions[configuration.applied.transaction].change.apply \in Done
                     \/ /\ configuration.applied.target < configuration.applied.transaction
                        /\ transactions[configuration.applied.transaction].rollback.apply \in Done
               /\ configuration' = [configuration EXCEPT !.applied.target = i]
               /\ history' = Append(history, [
                                 type   |-> Change, 
                                 phase  |-> Apply, 
                                 index  |-> i,
                                 status |-> InProgress])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.applied.target = i
               /\ transactions' = [transactions EXCEPT ![i].change.apply = InProgress]
               /\ UNCHANGED <<configuration, history>>
         /\ UNCHANGED <<target>>
      \/ /\ transactions[i].change.apply = InProgress
            \* If the change has not yet been applied, attempt to apply it.
         /\ \/ /\ configuration.applied.seqnum # transactions[i].change.seqnum
                  \* If the previous transaction was applied successfully, apply the change.
               /\ \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ configuration.state = Complete
                     /\ configuration.term = mastership.term
                     /\ conn[n].id = mastership.conn
                     /\ conn[n].connected
                     /\ target.running
                     /\ \/ /\ target' = [target EXCEPT !.values = transactions[i].change.values @@ target.values]
                           /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                                     !.applied.seqnum      = transactions[i].change.seqnum,
                                                                     !.applied.revision    = i,
                                                                     !.applied.values      = transactions[i].change.values @@
                                                                                                configuration.applied.values]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Complete])
                        \/ /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                                     !.applied.seqnum      = transactions[i].change.seqnum]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Failed])
                           /\ UNCHANGED <<target>>
                  \* If the previous transaction could not be applied, abort the change.
                  \/ /\ configuration.applied.revision < transactions[i].rollback.index
                     /\ configuration' = [configuration EXCEPT !.applied.transaction = i, 
                                                               !.applied.seqnum      = transactions[i].change.seqnum]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Apply, 
                                       index  |-> i,
                                       status |-> Aborted])
                     /\ UNCHANGED <<target>>
               /\ UNCHANGED <<transactions>>
            \* If the change has been applied, update the transaction status.
            \/ /\ configuration.applied.seqnum = transactions[i].change.seqnum
               /\ \/ /\ configuration.applied.revision = i
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Complete]
                  \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Failed]
                  \/ /\ configuration.applied.revision < transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Aborted]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

ApplyRollback(n, i) ==
   /\ transactions[i].rollback.commit = Complete
   /\ \/ /\ transactions[i].rollback.apply = Pending
            \* If the change hasn't yet been applied, abort (Pending) or fail (InProgress) the change.
         /\ \/ /\ configuration.applied.seqnum = transactions[i].change.seqnum - 1
               /\ \/ /\ configuration.applied.target # i
                     /\ configuration.applied.transaction \in DOMAIN transactions =>
                           \/ /\ configuration.applied.target = configuration.applied.transaction
                              /\ transactions[configuration.applied.transaction].change.apply \in Done
                           \/ /\ configuration.applied.target < configuration.applied.transaction
                              /\ transactions[configuration.applied.transaction].rollback.apply \in Done
                     /\ configuration' = [configuration EXCEPT !.applied.target      = i,
                                                               !.applied.transaction = i, 
                                                               !.applied.seqnum      = transactions[i].change.seqnum]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Apply, 
                                       index  |-> i,
                                       status |-> Aborted])
                     /\ UNCHANGED <<transactions>>
                  \/ /\ configuration.applied.target = i
                     /\ \/ /\ transactions[i].change.apply = Pending
                           /\ transactions' = [transactions EXCEPT ![i].change.apply = InProgress]
                           /\ UNCHANGED <<configuration, history>>
                        \/ /\ transactions[i].change.apply = InProgress
                           /\ configuration' = [configuration EXCEPT !.applied.transaction = i, 
                                                                     !.applied.seqnum      = transactions[i].change.seqnum]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Failed])
                           /\ UNCHANGED <<transactions>>
            \* If the change sequence number has been applied but the change status hasn't been
            \* updated, update the change status according to the applied indexes.
            \/ /\ configuration.applied.seqnum = transactions[i].change.seqnum
               /\ transactions[i].change.apply \notin Done
               /\ \/ /\ configuration.applied.revision = i
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Complete]
                  \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Failed]
                  \/ /\ configuration.applied.revision < transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Aborted]
               /\ UNCHANGED <<configuration, history>>
            \/ /\ configuration.applied.seqnum = transactions[i].rollback.seqnum - 1
               /\ \/ /\ configuration.applied.target # transactions[i].rollback.index
                     /\ \/ /\ configuration.applied.transaction = i
                           /\ transactions[configuration.applied.transaction].change.commit = Complete
                        \/ /\ configuration.applied.transaction > i
                           /\ transactions[configuration.applied.transaction].rollback.commit = Complete
                     /\ configuration' = [configuration EXCEPT !.applied.target = transactions[i].rollback.index]
                     /\ history' = Append(history, [
                                       type   |-> Rollback, 
                                       phase  |-> Apply, 
                                       index  |-> i,
                                       status |-> InProgress])
                     /\ UNCHANGED <<transactions>>
                  \/ /\ configuration.applied.target = transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].rollback.apply = InProgress]
                     /\ UNCHANGED <<configuration, history>>
         /\ UNCHANGED <<target>>
      \/ /\ transactions[i].rollback.apply = InProgress
            \* If this transaction has not yet been applied, attempt to apply it.
         /\ \/ /\ configuration.applied.seqnum # transactions[i].rollback.seqnum
                  \* If the previous transaction was applied successfully, apply the rollback.
               /\ \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ configuration.state = Complete
                     /\ configuration.term = mastership.term
                     /\ conn[n].id = mastership.conn
                     /\ conn[n].connected
                     /\ target.running
                     /\ target' = [target EXCEPT !.values = transactions[i].rollback.values @@ target.values]
                     /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                               !.applied.seqnum      = transactions[i].rollback.seqnum,
                                                               !.applied.revision    = transactions[i].rollback.index,
                                                               !.applied.values      = transactions[i].rollback.values @@
                                                                                          configuration.applied.values]
                     /\ history' = Append(history, [
                                       type   |-> Rollback, 
                                       phase  |-> Apply, 
                                       index  |-> i,
                                       status |-> Complete])
                  \* If the previous transaction could not be applied, abort the rollback.
                  \/ /\ configuration.applied.revision < transactions[i].rollback.index
                     /\ configuration' = [configuration EXCEPT !.applied.transaction = i, 
                                                               !.applied.seqnum      = transactions[i].change.seqnum]
                     /\ UNCHANGED <<target, history>>
               /\ UNCHANGED <<transactions>>
               \* If the change has been applied, update the transaction status.
            \/ /\ configuration.applied.seqnum = transactions[i].rollback.seqnum
               /\ \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Complete]
                  \/ /\ configuration.applied.revision # transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Aborted]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

ReconcileChange(n, i) ==
   /\ transactions[i].phase = Change
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)

ReconcileRollback(n, i) ==
   /\ transactions[i].phase = Rollback
   /\ \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transactions
   /\ mastership.master = n
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)

----

(*

CommitChange(n, i) ==
   /\ \/ /\ transactions[i].change.commit = Pending
         /\ \A j \in DOMAIN transactions : j < i => 
               /\ transactions[j].change.commit \in Done
               /\ transactions[j].rollback.commit # InProgress
         /\ transactions' = [transactions EXCEPT ![i].change.commit   = InProgress,
                                                 ![i].rollback.values = [
                                                    p \in DOMAIN transactions[i].change.values |-> 
                                                       IF p \in DOMAIN configuration.committed.values THEN
                                                          configuration.committed.value[p]
                                                       ELSE Nil]]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ transactions[i].change.commit = InProgress
         \* Changes are validated during the commit phase. If a change fails validation,
         \* it will be marked failed before being applied to the configuration.
         \* If all the change values are valid, record the changes required to roll
         \* back the transactions and the index to which the rollback changes
         \* will roll back the configuration.
         /\ \/ /\ configuration' = [configuration EXCEPT !.committed.values = transactions[i].change.values @@ 
                                                                                 configuration.committed.values]
               /\ transactions' = [transactions EXCEPT ![i].change.commit = Complete]
               /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
            \/ /\ transactions' = [transactions EXCEPT ![i].change.commit = Failed]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

CommitRollback(n, i) ==
   /\ \/ /\ transactions[i].rollback.commit = Pending
         /\ \A j \in DOMAIN transactions : 
               /\ j > i 
               /\ transactions[j].phase # Nil
               /\ transactions[j].change.commit # Pending 
               => transactions[j].rollback.commit = Complete
         /\ transactions' = [transactions EXCEPT ![i].rollback.commit = InProgress]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ transactions[i].rollback.commit = InProgress
         /\ configuration' = [configuration EXCEPT !.committed.values = transactions[i].rollback.values @@ 
                                                                           configuration.committed.values]
         /\ transactions' = [transactions EXCEPT ![i].rollback.commit = Complete]
         /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
   /\ UNCHANGED <<mastership, conn, target>>

ApplyChange(n, i) ==
   /\ \/ /\ transactions[i].change.apply = Pending
         /\ \/ /\ transactions[i].change.commit = Complete
               /\ \A j \in DOMAIN transactions : j < i =>
                     \/ /\ transactions[j].change.apply = Complete
                        /\ transactions[j].rollback.apply # InProgress
                     \/ /\ transactions[j].change.apply = Failed
                        /\ transactions[j].rollback.apply = Complete
               /\ i-1 \in DOMAIN transactions /\ transactions[i-1].change.apply = Failed =>
                     transactions[i-1].rollback.apply = Complete
               /\ transactions' = [transactions EXCEPT ![i].change.apply = InProgress]
            \/ /\ transactions[i].change.commit = Failed
               /\ transactions' = [transactions EXCEPT ![i].change.apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ transactions[i].change.apply = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ mastership.conn = conn[n].id
         /\ target.running
         \* Model successful and failed target update requests.
         /\ \/ /\ target' = [target EXCEPT !.values = transactions[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.values = transactions[i].change.values @@ 
                                                                               configuration.applied.values]
               /\ transactions' = [transactions EXCEPT ![i].change.apply = Complete]
               /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
            \/ /\ transactions' = [transactions EXCEPT ![i].change.apply = Failed]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

ApplyRollback(n, i) ==
   /\ \/ /\ transactions[i].rollback.apply = Pending
         /\ transactions[i].rollback.commit = Complete
         /\ \A j \in DOMAIN transactions : 
               /\ j > i 
               /\ transactions[j].phase # Nil 
               /\ transactions[j].change.apply # Pending 
               => transactions[j].rollback.apply \in Done
         /\ \/ /\ transactions[i].change.apply = Pending
               /\ transactions' = [transactions EXCEPT ![i].change.apply   = Aborted,
                                                       ![i].rollback.apply = Complete]
            \/ /\ transactions[i].change.apply \in Done
               /\ transactions' = [transactions EXCEPT ![i].rollback.apply = InProgress]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ transactions[i].rollback.apply = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = transactions[i].rollback.values @@ target.values]
         /\ configuration' = [configuration EXCEPT !.applied.values = transactions[i].rollback.values @@
                                                                         configuration.applied.values]
         /\ transactions' = [transactions EXCEPT ![i].rollback.apply = Complete]
         /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
   /\ UNCHANGED <<mastership, conn>>

ReconcileChange(n, i) ==
   /\ transactions[i].phase = Change
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)

ReconcileRollback(n, i) ==
   /\ transactions[i].phase = Rollback
   /\ \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transactions
   /\ mastership.master = n
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)

*)

----

(*
TODO: 
   
   Change:
   - if configuration.committed.index = i-1 and associated transaction change commit is done
   - increment configuration.committed.index
   - change transaction commit status to InProgress and store rollback revision and values
   - if configuration.committed.index = i then validate and commit change
   - increment configuration.committed.revision to i if valid

   Rollback:
   - if configuration.committed.revision = i
   - set configuration.committed.index to i and change rollback commit status to InProgress
   - change configuration.committed.values to rollback values and revision to rollback revision

   - if configuration.committed.index = i+1 and associated transaction change commit failed or rollback is committed
   - or if configuration.committed.index = i and transaction change is committed
   - if transactions[configuration.committed.index].commit i
   - decrement configuration.committed.index

TRANSACTION 1 [index=1, phase=Change, change=(commit=Pending, apply=Pending), rollback=(commit=Pending, apply=Pending)]

CHANGE

commit=Pending
   \/ /\ transactions[configuration.committed.index].phase = Change
      /\ transactions[configuration.committed.index].change.commit \in Done
   \/ /\ transactions[configuration.committed.index].phase = Rollback
      /\ transactions[configuration.committed.index].rollback.commit \in Done
      
   else if transactions[configuration.committed.index].phase = Rollback

apply=Pending

ROLLBACK
*)

(*
configuration == [
   index     |-> 0,
   version   |-> 0, \* transaction version number
   committed |-> [
      index    |-> 0, \* committed transaction number
      version  |-> 0, \* committed serial number
      revision |-> 0, \* committed revision number
      values   |-> [...]],
   applied   |-> [
      index    |-> 0, \* applied transaction number
      version  |-> 0, \* applied serial number
      revision |-> 0, \* applied revision number
      values   |-> [...]]]
*)

\* TODO: Serialize transactions by managing the next transaction for changes and the previous transaction for rollbacks
\* When change is committed, set next transaction's change commit to InProgress
\* WHen rollback is committed, set previous transaction's rollback commit to InProgress

(*

  CHANGE [index=1, change=(prev=0), rollback=()]        

      configuration.transaction = 1
      configuration.revision = 1

  CHANGE [index=1, change=(prev=0), rollback=()]
  CHANGE [index=2, change=(prev=1), rollback=()]

      configuration.transaction = 2
      configuration.revision = 2

  CHANGE [index=1, change=(prev=0), rollback=()]
  CHANGE [index=2, change=(prev=1), rollback=()]
  CHANGE [index=3, change=(prev=2), rollback=()]

      configuration.transaction = 3
      configuration.revision = 3

  CHANGE [index=1, change=(prev=0), rollback=()]
  CHANGE [index=2, change=(prev=1), rollback=()]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]

      configuration.transaction = 3
      configuration.revision = 2

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]

      configuration.transaction = 2
      configuration.revision = 1

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
  CHANGE [index=4, change=(prev=2), rollback=()]

      configuration.transaction = 4
      configuration.revision = 4

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
  CHANGE [index=4, change=(prev=2), rollback=()]
  CHANGE [index=5, change=(prev=4), rollback=()]

      configuration.transaction = 5
      configuration.revision = 5

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=()]
  CHANGE [index=5, change=(prev=4), rollback=()]

      configuration.transaction = 5
      configuration.revision = 5

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=(prev=5)]
ROLLBACK [index=5, change=(prev=4), rollback=(prev=5)]

      configuration.transaction = 5
      configuration.revision = 4

      configuration.transaction = 4
      configuration.revision = 1

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=(prev=5)]
ROLLBACK [index=5, change=(prev=4), rollback=(prev=5)]
  CHANGE [index=6, change=(prev=2, commit=Complete, apply=Failed), rollback=()]
  CHANGE [index=7, change=(prev=6, commit=Complete, apply=Aborted), rollback=()]
  CHANGE [index=8, change=(prev=7, commit=Complete, apply=Aborted), rollback=()]

      configuration.transaction = 6
      configuration.revision = 6

      configuration.transaction = 7
      configuration.revision = 7

      configuration.transaction = 8
      configuration.revision = 8

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=(prev=5)]
ROLLBACK [index=5, change=(prev=4), rollback=(prev=5)]
  CHANGE [index=6, change=(prev=2, commit=Complete, apply=Failed), rollback=()]
  CHANGE [index=7, change=(prev=6, commit=Complete, apply=Aborted), rollback=()]
ROLLBACK [index=8, change=(prev=7, commit=Complete, apply=Aborted), rollback=(prev=8)]

      configuration.transaction = 8
      configuration.revision = 7

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=(prev=5)]
ROLLBACK [index=5, change=(prev=4), rollback=(prev=5)]
  CHANGE [index=6, change=(prev=2, commit=Complete, apply=Failed), rollback=()]
ROLLBACK [index=7, change=(prev=6, commit=Complete, apply=Aborted), rollback=(prev=8)]
ROLLBACK [index=8, change=(prev=7, commit=Complete, apply=Aborted), rollback=(prev=8)]

      configuration.transaction = 7
      configuration.revision = 6

  CHANGE [index=1, change=(prev=0), rollback=()]
ROLLBACK [index=2, change=(prev=1), rollback=(prev=3)]
ROLLBACK [index=3, change=(prev=2), rollback=(prev=3)]
ROLLBACK [index=4, change=(prev=2), rollback=(prev=5)]
ROLLBACK [index=5, change=(prev=4), rollback=(prev=5)]
ROLLBACK [index=6, change=(prev=2, commit=Complete, apply=Failed), rollback=(prev=7)]
ROLLBACK [index=7, change=(prev=6, commit=Complete, apply=Aborted), rollback=(prev=8)]
ROLLBACK [index=8, change=(prev=7, commit=Complete, apply=Aborted), rollback=(prev=8)]
  CHANGE [index=9, change=(prev=6), rollback=()]

      configuration.transaction = 6
      configuration.revision = 1

*)

=============================================================================
