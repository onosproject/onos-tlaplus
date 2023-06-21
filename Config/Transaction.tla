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

\* Transaction phase constants
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
                  index   |-> Len(transactions)+1,
                  ordinal |-> 0,
                  values  |-> (p :> v),
                  commit  |-> Pending,
                  apply   |-> Pending],
               rollback |-> [
                  index   |-> 0,
                  ordinal |-> 0,
                  values  |-> Empty,
                  commit  |-> Nil,
                  apply   |-> Nil]]
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

CommitChange(n, i) ==
   /\ \/ /\ transactions[i].change.commit = Pending
         /\ configuration.committed.change = i-1
         /\ \/ /\ configuration.committed.target # i
               /\ configuration.committed.index = configuration.committed.target
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
                                                               !.committed.change      = i,
                                                               !.committed.revision    = i,
                                                               !.committed.ordinal     = configuration.committed.ordinal+1,
                                                               !.committed.values      = transactions[i].change.values @@
                                                                                            configuration.committed.values]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Commit, 
                                       index  |-> i,
                                       status |-> Complete])
                  \/ /\ configuration' = [configuration EXCEPT !.committed.transaction = i,
                                                               !.committed.index       = i,
                                                               !.committed.change    = i]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Commit, 
                                       index  |-> i,
                                       status |-> Failed])
               /\ UNCHANGED <<transactions>>
            \/ /\ configuration.committed.index = i
               /\ \/ /\ configuration.committed.revision = i
                     /\ transactions' = [transactions EXCEPT ![i].change.commit  = Complete,
                                                             ![i].change.ordinal = configuration.committed.ordinal]
                  \/ /\ configuration.committed.revision # i
                     /\ transactions' = [transactions EXCEPT ![i].change.commit = Failed,
                                                             ![i].change.apply  = Canceled]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

CommitRollback(n, i) ==
   /\ \/ /\ transactions[i].rollback.commit = Pending
         /\ configuration.committed.revision = i
         /\ \/ /\ configuration.committed.target = i
               /\ configuration.committed.index = configuration.committed.target
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
                                                         !.committed.index       = i,
                                                         !.committed.ordinal     = configuration.committed.ordinal+1,
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
               /\ transactions' = [transactions EXCEPT ![i].rollback.commit  = Complete,
                                                       ![i].rollback.ordinal = configuration.committed.ordinal]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

ApplyChange(n, i) ==
   /\ transactions[i].change.commit = Complete
   /\ \/ /\ transactions[i].change.apply = Pending
         /\ \/ /\ configuration.applied.ordinal = transactions[i].change.ordinal - 1
               /\ \/ /\ configuration.applied.target # i
                     /\ configuration.applied.transaction \in DOMAIN transactions =>
                           \/ /\ configuration.applied.target = configuration.applied.transaction
                              /\ transactions[configuration.applied.transaction].change.apply \in Done
                           \/ /\ configuration.applied.target < configuration.applied.transaction
                              /\ transactions[configuration.applied.transaction].rollback.apply \in Done
                     /\ \/ /\ configuration.applied.revision = transactions[i].rollback.index
                           /\ configuration' = [configuration EXCEPT !.applied.target = i,
                                                                     !.applied.index  = i]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> InProgress])
                        \/ /\ \/ transactions[i].phase = Rollback
                              \/ configuration.applied.revision < transactions[i].rollback.index
                           /\ configuration' = [configuration EXCEPT !.applied.target      = i,
                                                                     !.applied.transaction = i,
                                                                     !.applied.ordinal     = transactions[i].change.ordinal]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Aborted])
                     /\ UNCHANGED <<transactions>>
                  \/ /\ configuration.applied.target = i
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = InProgress]
                     /\ UNCHANGED <<configuration, history>>
            \/ /\ configuration.applied.ordinal = transactions[i].change.ordinal
               /\ transactions' = [transactions EXCEPT ![i].change.apply = Aborted]
               /\ UNCHANGED <<configuration, history>>
         /\ UNCHANGED <<target>>
      \/ /\ transactions[i].change.apply = InProgress
            \* If the change has not yet been applied, attempt to apply it.
         /\ \/ /\ configuration.applied.ordinal # transactions[i].change.ordinal
               /\ \/ /\ transactions[i].phase = Change
                     /\ configuration.state = Complete
                     /\ configuration.term = mastership.term
                     /\ conn[n].id = mastership.conn
                     /\ conn[n].connected
                     /\ target.running
                     /\ \/ /\ target' = [target EXCEPT !.values = transactions[i].change.values @@ target.values]
                           /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                                     !.applied.ordinal     = transactions[i].change.ordinal,
                                                                     !.applied.revision    = i,
                                                                     !.applied.values      = transactions[i].change.values @@
                                                                                                configuration.applied.values]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Complete])
                        \/ /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                                     !.applied.ordinal     = transactions[i].change.ordinal]
                           /\ history' = Append(history, [
                                             type   |-> Change, 
                                             phase  |-> Apply, 
                                             index  |-> i,
                                             status |-> Failed])
                           /\ UNCHANGED <<target>>
                  \/ /\ transactions[i].phase = Rollback
                     /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                               !.applied.ordinal     = transactions[i].change.ordinal]
                     /\ history' = Append(history, [
                                       type   |-> Change, 
                                       phase  |-> Apply, 
                                       index  |-> i,
                                       status |-> Failed])
                     /\ UNCHANGED <<target>>
               /\ UNCHANGED <<transactions>>
            \* If the change has been applied, update the transaction status.
            \/ /\ configuration.applied.ordinal = transactions[i].change.ordinal
               /\ \/ /\ configuration.applied.revision = i
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Complete]
                  \/ /\ configuration.applied.revision = transactions[i].rollback.index
                     /\ transactions' = [transactions EXCEPT ![i].change.apply = Failed]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

ApplyRollback(n, i) ==
   /\ transactions[i].rollback.commit = Complete
   /\ \/ /\ transactions[i].rollback.apply = Pending
         /\ \/ /\ configuration.applied.ordinal = transactions[i].rollback.ordinal - 1
               /\ \/ /\ configuration.applied.target # transactions[i].rollback.index
                     /\ \/ /\ configuration.applied.transaction = i
                           /\ transactions[configuration.applied.transaction].change.apply \in Done
                        \/ /\ configuration.applied.transaction > i
                           /\ transactions[configuration.applied.transaction].rollback.apply \in Done
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
         /\ \/ /\ configuration.applied.ordinal # transactions[i].rollback.ordinal
               /\ configuration.state = Complete
               /\ configuration.term = mastership.term
               /\ conn[n].id = mastership.conn
               /\ conn[n].connected
               /\ target.running
               /\ target' = [target EXCEPT !.values = transactions[i].rollback.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.transaction = i,
                                                         !.applied.ordinal     = transactions[i].rollback.ordinal,
                                                         !.applied.revision    = transactions[i].rollback.index,
                                                         !.applied.values      = transactions[i].rollback.values @@
                                                                                    configuration.applied.values]
               /\ history' = Append(history, [
                                 type   |-> Rollback, 
                                 phase  |-> Apply, 
                                 index  |-> i,
                                 status |-> Complete])
               /\ UNCHANGED <<transactions>>
               \* If the change has been applied, update the transaction status.
            \/ /\ configuration.applied.ordinal = transactions[i].rollback.ordinal
               /\ configuration.applied.revision = transactions[i].rollback.index
               /\ transactions' = [transactions EXCEPT ![i].rollback.apply = Complete]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transactions
   /\ mastership.master = n
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)

=============================================================================
