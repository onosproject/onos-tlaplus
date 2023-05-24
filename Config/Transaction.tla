------------------------------- MODULE Transaction -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Transaction type constants
CONSTANTS
   Change,
   Rollback

Type == {Change, Rollback}

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
   Failed

Status == {Pending, InProgress, Complete, Aborted, Failed}

Done == {Complete, Aborted, Failed}

\* The set of all nodes
CONSTANT Node

Empty == [p \in {} |-> Nil]

----

\* Variables defined by other modules.
VARIABLES 
   proposal,
   configuration

\* A transaction log. Transactions may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE transaction

TypeOK == 
   \A i \in DOMAIN transaction :
      /\ transaction[i].type \in Type
      /\ transaction[i].proposal \in Nat
      /\ transaction[i].init \in Status
      /\ transaction[i].commit \in Status
      /\ transaction[i].apply \in Status
      /\ \A p \in DOMAIN transaction[i].values :
            transaction[i].values[p] # Nil => transaction[i].values[p] \in STRING

LOCAL State == [
   transactions  |-> [i \in DOMAIN transaction |-> transaction[i] @@ [index |-> i]],
   proposals     |-> [i \in DOMAIN proposal |-> proposal[i] @@ [index |-> i]],
   configuration |-> configuration]

LOCAL Transitions ==
   LET
      transactions == {i \in DOMAIN transaction' : 
                           i \in DOMAIN transaction => transaction'[i] # transaction[i]}
      proposals    == {i \in DOMAIN proposal' : 
                           i \in DOMAIN proposal => proposal'[i] # proposal[i]}
   IN 
     [transactions |-> [i \in transactions |-> transaction'[i] @@ [index |-> i]],
      proposals    |-> [i \in proposals    |-> proposal'[i] @@ [index |-> i]]]

Test == INSTANCE Test WITH 
   File <- "Transaction.log"

----

(*
This section models configuration changes and rollbacks. Changes
are appended to the transaction log and processed asynchronously.
*)

\* Add a set of changes 'c' to the transaction log
RequestChange(p, v) ==
   /\ transaction' = Append(transaction, [
                        type     |-> Change,
                        proposal |-> 0,
                        values   |-> (p :> v),
                        init     |-> InProgress,
                        commit   |-> Pending,
                        apply    |-> Pending])
   /\ UNCHANGED <<proposal, configuration>>

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(i) ==
   /\ transaction' = Append(transaction, [
                        type     |-> Rollback,
                        proposal |-> i,
                        values   |-> Empty,
                        init     |-> InProgress,
                        commit   |-> Pending,
                        apply    |-> Pending])
   /\ UNCHANGED <<proposal, configuration>>

----

(*
This section models the Transaction log reconciler.
*)

LOCAL IsInitialized(i) ==
   i \in DOMAIN transaction => transaction[i].init \in Done


LOCAL IsCommitted(i) ==
   i \in DOMAIN transaction => transaction[i].commit \in Done


LOCAL IsApplied(i) ==
   i \in DOMAIN transaction => transaction[i].apply \in Done


InitChange(n, i) ==
   /\ \/ /\ transaction[i].init = InProgress
         \* If the prior transaction has been initialized, initialize the transaction by
         \* appending the proposal and updating the proposal index.
         /\ IsInitialized(i-1)
         /\ proposal' = Append(proposal, [
                           phase    |-> Change,
                           change   |-> [
                              commit |-> Pending,
                              apply  |-> Pending,
                              values |-> [
                                 p \in DOMAIN transaction[i].values |-> [
                                    index |-> Len(proposal)+1,
                                    value |-> transaction[i].values[p]]]],
                           rollback |-> [
                              commit   |-> Nil,
                              apply    |-> Nil,
                              revision |-> 0, 
                              values   |-> Empty]])
         /\ transaction' = [transaction EXCEPT ![i].proposal = Len(proposal'),
                                               ![i].init     = Complete]


CommitChange(n, i) ==
   /\ \/ /\ transaction[i].commit = Pending
         /\ transaction[i].init = Complete
         \* A transaction cannot be committed until the prior transaction has been committed.
         /\ IsCommitted(i-1)
         /\ transaction' = [transaction EXCEPT ![i].commit = InProgress]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].commit = InProgress
            \* If the change commit is still in the Pending state, set it to InProgress.
         /\ \/ /\ proposal[transaction[i].proposal].change.commit = Pending
               /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].change.commit     = InProgress,
                                               ![transaction[i].proposal].rollback.revision = configuration.committed.revision,
                                               ![transaction[i].proposal].rollback.values   = [
                                                   p \in DOMAIN proposal[transaction[i].proposal].change.values |-> 
                                                      IF p \in DOMAIN configuration.committed.values THEN
                                                         configuration.committed.values[p]
                                                      ELSE
                                                         [index |-> 0, value |-> Nil]]]
               /\ UNCHANGED <<transaction>>
            \* If the change commit is Complete, mark the transaction Complete.
            \/ /\ proposal[transaction[i].proposal].change.commit = Complete
               /\ transaction' = [transaction EXCEPT ![i].commit = Complete]
               /\ UNCHANGED <<proposal>>
            \* If the change commit Failed, mark the transaction Failed.
            \/ /\ proposal[transaction[i].proposal].change.commit = Failed
               /\ transaction' = [transaction EXCEPT ![i].commit = Failed]
               /\ UNCHANGED <<proposal>>


ApplyChange(n, i) ==
   /\ \/ /\ transaction[i].apply = Pending
            \* If the commit phase was completed successfully, start the apply phase.
         /\ \/ /\ transaction[i].commit = Complete
                  \* If the proposal is in the apply phase and the previous transaction has completed
                  \* the apply phase, start applying the change.
               /\ \/ /\ proposal[transaction[i].proposal].change.apply = Pending
                     \* A transaction cannot be applied until the prior transaction has been applied.
                     /\ IsApplied(i-1)
                     \* If the prior change failed being applied, it must be rolled back before
                     \* new changes can be applied.
                     /\ /\ transaction[i].proposal-1 \in DOMAIN proposal
                        /\ proposal[transaction[i].proposal-1].change.apply = Failed
                        => proposal[transaction[i].proposal-1].rollback.apply = Complete
                     /\ transaction' = [transaction EXCEPT ![i].apply = InProgress]
                     /\ UNCHANGED <<proposal>>
            \* If the commit phase was aborted or failed, abort the apply phase once the previous
            \* transaction has completed the apply phase.
            \/ /\ transaction[i].commit \in {Aborted, Failed}
               \* A transaction cannot be applied until the prior transaction has been applied.
               /\ IsApplied(i-1)
               \* If the prior change failed being applied, it must be rolled back before
               \* new changes can be applied.
               /\ /\ transaction[i].proposal-1 \in DOMAIN proposal
                  /\ proposal[transaction[i].proposal-1].change.apply = Failed
                  => proposal[transaction[i].proposal-1].rollback.apply = Complete
               /\ transaction' = [transaction EXCEPT ![i].apply = Aborted]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].apply = InProgress
            \* If the change apply is still in the Pending state, set it to InProgress.
         /\ \/ /\ proposal[transaction[i].proposal].change.apply = Pending
               /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].change.apply = InProgress]
               /\ UNCHANGED <<transaction>>
            \* If the change apply is Complete, mark the transaction Complete.
            \/ /\ proposal[transaction[i].proposal].change.apply = Complete
               /\ transaction' = [transaction EXCEPT ![i].apply = Complete]
               /\ UNCHANGED <<proposal>>
            \* If the change apply Failed, mark the transaction Failed.
            \/ /\ proposal[transaction[i].proposal].change.apply = Failed
               /\ transaction' = [transaction EXCEPT ![i].apply = Failed]
               /\ UNCHANGED <<proposal>>


ReconcileChange(n, i) ==
   /\ transaction[i].type = Change
   /\ \/ InitChange(n, i)
      \/ CommitChange(n, i)
      \/ ApplyChange(n, i)


InitRollback(n, i) ==
   /\ \/ /\ transaction[i].init = InProgress
         \* Rollbacks cannot be initialized until all prior transactions have been initialized.
         /\ IsInitialized(i-1)
            \* Rollback transactions must target valid proposal index.
         /\ \/ /\ transaction[i].proposal \in DOMAIN proposal
                  \* To roll back a transaction, all subsequent transactions must be rolled back first.
                  \* Check whether the following proposal is being rolled back.
               /\ \/ /\ transaction[i].proposal+1 \in DOMAIN proposal =>
                           proposal[transaction[i].proposal+1].phase = Rollback
                     /\ transaction' = [transaction EXCEPT ![i].init = Complete]
                  \* If the subsequent proposal is not being rolled back, fail the rollback transaction.
                  \/ /\ transaction[i].proposal+1 \in DOMAIN proposal
                     /\ proposal[transaction[i].proposal+1].phase = Change
                     /\ transaction' = [transaction EXCEPT ![i].init = Failed]
            \* If the proposal index is not valid, fail the rollback request.
            \/ /\ transaction[i].proposal \notin DOMAIN proposal
               /\ transaction' = [transaction EXCEPT ![i].init = Failed]
   /\ UNCHANGED <<proposal>>


CommitRollback(n, i) ==
   /\ \/ /\ transaction[i].commit = Pending
         \* A transaction cannot be committed until the prior transaction has been committed.
         \* In the case of rollbacks, we serialize all state changes to ensure consistency
         \* when rolling back changes.
         /\ IsCommitted(i-1)
            \* If the transaction was initialized successfully, commit the rollback.
         /\ \/ /\ transaction[i].init = Complete
                  \* If the target proposal is not yet being rolled back, transition the proposal.
               /\ \/ /\ proposal[transaction[i].proposal].phase = Change
                        \* If the target change is still pending, abort the change and rollback.
                     /\ \/ /\ proposal[transaction[i].proposal].change.commit = Pending
                           /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].phase = Rollback,
                                                           ![transaction[i].proposal].change.commit   = Aborted,
                                                           ![transaction[i].proposal].rollback.commit = Aborted]
                           /\ UNCHANGED <<transaction>>
                        \* If the target change is complete, start the rollback commit phase.
                        \/ /\ proposal[transaction[i].proposal].change.commit = Complete
                           /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].phase = Rollback,
                                                           ![transaction[i].proposal].rollback.commit = Pending,
                                                           ![transaction[i].proposal].rollback.apply  = Pending]
                           /\ UNCHANGED <<transaction>>
                        \* If the target change failed commit, complete the rollback commit.
                        \/ /\ proposal[transaction[i].proposal].change.commit \in {Aborted, Failed}
                           /\ transaction' = [transaction EXCEPT ![i].commit = Complete]
                           /\ UNCHANGED <<proposal>>
                  \* If the target proposal is being rolled back, transition the underlying proposal.
                  \/ /\ proposal[transaction[i].proposal].phase = Rollback
                        \* If the target proposal is being rolled back, begin the rollback commit
                        \* once the prior transaction has completed the commit phase.
                     /\ \/ /\ proposal[transaction[i].proposal].rollback.commit = Pending
                           /\ transaction' = [transaction EXCEPT ![i].commit = InProgress]
                           /\ UNCHANGED <<proposal>>
                        \* If the target rollback was aborted, abort the transaction rollback
                        \* once the prior transaction has completed the commit phase.
                        \/ /\ proposal[transaction[i].proposal].rollback.commit = Aborted
                           /\ transaction' = [transaction EXCEPT ![i].commit = Aborted]
                           /\ UNCHANGED <<proposal>>
            \* If the transaction failed initialization, abort the commit phase.
            \/ /\ transaction[i].init \in {Aborted, Failed}
               /\ transaction' = [transaction EXCEPT ![i].commit = Aborted]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].commit = InProgress
            \* If the rollback commit is still in the Pending state, set it to InProgress.
         /\ \/ /\ proposal[transaction[i].proposal].rollback.commit = Pending
               /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].rollback.commit = InProgress]
               /\ UNCHANGED <<transaction>>
            \* If the rollback commit is Complete, mark the transaction Complete.
            \/ /\ proposal[transaction[i].proposal].rollback.commit = Complete
               /\ transaction' = [transaction EXCEPT ![i].commit = Complete]
               /\ UNCHANGED <<proposal>>
            \* If the rollback commit Failed, mark the transaction Failed.
            \/ /\ proposal[transaction[i].proposal].rollback.commit = Failed
               /\ transaction' = [transaction EXCEPT ![i].commit = Failed]
               /\ UNCHANGED <<proposal>>


ApplyRollback(n, i) ==
   /\ \/ /\ transaction[i].apply = Pending
         \* A transaction cannot be applied until the prior transaction has been applied.
         \* In the case of rollbacks, we serialize all state changes to ensure consistency
         \* when rolling back changes.
         /\ IsApplied(i-1)
            \* If the commit phase was completed successfully, start the apply phase.
         /\ \/ /\ transaction[i].commit = Complete
                  \* If the target proposal is being rolled back, begin the rollback apply
                  \* once the prior transaction has completed the apply phase.
               /\ \/ /\ proposal[transaction[i].proposal].rollback.apply = Pending
                        \* If the target change has not yet been applied, abort the change and rollback.
                     /\ \/ /\ \/ proposal[transaction[i].proposal].change.commit \notin Done
                              \/ proposal[transaction[i].proposal].change.apply = Pending
                           /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].change.apply   = Aborted,
                                                           ![transaction[i].proposal].rollback.apply = Aborted]
                           /\ UNCHANGED <<transaction>>
                        \* If the target change has been applied, begin applying the rollback.
                        \/ /\ proposal[transaction[i].proposal].change.apply \in {Complete, Failed}
                           /\ transaction' = [transaction EXCEPT ![i].apply = InProgress]
                           /\ UNCHANGED <<proposal>>
                        \* If the target change was aborted or failed, complete applying the rollback.
                        \/ /\ proposal[transaction[i].proposal].change.apply = Aborted
                           /\ transaction' = [transaction EXCEPT ![i].apply = Complete]
                           /\ UNCHANGED <<proposal>>
                  \* If the target rollback was aborted, abort the transaction rollback
                  \* once the prior transaction has completed the apply phase.
                  \/ /\ proposal[transaction[i].proposal].rollback.apply = Aborted
                     /\ transaction' = [transaction EXCEPT ![i].apply = Aborted]
                     /\ UNCHANGED <<proposal>>
            \* If the transaction failed commit, abort the apply phase.
            \/ /\ transaction[i].commit \in {Aborted, Failed}
               /\ transaction' = [transaction EXCEPT ![i].apply = Aborted]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].apply = InProgress
            \* If the rollback apply is still in the Pending state, set it to InProgress.
         /\ \/ /\ proposal[transaction[i].proposal].rollback.apply = Pending
               /\ proposal' = [proposal EXCEPT ![transaction[i].proposal].rollback.apply = InProgress]
               /\ UNCHANGED <<transaction>>
            \* If the rollback apply is Complete, mark the transaction Complete.
            \/ /\ proposal[transaction[i].proposal].rollback.apply = Complete
               /\ transaction' = [transaction EXCEPT ![i].apply = Complete]
               /\ UNCHANGED <<proposal>>
            \* If the rollback apply Failed, mark the transaction Failed.
            \/ /\ proposal[transaction[i].proposal].rollback.apply = Failed
               /\ transaction' = [transaction EXCEPT ![i].apply = Failed]
               /\ UNCHANGED <<proposal>>


ReconcileRollback(n, i) ==
   /\ transaction[i].type = Rollback
   /\ \/ InitRollback(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)


\* Reconcile a transaction
ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)
   /\ UNCHANGED <<configuration>>

=============================================================================
