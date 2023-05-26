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

Done == {Complete, Aborted, Failed}

\* The set of all nodes
CONSTANT Node

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

\* A proposal log.
VARIABLE proposal

\* A sequence of configuration changes used for model checking.
VARIABLE history

TransactionOK == 
   \A i \in DOMAIN transaction :
      /\ transaction[i].phase \in {Change, Rollback}
      /\ transaction[i].change.proposal \in Nat
      /\ transaction[i].change.revision \in Nat
      /\ \A p \in DOMAIN transaction[i].change.values :
            transaction[i].change.values[p] # Nil => 
               transaction[i].change.values[p] \in STRING
      /\ transaction[i].rollback.proposal \in Nat
      /\ transaction[i].rollback.revision \in Nat
      /\ \A p \in DOMAIN transaction[i].rollback.values :
            transaction[i].rollback.values[p] # Nil => 
               transaction[i].rollback.values[p] \in STRING

ProposalOK == 
   \A i \in DOMAIN proposal :
      /\ proposal[i].transaction \in Nat
      /\ proposal[i].commit \in Status
      /\ proposal[i].apply \in Status

TypeOK == TransactionOK /\ ProposalOK

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
AppendChange(p, v) ==
   /\ transaction' = Append(transaction, [
                        phase    |-> Change,
                        change   |-> [
                           proposal |-> 0,
                           revision    |-> Len(transaction)+1,
 	                        values   |-> (p :> v)],
                        rollback |-> [
                           proposal |-> 0,
                           revision    |-> 0,
                           values   |-> Empty]])
   /\ UNCHANGED <<proposal, configuration, mastership, conn, target, history>>

\* Add a rollback of transaction 't' to the transaction log
RollbackChange(i) ==
   /\ i \in DOMAIN transaction
   /\ transaction[i].phase = Change
   /\ transaction[i].change.proposal # 0
   /\ proposal[transaction[i].change.proposal].commit # Pending
   /\ transaction' = [transaction EXCEPT ![i].phase = Rollback]
   /\ UNCHANGED <<proposal, configuration, mastership, conn, target, history>>

----

ReconcileChange(n, i) ==
   /\ transaction[i].phase = Change
      \* The change proposal has not yet been created.
   /\ \/ /\ transaction[i].change.proposal = 0
         \* The prior transaction must have created a change proposal.
         /\ i-1 \in DOMAIN transaction => transaction[i-1].change.proposal # 0
         /\ proposal' = Append(proposal, [transaction |-> i, commit |-> Pending, apply |-> Pending])
         /\ transaction' = [transaction EXCEPT ![i].change.proposal = Len(proposal')]
         /\ UNCHANGED <<configuration, target, history>>
      \* The change proposal has been created.
      \/ /\ transaction[i].change.proposal # 0
            \* The change is pending commit. Validate and commit the change once the prior
            \* change has been committed.
         /\ \/ /\ proposal[transaction[i].change.proposal].commit = Pending
               \* The prior proposal has been committed.
               /\ transaction[i].change.proposal-1 \in DOMAIN proposal =>
                     proposal[transaction[i].change.proposal-1].commit \in Done
               \* The prior change has been committed.
               /\ configuration.committed.index = i-1
                  \* Valid change is committed to the configuration.
               /\ \/ /\ transaction' = [transaction EXCEPT ![i].rollback.revision = configuration.committed.revision,
                                                           ![i].rollback.values   = [
                                                               p \in DOMAIN transaction[i].change.values |-> 
                                                                  IF p \in DOMAIN configuration.committed.values THEN
                                                                     configuration.committed.values[p]
                                                                  ELSE
                                                                     Nil]]
                     /\ configuration' = [configuration EXCEPT !.committed.index    = i,
                                                               !.committed.revision = i,
                                                               !.committed.values   = transaction[i].change.values @@ 
                                                                                         configuration.committed.values]
                     /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].commit = Complete]
                     /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
                  \* The change is invalid. Increment the committed index and mark the change Failed.
                  \/ /\ configuration' = [configuration EXCEPT !.committed.index = i]
                     /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].commit = Failed]
                     /\ UNCHANGED <<transaction, history>>
               /\ UNCHANGED <<target>>
            \* The change apply is pending.
            \/ /\ proposal[transaction[i].change.proposal].apply = Pending
               \* The prior proposal has been applied.
               /\ transaction[i].change.proposal-1 \in DOMAIN proposal =>
                     proposal[transaction[i].change.proposal-1].apply \in Done
               \* The prior change has been applied.
               /\ configuration.applied.index = i-1
                  \* If the transaction proposal was committed, attempt to apply the transaction.
               /\ \/ /\ proposal[transaction[i].change.proposal].commit = Complete
                     /\ configuration.state = Complete
                     /\ configuration.term = mastership.term
                     /\ conn[n].id = mastership.conn
                     /\ conn[n].connected
                     /\ target.running
                        \* The change is successfully applied to the target.
                     /\ \/ /\ target' = [target EXCEPT !.values = transaction[i].change.values @@ target.values]
                           /\ configuration' = [configuration EXCEPT !.applied.revision = i,
                                                                     !.applied.values   = transaction[i].change.values @@
                                                                                             configuration.applied.values]
                           /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].apply = Complete]
                           /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
                        \* The change fails being applied to the target.
                        \* The configuration's applied index is not incremented here to block applying
                        \* subsequent changes until the failed change is rolled back.
                        \/ /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].apply = Failed]
                           /\ UNCHANGED <<configuration, target, history>>
                  \* If the transaction proposal failed commit, abort applying the transaction.
                  \/ /\ proposal[transaction[i].change.proposal].commit = Failed
                     /\ configuration' = [configuration EXCEPT !.applied.index = i]
                     /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].apply = Aborted]
                     /\ UNCHANGED <<target, history>>
               /\ UNCHANGED <<transaction>>

ReconcileRollback(n, i) ==
   /\ transaction[i].phase = Rollback
      \* The rollback proposal has not yet been created.
   /\ \/ /\ transaction[i].rollback.proposal = 0
         \* The subsequent transaction must have created a rollback proposal.
         /\ i+1 \in DOMAIN transaction => transaction[i+1].rollback.proposal # 0
         /\ proposal' = Append(proposal, [transaction |-> i, commit |-> Pending, apply |-> Pending])
         /\ transaction' = [transaction EXCEPT ![i].rollback.proposal = Len(proposal')]
         /\ UNCHANGED <<configuration, target, history>>
      \* The rollback proposal has been created.
      \/ /\ transaction[i].rollback.proposal # 0
            \* The rollback commit is pending.
         /\ \/ /\ proposal[transaction[i].rollback.proposal].commit = Pending
                  \* The change has been committed. Commit the rollback.
               /\ \/ /\ proposal[transaction[i].change.proposal].commit \in Done
                        \* If the change proposal completed, commit the rollback proposal.
                     /\ \/ /\ proposal[transaction[i].change.proposal].commit = Complete
                           /\ configuration.committed.revision = i
                           /\ configuration' = [configuration EXCEPT !.committed.revision = transaction[i].rollback.revision,
                                                                     !.committed.values   = transaction[i].rollback.values @@ 
                                                                                               configuration.committed.values]
                           /\ proposal' = [proposal EXCEPT ![transaction[i].rollback.proposal].commit = Complete]
                           /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
                        \* If the change proposal failed, complete the rollback commit.
                        \/ /\ proposal[transaction[i].change.proposal].commit = Failed
                           /\ proposal' = [proposal EXCEPT ![transaction[i].rollback.proposal].commit = Complete]
                           /\ UNCHANGED <<configuration, history>>
                  \* The change has not been committed. Abort the change once the prior change is committed.
                  \/ /\ proposal[transaction[i].change.proposal].commit = Pending
                     /\ i-1 \in DOMAIN transaction =>
                           proposal[transaction[i-1].change.proposal].commit \in Done
                     /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].commit = Aborted]
                     /\ UNCHANGED <<configuration, history>>
               /\ UNCHANGED <<target>>
            \* The rollback commit is complete, increment the configuration's committed index if necessary.
            \/ /\ proposal[transaction[i].rollback.proposal].commit = Complete
               /\ configuration.committed.index = i-1
               /\ configuration' = [configuration EXCEPT !.committed.index = i]
               /\ UNCHANGED <<proposal, target, history>>
            \* The rollback apply is pending.
            \/ /\ proposal[transaction[i].rollback.proposal].apply = Pending
                  \* The change has been applied and the rollback has been committed. 
                  \* Apply the rollback.
               /\ \/ /\ proposal[transaction[i].change.proposal].apply \in Done
                     /\ proposal[transaction[i].rollback.proposal].commit = Complete
                        \* If the change apply was completed or failed, apply the rollback.
                        \* Rollbacks are applied when change apply failed to account for
                        \* partial failures in changes to the target.
                     /\ \/ /\ proposal[transaction[i].change.proposal].apply \in {Complete, Failed}
                           /\ configuration.applied.revision = i
                           /\ configuration.state = Complete
                           /\ configuration.term = mastership.term
                           /\ conn[n].id = mastership.conn
                           /\ conn[n].connected
                           /\ target.running
                           \* Rollbacks are applied until successful.
                           /\ target' = [target EXCEPT !.values = transaction[i].rollback.values @@ target.values]
                           /\ configuration' = [configuration EXCEPT !.applied.target   = target.id,
                                                                     !.applied.revision = transaction[i].rollback.revision,
                                                                     !.applied.values   = transaction[i].rollback.values @@
                                                                                             configuration.applied.values]
                           /\ proposal' = [proposal EXCEPT ![transaction[i].rollback.proposal].apply = Complete]
                           /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
                        \* If the change apply was aborted, complete the rollback apply without changes to the target.
                        \/ /\ proposal[transaction[i].change.proposal].apply = Aborted
                           /\ proposal' = [proposal EXCEPT ![transaction[i].rollback.proposal].apply = Complete]
                           /\ UNCHANGED <<configuration, target, history>>
                  \* The change has not been applied. Abort the change once the prior change is applied.
                  \/ /\ proposal[transaction[i].change.proposal].apply = Pending
                     /\ i-1 \in DOMAIN transaction =>
                           proposal[transaction[i-1].change.proposal].apply \in Done
                     /\ proposal' = [proposal EXCEPT ![transaction[i].change.proposal].apply = Aborted]
                     /\ UNCHANGED <<configuration, target, history>>
            \* The rollback apply is complete, increment the configuration's applied index if necessary.
            \/ /\ proposal[transaction[i].rollback.proposal].apply = Complete
               /\ configuration.applied.index = i-1
               /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ UNCHANGED <<proposal, target, history>>
         /\ UNCHANGED <<transaction>>

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
	/\ \/ ReconcileChange(n, i)
		\/ ReconcileRollback(n, i)
	/\ UNCHANGED <<mastership, conn>>

=============================================================================
