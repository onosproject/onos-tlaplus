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

\* Phase constants
CONSTANTS
   Initialize,
   Validate,
   Abort,
   Commit,
   Apply

Phase ==
   {Initialize,
    Validate,
    Commit,
    Apply}

\* Status constants
CONSTANTS
   InProgress,
   Complete,
   Failed

State == 
   {InProgress,
    Complete,
    Failed}

CONSTANTS
   Valid,
   Invalid

CONSTANTS
   Success,
   Failure

\* The set of all nodes
CONSTANT Node

Empty == [p \in {} |-> [value |-> Nil, delete |-> FALSE]]

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

Test == INSTANCE Test WITH 
   File      <- "Transaction.log",
   CurrState <- [
      transactions  |-> transaction,
      proposals     |-> proposal,
      configuration |-> configuration,
      mastership    |-> mastership,
      target        |-> target],
   SuccState <- [
      transactions  |-> transaction',
      proposals     |-> proposal',
      configuration |-> configuration',
      mastership    |-> mastership',
      target        |-> target']

----

(*
This section models configuration changes and rollbacks. Changes
are appended to the transaction log and processed asynchronously.
*)

\* Add a set of changes 'c' to the transaction log
RequestChange(p, v) ==
   /\ transaction' = Append(transaction, [type      |-> Change,
                                          change    |-> (p :> [index |-> Len(transaction)+1, value |-> v]),
                                          phase     |-> Initialize,
                                          state     |-> InProgress])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(i) ==
   /\ transaction' = Append(transaction, [type      |-> Rollback,
                                          rollback  |-> i,
                                          phase     |-> Initialize,
                                          state     |-> InProgress])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

----

(*
This section models the Transaction log reconciler.

Transactions come in two flavors:
- Change transactions contain a set of changes to be applied to a set 
of targets
- Rollback transactions reference a prior change transaction to be
reverted to the previous state

Transacations proceed through a series of phases:
* Initialize - create and link Proposals
* Validate - validate changes and rollbacks
* Commit - commit changes to Configurations
* Apply - commit changes to Targets
*)

\* Reconcile a transaction
ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transaction
      \* Initialize is the only transaction phase that's globally serialized.
      \* While in the Initializing phase, the reconciler checks whether the
      \* prior transaction has been Initialized before creating Proposals in
      \* the Initialize phase. Once all of the transaction's proposals have
      \* been Initialized, the transaction will be marked Initialized. If any
      \* proposal is Failed, the transaction will be marked Failed as well.
   /\ \/ /\ transaction[i].phase = Initialize
         /\ \/ /\ transaction[i].state = InProgress
               \* The transaction can only be initialized once the prior transaction
               \* has been initialized.
               /\ i-1 \in DOMAIN transaction => 
                     \/ transaction[i-1].phase = Initialize => transaction[i-1].state = Complete
                     \/ transaction[i-1].phase # Initialize
                  \* If the proposal does not exist in the queue, create it.
               /\ \/ /\ i \notin DOMAIN proposal
                        \* Append a change proposal.
                     /\ \/ /\ transaction[i].type = Change
                           /\ proposal' = proposal @@ (i :> [
                                                         type       |-> Change,
                                                         change     |-> [
                                                            index  |-> i,
                                                            values |-> transaction[i].change],
                                                         rollback   |-> [
                                                            index  |-> 0, 
                                                            values |-> Empty],
                                                         phase      |-> Initialize,
                                                         state      |-> InProgress])
                           /\ UNCHANGED <<transaction>>
                        \* Append a rollback proposal.
                        \/ /\ transaction[i].type = Rollback
                              \* If the rollback index is a valid Change transaction, 
                              \* initialize the proposal.
                           /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                 /\ transaction[transaction[i].rollback].type = Change
                                 /\ proposal' = proposal @@ (i :> [
                                                               type       |-> Rollback,
                                                               change   |-> [
                                                                  index  |-> 0, 
                                                                  values |-> Empty],
                                                               rollback   |-> [
                                                                  index  |-> transaction[i].rollback,
                                                                  values |-> Empty],
                                                               phase      |-> Initialize,
                                                               state      |-> InProgress])
                                 /\ UNCHANGED <<transaction>>
                              \* If the rollback index is not a valid Change transaction
                              \* fail the Rollback transaction.
                              \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                       /\ transaction[transaction[i].rollback].type = Rollback
                                    \/ transaction[i].rollback \notin DOMAIN transaction
                                 /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                                 /\ UNCHANGED <<proposal>>
                  \* If the transaction's proposal has been created, check for completion or failures.
                  \/ /\ i \in DOMAIN proposal
                        \* If the proposal has been Complete, mark the transaction Complete.
                     /\ \/ /\ proposal[i].phase = Initialize
                           /\ proposal[i].state = Complete
                           /\ transaction' = [transaction EXCEPT ![i].state = Complete]
                           /\ UNCHANGED <<proposal>>
                        \* If the proposal has been Failed, mark the transaction Failed.
                        \/ /\ proposal[i].phase = Initialize
                           /\ proposal[i].state = Failed
                           /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                           /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Initialized, move it to the validate phase.
            \/ /\ transaction[i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].phase = Validate,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Validate
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Validating state
               /\ \/ /\ proposal[i].phase # Validate
                     /\ proposal' = [proposal EXCEPT ![i].phase = Validate,
                                                      ![i].state = InProgress]
                     /\ UNCHANGED <<transaction>>
                  \* If the proposals is Complete, mark the transaction Complete.
                  \/ /\ proposal[i].phase = Validate
                     /\ proposal[i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state = Complete]
                     /\ UNCHANGED <<proposal>>
                  \* If the proposal has been Failed, mark the transaction Failed.
                  \/ /\ proposal[i].phase = Validate
                     /\ proposal[i].state = Failed
                     /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Validated, move it to the commit phase.
            \/ /\ transaction[i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].phase = Commit,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Commit
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Committing state
               /\ \/ /\ proposal[i].phase # Commit
                     /\ proposal' = [proposal EXCEPT ![i].phase = Commit,
                                                     ![i].state = InProgress]
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ proposal[i].phase = Commit
                     /\ proposal[i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state = Complete]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Committed, proceed to the Apply phase.
            \/ /\ transaction[i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].phase = Apply,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Apply
         /\ transaction[i].state = InProgress
            \* Move the transaction's proposals to the Applying state
         /\ \/ /\ proposal[i].phase # Apply
               /\ proposal' = [proposal EXCEPT ![i].phase = Apply,
                                               ![i].state = InProgress]
               /\ UNCHANGED <<transaction>>
            \* If the proposal has been Complete, mark the transaction Complete.
            \/ /\ proposal[i].phase = Apply
               /\ proposal[i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].state = Complete]
               /\ UNCHANGED <<proposal>>
            \* If the proposal has been Failed, mark the transaction Failed.
            \/ /\ proposal[i].phase  = Apply
               /\ proposal[i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].state = Failed]
               /\ UNCHANGED <<proposal>>
   /\ UNCHANGED <<configuration, mastership, target>>

=============================================================================
