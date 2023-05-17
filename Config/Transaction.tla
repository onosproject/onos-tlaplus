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

\* Transaction isolation constants
CONSTANTS
   ReadCommitted,
   Serializable

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
    Abort,
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

\* State constants
CONSTANTS
   Pending,
   Validated,
   Committed,
   Applied,
   Aborted

Status ==
   {Pending,
    Validated,
    Committed,
    Applied,
    Aborted}

CONSTANTS
   Valid,
   Invalid

CONSTANTS
   Success,
   Failure

\* The set of all nodes
CONSTANT Node

(*
Target is the set of all targets and their possible paths and values.

Example:
   Target == 
      [target1 |-> 
         [persistent |-> FALSE,
          values |-> [
            path1 |-> {"value1", "value2"},
            path2 |-> {"value2", "value3"}]],
      target2 |-> 
         [persistent |-> TRUE,
          values |-> [
            path2 |-> {"value3", "value4"},
            path3 |-> {"value4", "value5"}]]]
*)
CONSTANT Target

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
RequestChange(i, c) ==
   /\ i = Len(transaction) + 1
   /\ \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (i :> [type      |-> Change,
                                                 isolation |-> isolation,
                                                 change    |-> c,
                                                 targets   |-> {},
                                                 phase     |-> Initialize,
                                                 state     |-> InProgress,
                                                 status    |-> Pending])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(i, j) ==
   /\ i = Len(transaction) + 1
   /\ \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (i :> [type      |-> Rollback,
                                                 isolation |-> isolation,
                                                 rollback  |-> j,
                                                 targets   |-> {},
                                                 phase     |-> Initialize,
                                                 state     |-> InProgress,
                                                 status    |-> Pending])
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
      \* Initialize is the only transaction phase that's globally serialized.
      \* While in the Initializing phase, the reconciler checks whether the
      \* prior transaction has been Initialized before creating Proposals in
      \* the Initialize phase. Once all of the transaction's proposals have
      \* been Initialized, the transaction will be marked Initialized. If any
      \* proposal is Failed, the transaction will be marked Failed as well.
   /\ \/ /\ transaction[i].phase = Initialize
         /\ \/ /\ transaction[i].state = InProgress
               \* All prior transaction must be initialized before proceeding
               \* to initialize this transaction.
               /\ ~\E j \in DOMAIN transaction :
                     /\ j < i
                     /\ transaction[j].phase = Initialize
                     /\ transaction[j].state = InProgress
                  \* If the transaction's targets are not yet set, create proposals
                  \* and add targets to the transaction state.
               /\ \/ /\ transaction[i].targets = {}
                        \* If the transaction is a change, the targets are taken
                        \* from the change values.
                     /\ \/ /\ transaction[i].type = Change
                           /\ transaction' = [transaction EXCEPT ![i].targets = DOMAIN transaction[i].change]
                           /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in DOMAIN transaction[i].change THEN
                                    proposal[t] @@ (i :> [type       |-> Change,
                                                          change     |-> 
                                                            [index  |-> i,
                                                             values |-> transaction[i].change[t]],
                                                          rollback   |-> 
                                                            [index  |-> 0, 
                                                             values |-> Empty],
                                                          dependency |-> [index |-> 0],
                                                          phase      |-> Initialize,
                                                          state      |-> InProgress])
                                 ELSE
                                    proposal[t]]
                        \* If the transaction is a rollback, the targets affected are 
                        \* the targets of the change transaction being rolled back.
                        \/ /\ transaction[i].type = Rollback
                              \* If the rollback index is a valid Change transaction, 
                              \* initialize proposals for all of the Change targets.
                           /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                 /\ transaction[transaction[i].rollback].type = Change
                                 /\ transaction' = [transaction EXCEPT ![i].targets = 
                                                      DOMAIN transaction[transaction[i].rollback].change]
                                 /\ proposal' = [t \in DOMAIN proposal |-> 
                                       IF t \in DOMAIN transaction[transaction[i].rollback].change THEN
                                          proposal[t] @@ (i :> [type       |-> Rollback,
                                                                change   |-> 
                                                                  [index  |-> 0, 
                                                                   values |-> Empty],
                                                                rollback   |-> 
                                                                  [index  |-> transaction[i].rollback,
                                                                   values |-> Empty],
                                                                dependency |-> [index |-> 0],
                                                                phase      |-> Initialize,
                                                                state      |-> InProgress])
                                       ELSE
                                          proposal[t]]
                              \* If the rollback index is not a valid Change transaction
                              \* fail the Rollback transaction.
                              \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                       /\ transaction[transaction[i].rollback].type = Rollback
                                    \/ transaction[i].rollback \notin DOMAIN transaction
                                 /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                                 /\ UNCHANGED <<proposal>>
                  \* If the transaction's proposals have been initialized, check proposals
                  \* for completion or failures.
                  \/ /\ transaction[i].targets # {}
                        \* If all proposals have been Complete, mark the transaction Complete.
                     /\ \/ /\ \A t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase = Initialize
                                 /\ proposal[t][i].state = Complete
                           /\ transaction' = [transaction EXCEPT ![i].state = Complete]
                           /\ UNCHANGED <<proposal>>
                        \* If any proposal has been Failed, mark the transaction Failed.
                        \/ /\ \E t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase  = Initialize
                                 /\ proposal[t][i].state = Failed
                           /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                           /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Initialized, proceed to the Validate phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Validated to preserve serializability before 
            \* moving the transaction to the Validate phase.
            \/ /\ transaction[i].state = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependency.index \in DOMAIN transaction
                     /\ transaction[proposal[t][i].dependency.index].isolation = Serializable
                     => transaction[proposal[t][i].dependency.index].status \in {Validated, Committed, Applied, Aborted}
               /\ transaction' = [transaction EXCEPT ![i].phase = Validate,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
            \* If the transaction failed initialization, proceed to the Abort phase
            \* to ensure indexes are still updated for the target configurations.
            \/ /\ transaction[i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase = Abort,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Validate
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Validating state
               /\ \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase # Validate
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].phase = Validate,
                                                                 ![i].state = InProgress]]
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                           ![i].status = Validated]
                     /\ UNCHANGED <<proposal>>
                  \* If any proposal has been Failed, mark the transaction Failed.
                  \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].state = Failed
                     /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Validated, proceed to the Commit phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Committed to preserve serializability before 
            \* moving the transaction to the Commit phase.
            \/ /\ transaction[i].state = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependency.index \in DOMAIN transaction
                     /\ transaction[proposal[t][i].dependency.index].isolation = Serializable
                     => transaction[proposal[t][i].dependency.index].status \in {Committed, Applied, Aborted}
               /\ transaction' = [transaction EXCEPT ![i].phase = Commit,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
            \* If the transaction failed validation, proceed to the Abort phase
            \* to ensure indexes are still updated for the target configurations.
            \/ /\ transaction[i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase = Abort,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Commit
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Committing state
               /\ \/ /\ \E t \in transaction[i].targets :
                           /\ proposal[t][i].phase # Commit
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].phase = Commit,
                                                                 ![i].state = InProgress]]
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Commit
                           /\ proposal[t][i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                           ![i].status = Committed]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Committed, proceed to the Apply phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Applied to preserve serializability before 
            \* moving the transaction to the Apply phase.
            \/ /\ transaction[i].state = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependency.index \in DOMAIN transaction
                     /\ transaction[proposal[t][i].dependency.index].isolation = Serializable
                     => transaction[proposal[t][i].dependency.index].status \in {Applied, Aborted}
               /\ transaction' = [transaction EXCEPT ![i].phase = Apply,
                                                     ![i].state = InProgress]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Apply
         /\ transaction[i].state = InProgress
            \* Move the transaction's proposals to the Applying state
         /\ \/ /\ \E t \in transaction[i].targets :
                     /\ proposal[t][i].phase # Apply
                     /\ proposal' = [proposal EXCEPT ![t] = 
                                       [proposal[t] EXCEPT ![i].phase = Apply,
                                                           ![i].state = InProgress]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                     ![i].status = Applied]
               /\ UNCHANGED <<proposal>>
            \* If any proposal has been Failed, mark the transaction Failed.
            \/ /\ \E t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].state = Failed]
               /\ UNCHANGED <<proposal>>
      \* The Aborting state is used to clean up transactions that have failed during
      \* the Initializing or Validating phases.
      \/ /\ transaction[i].phase = Abort
         /\ transaction[i].state = InProgress
            \* Move the transaction's proposals to the Aborting state
         /\ \/ /\ \E t \in transaction[i].targets :
                     /\ proposal[t][i].phase # Abort
                     /\ proposal' = [proposal EXCEPT ![t] = 
                                       [proposal[t] EXCEPT ![i].phase = Abort,
                                                           ![i].state = InProgress]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Abort
                     /\ proposal[t][i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                     ![i].status = Aborted]
               /\ UNCHANGED <<proposal>>
   /\ UNCHANGED <<configuration, mastership, target>>

=============================================================================
