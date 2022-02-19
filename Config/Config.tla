------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

LOCAL INSTANCE Json

LOCAL INSTANCE IOUtils

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

\* The number of transactions to use for model checking
CONSTANT NumTransactions

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

CONSTANT 
   TransactionFile,
   ProposalFile,
   ConfigurationFile

TraceFile ==
   {TransactionFile,
    ProposalFile,
    ConfigurationFile}

----

(*
Configuration update/rollback requests are tracked and processed through
two data types. Transactions represent the lifecycle of a single configuration
change request and are stored in an append-only log. Configurations represent
the desired configuration of a gNMI target based on the aggregate of relevant
changes in the Transaction log.

   TYPE Type ::= type \in
      {Change,
       Rollback}
       
   TYPE Phase ::= phase \in
      {Initialize,
       Validate,
       Abort,
       Commit,
       Apply}

   TYPE State ::= state \in 
      {InProgress,
       Complete,
       Failed}

   TYPE Status ::= status \in 
      {Pending,
       Validated,
       Committed,
       Applied,
       Aborted}
   
   TYPE Isolation ::= isolation \in
      {ReadCommitted, 
       Serializable}

   TYPE Transaction == 
      [type      ::= type \in Type,
       isolation ::= isolation \in Isolation
       change    ::= 
         [target \in SUBSET (DOMAIN Target) |-> 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       rollback  ::= index \in Nat,
       targets   ::= targets \in SUBSET (DOMAIN Target)
       phase     ::= phase \in Phase,
       state     ::= state \in State,
       status    ::= status \in Status]
   
   TYPE Proposal == 
      [type       ::= type \in Type,
       change     ::= 
         [index  ::= index \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       rollback   ::= 
         [index  ::= index \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       dependency ::= [index \in Nat],
       phase      ::= phase \in Phase,
       state      ::= state \in State]
   
   TYPE Configuration == 
      [config    ::= 
         [index  ::= index \in Nat,
          term   ::= term \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target]) |-> 
               [value   ::= value \in STRING, 
                index   ::= index \in Nat,
                deleted ::= delete \in BOOLEAN]]],
       proposal ::= [index ::= index \in Nat],
       commit   ::= [index ::= index \in Nat],
       target   ::= 
         [index  ::= index \in Nat,
          term   ::= term \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target]) |-> 
               [value   ::= value \in STRING, 
                index   ::= index \in Nat,
                deleted ::= delete \in BOOLEAN]]],
       state    ::= state \in State]
*)

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

vars == <<transaction, proposal, configuration, mastership, target>>

----

InitTrace(f) ==
   LET ret == IOExec(<<"rm", f>>)
   IN  TRUE

LogTrace(f, s) ==
   LET trace == [init   |-> [transactions   |-> transaction,
                             proposals      |-> proposal,
                             configurations |-> configuration,
                             masterships    |-> mastership],
                 next   |-> s]
       ret   == IOExecTemplate(<<"/bin/sh", "-c", "echo '%s' >> %s">>, <<ToJsonObject(trace), f>>)
   IN ret.exitValue = 0

----

(*
This section models mastership for the configuration service.

Mastership is used primarily to track the lifecycle of individual
configuration targets and react to state changes on the southbound.
Each target is assigned a master from the Node set, and masters
can be unset when the target disconnects.
*)

\* Set node n as the master for target t
SetMaster(n, t) ==
   /\ mastership[t].master # n
   /\ mastership' = [mastership EXCEPT ![t].term   = mastership[t].term + 1,
                                       ![t].master = n]
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

UnsetMaster(t) ==
   /\ mastership[t].master # Nil
   /\ mastership' = [mastership EXCEPT ![t].master = Nil]
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

----

(*
This section models configuration changes and rollbacks. Changes
are appended to the transaction log and processed asynchronously.
*)

Value(s, t, p) ==
   LET value == CHOOSE v \in s : v.target = t /\ v.path = p
   IN
      [value  |-> value.value,
       delete |-> value.delete]

Paths(s, t) ==
   [p \in {v.path : v \in {v \in s : v.target = t}} |-> Value(s, t, p)]

Changes(s) ==
   [t \in {v.target : v \in s} |-> Paths(s, t)]

ValidValues(t, p) ==
   UNION {{[value |-> v, delete |-> FALSE] : v \in Target[t].values[p]}, {[value |-> Nil, delete |-> TRUE]}}

ValidPaths(t) ==
   UNION {{v @@ [path |-> p] : v \in ValidValues(t, p)} : p \in DOMAIN Target[t].values}

ValidTargets ==
   UNION {{p @@ [target |-> t] : p \in ValidPaths(t)} : t \in DOMAIN Target}

\* The set of all valid sets of changes to all targets and their paths. 
\* The set of possible changes is computed from the Target model value.
ValidChanges == 
   LET changeSets == {s \in SUBSET ValidTargets :
                         \A t \in DOMAIN Target :
                            \A p \in DOMAIN Target[t].values :
                               Cardinality({v \in s : v.target = t /\ v.path = p}) <= 1}
   IN
      {Changes(s) : s \in changeSets}

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
                           /\ LogTrace(TransactionFile, [transactions |-> transaction', 
                                                         proposals    |-> proposal'])
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
                                 /\ LogTrace(TransactionFile, [transactions |-> transaction', 
                                                               proposals    |-> proposal'])
                              \* If the rollback index is not a valid Change transaction
                              \* fail the Rollback transaction.
                              \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                       /\ transaction[transaction[i].rollback].type = Rollback
                                    \/ transaction[i].rollback \notin DOMAIN transaction
                                 /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                                 /\ LogTrace(TransactionFile, [transactions |-> transaction'])
                                 /\ UNCHANGED <<proposal>>
                  \* If the transaction's proposals have been initialized, check proposals
                  \* for completion or failures.
                  \/ /\ transaction[i].targets # {}
                        \* If all proposals have been Complete, mark the transaction Complete.
                     /\ \/ /\ \A t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase = Initialize
                                 /\ proposal[t][i].state = Complete
                           /\ transaction' = [transaction EXCEPT ![i].state = Complete]
                           /\ LogTrace(TransactionFile, [transactions |-> transaction'])
                           /\ UNCHANGED <<proposal>>
                        \* If any proposal has been Failed, mark the transaction Failed.
                        \/ /\ \E t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase  = Initialize
                                 /\ proposal[t][i].state = Failed
                           /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                           /\ LogTrace(TransactionFile, [transactions |-> transaction'])
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
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
            \* If the transaction failed initialization, proceed to the Abort phase
            \* to ensure indexes are still updated for the target configurations.
            \/ /\ transaction[i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase = Abort,
                                                     ![i].state = InProgress]
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Validate
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Validating state
               /\ \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase # Validate
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].phase = Validate,
                                                                 ![i].state = InProgress]]
                     /\ LogTrace(TransactionFile, [proposals |-> proposal'])
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                           ![i].status = Validated]
                     /\ LogTrace(TransactionFile, [transactions |-> transaction'])
                     /\ UNCHANGED <<proposal>>
                  \* If any proposal has been Failed, mark the transaction Failed.
                  \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].state = Failed
                     /\ transaction' = [transaction EXCEPT ![i].state = Failed]
                     /\ LogTrace(TransactionFile, [transactions |-> transaction'])
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
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
            \* If the transaction failed validation, proceed to the Abort phase
            \* to ensure indexes are still updated for the target configurations.
            \/ /\ transaction[i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase = Abort,
                                                     ![i].state = InProgress]
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Commit
         /\ \/ /\ transaction[i].state = InProgress
                  \* Move the transaction's proposals to the Committing state
               /\ \/ /\ \E t \in transaction[i].targets :
                           /\ proposal[t][i].phase # Commit
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].phase = Commit,
                                                                 ![i].state = InProgress]]
                           /\ LogTrace(TransactionFile, [proposals |-> proposal'])
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Commit
                           /\ proposal[t][i].state = Complete
                     /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                           ![i].status = Committed]
                     /\ LogTrace(TransactionFile, [transactions |-> transaction'])
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
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Apply
         /\ transaction[i].state = InProgress
            \* Move the transaction's proposals to the Applying state
         /\ \/ /\ \E t \in transaction[i].targets :
                     /\ proposal[t][i].phase # Apply
                     /\ proposal' = [proposal EXCEPT ![t] = 
                                       [proposal[t] EXCEPT ![i].phase = Apply,
                                                           ![i].state = InProgress]]
                     /\ LogTrace(TransactionFile, [proposals |-> proposal'])
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                     ![i].status = Applied]
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
            \* If any proposal has been Failed, mark the transaction Failed.
            \/ /\ \E t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].state = Failed
               /\ transaction' = [transaction EXCEPT ![i].state = Failed]
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
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
                     /\ LogTrace(TransactionFile, [proposals |-> proposal'])
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Abort
                     /\ proposal[t][i].state = Complete
               /\ transaction' = [transaction EXCEPT ![i].state  = Complete,
                                                     ![i].status = Aborted]
               /\ LogTrace(TransactionFile, [transactions |-> transaction'])
               /\ UNCHANGED <<proposal>>
   /\ UNCHANGED <<configuration, mastership, target>>

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].phase = Initialize
         /\ proposal[t][i].state = InProgress
         /\ proposal' = [proposal EXCEPT ![t] = 
               [proposal[t] EXCEPT ![i].state = Complete,
                                   ![i].dependency.index = configuration[t].proposal.index]]
         /\ configuration' = [configuration EXCEPT ![t].proposal.index = i]
         /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                    configurations |-> configuration'])
         /\ UNCHANGED <<target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].phase = Validate
         /\ proposal[t][i].state = InProgress
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
            \* For Change proposals validate the set of requested changes.
         /\ \/ /\ proposal[t][i].type = Change
               /\ LET rollbackIndex  == configuration[t].config.index
                      rollbackValues == [p \in DOMAIN proposal[t][i].change.values |-> 
                                           IF p \in DOMAIN configuration[t].config.values THEN
                                              configuration[t].config.values[p]
                                           ELSE
                                              [value  |-> Nil, 
                                               delete |-> TRUE]]
                  \* Model validation successes and failures with Valid and Invalid results.
                  IN \E r \in {Valid, Invalid} :
                        \* If the Change is Valid, record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        \/ /\ r = Valid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].rollback.index  = rollbackIndex,
                                                                 ![i].rollback.values = rollbackValues,
                                                                 ![i].state           = Complete]]
                        \/ /\ r = Invalid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].state = Failed]]
               /\ LogTrace(ProposalFile, [proposals |-> proposal'])
            \* For Rollback proposals, validate the rollback changes which are
            \* proposal being rolled back.
            \/ /\ proposal[t][i].type = Rollback
                  \* Rollbacks can only be performed on Change type proposals.
               /\ \/ /\ proposal[t][proposal[t][i].rollback.index].type = Change
                        \* Only roll back the change if it's the lastest change made
                        \* to the configuration based on the configuration index.
                     /\ \/ /\ configuration[t].config.index = proposal[t][i].rollback.index
                           /\ LET changeIndex    == proposal[t][proposal[t][i].rollback.index].rollback.index
                                  changeValues   == proposal[t][proposal[t][i].rollback.index].rollback.values
                                  rollbackValues == proposal[t][proposal[t][i].rollback.index].change.values
                              IN \E r \in {Valid, Invalid} :
                                    \* If the Rollback is Valid, record the changes required to
                                    \* roll back the target proposal and the index to which the
                                    \* configuration is being rolled back.
                                    \/ /\ r = Valid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].change.index    = changeIndex,
                                                                 ![i].change.values   = changeValues,
                                                                 ![i].rollback.values = rollbackValues,
                                                                 ![i].state           = Complete]]
                                       /\ LogTrace(ProposalFile, [proposals |-> proposal'])
                                    \/ /\ r = Invalid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                                         [proposal[t] EXCEPT ![i].state = Failed]]
                                       /\ LogTrace(ProposalFile, [proposals |-> proposal'])
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration[t].config.index # proposal[t][i].rollback.index
                           /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Failed]]
                           /\ LogTrace(ProposalFile, [proposals |-> proposal'])
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[t][proposal[t][i].rollback.index].type = Rollback
                     /\ proposal' = [proposal EXCEPT ![t] = 
                           [proposal[t] EXCEPT ![i].state = Failed]]
                     /\ LogTrace(ProposalFile, [proposals |-> proposal'])
         /\ UNCHANGED <<configuration, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].phase = Commit
         /\ proposal[t][i].state = InProgress
         \* Only commit the proposal if the prior proposal has already been committed.
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
         /\ configuration' = [configuration EXCEPT ![t].config.values = proposal[t][i].change.values,
                                                         ![t].config.index  = proposal[t][i].change.index,
                                                         ![t].commit.index  = i]
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
         /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                    configurations |-> configuration'])
         /\ UNCHANGED <<target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[t][i].phase = Apply
         /\ proposal[t][i].state = InProgress
         /\ configuration[t].target.index = proposal[t][i].dependency.index
         /\ configuration[t].target.term  = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                  /\ target' = [target EXCEPT ![t] = proposal[t][i].change.values @@ target[t]]
                  /\ configuration' = [configuration EXCEPT 
                                          ![t].target.index  = i,
                                          ![t].target.values = proposal[t][i].change.values 
                                             @@ configuration[t].target.values]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
                  /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                             configurations |-> configuration'])
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT ![t].target.index = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Failed]]
                  /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                             configurations |-> configuration'])
                  /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].phase = Abort
         /\ proposal[t][i].state = InProgress
            \* The commit.index will always be greater than or equal to the target.index.
            \* If only the commit.index matches the proposal's dependency.index, update
            \* the commit.index to enable commits of later proposals, but do not
            \* mark the Abort phase Complete until the target.index has been incremented.
         /\ \/ /\ configuration[t].commit.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].commit.index = i]
                  /\ LogTrace(ProposalFile, [configurations |-> configuration'])
               /\ UNCHANGED <<proposal>>
            \* If the configuration's target.index matches the proposal's dependency.index, 
            \* update the target.index and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].commit.index >= i
               /\ configuration[t].target.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].target.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
               /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                          configurations |-> configuration'])
            \* If both the configuration's commit.index and target.index match the
            \* proposal's dependency.index, update the commit.index and target.index
            \* and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].commit.index = proposal[t][i].dependency.index
               /\ configuration[t].target.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].commit.index = i,
                                                         ![t].target.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
               /\ LogTrace(ProposalFile, [proposals      |-> proposal',
                                          configurations |-> configuration'])
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<transaction, mastership>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].state # Complete
         /\ configuration' = [configuration EXCEPT ![t].state = Complete]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ \/ mastership[t].term > configuration[t].config.term
            \/ /\ mastership[t].term = configuration[t].config.term
               /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].config.term = mastership[t].term,
                                                   ![t].state       = InProgress]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].state = InProgress
         /\ mastership[t].term = configuration[t].config.term
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].target.values]
         /\ configuration' = [configuration EXCEPT ![t].target.term = mastership[t].term,
                                                   ![t].state       = Complete]
   /\ UNCHANGED <<proposal, transaction, mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [i \in {} |->
                       [type   |-> Change,
                        phase  |-> Initialize,
                        state  |-> InProgress,
                        status |-> Pending]]
   /\ proposal = [t \in DOMAIN Target |->
                    [i \in {} |-> 
                       [phase |-> Initialize,
                        state |-> InProgress]]]
   /\ configuration = [t \in DOMAIN Target |-> 
                         [state  |-> InProgress,
                          config |-> 
                            [index  |-> 0,
                             term   |-> 0,
                             values |-> 
                                [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]]],
                          proposal  |-> [index |-> 0],
                          commit    |-> [index |-> 0],
                          target    |-> 
                            [index  |-> 0,
                             term   |-> 0,
                             values |-> 
                               [path \in {} |-> 
                                  [path    |-> path,
                                   value   |-> Nil,
                                   index   |-> 0,
                                   deleted |-> FALSE]]]]]
   /\ target = [t \in DOMAIN Target |-> 
                  [path \in {} |-> 
                     [value |-> Nil]]]
   /\ mastership = [t \in DOMAIN Target |-> [master |-> Nil, term |-> 0]]
   /\ InitTrace(TransactionFile)
   /\ InitTrace(ProposalFile)
   /\ InitTrace(ConfigurationFile)

Next ==
   \/ \E i \in 1..NumTransactions :
         \E c \in ValidChanges : 
            RequestChange(i, c)
   \/ \E i \in 1..NumTransactions :
         \E j \in DOMAIN transaction :
            RequestRollback(i, j)
   \/ \E n \in Node :
         \E t \in DOMAIN Target :
            SetMaster(n, t)
   \*\/ \E t \in DOMAIN Target :
   \*      UnsetMaster(t)
   \/ \E n \in Node :
         \E t \in DOMAIN transaction :
            ReconcileTransaction(n, t)
   \/ \E n \in Node :
         \E t \in DOMAIN proposal :
            \E i \in DOMAIN proposal[t] :
               ReconcileProposal(n, t, i)
   \/ \E n \in Node :
         \E c \in DOMAIN configuration :
            ReconcileConfiguration(n, c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Order ==
   \A t \in DOMAIN proposal :
      \A i \in DOMAIN proposal[t] :
         /\ /\ proposal[t][i].phase = Commit
            /\ proposal[t][i].state = InProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = Commit
                  /\ proposal[t][j].state = Complete
         /\ /\ proposal[t][i].phase = Apply
            /\ proposal[t][i].state = InProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = Apply
                  /\ proposal[t][j].state = Complete

Consistency == 
   \A t \in DOMAIN target :
      LET 
          \* Compute the transaction indexes that have been applied to the target
          targetIndexes == {i \in DOMAIN transaction : 
                               /\ i \in DOMAIN proposal[t]
                               /\ proposal[t][i].phase = Apply
                               /\ proposal[t][i].state = Complete
                               /\ t \in transaction[i].targets
                               /\ ~\E j \in DOMAIN transaction :
                                     /\ j > i
                                     /\ transaction[j].type = Rollback
                                     /\ transaction[j].rollback = i
                                     /\ transaction[j].phase = Apply
                                     /\ transaction[j].state = Complete}
          \* Compute the set of paths in the target that have been updated by transactions
          appliedPaths   == UNION {DOMAIN proposal[t][i].change.values : i \in targetIndexes}
          \* Compute the highest index applied to the target for each path
          pathIndexes    == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                                    \A j \in targetIndexes :
                                          /\ i >= j 
                                          /\ p \in DOMAIN proposal[t][i].change.values]
          \* Compute the expected target configuration based on the last indexes applied
          \* to the target for each path.
          expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[t][pathIndexes[p]].change.values[p]]
      IN 
          target[t] = expectedConfig

Isolation ==
   \A i \in DOMAIN transaction :
      /\ /\ transaction[i].phase = Commit
         /\ transaction[i].state = InProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = Commit
      /\ /\ transaction[i].phase = Apply
         /\ transaction[i].state = InProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = Apply

Safety == [](Order /\ Consistency /\ Isolation)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN transaction
   /\ transaction[i].phase \in {Apply, Abort}
   /\ transaction[i].state = Complete

Termination ==
   \A i \in 1..NumTransactions : Terminated(i)

Liveness == <>Termination

THEOREM Spec => Liveness

----

(*
Type assumptions.
*)

ASSUME Nil \in STRING

ASSUME \A phase \in Phase : phase \in STRING

ASSUME \A state \in State : state \in STRING

ASSUME \A status \in Status : status \in STRING

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \notin DOMAIN Target 
             /\ n \in STRING
             
ASSUME /\ \A t \in DOMAIN Target : 
             /\ t \notin Node 
             /\ t \in STRING
             /\ Target[t].persistent \in BOOLEAN
             /\ \A p \in DOMAIN Target[t].values :
                   IsFiniteSet(Target[t].values[p])

=============================================================================
\* Modification History
\* Last modified Fri Feb 18 16:20:51 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
