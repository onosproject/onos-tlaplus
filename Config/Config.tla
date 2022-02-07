------------------------------- MODULE Config -------------------------------

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
   LET phases == <<Initialize,
                   Validate,
                   Abort,
                   Commit,
                   Apply>>
   IN [p \in {phases[i] : i \in DOMAIN phases} |-> 
         CHOOSE i \in DOMAIN phases : phases[i] = p]

\* Status constants
CONSTANTS 
   Pending,
   Complete,
   Failed

Status == 
   LET statuses == <<Pending,
                     Complete,
                     Failed>>
   IN [s \in {statuses[i] : i \in DOMAIN statuses} |-> 
         CHOOSE i \in DOMAIN statuses : statuses[i] = s]

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
   Target == [
      target1 |-> [
         persistent |-> FALSE,
         values |-> [
            path1 |-> {"value1", "value2"},
            path2 |-> {"value2", "value3"}]],
      target2 |-> [
         persistent |-> TRUE,
         values |-> [
            path2 |-> {"value3", "value4"},
            path3 |-> {"value4", "value5"}]]]
*)
CONSTANT Target

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

   TYPE Status ::= status \in 
      {Pending,
       Initializing,
       Initialized,
       Validating,
       Validated,
       Committing,
       Committed,
       Applying,
       Applied,
       Synchronizing,
       Synchronized,
       Persisted,
       Failed}

   TYPE Transaction == [
      type      ::= type \in Type,
      index     ::= index \in Nat,
      isolation ::= isolation \in {IsolationDefault, IsolationSerializable}
      values    ::= [
         target \in SUBSET (DOMAIN Target) |-> [
            path \in SUBSET (DOMAIN Target[target].values) |-> [
               value  ::= value \in STRING, 
               delete ::= delete \in BOOLEAN]]],
      rollback  ::= index \in Nat,
      targets   ::= targets \in SUBSET (DOMAIN Target)
      phase     ::= phase \in Phase]
      status    ::= status \in Status]
   
   TYPE Proposal == [
      type            ::= type \in Type,
      index           ::= index \in Nat,
      values          ::= [
         path \in SUBSET (DOMAIN Target[target].values) |-> [
            value  ::= value \in STRING, 
            delete ::= delete \in BOOLEAN]],
      rollback        ::= index \in Nat,
      dependencyIndex ::= dependencyIndex \in Nat,
      rollbackIndex   ::= rollbackIndex \in Nat,
      rollbackValues  ::= [
         path \in SUBSET (DOMAIN Target[target].values) |-> [
            value  ::= value \in STRING, 
            delete ::= delete \in BOOLEAN]],
      phase        ::= phase \in Phase]
      status       ::= status \in Status]
   
   TYPE Configuration == [
      id             ::= id \in STRING,
      target         ::= target \in STRING,
      values         ::= [
         path \in SUBSET (DOMAIN Target[target]) |-> [
            value   ::= value \in STRING, 
            index   ::= index \in Nat,
            deleted ::= delete \in BOOLEAN]],
      configIndex    ::= configIndex \in Nat,
      configTerm     ::= configTerm \in Nat,
      proposedIndex  ::= proposedIndex \in Nat,
      committedIndex ::= committedIndex \in Nat,
      appliedIndex   ::= appliedIndex \in Nat,
      appliedTerm    ::= appliedTerm \in Nat,
      appliedValues  ::= [
         path \in SUBSET (DOMAIN Target[target]) |-> [
            value   ::= value \in STRING, 
            index   ::= index \in Nat,
            deleted ::= delete \in BOOLEAN]],
      status    ::= status \in Status]
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

\* The next available index in the transaction log.
\* This is computed as the max of the existing indexes in the log to
\* allow for changes to the log (e.g. log compaction) to be modeled.
NextIndex ==
   IF DOMAIN transaction = {} THEN
      1
   ELSE 
      LET i == CHOOSE i \in DOMAIN transaction :
         \A j \in DOMAIN transaction : i >= j
      IN i + 1

\* Add a set of changes 'c' to the transaction log
RequestChange(c) ==
   /\ \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (NextIndex :> [type      |-> Change,
                                                         index     |-> NextIndex,
                                                         isolation |-> isolation,
                                                         values    |-> c,
                                                         targets   |-> {},
                                                         phase     |-> Initialize,
                                                         status    |-> Pending])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(t) ==
   /\ \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (NextIndex :> [type      |-> Rollback,
                                                         index     |-> NextIndex,
                                                         isolation |-> isolation,
                                                         rollback  |-> t,
                                                         targets   |-> {},
                                                         phase     |-> Initialize,
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
         /\ \/ /\ transaction[i].status = Pending
               \* Serialize transaction initialization
               /\ i-1 \in DOMAIN transaction =>
                     \/ Phase[transaction[i-1].phase] > Phase[Initialize]
                     \/ transaction[i-1].status # Pending
               \* If the transaction's targets are not yet set, create proposals
               \* and add targets to the transaction state.
               /\ \/ /\ transaction[i].targets = {}
                        \* If the transaction is a change, the targets are taken
                        \* from the change values.
                     /\ \/ /\ transaction[i].type = Change
                           /\ transaction' = [transaction EXCEPT ![i].targets = DOMAIN transaction[i].values]
                           /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in DOMAIN transaction[i].values THEN
                                    proposal[t] @@ (i :> [type            |-> Change,
                                                          index           |-> i,
                                                          values          |-> transaction[i].values[t],
                                                          dependencyIndex |-> 0,
                                                          rollbackIndex   |-> 0,
                                                          rollbackValues  |-> <<>>,
                                                          phase           |-> Initialize,
                                                          status          |-> Pending])
                                 ELSE
                                    proposal[t]]
                        \* If the transaction is a rollback, the targets affected are 
                        \* the targets of the change transaction being rolled back.
                        \/ /\ transaction[i].type = Rollback
                           /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                 /\ transaction[transaction[i].rollback].type = Change
                                 /\ transaction' = [transaction EXCEPT ![i].targets = 
                                                      DOMAIN transaction[transaction[i].rollback].values]
                                 /\ proposal' = [t \in DOMAIN proposal |-> 
                                       IF t \in DOMAIN transaction[transaction[i].rollback].values THEN
                                          proposal[t] @@ (i :> [type            |-> Rollback,
                                                                index           |-> i,
                                                                rollback        |-> transaction[i].rollback,
                                                                dependencyIndex |-> 0,
                                                                rollbackIndex   |-> 0,
                                                                rollbackValues  |-> <<>>,
                                                                phase           |-> Initialize,
                                                                status          |-> Pending])
                                       ELSE
                                          proposal[t]]
                              \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                       /\ transaction[transaction[i].rollback].type = Rollback
                                    \/ transaction[i].rollback \notin DOMAIN transaction
                                 /\ transaction' = [transaction EXCEPT ![i].status = Failed]
                                 /\ UNCHANGED <<proposal>>                     
                  \/ /\ transaction[i].targets # {}
                        \* If all proposals have been Complete, mark the transaction Complete.
                     /\ \/ /\ \A t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase  = Initialize
                                 /\ proposal[t][i].status = Complete
                           /\ transaction' = [transaction EXCEPT ![i].status = Complete]
                           /\ UNCHANGED <<proposal>>
                        \* If any proposal has been Failed, mark the transaction Failed.
                        \/ /\ \E t \in transaction[i].targets : 
                                 /\ proposal[t][i].phase  = Initialize
                                 /\ proposal[t][i].status = Failed
                           /\ transaction' = [transaction EXCEPT ![i].status = Failed]
                           /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Initialized, proceed to the Validate phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Validated to preserve serializability before 
            \* moving the transaction to the Validate phase.
            \/ /\ transaction[i].status = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependencyIndex > 0 =>
                           \/ transaction[proposal[t][i].dependencyIndex].isolation # Serializable
                           \/ Phase[transaction[proposal[t][i].dependencyIndex].phase] > Phase[Validate]
                           \/ /\ transaction[proposal[t][i].dependencyIndex].phase = Validate
                              /\ transaction[proposal[t][i].dependencyIndex].status \in {Complete, Failed}
               /\ transaction' = [transaction EXCEPT ![i].phase  = Validate,
                                                     ![i].status = Pending]
               /\ UNCHANGED <<proposal>>
            \/ /\ transaction[i].status = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase  = Abort,
                                                     ![i].status = Pending]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Validate
         /\ \/ /\ transaction[i].status = Pending
                  \* Move the transaction's proposals to the Validating state
               /\ \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase # Validate
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                              proposal[t] EXCEPT ![i].phase  = Validate,
                                                                 ![i].status = Pending]]
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].status = Complete
                     /\ transaction' = [transaction EXCEPT ![i].status = Complete]
                     /\ UNCHANGED <<proposal>>
                  \* If any proposal has been Failed, mark the transaction Failed.
                  \/ /\ \E t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Validate
                           /\ proposal[t][i].status = Failed
                     /\ transaction' = [transaction EXCEPT ![i].status = Failed]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Validated, proceed to the Commit phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Committed to preserve serializability before 
            \* moving the transaction to the Commit phase.
            \/ /\ transaction[i].status = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependencyIndex > 0 =>
                           \/ transaction[proposal[t][i].dependencyIndex].isolation # Serializable
                           \/ Phase[transaction[proposal[t][i].dependencyIndex].phase] > Phase[Commit]
                           \/ /\ transaction[proposal[t][i].dependencyIndex].phase = Commit
                              /\ transaction[proposal[t][i].dependencyIndex].status \in {Complete, Failed}
               /\ transaction' = [transaction EXCEPT ![i].phase  = Commit,
                                                     ![i].status = Pending]
               /\ UNCHANGED <<proposal>>
            \/ /\ transaction[i].status = Failed
               /\ transaction' = [transaction EXCEPT ![i].phase  = Abort,
                                                     ![i].status = Pending]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Commit
         /\ \/ /\ transaction[i].status = Pending
                  \* Move the transaction's proposals to the Committing state
               /\ \/ /\ \E t \in transaction[i].targets :
                           /\ proposal[t][i].phase # Validate
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                              proposal[t] EXCEPT ![i].phase  = Commit,
                                                                 ![i].status = Pending]]
                     /\ UNCHANGED <<transaction>>
                  \* If all proposals have been Complete, mark the transaction Complete.
                  \/ /\ \A t \in transaction[i].targets : 
                           /\ proposal[t][i].phase  = Commit
                           /\ proposal[t][i].status = Complete
                     /\ transaction' = [transaction EXCEPT ![i].status = Complete]
                     /\ UNCHANGED <<proposal>>
            \* Once the transaction has been Committed, proceed to the Apply phase.
            \* If any of the transaction's proposals depend on a Serializable transaction,
            \* verify the dependency has been Applied to preserve serializability before 
            \* moving the transaction to the Apply phase.
            \/ /\ transaction[i].status = Complete
               /\ \A t \in transaction[i].targets :
                     /\ proposal[t][i].dependencyIndex > 0 =>
                           \/ transaction[proposal[t][i].dependencyIndex].isolation # Serializable
                           \/ Phase[transaction[proposal[t][i].dependencyIndex].phase] > Phase[Apply]
                           \/ /\ transaction[proposal[t][i].dependencyIndex].phase = Apply
                              /\ transaction[proposal[t][i].dependencyIndex].status \in {Complete, Failed}
               /\ transaction' = [transaction EXCEPT ![i].phase  = Apply,
                                                     ![i].status = Pending]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].phase = Apply
         /\ transaction[i].status = Pending
            \* Move the transaction's proposals to the Applying state
         /\ \/ /\ \E t \in transaction[i].targets :
                     /\ proposal[t][i].phase # Validate
                     /\ proposal' = [proposal EXCEPT ![t] = [
                                        proposal[t] EXCEPT ![i].phase  = Apply,
                                                           ![i].status = Pending]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].status = Complete
               /\ transaction' = [transaction EXCEPT ![i].status = Complete]
               /\ UNCHANGED <<proposal>>
            \* If any proposal has been Failed, mark the transaction Failed.
            \/ /\ \E t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Apply
                     /\ proposal[t][i].status = Failed
               /\ transaction' = [transaction EXCEPT ![i].status = Failed]
               /\ UNCHANGED <<proposal>>
      \* The Aborting state is used to clean up transactions that have failed during
      \* the Initializing or Validating phases.
      \/ /\ transaction[i].phase = Abort
         /\ transaction[i].status = Pending
            \* Move the transaction's proposals to the Aborting state
         /\ \/ /\ \E t \in transaction[i].targets :
                     /\ proposal[t][i].phase # Validate
                     /\ proposal' = [proposal EXCEPT ![t] = [
                                        proposal[t] EXCEPT ![i].phase  = Abort,
                                                           ![i].status = Pending]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Complete, mark the transaction Complete.
            \/ /\ \A t \in transaction[i].targets : 
                     /\ proposal[t][i].phase  = Abort
                     /\ proposal[t][i].status = Complete
               /\ transaction' = [transaction EXCEPT ![i].status = Complete]
               /\ UNCHANGED <<proposal>>
   /\ UNCHANGED <<configuration, mastership, target>>

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].phase = Initialize
         /\ proposal[t][i].status = Pending
         /\ proposal' = [proposal EXCEPT ![t] = [
               proposal[t] EXCEPT ![i] = [
                  status          |-> Complete, 
                  dependencyIndex |-> configuration[t].proposedIndex] @@ proposal[t][i]]]
         /\ configuration' = [configuration EXCEPT ![t].proposedIndex = i]
         /\ UNCHANGED <<target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].phase = Validate
         /\ proposal[t][i].status = Pending
         /\ configuration[t].committedIndex = proposal[t][i].dependencyIndex
            \* For Change proposals validate the set of requested changes.
         /\ \/ /\ proposal[t][i].type = Change
               /\ LET rollbackIndex == configuration[t].configIndex
                      rollbackValues == [p \in DOMAIN proposal[t][i].values |-> 
                                           IF p \in DOMAIN configuration[t].values THEN
                                              configuration[t].values[p]
                                           ELSE
                                              [value  |-> Nil, 
                                               delete |-> TRUE]]
                  \* Model validation successes and failures with Valid and Invalid results.
                  IN \E r \in {Valid, Invalid} :
                        \* If the Change is Valid, record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        \/ /\ r = Valid
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].rollbackIndex  = rollbackIndex,
                                                                ![i].rollbackValues = rollbackValues,
                                                                ![i].status         = Complete]]
                        \/ /\ r = Invalid
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].status = Failed]]
            \* For Rollback proposals, validate the rollback changes which are
            \* proposal being rolled back.
            \/ /\ proposal[t][i].type = Rollback
                  \* Rollbacks can only be performed on Change type proposals.
               /\ \/ /\ proposal[t][proposal[t][i].rollback].type = Change
                        \* Only roll back the change if it's the lastest change made
                        \* to the configuration based on the configuration index.
                     /\ \/ /\ configuration[t].configIndex = proposal[t][i].rollback
                           /\ LET rollbackIndex  == proposal[t][proposal[t][i].rollback].rollbackIndex
                                  rollbackValues == proposal[t][proposal[t][i].rollback].rollbackValues
                              IN \E r \in {Valid, Invalid} :
                                    \* If the Rollback is Valid, record the changes required to
                                    \* roll back the target proposal and the index to which the
                                    \* configuration is being rolled back.
                                    \/ /\ r = Valid
                                       /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].rollbackIndex  = rollbackIndex,
                                                                ![i].rollbackValues = rollbackValues,
                                                                ![i].status         = Complete]]
                                    \/ /\ r = Invalid
                                       /\ proposal' = [proposal EXCEPT ![t] = [
                                                         proposal[t] EXCEPT ![i].status = Failed]]
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration[t].configIndex # proposal[t][i].rollback
                           /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Failed]]
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[t][proposal[t][i].rollback].type = Rollback
                     /\ proposal' = [proposal EXCEPT ![t] = [
                           proposal[t] EXCEPT ![i].status = Failed]]
         /\ UNCHANGED <<configuration, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].phase = Commit
         /\ proposal[t][i].status = Pending
         \* Only commit the proposal if the prior proposal has already been committed.
         /\ configuration[t].committedIndex = proposal[t][i].dependencyIndex
            \* If the proposal is a change, commit the change values and set the configuration
            \* index to the proposal index.
         /\ \/ /\ proposal[t][i].type = Change
               /\ configuration' = [configuration EXCEPT ![t].values         = proposal[t][i].values,
                                                         ![t].configIndex    = i,
                                                         ![t].committedIndex = i]
            \* If the proposal is a rollback, commit the rollback values and index. This
            \* will cause the configuration index to be reverted to the index prior to
            \* the transaction/proposal being rolled back.
            \/ /\ proposal[t][i].type = Rollback
               /\ configuration' = [configuration EXCEPT ![t].values         = proposal[t][i].rollbackValues,
                                                         ![t].configIndex    = proposal[t][i].rollbackIndex,
                                                         ![t].committedIndex = i]
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Complete]]
         /\ UNCHANGED <<target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[t][i].phase = Apply
         /\ proposal[t][i].status = Pending
         /\ configuration[t].appliedIndex = proposal[t][i].dependencyIndex
         /\ configuration[t].appliedTerm = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                     \* If the proposal is a change, apply the change values to the target
                     \* and update the configuration's applied index and values.
                  /\ \/ /\ proposal[t][i].type = Change
                        /\ target' = [target EXCEPT ![t] = proposal[t][i].values @@ target[t]]
                        /\ configuration' = [configuration EXCEPT 
                              ![t].appliedIndex = i,
                              ![t].appliedValues = proposal[t][i].values @@ configuration[t].appliedValues]
                     \* If the proposal is a rollback, apply the rollback values and update the
                     \* configuration's applied values with the rolled back values.
                     \/ /\ proposal[t][i].type = Rollback
                        /\ target' = [target EXCEPT ![t] = proposal[t][i].rollbackValues @@ target[t]]
                        /\ configuration' = [configuration EXCEPT 
                              ![t].appliedIndex  = i,
                              ![t].appliedValues = proposal[t][i].rollbackValues @@ configuration[t].appliedValues]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Complete]]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT ![t].appliedIndex = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Failed]]
                  /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].phase = Abort
         /\ proposal[t][i].status = Pending
            \* The committedIndex will always be greater than or equal to the appliedIndex.
            \* If only the committedIndex matches the proposal's dependencyIndex, update
            \* the committedIndex to enable commits of later proposals, but do not
            \* mark the Abort phase Complete until the appliedIndex has been incremented.
         /\ \/ /\ configuration[t].committedIndex = proposal[t][i].dependencyIndex
               /\ configuration[t].appliedIndex # proposal[t][i].dependencyIndex
               /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
               /\ UNCHANGED <<proposal>>
            \* If both the configuration's committedIndex and appliedIndex match the
            \* proposal's dependencyIndex, update the committedIndex and appliedIndex
            \* and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].committedIndex = proposal[t][i].dependencyIndex
               /\ configuration[t].appliedIndex = proposal[t][i].dependencyIndex
               /\ configuration' = [configuration EXCEPT ![t].committedIndex = i,
                                                         ![t].appliedIndex   = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Complete]]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<transaction, mastership>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].status # Complete
         /\ configuration' = [configuration EXCEPT ![t].status = Complete]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ \/ mastership[t].term > configuration[t].configTerm
            \/ /\ mastership[t].term = configuration[t].configTerm
               /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].configTerm = mastership[t].term,
                                                   ![t].status     = Pending]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].status = Pending
         /\ mastership[t].term = configuration[t].configTerm
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].appliedValues]
         /\ configuration' = [configuration EXCEPT ![t].appliedTerm = mastership[t].term,
                                                   ![t].status      = Complete]
   /\ UNCHANGED <<proposal, transaction, mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = <<>>
   /\ proposal = [t \in DOMAIN Target |->
                     [p \in {} |-> [phase  |-> Initialize,
                                    status |-> Pending]]]
   /\ configuration = [t \in DOMAIN Target |-> 
                           [target |-> t,
                            status |-> Pending,
                            values |-> 
                               [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]],
                            configIndex    |-> 0,
                            configTerm     |-> 0,
                            proposedIndex  |-> 0,
                            committedIndex |-> 0,
                            appliedIndex   |-> 0,
                            appliedTerm    |-> 0,
                            appliedValues  |->
                               [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]]]]
   /\ target = [t \in DOMAIN Target |-> 
                    [path \in {} |-> 
                        [value |-> Nil]]]
   /\ mastership = [t \in DOMAIN Target |-> [master |-> Nil, term |-> 0]]

Next ==
   \/ \E c \in ValidChanges : 
         RequestChange(c)
   \/ \E t \in DOMAIN transaction :
         RequestRollback(t)
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

Spec == Init /\ [][Next]_vars

Order ==
   /\ \A i, j \in DOMAIN transaction :
         \/ j <= i
         \/ Phase[transaction[i].phase] >= Phase[transaction[j].phase]
         \/ transaction[i].targets \cap transaction[j].targets = {}
         \/ transaction[j].status \in {Pending, Failed}
   /\ \A t \in DOMAIN proposal :
         \A i, j \in DOMAIN proposal[t] :
            \/ j <= i
            \/ Phase[proposal[t][i].phase] >= Phase[proposal[t][j].phase]
            \/ proposal[t][j].status \in {Pending, Failed}

Consistency == 
   \A t \in DOMAIN target :
      LET 
          \* Compute the transaction indexes that have been applied to the target
          appliedIndexes == {i \in DOMAIN transaction : 
                               /\ transaction[i].type = Change 
                               /\ i \in DOMAIN proposal[t]
                               /\ proposal[t][i].phase = Apply
                               /\ proposal[t][i].status = Complete
                               /\ t \in DOMAIN transaction[i].values
                               /\ ~\E j \in DOMAIN transaction :
                                     /\ j > i
                                     /\ transaction[j].type = Rollback
                                     /\ transaction[j].rollback = i
                                     /\ transaction[j].phase = Apply
                                     /\ transaction[j].status = Complete}
          \* Compute the set of paths in the target that have been updated by transactions
          appliedPaths   == UNION {DOMAIN transaction[i].values[t] : i \in appliedIndexes}
          \* Compute the highest index applied to the target for each path
          pathIndexes    == [p \in appliedPaths |-> CHOOSE i \in appliedIndexes : 
                                    \A j \in appliedIndexes :
                                          /\ i >= j 
                                          /\ p \in DOMAIN transaction[i].values[t]]
          \* Compute the expected target configuration based on the last indexes applied
          \* to the target for each path.
          expectedConfig == [p \in DOMAIN pathIndexes |-> transaction[pathIndexes[p]].values[t][p]]
      IN 
          target[t] = expectedConfig

Isolation ==
   \A i, j \in DOMAIN transaction :
         \/ j <= i
         \/ transaction[i].targets \cap transaction[j].targets = {}
         \/ transaction[i].isolation # Serializable
         \/ /\ \/ /\ transaction[i].phase \in {Commit, Abort}
                  /\ transaction[i].status \in {Complete, Failed}
               \/ Phase[transaction[i].phase] > Phase[Commit]
               \/ Phase[transaction[j].phase] < Phase[Commit]
            /\ \/ /\ transaction[i].phase \in {Apply, Abort}
                  /\ transaction[i].status \in {Complete, Failed}
               \/ Phase[transaction[j].phase] < Phase[Apply]
         \/ transaction[j].status = Failed

THEOREM Safety == Spec => [](Order /\ Consistency /\ Isolation)

Completion == 
   /\ \A i \in DOMAIN transaction : 
         /\ transaction[i].phase = Commit
         /\ transaction[i].status \in {Complete, Failed}
   /\ \A i \in DOMAIN transaction : 
         /\ transaction[i].phase = Apply
         /\ transaction[i].status \in {Complete, Failed}
   /\ \A t \in DOMAIN proposal :
         \A i \in DOMAIN proposal[t] :
            /\ proposal[t][i].phase = Commit
            /\ proposal[t][i].status \in {Complete, Failed}
   /\ \A t \in DOMAIN proposal :
         \A i \in DOMAIN proposal[t] :
            /\ proposal[t][i].phase = Apply
            /\ proposal[t][i].status \in {Complete, Failed}

THEOREM Liveness == Spec => <>Completion

----

(*
Type assumptions.
*)

ASSUME Nil \in STRING

ASSUME \A phase \in DOMAIN Phase : phase \in STRING

ASSUME \A status \in DOMAIN Status : status \in STRING

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
\* Last modified Mon Feb 07 14:58:32 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
