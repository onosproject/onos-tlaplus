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

\* Status constants
CONSTANTS 
   Pending,
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
   Failed

Status == 
   <<Initializing,
     Initialized,
     Validating,
     Validated,
     Committing,
     Committed,
     Applying,
     Applied,
     Failed>>

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

Phase(s) == CHOOSE i \in DOMAIN Status : Status[i] = s

ASSUME Nil \in STRING

ASSUME Pending \in STRING
ASSUME Initializing \in STRING
ASSUME Initialized \in STRING
ASSUME Validating \in STRING
ASSUME Validated \in STRING
ASSUME Committing \in STRING
ASSUME Committed \in STRING
ASSUME Applying \in STRING
ASSUME Applied \in STRING
ASSUME Synchronizing \in STRING
ASSUME Synchronized \in STRING
ASSUME Persisted \in STRING
ASSUME Failed \in STRING

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
      status       ::= status \in Status]
   
   TYPE ConfigurationStatus ::= status \in 
      {ConfigurationUnknown,
       ConfigurationSynchronizing,
       ConfigurationSynchronized,
       ConfigurationPersisted,
       ConfigurationFailed}
   
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
                                                         status    |-> Initializing])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(t) ==
   /\ \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (NextIndex :> [type      |-> Rollback,
                                                         index     |-> NextIndex,
                                                         isolation |-> isolation,
                                                         rollback  |-> t,
                                                         targets   |-> {},
                                                         status    |-> Initializing])
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
      \* Initializing is the only transaction phase that's globally serialized.
      \* While in the Initializing phase, the reconciler checks whether the
      \* prior transaction has been Initialized before creating Proposals in
      \* the Initialize phase. Once all of the transaction's proposals have
      \* been Initialized, the transaction will be marked Initialized. If any
      \* proposal is Failed, the transaction will be marked Failed as well.
   /\ \/ /\ transaction[i].status = Initializing
         \* Serialize transaction initialization
         /\ i-1 \in DOMAIN transaction => 
               Phase(transaction[i-1].status) > Phase(Initializing)
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
                                                    status |-> Initializing])
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
                                                          status          |-> Initializing])
                                 ELSE
                                    proposal[t]]
                        \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                 /\ transaction[transaction[i].rollback].type = Rollback
                              \/ transaction[i].rollback \notin DOMAIN transaction
                           /\ transaction' = [transaction EXCEPT ![i].status = Failed]
                           /\ UNCHANGED <<proposal>>                     
            \/ /\ transaction[i].targets # {}
                  \* If all proposals have been Initialized, mark the transaction Initialized.
               /\ \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = Initialized
                     /\ transaction' = [transaction EXCEPT ![i].status = Initialized]
                     /\ UNCHANGED <<proposal>>
                  \* If any proposal has been Failed, mark the transaction Failed.
                  \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = Failed
                     /\ transaction' = [transaction EXCEPT ![i].status = Failed]
                     /\ UNCHANGED <<proposal>>
      \* Once the transaction has been Initialized, proceed to the Validate phase.
      \* If any of the transaction's proposals depend on a Serializable transaction,
      \* verify the dependency has been Validated to preserve serializability before 
      \* moving the transaction to the Validate phase.
      \/ /\ transaction[i].status = Initialized
         /\ \A t \in transaction[i].targets :
               proposal[t][i].dependencyIndex # 0 =>
                  (transaction[proposal[t][i].dependencyIndex].isolation = Serializable =>
                     Phase(transaction[proposal[t][i].dependencyIndex].status) >= Phase(Validated))
         /\ transaction' = [transaction EXCEPT ![i].status = Validating]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = Validating
            \* Move the transaction's proposals to the Validating state
         /\ \/ /\ \E t \in transaction[i].targets : Phase(proposal[t][i].status) < Phase(Validating)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = Validating]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Validated, mark the transaction Validated.
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = Validated
               /\ transaction' = [transaction EXCEPT ![i].status = Validated]
               /\ UNCHANGED <<proposal>>
            \* If any proposal has been Failed, mark the transaction Failed.
            \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = Failed
               /\ transaction' = [transaction EXCEPT ![i].status = Failed]
               /\ UNCHANGED <<proposal>>
      \* Once the transaction has been Validated, proceed to the Commit phase.
      \* If any of the transaction's proposals depend on a Serializable transaction,
      \* verify the dependency has been Committed to preserve serializability before 
      \* moving the transaction to the Commit phase.
      \/ /\ transaction[i].status = Validated
         /\ \A t \in transaction[i].targets :
               proposal[t][i].dependencyIndex # 0 =>
                  (transaction[proposal[t][i].dependencyIndex].isolation = Serializable =>
                     Phase(transaction[proposal[t][i].dependencyIndex].status) >= Phase(Committed))
         /\ transaction' = [transaction EXCEPT ![i].status = Committing]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = Committing
            \* Move the transaction's proposals to the Committing state
         /\ \/ /\ \E t \in transaction[i].targets : Phase(proposal[t][i].status) < Phase(Committing)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = Committing]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Committed, mark the transaction Committed.
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = Committed
               /\ transaction' = [transaction EXCEPT ![i].status = Committed]
               /\ UNCHANGED <<proposal>>
      \* Once the transaction has been Committed, proceed to the Apply phase.
      \* If any of the transaction's proposals depend on a Serializable transaction,
      \* verify the dependency has been Applied to preserve serializability before 
      \* moving the transaction to the Apply phase.
      \/ /\ transaction[i].status = Committed
         /\ \A t \in transaction[i].targets :
               proposal[t][i].dependencyIndex # 0 =>
                  (transaction[proposal[t][i].dependencyIndex].isolation = Serializable =>
                     Phase(transaction[proposal[t][i].dependencyIndex].status) >= Phase(Applied))
         /\ transaction' = [transaction EXCEPT ![i].status = Applying]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = Applying
            \* Move the transaction's proposals to the Applying state
         /\ \/ /\ \E t \in transaction[i].targets : Phase(proposal[t][i].status) < Phase(Applying)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = Applying]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \* If all proposals have been Applied, mark the transaction Applied.
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = Applied
               /\ transaction' = [transaction EXCEPT ![i].status = Applied]
               /\ UNCHANGED <<proposal>>
            \* If any proposal has been Failed, mark the transaction Failed.
            \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = Failed
               /\ transaction' = [transaction EXCEPT ![i].status = Failed]
               /\ UNCHANGED <<proposal>>
   /\ UNCHANGED <<configuration, mastership, target>>

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].status = Initializing
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT 
               ![i] = [status          |-> Initialized, 
                       dependencyIndex |-> configuration[t].proposedIndex] @@ proposal[t][i]]]
         /\ configuration' = [configuration EXCEPT ![t].proposedIndex = i]
         /\ UNCHANGED <<target>>
      \* While in the Validating state, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].status = Validating
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
                                                                ![i].status         = Validated]]
                           /\ UNCHANGED <<configuration>>
                        \/ /\ r = Invalid
                           /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
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
                                                                ![i].status         = Validated]]
                                       /\ UNCHANGED <<configuration>>
                                    \/ /\ r = Invalid
                                       /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
                                       /\ proposal' = [proposal EXCEPT ![t] = [
                                                         proposal[t] EXCEPT ![i].status = Failed]]
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration[t].configIndex # proposal[t][i].rollback
                           /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
                           /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Failed]]
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[t][proposal[t][i].rollback].type = Rollback
                     /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
                     /\ proposal' = [proposal EXCEPT ![t] = [
                           proposal[t] EXCEPT ![i].status = Failed]]
         /\ UNCHANGED <<target>>
      \* While in the Committing state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].status = Committing
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
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Committed]]
         /\ UNCHANGED <<target>>
      \* While in the Applying state, apply the proposed changes to the target.
      \/ /\ proposal[t][i].status = Applying
         /\ configuration[t].appliedIndex = proposal[t][i].dependencyIndex
         /\ configuration[t].appliedTerm = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                     \* If the proposal is a change, apply the change values to the target
                     \* and update the configuration's applied index and values.
                  /\ \/ /\ proposal[t][i].type = Change
                        /\ LET updatedPaths == {p \in DOMAIN proposal[t][i].values : 
                                                 ~proposal[t][i].values[p].delete}
                               unchangedPaths == (DOMAIN target[t]) \ (DOMAIN proposal[t][i].values)
                           IN
                              \* Update the target paths by adding/updating paths that have changed and
                              \* removing paths that are deleted by the change.
                              /\ target' = [target EXCEPT ![t] = 
                                    [p \in updatedPaths |-> proposal[t][i].values[p].value] 
                                       @@ [p \in unchangedPaths |-> target[t][p]]]
                        /\ configuration' = [configuration EXCEPT 
                              ![t].appliedIndex = i,
                              ![t].appliedValues = proposal[t][i].values @@ configuration[t].appliedValues]
                     \* If the proposal is a rollback, apply the rollback values and update the
                     \* configuration's applied values with the rolled back values.
                     \/ /\ proposal[t][i].type = Rollback
                        /\ LET updatedPaths == {p \in DOMAIN proposal[t][i].rollbackValues : 
                                                 ~proposal[t][i].rollbackValues[p].delete}
                               unchangedPaths == (DOMAIN target[t]) \ (DOMAIN proposal[t][i].rollbackValues)
                           IN
                              \* Update the target paths by adding/updating paths that have changed and
                              \* removing paths that are deleted by the change.
                              /\ target' = [target EXCEPT ![t] = 
                                    [p \in updatedPaths |-> proposal[t][i].rollbackValues[p].value] 
                                       @@ [p \in unchangedPaths |-> target[t][p]]]
                        /\ configuration' = [configuration EXCEPT 
                              ![t].appliedIndex  = i,
                              ![t].appliedValues = proposal[t][i].rollbackValues @@ configuration[t].appliedValues]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Applied]]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT ![t].appliedIndex = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = Failed]]
                  /\ UNCHANGED <<target>>
   /\ UNCHANGED <<transaction, mastership>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].status # Persisted
         /\ configuration' = [configuration EXCEPT ![t].status = Persisted]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ mastership[t].term > configuration[t].configTerm
         /\ configuration' = [configuration EXCEPT ![t].configTerm = mastership[t].term,
                                                   ![t].status     = Synchronizing]                                          
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ configuration[t].status # Pending
         /\ mastership[t].term = configuration[t].configTerm
         /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].status = Pending]                                        
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].status = Synchronizing
         /\ mastership[t].term = configuration[t].configTerm
         /\ mastership[t].master = n
         /\ LET setPaths == {p \in DOMAIN configuration[t].appliedValues : 
                   ~configuration[t].appliedValues[p].delete}
            IN
               /\ target' = [target EXCEPT ![t] = [
                     p \in setPaths |-> configuration[t].appliedValues[p].value]]
         /\ configuration' = [configuration EXCEPT ![t].appliedTerm = mastership[t].term,
                                                   ![t].status      = Synchronized]
   /\ UNCHANGED <<proposal, transaction, mastership>>

----

(*
Init and next state predicates
*)

Init ==
   /\ transaction = <<>>
   /\ proposal = [t \in DOMAIN Target |->
                     [p \in {} |-> [status |-> Initializing]]]
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

Isolation ==
   /\ \A i, j \in DOMAIN transaction :
            \/ j <= i
            \/ transaction[i].targets \cap transaction[j].targets = {}
            \/ transaction[i].isolation # Serializable
            \/ Phase(transaction[i].status) < Phase(Committed)
            \/ Phase(transaction[j].status) < Phase(Committing)

Order == TRUE \* TODO redefine order spec

THEOREM Safety == Spec => [](Order /\ Isolation)

Completion == \A i \in DOMAIN transaction : 
                 transaction[i].status \in {Applied, Failed}

THEOREM Liveness == Spec => <>Completion

=============================================================================
\* Modification History
\* Last modified Sun Feb 06 15:56:34 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
