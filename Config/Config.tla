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
   TransactionChange,
   TransactionRollback

\* Transaction isolation constants
CONSTANTS
   IsolationDefault,
   IsolationSerializable

\* Transaction status constants
CONSTANTS 
   TransactionInitializing,
   TransactionInitialized,
   TransactionValidating,
   TransactionValidated,
   TransactionCommitting,
   TransactionCommitted,
   TransactionApplying,
   TransactionApplied,
   TransactionFailed

TransactionStatus == 
   <<TransactionInitializing,
     TransactionInitialized,
     TransactionValidating,
     TransactionValidated,
     TransactionCommitting,
     TransactionCommitted,
     TransactionApplying,
     TransactionApplied,
     TransactionFailed>>

\* Proposal type constants
CONSTANTS
   ProposalChange,
   ProposalRollback

\* Proposal status constants
CONSTANTS 
   ProposalInitializing,
   ProposalInitialized,
   ProposalValidating,
   ProposalValidated,
   ProposalCommitting,
   ProposalCommitted,
   ProposalApplying,
   ProposalApplied,
   ProposalFailed

ProposalStatus == 
   <<ProposalInitializing,
     ProposalInitialized,
     ProposalValidating,
     ProposalValidated,
     ProposalCommitting,
     ProposalCommitted,
     ProposalApplying,
     ProposalApplied,
     ProposalFailed>>

\* Configuration status constants
CONSTANTS 
   ConfigurationUnknown,
   ConfigurationSynchronizing,
   ConfigurationSynchronized,
   ConfigurationPersisted,
   ConfigurationFailed

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

Phase(S, s) == CHOOSE i \in DOMAIN S : S[i] = s

TransactionPhase(s) == Phase(TransactionStatus, s)

ProposalPhase(s) == Phase(ProposalStatus, s)

ASSUME Nil \in STRING

ASSUME TransactionInitializing \in STRING
ASSUME TransactionInitialized \in STRING
ASSUME TransactionValidating \in STRING
ASSUME TransactionValidated \in STRING
ASSUME TransactionCommitting \in STRING
ASSUME TransactionCommitted \in STRING
ASSUME TransactionApplying \in STRING
ASSUME TransactionApplied \in STRING
ASSUME TransactionFailed \in STRING

ASSUME ProposalInitializing \in STRING
ASSUME ProposalInitialized \in STRING
ASSUME ProposalValidating \in STRING
ASSUME ProposalValidated \in STRING
ASSUME ProposalCommitting \in STRING
ASSUME ProposalCommitted \in STRING
ASSUME ProposalApplying \in STRING
ASSUME ProposalApplied \in STRING
ASSUME ProposalFailed \in STRING

ASSUME ConfigurationUnknown \in STRING
ASSUME ConfigurationSynchronizing \in STRING
ASSUME ConfigurationSynchronized \in STRING
ASSUME ConfigurationPersisted \in STRING
ASSUME ConfigurationFailed \in STRING

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

   TYPE TransactionType ::= type \in
      {TransactionChange,
       TransactionRollback}

   TYPE TransactionStatus ::= status \in 
      {TransactionInitializing,
       TransactionInitialized,
       TransactionValidating,
       TransactionValidated,
       TransactionCommitting,
       TransactionCommitted,
       TransactionApplying,
       TransactionApplied,
       TransactionFailed}

   TYPE Transaction == [
      type      ::= type \in TransactionType,
      index     ::= index \in Nat,
      isolation ::= isolation \in {IsolationDefault, IsolationSerializable}
      values    ::= [
         target \in SUBSET (DOMAIN Target) |-> [
            path \in SUBSET (DOMAIN Target[target].values) |-> [
               value  ::= value \in STRING, 
               delete ::= delete \in BOOLEAN]]],
      rollback  ::= index \in Nat,
      targets   ::= targets \in SUBSET (DOMAIN Target)
      status    ::= status \in TransactionStatus]
   
   TYPE ProposalStatus ::= status \in 
      {ProposalInitializing,
       ProposalInitialized,
       ProposalValidating,
       ProposalValidated,
       ProposalCommitting,
       ProposalCommitted,
       ProposalApplying,
       ProposalApplied,
       ProposalFailed}

   TYPE Proposal == [
      index          ::= index \in Nat,
      values         ::= [
         path \in SUBSET (DOMAIN Target[target].values) |-> [
            value  ::= value \in STRING, 
            delete ::= delete \in BOOLEAN]],
      rollback       ::= index \in Nat,
      prevIndex      ::= prevIndex \in Nat,
      nextIndex      ::= nextIndex \in Nat,
      rollbackIndex  ::= rollbackIndex \in Nat,
      rollbackValues ::= [
         path \in SUBSET (DOMAIN Target[target].values) |-> [
            value  ::= value \in STRING, 
            delete ::= delete \in BOOLEAN]],
      status       ::= status \in ProposalStatus]
   
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
      status    ::= status \in ConfigurationStatus]
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
Change(c) ==
   /\ \E isolation \in {IsolationDefault, IsolationSerializable} :
         /\ transaction' = transaction @@ (NextIndex :> [type      |-> TransactionChange,
                                                         index     |-> NextIndex,
                                                         isolation |-> isolation,
                                                         values    |-> c,
                                                         targets   |-> {},
                                                         status    |-> TransactionInitializing])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

\* Add a rollback of transaction 't' to the transaction log
Rollback(t) ==
   /\ \E isolation \in {IsolationDefault, IsolationSerializable} :
         /\ transaction' = transaction @@ (NextIndex :> [type      |-> TransactionRollback,
                                                         index     |-> NextIndex,
                                                         isolation |-> isolation,
                                                         rollback  |-> t,
                                                         targets   |-> {},
                                                         status    |-> TransactionInitializing])
   /\ UNCHANGED <<proposal, configuration, mastership, target>>

----

(*
This section models the Transaction log reconciler.

Transactions come in two flavors:
- Change transactions contain a set of changes to be applied to a set 
of targets
- Rollback transactions reference a prior change transaction to be
reverted to the previous state

Both types of transaction are reconciled in stages:
* Pending - waiting for prior transactions to complete
* Validating - validating the requested changes
* Applying - applying the changes to target configurations
* Complete - completed applying changes successfully
* Failed - failed applying changes
*)

\* Reconcile a transaction
ReconcileTransaction(n, i) ==
   /\ \/ /\ transaction[i].status = TransactionInitializing
         /\ i-1 \in DOMAIN transaction => 
               TransactionPhase(transaction[i-1].status) > TransactionPhase(TransactionInitializing)
         /\ \/ /\ transaction[i].targets = {}
               /\ \/ /\ transaction[i].type = TransactionChange
                     /\ transaction' = [transaction EXCEPT ![i].targets = DOMAIN transaction[i].values]
                     /\ proposal' = [t \in DOMAIN proposal |-> 
                           IF t \in DOMAIN transaction[i].values THEN
                              proposal[t] @@ (i :> [type           |-> ProposalChange,
                                                    index          |-> i,
                                                    values         |-> transaction[i].values[t],
                                                    prevIndex      |-> 0,
                                                    nextIndex      |-> 0,
                                                    rollbackIndex  |-> 0,
                                                    rollbackValues |-> <<>>,
                                                    status |-> ProposalInitializing])
                           ELSE
                              proposal[t]]
                  \/ /\ transaction[i].type = TransactionRollback
                     /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                           /\ transaction[transaction[i].rollback].type = TransactionChange
                           /\ transaction' = [transaction EXCEPT ![i].targets = 
                                                DOMAIN transaction[transaction[i].rollback].values]
                           /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in DOMAIN transaction[transaction[i].rollback].values THEN
                                    proposal[t] @@ (i :> [type           |-> ProposalRollback,
                                                          index          |-> i,
                                                          rollback       |-> transaction[i].rollback,
                                                          prevIndex      |-> 0,
                                                          nextIndex      |-> 0,
                                                          rollbackIndex  |-> 0,
                                                          rollbackValues |-> <<>>,
                                                          status         |-> ProposalInitializing])
                                 ELSE
                                    proposal[t]]
                        \/ /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                                 /\ transaction[transaction[i].rollback].type = TransactionRollback
                              \/ transaction[i].rollback \notin DOMAIN transaction
                           /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
                           /\ UNCHANGED <<proposal>>
            \/ /\ transaction[i].targets # {}
               /\ \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = ProposalInitialized
                     /\ transaction' = [transaction EXCEPT ![i].status = TransactionInitialized]
                     /\ UNCHANGED <<proposal>>
                  \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = ProposalFailed
                     /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
                     /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionInitialized
         /\ \A t \in transaction[i].targets :
               proposal[t][i].prevIndex # 0 =>
                  (transaction[proposal[t][i].prevIndex].isolation = IsolationSerializable =>
                     TransactionPhase(transaction[proposal[t][i].prevIndex].status) >= 
                        TransactionPhase(TransactionValidated))
         /\ transaction' = [transaction EXCEPT ![i].status = TransactionValidating]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionValidating
         /\ \/ /\ \E t \in transaction[i].targets : 
                     ProposalPhase(proposal[t][i].status) < ProposalPhase(ProposalValidating)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = ProposalValidating]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = ProposalValidated
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionValidated]
               /\ UNCHANGED <<proposal>>
            \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = ProposalFailed
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionValidated
         /\ \A t \in transaction[i].targets :
               proposal[t][i].prevIndex # 0 =>
                  (transaction[proposal[t][i].prevIndex].isolation = IsolationSerializable =>
                     TransactionPhase(transaction[proposal[t][i].prevIndex].status) >= 
                        TransactionPhase(TransactionCommitted))
         /\ transaction' = [transaction EXCEPT ![i].status = TransactionCommitting]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionCommitting
         /\ \/ /\ \E t \in transaction[i].targets : 
                     ProposalPhase(proposal[t][i].status) < ProposalPhase(ProposalCommitting)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = ProposalCommitting]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = ProposalCommitted
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionCommitted]
               /\ UNCHANGED <<proposal>>
            \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = ProposalFailed
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionCommitted
         /\ \A t \in transaction[i].targets :
               proposal[t][i].prevIndex # 0 =>
                  (transaction[proposal[t][i].prevIndex].isolation = IsolationSerializable =>
                     TransactionPhase(transaction[proposal[t][i].prevIndex].status) >= 
                        TransactionPhase(TransactionApplied))
         /\ transaction' = [transaction EXCEPT ![i].status = TransactionApplying]
         /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionApplying
         /\ \/ /\ \E t \in transaction[i].targets : 
                     ProposalPhase(proposal[t][i].status) < ProposalPhase(ProposalApplying)
               /\ proposal' = [t \in DOMAIN proposal |-> 
                                 IF t \in transaction[i].targets THEN
                                    [proposal[t] EXCEPT ![i].status = ProposalApplying]
                                 ELSE
                                    proposal[t]]
               /\ UNCHANGED <<transaction>>
            \/ /\ \A t \in transaction[i].targets : proposal[t][i].status = ProposalApplied
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionApplied]
               /\ UNCHANGED <<proposal>>
            \/ /\ \E t \in transaction[i].targets : proposal[t][i].status = ProposalFailed
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
               /\ UNCHANGED <<proposal>>
      \/ /\ transaction[i].status = TransactionApplied
   /\ UNCHANGED <<configuration, mastership, target>>

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].status = ProposalInitializing
         /\ \/ /\ configuration[t].proposedIndex > 0
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT 
                                 ![i] = [status    |-> ProposalInitialized, 
                                         prevIndex |-> configuration[t].proposedIndex] @@ proposal[t][i],
                                 ![configuration[t].proposedIndex] = [nextIndex |-> i] @@ 
                                       proposal[t][configuration[t].proposedIndex]]]
            \/ /\ configuration[t].proposedIndex = 0
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = ProposalInitialized]]
         /\ configuration' = [configuration EXCEPT ![t].proposedIndex = i]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].status = ProposalValidating
         /\ configuration[t].committedIndex = proposal[t][i].prevIndex
         /\ \/ /\ proposal[t][i].type = ProposalChange
               /\ LET rollbackIndex == configuration[t].configIndex
                      rollbackValues == [p \in DOMAIN proposal[t][i].values |-> [
                                           p |-> IF p \in DOMAIN configuration[t].config THEN
                                                    configuration[t].values[p]
                                                 ELSE
                                                    [delete |-> TRUE]]]
                  IN \E r \in {Valid, Invalid} :
                        \/ /\ r = Valid
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].rollbackIndex  = rollbackIndex,
                                                                ![i].rollbackValues = rollbackValues,
                                                                ![i].status         = ProposalValidated]]
                        \/ /\ r = Invalid
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].status = ProposalFailed]]
            \/ /\ proposal[t][i].type = ProposalRollback
               /\ \/ /\ configuration[t].index = proposal[t][i].rollback
                     /\ \/ /\ proposal[t][proposal[t][i].rollback].type = ProposalChange
                           /\ LET rollbackIndex == proposal[t][proposal[t][i].rollback].rollbackIndex
                                  rollbackValues == proposal[t][proposal[t][i].rollback].rollbackValues
                              IN \E r \in {Valid, Invalid} :
                                    \/ /\ r = Valid
                                       /\ proposal' = [proposal EXCEPT ![t] = [
                                             proposal[t] EXCEPT ![i].rollbackIndex  = rollbackIndex,
                                                                ![i].rollbackValues = rollbackValues,
                                                                ![i].status         = ProposalValidated]]
                                    \/ /\ r = Invalid
                                       /\ proposal' = [proposal EXCEPT ![t] = [
                                                         proposal[t] EXCEPT ![i].status = ProposalFailed]]
                        \/ /\ proposal[t][proposal[t][i].rollabck].type = ProposalRollback
                           /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
                           /\ proposal' = [proposal EXCEPT ![t] = [
                                 proposal[t] EXCEPT ![i].status = ProposalFailed]]
                  \/ /\ configuration[t].index # proposal[t][i].rollback
                     /\ configuration' = [configuration EXCEPT ![t].committedIndex = i]
                     /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = ProposalFailed]]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].status = ProposalCommitting
         /\ configuration[t].committedIndex = proposal[t][i].prevIndex
         /\ \/ /\ proposal[t][i].type = ProposalChange
               /\ configuration' = [configuration EXCEPT ![t].values         = proposal[t][i].values,
                                                         ![t].configIndex    = i,
                                                         ![t].committedIndex = i]
            \/ /\ proposal[t][i].type = ProposalRollback
               /\ configuration' = [configuration EXCEPT ![t].values         = proposal[t][i].rollbackValues,
                                                         ![t].configIndex    = proposal[t][i].rollbackIndex,
                                                         ![t].committedIndex = i]
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = ProposalCommitted]]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].status = ProposalApplying
         /\ configuration[t].appliedIndex = proposal[t][i].prevIndex
         /\ configuration[t].appliedTerm = mastership[t].term
         /\ mastership[t].master = n
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                  /\ target' = [target EXCEPT ![t] = proposal[t][i].values @@ target[t]]
                  /\ configuration' = [configuration EXCEPT 
                        ![t].appliedIndex = i,
                        ![t].appliedValues = proposal[t][i].values @@ configuration[i].appliedValues]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = ProposalApplied]]
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT ![t].appliedIndex = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].status = ProposalFailed]]
   /\ UNCHANGED <<transaction, mastership>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].status # ConfigurationPersisted
         /\ configuration' = [configuration EXCEPT ![t].status = ConfigurationPersisted]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ mastership[t].term > configuration[t].configTerm
         /\ configuration' = [configuration EXCEPT ![t].configTerm = mastership[t].term,
                                                   ![t].status     = ConfigurationSynchronizing]                                          
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ configuration[t].status # ConfigurationUnknown
         /\ mastership[t].term = configuration[t].configTerm
         /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].status = ConfigurationUnknown]                                        
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].status = ConfigurationSynchronizing
         /\ mastership[t].term = configuration[t].configTerm
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].values]
         /\ configuration' = [configuration EXCEPT ![t].appliedTerm = mastership[t].term,
                                                   ![t].status      = ConfigurationSynchronized]
   /\ UNCHANGED <<proposal, transaction, mastership>>

----

(*
Init and next state predicates
*)

Init ==
   /\ transaction = <<>>
   /\ proposal = [t \in DOMAIN Target |->
                     [p \in {} |-> [status |-> ProposalInitializing]]]
   /\ configuration = [t \in DOMAIN Target |-> 
                           [target |-> t,
                            status |-> ConfigurationUnknown,
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
         Change(c)
   \/ \E t \in DOMAIN transaction :
         Rollback(t)
   \/ \E n \in Node :
         \E t \in DOMAIN Target :
            SetMaster(n, t)
   \/ \E t \in DOMAIN Target :
         UnsetMaster(t)
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

Order == TRUE \* TODO redefine order spec

THEOREM Safety == Spec => []Order

Completion == \A i \in DOMAIN transaction : 
                 transaction[i].status \in {TransactionApplied, TransactionFailed}

THEOREM Liveness == Spec => <>Completion

=============================================================================
\* Modification History
\* Last modified Sun Feb 06 02:16:54 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
