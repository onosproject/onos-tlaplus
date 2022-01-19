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

\* Transaction status constants
CONSTANTS 
   TransactionPending,
   TransactionValidating,
   TransactionApplying,
   TransactionComplete,
   TransactionFailed

\* Configuration status constants
CONSTANTS 
   ConfigurationPending,
   ConfigurationInitializing,
   ConfigurationUpdating,
   ConfigurationComplete,
   ConfigurationFailed

\* The set of all nodes
CONSTANT Node

(*
Target is the set of all targets and their possible paths and values.

Example:
   Target == [
      target1 |-> [
         path1 |-> {"value1", "value2"},
         path2 |-> {"value2", "value3"}],
      target2 |-> [
         path2 |-> {"value3", "value4"},
         path3 |-> {"value4", "value5"}]]
*)
CONSTANT Target

ASSUME Nil \in STRING

ASSUME TransactionPending \in STRING
ASSUME TransactionValidating \in STRING
ASSUME TransactionApplying \in STRING
ASSUME TransactionComplete \in STRING
ASSUME TransactionFailed \in STRING

ASSUME ConfigurationPending \in STRING
ASSUME ConfigurationInitializing \in STRING
ASSUME ConfigurationUpdating \in STRING
ASSUME ConfigurationComplete \in STRING
ASSUME ConfigurationFailed \in STRING

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \notin DOMAIN Target 
             /\ n \in STRING
             
ASSUME /\ \A t \in DOMAIN Target : 
             /\ t \notin Node 
             /\ t \in STRING
             /\ \A p \in DOMAIN Target[t] :
                   IsFiniteSet(Target[t][p])

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
      {TransactionPending, 
       TransactionValidating,
       TransactionApplying, 
       TransactionComplete, 
       TransactionFailed}

   TYPE Transaction == [
      type     ::= type \in TransactionType,
      index    ::= index \in Nat,
      revision ::= revision \in Nat,
      atomic   ::= atomic \in BOOLEAN,
      sync     ::= sync \in BOOLEAN,
      changes  ::= [
         target \in SUBSET (DOMAIN Target) |-> [
            path \in SUBSET (DOMAIN Target[target]) |-> [
               value  ::= value \in STRING, 
               delete ::= delete \in BOOLEAN]]],
      rollback ::= index \in Nat,
      sources  ::= 
         target \in SUBSET (DOMAIN Target) |-> [
            path \in SUBSET (DOMAIN Target[target]) |-> [
               value ::= value \in STRING,
               index ::= index \in Nat]]],
      status   ::= status \in TransactionStatus]
   
   TYPE ConfigurationStatus ::= status \in 
      {ConfigurationPending, 
       ConfigurationInitializing,
       ConfigurationUpdating, 
       ConfigurationComplete, 
       ConfigurationFailed}
   
   TYPE Configuration == [
      id       ::= id \in STRING,
      revision ::= revision \in Nat,
      target   ::= target \in STRING,
      paths    ::= [
         path \in SUBSET (DOMAIN Target[target]) |-> [
            value   ::= value \in STRING, 
            index   ::= index \in Nat,
            deleted ::= delete \in BOOLEAN]],
      txIndex   ::= txIndex \in Nat,
      syncIndex ::= syncIndex \in Nat,
      term      ::= term \in Nat,
      status    ::= status \in ConfigurationStatus]
*)

\* A transaction log. Transactions may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE transaction

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masters
VARIABLE master

\* A history variable tracking past configuration changes
VARIABLE history

vars == <<transaction, configuration, master, target, history>>

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
   /\ master[t].master # n
   /\ master' = [master EXCEPT ![t].term   = master[t].term + 1,
                               ![t].master = n]
   /\ UNCHANGED <<transaction, configuration, target, history>>

UnsetMaster(t) ==
   /\ master[t].master # Nil
   /\ master' = [master EXCEPT ![t].master = Nil]
   /\ UNCHANGED <<transaction, configuration, target, history>>

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
   UNION {{[value |-> v, delete |-> FALSE] : v \in Target[t][p]}, {[value |-> Nil, delete |-> TRUE]}}

ValidPaths(t) ==
   UNION {{v @@ [path |-> p] : v \in ValidValues(t, p)} : p \in DOMAIN Target[t]}

ValidTargets ==
   UNION {{p @@ [target |-> t] : p \in ValidPaths(t)} : t \in DOMAIN Target}

\* The set of all valid sets of changes to all targets and their paths. 
\* The set of possible changes is computed from the Target model value.
ValidChanges == 
   LET changeSets == {s \in SUBSET ValidTargets :
                         \A t \in DOMAIN Target :
                            \A p \in DOMAIN Target[t] :
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
   /\ transaction' = transaction @@ (NextIndex :> [type    |-> TransactionChange,
                                                   index   |-> NextIndex,
                                                   atomic  |-> FALSE,
                                                   sync    |-> FALSE,
                                                   changes |-> c,
                                                   sources |-> <<>>,
                                                   status  |-> TransactionPending])
   /\ UNCHANGED <<configuration, master, target, history>>

\* Add a rollback of transaction 't' to the transaction log
Rollback(t) ==
   /\ transaction[t].type = TransactionChange
   /\ transaction' = transaction @@ (NextIndex :> [type     |-> TransactionRollback,
                                                   index    |-> NextIndex,
                                                   atomic   |-> FALSE,
                                                   sync     |-> FALSE,
                                                   rollback |-> t,
                                                   status   |-> TransactionPending])
   /\ UNCHANGED <<configuration, master, target, history>>

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

\* Reconcile a change transaction
ReconcileChange(n, i) ==
   \* If the transaction is Pending, begin validation if the prior transaction
   \* has already been applied. This simplifies concurrency control in the controller
   \* and guarantees transactions are applied to the configurations in sequential order.
   \/ /\ transaction[i].status = TransactionPending
      /\ \/ /\ i - 1 \in DOMAIN transaction
            /\ transaction[i - 1].status \in {TransactionComplete, TransactionFailed}
         \/ i - 1 \notin DOMAIN transaction
      /\ transaction' = [transaction EXCEPT ![i].status = TransactionValidating]
      /\ UNCHANGED <<configuration, history>>
   \* If the transaction is in the Validating state, compute and validate the 
   \* Configuration for each target. 
   \/ /\ transaction[i].status = TransactionValidating
      \* If validation fails any target, mark the transaction Failed. 
      \* If validation is successful, proceed to Applying.
      /\ \E valid \in BOOLEAN :
            IF valid THEN
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionApplying]
            ELSE
               /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
      /\ UNCHANGED <<configuration, history>>
   \* If the transaction is in the Applying state, update the Configuration for each
   \* target and Complete the transaction.
   \/ /\ transaction[i].status = TransactionApplying
      \* Update the target configurations, adding the transaction index to each updated path
      /\ configuration' = [
            t \in DOMAIN Target |-> 
               IF t \in DOMAIN transaction[i].changes THEN
                  [configuration[t] EXCEPT 
                     !.paths = [p \in DOMAIN transaction[i].changes[t] |-> 
                                  [index   |-> transaction[i].index,
                                   value   |-> transaction[i].changes[t][p].value,
                                   deleted |-> transaction[i].changes[t][p].delete]]
                           @@ configuration[t].paths,
                     !.txIndex = transaction[i].index,
                     !.status  = ConfigurationPending]
               ELSE
                  configuration[t]]
      /\ history' = [r \in DOMAIN Target |-> Append(history[r], configuration'[r])]
      \* The transaction state is updated to include the source configuration modified.
      \* The source configuration is used to optimize rollbacks.
      \* Note that in a real-world implementation, the order of updates to the configuration
      \* and to add the source info to the transaction could have serious ramifications.
      \* If one is updated without the other, rollbacks may not be possible.
      /\ transaction' = [transaction EXCEPT 
            ![i].status  = TransactionComplete,
            ![i].sources = [t \in DOMAIN transaction[i].changes |->
               LET updatePaths == {p \in DOMAIN transaction[i].changes[t] : 
                                     ~transaction[i].changes[t][p].delete} 
               IN [p \in updatePaths \intersect DOMAIN configuration[t].paths |-> configuration[t].paths[p]]]]

\* Reconcile a rollback transaction
ReconcileRollback(n, i) ==
   \* If the transaction is Pending, begin validation if the prior transaction
   \* has already been applied. This simplifies concurrency control in the controller
   \* and guarantees transactions are applied to the configurations in sequential order.
   \/ /\ transaction[i].status = TransactionPending
      /\ \/ /\ i - 1 \in DOMAIN transaction
            /\ transaction[i - 1].status \in {TransactionComplete, TransactionFailed}
         \/ i - 1 \notin DOMAIN transaction
      /\ transaction' = [transaction EXCEPT ![i].status = TransactionValidating]
      /\ UNCHANGED <<configuration, history>>
   \* If the transaction is in the Validating state, validate the rollback.
   \* A transaction can only be rolled back if:
   \* 1. The source transaction is in the log
   \* 2. The source transaction was applied successfully (did not fail validation)
   \* 3. The source transaction is the most recent change for each path is modified
   \/ /\ transaction[i].status = TransactionValidating
      /\ \/ /\ transaction[transaction[i].rollback].status = TransactionComplete
            /\ \/ /\ transaction[i].rollback \in DOMAIN transaction
                  \* Determine whether the source transaction is the most recent change
                  \* by comparing the configuration path indexes to the transaction index.
                  /\ LET canRollback == \A t \in DOMAIN transaction[transaction[i].rollback].changes :
                                           \A p \in DOMAIN transaction[transaction[i].rollback].changes[t] :
                                              configuration[t].paths[p].index = transaction[i].rollback
                     IN
                        IF canRollback THEN
                           /\ transaction' = [transaction EXCEPT ![i].status = TransactionApplying]
                        ELSE
                           /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
               \* If the source transaction is not in the log, fail the rollback.
               \/ /\ transaction[i].rollback \notin DOMAIN transaction
                  /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
         \* If the source transaction failed, fail the rollback.
         \/ /\ transaction[transaction[i].rollback].status = TransactionFailed
            /\ transaction' = [transaction EXCEPT ![i].status = TransactionFailed]
      /\ UNCHANGED <<configuration, history>>
   \* If the transcation is in the Applying state, roll back the Configuration for
   \* each target and Complete the transaction.
   \/ /\ transaction[i].status = TransactionApplying
      \* Target configurations are rolled back by reverting to the source paths/values
      \* stored in the transaction when it was applied.
      /\ configuration' = [
            t \in DOMAIN Target |-> 
               IF t \in DOMAIN transaction[transaction[i].rollback].changes THEN
                  LET adds      == {p \in DOMAIN transaction[transaction[i].rollback].changes[t] : 
                                      /\ p \notin DOMAIN transaction[transaction[i].rollback].sources[t]
                                      /\ ~transaction[transaction[i].rollback].changes[t][p].delete}
                      updates   == {p \in DOMAIN transaction[transaction[i].rollback].changes[t] : 
                                      /\ p \in DOMAIN transaction[transaction[i].rollback].sources[t]
                                      /\ ~transaction[transaction[i].rollback].changes[t][p].delete}
                      removes   == {p \in DOMAIN transaction[transaction[i].rollback].changes[t] : 
                                      /\ p \in DOMAIN transaction[transaction[i].rollback].sources[t]
                                      /\ transaction[transaction[i].rollback].changes[t][p].delete}
                      changes   == adds \union updates \union removes
                      unchanges == DOMAIN configuration[t].paths \ changes
                  IN
                     [configuration[t] EXCEPT 
                        !.paths = [p \in unchanges |-> configuration[t].paths[p]]
                                     @@ [p \in updates \union removes |-> 
                                            transaction[transaction[i].rollback].sources[t][p]],
                        !.txIndex = transaction[i].index,
                        !.status  = ConfigurationPending]
               ELSE
                  configuration[t]]
      /\ history' = [r \in DOMAIN Target |-> Append(history[r], configuration'[r])]
      /\ transaction' = [transaction EXCEPT ![i].status = TransactionComplete]

\* Reconcile a transaction in the transaction log
\* Transactions can be of one of two types: Change and Rollback.
\* The logic for processing different types of transactions differs.
ReconcileTransaction(n, i) ==
   /\ \/ /\ transaction[i].type = TransactionChange
         /\ ReconcileChange(n, i)
      \/ /\ transaction[i].type = TransactionRollback
         /\ ReconcileRollback(n, i)
   /\ UNCHANGED <<master, target>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, c) ==
   /\ \/ /\ configuration[c].status = ConfigurationPending
         /\ master[configuration[c].target].master # Nil
            \* If the configuration is marked ConfigurationPending and mastership 
            \* has changed (indicated by an increased mastership term), mark the
            \* configuration ConfigurationInitializing to force full re-synchronization.
         /\ \/ /\ master[configuration[c].target].term > configuration[c].term
               /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationInitializing,
                                                         ![c].term   = master[configuration[c].target].term]
               /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
            \* If the configuration is marked ConfigurationPending and the values have
            \* changed (determined by comparing the transaction index to the last sync 
            \* index), mark the configuration ConfigurationUpdating to push the changes
            \* to the target.
            \/ /\ master[configuration[c].target].term = configuration[c].term
               /\ configuration[c].syncIndex < configuration[c].txIndex
               /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationUpdating]
               /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
         /\ UNCHANGED <<target>>
      \/ /\ configuration[c].status = ConfigurationInitializing
         /\ master[configuration[c].target].master = n
         \* Merge the configuration paths with the target paths, removing paths 
         \* that have been marked deleted
         /\ LET deletePaths == {p \in DOMAIN configuration[c].paths : configuration[c].paths[p].deleted}
                configPaths == DOMAIN configuration[c].paths \ deletePaths
                targetPaths == DOMAIN target[configuration[c].target] \ deletePaths
            IN
               /\ target' = [target EXCEPT ![configuration[c].target] = 
                     [p \in configPaths |-> [value |-> configuration[c].paths[p]]] 
                        @@ [p \in targetPaths |-> target[configuration[c].target][p]]]
               \* Set the configuration's status to Complete
         /\ configuration' = [configuration EXCEPT ![c].status    = ConfigurationComplete,
                                                   ![c].syncIndex = configuration[c].txIndex]
         /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
      \* If the configuration is marked ConfigurationUpdating, we only need to
      \* push paths that have changed since the target was initialized or last
      \* updated by the controller. The set of changes made since the last 
      \* synchronization are identified by comparing the index of each path-value
      \* to the last synchronization index, `syncIndex`.
      \/ /\ configuration[c].status = ConfigurationUpdating
         /\ master[configuration[c].target].master = n
         \* Compute the set of updated and deleted paths by comparing
         \* their indexes to the target's last sync index.
         /\ LET updatePaths == {p \in DOMAIN configuration[c].paths :
                                    configuration[c].paths[p].index > configuration[c].syncIndex}
                deletePaths == {p \in updatePaths : configuration[c].paths[p].deleted}
                configPaths == updatePaths \ deletePaths
                targetPaths == DOMAIN target[configuration[c].target] \ deletePaths
            IN
               \* Update the target paths by adding/updating paths that have changed and
               \* removing paths that have been deleted since the last sync.
               /\ target' = [target EXCEPT ![configuration[c].target] = 
                     [p \in configPaths |-> configuration[c].paths[p]] 
                        @@ [p \in targetPaths |-> target[configuration[c].target][p]]]
         /\ configuration' = [configuration EXCEPT ![c].status    = ConfigurationComplete,
                                                   ![c].syncIndex = configuration[c].txIndex]
         /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
      \* If the configuration is not already ConfigurationPending and mastership
      \* has been lost revert it. This can occur when the connection to the
      \* target has been lost and the mastership is no longer valid.
      \/ /\ configuration[c].status # ConfigurationPending
         /\ master[configuration[c].target].master = Nil
         /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationPending]
         /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<transaction, master>>

----

(*
Init and next state predicates
*)

Init ==
   /\ transaction = <<>>
   /\ configuration = [t \in DOMAIN Target |-> 
                           [target |-> t,
                            paths |-> 
                               [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]],
                            txIndex   |-> 0,
                            syncIndex |-> 0,
                            term      |-> 0,
                            status    |-> ConfigurationPending]]
   /\ target = [t \in DOMAIN Target |-> 
                    [path \in {} |-> 
                        [value |-> Nil]]]
   /\ master = [t \in DOMAIN Target |-> [master |-> Nil, term |-> 0]]
   /\ history = [t \in DOMAIN Target |-> <<>>]

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
         \E c \in DOMAIN configuration :
               ReconcileConfiguration(n, c)

Spec == Init /\ [][Next]_vars

Order ==
   /\ \A a, b \in DOMAIN transaction :
         transaction[a].index > transaction[b].index =>
            (transaction[a].status \in {TransactionComplete, TransactionFailed} => 
               transaction[b].status \in {TransactionComplete, TransactionFailed})
   /\ \A t \in DOMAIN Target :
         \A c \in DOMAIN history[t] :
            /\ configuration[t].txIndex >= history[t][c].txIndex
            /\ configuration[t].syncIndex >= history[t][c].syncIndex

THEOREM Safety == Spec => []Order

Completion == \A i \in DOMAIN transaction : 
                 transaction[i].status \in {TransactionComplete, TransactionFailed}

THEOREM Liveness == Spec => <>Completion

=============================================================================
\* Modification History
\* Last modified Wed Jan 19 00:12:18 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
