------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

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
Target is the possible targets, paths, and values

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
   TYPE TransactionStatus ::= status \in 
      {TransactionPending, 
       TransactionValidating,
       TransactionApplying, 
       TransactionComplete, 
       TransactionFailed}

   TYPE Transaction == [ 
      id       ::= id \in STRING,
      index    ::= index \in Nat,
      revision ::= revision \in Nat,
      atomic   ::= atomic \in BOOLEAN,
      sync     ::= sync \in BOOLEAN,
      changes  ::= [
         target \in SUBSET (DOMAIN Target) |-> [
            path \in SUBSET (DOMAIN Target[target]) |-> [
               value  ::= value \in STRING, 
               delete ::= delete \in BOOLEAN]]],
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

\* A sequence of transactions
\* Each transactions contains a record of 'changes' for a set of targets
VARIABLE transaction

\* A record of target configurations
\* Each configuration represents the desired state of the target
VARIABLE configuration

\* A record of target states
VARIABLE targets

\* A record of target masters
VARIABLE masters

VARIABLE history

vars == <<transaction, configuration, masters, targets, history>>

----

ChangeMaster(n, t) ==
   /\ masters[t].master # n
   /\ masters' = [masters EXCEPT ![t].term   = masters[t].term + 1,
                                 ![t].master = n]
   /\ UNCHANGED <<transaction, configuration, targets, history>>

----

(*
This section models the northbound API for the configuration service.
*)

ValidValues(t, p) ==
   UNION {{[value |-> v, delete |-> FALSE] : v \in Target[t][p]}, {[value |-> Nil, delete |-> TRUE]}}

ValidPaths(t) ==
   UNION {{v @@ [path |-> p] : v \in ValidValues(t, p)} : p \in DOMAIN Target[t]}

ValidTargets ==
   UNION {{p @@ [target |-> t] : p \in ValidPaths(t)} : t \in DOMAIN Target}

ValidPath(s, t, p) ==
   LET value == CHOOSE v \in s : v.target = t /\ v.path = p
   IN
      [value  |-> value.value,
       delete |-> value.delete]

ValidTarget(s, t) ==
   [p \in {v.path : v \in {v \in s : v.target = t}} |-> ValidPath(s, t, p)]

ValidChange(s) ==
   [t \in {v.target : v \in s} |-> ValidTarget(s, t)]

ValidChanges == 
   LET changeSets == {s \in SUBSET ValidTargets :
                         \A t \in DOMAIN Target :
                            \A p \in DOMAIN Target[t] :
                               Cardinality({v \in s : v.target = t /\ v.path = p}) <= 1}
   IN
      {ValidChange(s) : s \in changeSets}
                                

NextIndex ==
   IF Len(transaction) = 0 THEN
      1
   ELSE
      LET i == CHOOSE i \in DOMAIN transaction : 
          \A j \in DOMAIN transaction : 
              transaction[j].index <= transaction[i].index
      IN transaction[i].index + 1

\* Add a set of changes to the transaction log
Change ==
   /\ \E changes \in ValidChanges :
      /\ transaction' = Append(transaction, [index   |-> NextIndex,
                                             atomic  |-> FALSE,
                                             sync    |-> FALSE,
                                             changes |-> changes,
                                             status  |-> TransactionPending])
   /\ UNCHANGED <<configuration, masters, targets, history>>

----

(*
This section models the Transaction log reconciler.
*)

\* Reconcile the transaction log
ReconcileTransaction(n, t) ==
      \* If the transaction is Pending, begin validation if the prior transaction
      \* has already been applied. This simplifies concurrency control in the controller
      \* and guarantees transactions are applied to the configurations in sequential order.
   /\ \/ /\ transaction[t].status = TransactionPending
         /\ \/ /\ transaction[t].index - 1 \in DOMAIN transaction
               /\ transaction[transaction[t].index - 1].status \in {TransactionComplete, TransactionFailed}
            \/ transaction[t].index - 1 \notin DOMAIN transaction
         /\ transaction' = [transaction EXCEPT ![t].status = TransactionValidating]
         /\ UNCHANGED <<configuration, history>>
      \* If the transaction is in the Validating state, compute and validate the 
      \* Configuration for each target. 
      \/ /\ transaction[t].status = TransactionValidating
         \* If validation fails any target, mark the transaction Failed. 
         \* If validation is successful, proceed to Applying.
         /\ \E valid \in BOOLEAN :
               \/ /\ valid
                  /\ transaction' = [transaction EXCEPT ![t].status = TransactionApplying]
               \/ /\ ~valid
                  /\ transaction' = [transaction EXCEPT ![t].status = TransactionFailed]
         /\ UNCHANGED <<configuration, history>>
      \* If the transaction is in the Applying state, update the Configuration for each
      \* target and Complete the transaction.
      \/ /\ transaction[t].status = TransactionApplying
         /\ \/ /\ transaction[t].atomic
               \* TODO: Apply atomic transactions here
               /\ transaction' = [transaction EXCEPT ![t].status = TransactionComplete]
               /\ UNCHANGED <<configuration, history>>
            \/ /\ ~transaction[t].atomic
               \* Add the transaction index to each updated path
               /\ configuration' = [
                     r \in DOMAIN Target |-> 
                        IF r \in DOMAIN transaction[t].changes THEN
                           [configuration[r] EXCEPT 
                              !.paths = [p \in DOMAIN transaction[t].changes[r] |-> 
                                           [index   |-> transaction[t].index,
                                            value   |-> transaction[t].changes[r][p].value,
                                            deleted |-> transaction[t].changes[r][p].delete]]
                                    @@ configuration[r].paths,
                              !.txIndex = transaction[t].index,
                              !.status  = ConfigurationPending]
                        ELSE
                           configuration[r]]
               /\ history' = [r \in DOMAIN Target |-> Append(history[r], configuration'[r])]
               /\ transaction' = [transaction EXCEPT ![t].status = TransactionComplete]
   /\ UNCHANGED <<masters, targets>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, c) ==
   /\ \/ /\ configuration[c].status = ConfigurationPending
            \* If the configuration is marked ConfigurationPending and mastership 
            \* has changed (indicated by an increased mastership term), mark the
            \* configuration ConfigurationInitializing to force full re-synchronization.
         /\ \/ /\ masters[configuration[c].target].term > configuration[c].term
               /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationInitializing,
                                                         ![c].term   = masters[configuration[c].target].term]
               /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
            \* If the configuration is marked ConfigurationPending and the values have
            \* changed (determined by comparing the transaction index to the last sync 
            \* index), mark the configuration ConfigurationUpdating to push the changes
            \* to the target.
            \/ /\ configuration[c].syncIndex < configuration[c].txIndex
               /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationUpdating]
               /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
         /\ UNCHANGED <<targets>>
      \/ /\ configuration[c].status = ConfigurationInitializing
         /\ masters[configuration[c].target].master = n
         \* Merge the configuration paths with the target paths, removing paths 
         \* that have been marked deleted
         /\ LET deletePaths == {p \in DOMAIN configuration[c].paths : configuration[c].paths[p].deleted}
                configPaths == DOMAIN configuration[c].paths \ deletePaths
                targetPaths == DOMAIN targets[configuration[c].target] \ deletePaths
            IN
               /\ targets' = [targets EXCEPT ![configuration[c].target] = 
                     [p \in configPaths |-> [value |-> configuration[c].paths[p]]] 
                        @@ [p \in targetPaths |-> targets[configuration[c].target][p]]]
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
         /\ masters[configuration[c].target].master = n
         \* Compute the set of updated and deleted paths by comparing
         \* their indexes to the target's last sync index.
         /\ LET updatePaths == {p \in DOMAIN configuration[c].paths :
                                    configuration[c].paths[p].index > configuration[c].syncIndex}
                deletePaths == {p \in updatePaths : configuration[c].paths[p].deleted}
                configPaths == updatePaths \ deletePaths
                targetPaths == DOMAIN targets[configuration[c].target] \ deletePaths
            IN
               \* Update the target paths by adding/updating paths that have changed and
               \* removing paths that have been deleted since the last sync.
               /\ targets' = [targets EXCEPT ![configuration[c].target] = 
                     [p \in configPaths |-> configuration[c].paths[p]] 
                        @@ [p \in targetPaths |-> targets[configuration[c].target][p]]]
         /\ configuration' = [configuration EXCEPT ![c].status    = ConfigurationComplete,
                                                   ![c].syncIndex = configuration[c].txIndex]
         /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
      \* If the configuration is not already ConfigurationPending and mastership
      \* has been lost revert it. This can occur when the connection to the
      \* target has been lost and the mastership is no longer valid.
      \* TODO: We still need to model mastership changes
      \/ /\ configuration[c].status # ConfigurationPending
         /\ masters[configuration[c].target].master = Nil
         /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationPending]
         /\ history' = [history EXCEPT ![c] = Append(history[c], configuration'[c])]
         /\ UNCHANGED <<targets>>
   /\ UNCHANGED <<transaction, masters>>

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
   /\ targets = [t \in DOMAIN Target |-> 
                    [path \in {} |-> 
                        [value |-> Nil]]]
   /\ masters = [t \in DOMAIN Target |-> [master |-> Nil, term |-> 0]]
   /\ history = [t \in DOMAIN Target |-> <<>>]

Next ==
   \/ Change
   \/ \E n \in Node :
         \/ \E t \in DOMAIN Target :
               ChangeMaster(n, t)
         \/ \E t \in DOMAIN transaction :
               ReconcileTransaction(n, t)
         \/ \E t \in DOMAIN configuration :
               ReconcileConfiguration(n, t)

Spec == Init /\ [][Next]_vars

Inv ==
   /\ \A a, b \in DOMAIN transaction :
         transaction[a].index > transaction[b].index =>
            (transaction[a].status \in {TransactionComplete, TransactionFailed} => 
               transaction[b].status \in {TransactionComplete, TransactionFailed})
   /\ \A t \in DOMAIN Target :
         \A c \in DOMAIN history[t] :
            /\ configuration[t].txIndex >= history[t][c].txIndex
            /\ configuration[t].syncIndex >= history[t][c].syncIndex

=============================================================================
\* Modification History
\* Last modified Tue Jan 18 12:23:05 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
