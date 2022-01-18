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

vars == <<transaction, configuration, targets>>

----

ChangeMaster(n, t) ==
   /\ masters[t].master # n
   /\ masters' = [masters EXCEPT ![t].term   = masters[t].term + 1,
                                 ![t].master = n]
   /\ UNCHANGED <<transaction, configuration>>

----

(*
This section models the northbound API for the configuration service.
*)

\* This crazy thing returns the set of all possible sets of valid changes
ValidChanges == 
   LET allPaths == UNION {(DOMAIN Target[t]) : t \in DOMAIN Target}
       allValues == UNION {UNION {Target[t][p] : p \in DOMAIN Target[t]} : t \in DOMAIN Target}
   IN
      {targetPathValues \in SUBSET (Target \X allPaths \X allValues \X BOOLEAN) :
         /\ \A target \in DOMAIN Target : 
            LET targetIndexes == {i \in 1..Len(targetPathValues) : /\ targetPathValues[i][1] = target}
            IN \/ Cardinality(targetIndexes) = 0
               \/ /\ Cardinality(targetIndexes) = 1
                  /\ LET targetPathValue == targetPathValues[CHOOSE index \in targetIndexes : TRUE]
                         targetPath      == targetPathValue[2]
                         targetValue     == targetPathValue[3]
                     IN
                        /\ targetPath \ (DOMAIN Target[target]) = {}
                        /\ targetValue \in Target[target][targetPath]}

NextIndex ==
   IF Len(transaction) = 0 THEN
      1
   ELSE
      (CHOOSE i \in DOMAIN transaction : 
          \A j \in DOMAIN transaction : 
              transaction[j].index < transaction[i].index) + 1

\* Add a set of changes to the transaction log
Change ==
   /\ \E changes \in ValidChanges :
      /\ transaction' = Append(transaction, [index   |-> NextIndex,
                                             atomic  |-> FALSE,
                                             sync    |-> FALSE,
                                             changes |-> changes,
                                             status  |-> TransactionPending])
   /\ UNCHANGED <<configuration, targets>>

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
         /\ UNCHANGED <<configuration>>
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
         /\ UNCHANGED <<configuration>>
      \* If the transaction is in the Applying state, update the Configuration for each
      \* target and Complete the transaction.
      \/ /\ transaction[t].status = TransactionApplying
         /\ \/ /\ transaction[t].atomic
               \* TODO: Apply atomic transactions here
               /\ transaction' = [transaction EXCEPT ![t].status = TransactionComplete]
               /\ UNCHANGED <<configuration>>
            \/ /\ ~transaction[t].atomic
               \* Add the transaction index to each updated path
               /\ configuration' = [
                     r \in DOMAIN Target |-> [
                        configuration[r] EXCEPT 
                           !.paths = [path \in DOMAIN transaction[t].changes |-> 
                              transaction[t].changes[path] @@ [index |-> transaction[t].index]] 
                                 @@ configuration[t].paths,
                           !.txIndex = transaction[t].index,
                           !.status  = ConfigurationPending]]
               /\ transaction' = [transaction EXCEPT ![t].status = TransactionComplete]
   /\ UNCHANGED <<targets>>

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
            \* If the configuration is marked ConfigurationPending and the values have
            \* changed (determined by comparing the transaction index to the last sync 
            \* index), mark the configuration ConfigurationUpdating to push the changes
            \* to the target.
            \/ /\ configuration[c].syncIndex < configuration[c].txIndex
               /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationUpdating]
      \/ /\ configuration[c].status = ConfigurationInitializing
         /\ masters[configuration[c].target].master = n
         \* Merge the configuration paths with the target paths, removing paths 
         \* that have been marked deleted
         /\ LET deletePaths == {p \in DOMAIN configuration[c].paths : configuration[c].paths[p].deleted}
                configPaths == DOMAIN c.paths \ deletePaths
                targetPaths == DOMAIN targets[configuration[c].target] \ deletePaths
            IN
               /\ targets' = [targets EXCEPT ![configuration[c].target] = 
                     [p \in configPaths |-> [value |-> configuration[c].paths[p]]] 
                        @@ [p \in targetPaths |-> targets[configuration[c].target][p]]]
               \* Set the configuration's status to Complete
         /\ configuration' = [configuration EXCEPT ![c].status    = ConfigurationComplete,
                                                   ![c].syncIndex = configuration[c].txIndex]
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
      \* If the configuration is not already ConfigurationPending and mastership
      \* has been lost revert it. This can occur when the connection to the
      \* target has been lost and the mastership is no longer valid.
      \* TODO: We still need to model mastership changes
      \/ /\ c.status # ConfigurationPending
         /\ masters[configuration[c].target].master = Nil
         /\ configuration' = [configuration EXCEPT ![c].status = ConfigurationPending]
   /\ UNCHANGED <<transaction>>

----

(*
Init and next state predicates
*)

Init ==
   /\ transaction = <<>>
   /\ configuration = [t \in Target |-> 
                           [id     |-> t,
                            config |-> 
                               [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]]]]
   /\ targets = [t \in Target |-> 
                    [path \in {} |-> 
                        [value |-> Nil]]]
   /\ masters = [t \in Target |-> [master |-> Nil, term |-> 0]]

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

=============================================================================
\* Modification History
\* Last modified Tue Jan 18 00:24:57 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
