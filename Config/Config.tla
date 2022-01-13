------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Transaction constants
CONSTANTS 
   Pending,
   Validating,
   Applying,
   Complete,
   Failed

\* The set of all nodes
CONSTANT Node

\* The set of all targets
CONSTANT Target

\* The set of available paths
CONSTANT Path

\* The set of available values
CONSTANT Value

ASSUME Nil \in STRING

ASSUME Pending \in STRING
ASSUME Validating \in STRING
ASSUME Applying \in STRING
ASSUME Complete \in STRING
ASSUME Failed \in STRING

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \notin DOMAIN Target 
             /\ n \in STRING
             
ASSUME /\ \A t \in DOMAIN Target : 
             /\ IsFiniteSet(Target[t])
             /\ t \notin Node 
             /\ t \in STRING

----

(*
   TYPE Change == [ 
      target ::= target \in STRING,
      path   ::= path \in STRING, 
      value  ::= value \in STRING, 
      delete ::= delete \in BOOLEAN 
   ]

   TYPE State == state \in {Pending, Validating, Applying, Complete, Failed}

   TYPE Transaction == [ 
      id       ::= id \in STRING,
      index    ::= index \in Nat,
      revision ::= revision \in Nat,
      atomic   ::= atomic \in BOOLEAN,
      sync     ::= sync \in BOOLEAN,
      changes  ::= [i \in 1..Nat |-> changes[i] \in Change],
      status   ::= [state ::= state \in State]]
   
   TYPE Element == [
      path    ::= path \in STRING, 
      value   ::= value \in STRING, 
      index   ::= index \in Nat,
      deleted ::= deleted \in BOOLEAN]


   TYPE Configuration == [
      id       ::= id \in STRING,
      revision ::= revision \in Nat,
      target   ::= target \in STRING,
      elements ::= [i \in 1..Nat |-> elements[i] \in Element],
      status   ::= [
         transactionIndex ::= transactionIndex \in Nat,
         targetIndex      ::= targetIndex \in Nat,
         mastershipTerm   ::= mastershipTerm \in Nat]]
*)

\* A sequence of transactions
\* Each transactions contains a record of 'changes' for a set of targets
VARIABLE transactions

\* A record of target configurations
\* Each configuration represents the desired state of the target
VARIABLE configurations

\* A record of target states
VARIABLE targets

\* A record of target masters
VARIABLE masters

vars == <<transactions, configurations, targets>>

----

paths == Seq(Path)

values == Seq(Value)

----

(*
This section models the northbound API for the configuration service.
*)

\* Changes a set of paths/values on a set of targets
Change(n, ts, d) ==
   /\ LET tss == Seq(ts)
      IN
         /\ transactions' = Append(transactions, [index   |-> Len(transactions) + 1,
                                                  atomic  |-> FALSE,
                                                  sync    |-> FALSE,
                                                  changes |-> [i \in 1..Len(tss) |-> [
                                                     target |-> tss[i],
                                                     path   |-> paths[(i%Len(paths))+1],
                                                     value  |-> values[(i%Len(values))+1],
                                                     delete |-> d]],
                                                  status  |-> [state |-> Pending]])
   /\ UNCHANGED <<configurations, targets>>

----

(*
This section models the Transaction log reconciler.
*)

RemoveElement(elements, path) == [i \in {e \in DOMAIN elements : elements[e].path # path} |-> elements[i]]

AddElement(elements, element) == Append(elements, element)

UpdateElement(elements, element) == AddElement(RemoveElement(elements, element.path), element)

Paths(elements, changes) == {e.path : e \in elements} \cup {c.path : c \in elements}

UpdateElements(elements, changes) ==
   LET configPaths == {e.path : e \in elements}
       configMap == [path \in configPaths |-> CHOOSE e \in elements : e.path = path]
       changePaths == {c.path : c \in changes}
       changeMap == [path \in changePaths |-> CHOOSE c \in changes : c.path = path]
       allPaths == configPaths \cup changePaths
   IN
      Seq({IF path \in DOMAIN changeMap THEN changeMap[path] ELSE configMap[path] : path \in allPaths})

\* Reconcile the transaction log
ReconcileTransaction(n, tx) ==
      \* If the transaction is Pending, begin validation if the prior transaction
      \* has already been applied. This simplifies concurrency control in the controller
      \* and guarantees transactions are applied to the configurations in sequential order.
   /\ \/ /\ tx.status.state = Pending
         /\ \/ /\ tx.index > 1
               /\ transactions[tx.index - 1].status.state \in {Complete, Failed}
            \/ tx.index = 1
         /\ transactions' = [transactions EXCEPT ![tx.index].status.state = Validating]
         /\ UNCHANGED <<configurations>>
      \* If the transaction is in the Validating state, compute and validate the 
      \* Configuration for each target. Mark the transaction Failed if validation
      \* fails any target.
      \* TODO: Model validation failures here
      \/ /\ tx.status.state = Validating
         \* Validate the target configurations here
         \* Then change the transaction state to Applying
         /\ transactions' = [transactions EXCEPT ![tx.index].status.state = Applying]
         /\ UNCHANGED <<configurations>>
      \* If the transaction is in the Applying state, update the Configuration for each
      \* target and Complete the transaction.
      \/ /\ tx.status.state = Applying
         /\ \/ /\ tx.atomic
               \* TODO: Apply atomic transactions here
               /\ transactions' = [transactions EXCEPT ![tx.index].status.state = Complete]
               /\ UNCHANGED <<configurations>>
         /\ \/ /\ ~tx.atomic
               /\ configurations' = [t \in Target |-> [
                                        configurations[t] EXCEPT !.elements = UpdateElements(configurations[t].elements, tx.changes),
                                                                 !.status.transactionIndex = tx.index]]
               /\ transactions' = [transactions EXCEPT ![tx.index].status.state = Complete]
   /\ UNCHANGED <<targets>>

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, c) ==
   \* Only the master should reconcile the configuration
   /\ masters[c.target].master = n
   \* If the configuration's mastership term is less than the current mastership term,
   \* assume the target may have restarted/reconnected and perform a full reconciliation
   \* of the target configuration from the root path.
   /\ \/ /\ masters[c.target].term > c.status.mastershipTerm
         \* TODO: Reconcile the target state here
         /\ configurations' = [configurations EXCEPT ![c.id].status.mastershipTerm = masters[c.target].term,
                                                     ![c.id].status.targetIndex = c.status.transactionIndex]
   \* If the Configuration's transaction index is greater than the target index,
   \* reconcile the configuration with the target. Once the target has been updated,
   \* update the target index to match the reconciled transaction index.
   /\ \/ /\ masters[c.target].term = c.status.mastershipTerm
         /\ c.status.transactionIndex > c.status.targetIndex
         \* TODO: Reconcile the target state here
         /\ configurations' = [configurations EXCEPT ![c.id].status.targetIndex = c.status.transactionIndex]
   /\ UNCHANGED <<transactions>>

----

(*
Init and next state predicates
*)

Init ==
   /\ transactions = <<>>
   /\ configurations = [t \in Target |-> [
                           id       |-> t,
                           config |-> [path \in {} |-> [
                                          path    |-> path,
                                          value   |-> Nil,
                                          index   |-> 0,
                                          deleted |-> FALSE]]]]
   /\ targets = [t \in Target |-> [
                    id     |-> t,
                    config |-> [path \in {} |-> [
                                   path |-> path,
                                   value |-> Nil]]]]
   /\ masters = [t \in Target |-> [master |-> Nil, term |-> 0]]

Next ==
   \/ \E n \in Node :
         \E ts \in SUBSET Target :
            \E b \in BOOLEAN :
               Change(n, ts, b)
   \/ \E n \in Node :
         \E t \in DOMAIN transactions :
            ReconcileTransaction(n, t)
   \/ \E n \in Node :
         \E c \in configurations :
            ReconcileConfiguration(n, c)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Jan 13 04:08:17 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
