----------------------------- MODULE Northbound -----------------------------

EXTENDS Transaction

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

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
      {c \in {Changes(s) : s \in changeSets} : 
         DOMAIN c # {} /\ \A t \in DOMAIN c : DOMAIN c[t] # {}}

\* Add a set of changes 'c' to the transaction log
RequestChange(c) ==
   LET index == Len(transaction) + 1
   IN \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (index :> [type      |-> TransactionChange,
                                                     isolation |-> isolation,
                                                     change    |-> c,
                                                     targets   |-> {},
                                                     phase     |-> TransactionInitialize,
                                                     state     |-> TransactionInProgress,
                                                     status    |-> TransactionPending])

\* Add a rollback of transaction 't' to the transaction log
RequestRollback(i) ==
   LET index == Len(transaction) + 1
   IN \E isolation \in {ReadCommitted, Serializable} :
         /\ transaction' = transaction @@ (index :> [type      |-> TransactionRollback,
                                                     isolation |-> isolation,
                                                     rollback  |-> i,
                                                     targets   |-> {},
                                                     phase     |-> TransactionInitialize,
                                                     state     |-> TransactionInProgress,
                                                     status    |-> TransactionPending])

RequestSet ==
   \/ \E c \in ValidChanges : 
         RequestChange(c)
   \/ \E i \in DOMAIN transaction :
         RequestRollback(i)

----

(*
Formal specification, constraints, and theorems.
*)

InitNorthbound == TRUE

NextNorthbound ==
   \/ RequestSet

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:26 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:08:25 PST 2022 by jordanhalterman
