----------------------------- MODULE Northbound -----------------------------

EXTENDS Proposals

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

(*
This section models configuration changes and rollbacks. Changes
are appended to the proposal log and processed asynchronously.
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
   UNION {{[value |-> v, delete |-> FALSE, valid |-> TRUE] : v \in Target[t].values[p]}, 
             {[value |-> v, delete |-> FALSE, valid |-> FALSE] : v \in Target[t].values[p]}, 
                 {[value |-> Nil, delete |-> TRUE]}}

ValidPaths(t) ==
   UNION {{v @@ [target |-> t, path |-> p] : v \in ValidValues(t, p)} : p \in DOMAIN Target[t].values}

\* The set of all valid sets of changes to all targets and their paths. 
\* The set of possible changes is computed from the Target model value.
ValidChanges(t) == 
   LET changeSets == {s \in SUBSET ValidPaths(t) :
                        /\ \A p \in DOMAIN Target[t].values :
                           /\ Cardinality({v \in s : v.target = t /\ v.path = p}) <= 1}
   IN
      {c \in {Changes(s) : s \in changeSets} : DOMAIN c # {}}

\* Add change 'c' to the proposal log for target 't'
RequestChange(t, c) ==
   LET index == Cardinality(DOMAIN proposal[t])
   IN  proposal' = [proposal EXCEPT ![t] = proposal[t] @@ 
          (index :> [type       |-> ProposalChange,
                     index      |-> index,
                     change     |->  [index  |-> index,
                                      values |-> c],
                     rollback   |-> [index   |-> 0],
                     phase      |-> ProposalInitialize,
                     state      |-> ProposalInProgress])]

\* Add a rollback of proposal 'i' to the proposal log for target 't'
RequestRollback(t, i) ==
   LET index == Cardinality(DOMAIN proposal[t])
   IN  proposal' = [proposal EXCEPT ![t] = proposal[t] @@
          (index :> [type       |-> ProposalRollback,
                     index      |-> index,
                     change     |-> [index   |-> 0],
                     rollback   |-> [index   |-> i],
                     phase      |-> ProposalInitialize,
                     state      |-> ProposalInProgress])]

RequestSet ==
   \/ \E t \in DOMAIN Target :
         \E c \in ValidChanges(t) :
            RequestChange(t, c)
   \/ \E t \in DOMAIN proposal :
         \E i \in DOMAIN proposal[t] :
            RequestRollback(t, i)

----

(*
Formal specification, constraints, and theorems.
*)

InitNorthbound == TRUE

NextNorthbound ==
   \/ RequestSet

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 16:42:15 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:10:06 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:08:25 PST 2022 by jordanhalterman
