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

Value(s, p) ==
   LET value == CHOOSE v \in s : v.path = p
   IN
      [value  |-> value.value,
       delete |-> value.delete,
       valid  |-> value.valid]

Paths(s) ==
   [p \in {v.path : v \in s} |-> Value(s, p)]

ValidValues(p) ==
   UNION {{[value |-> v, delete |-> FALSE, valid |-> TRUE] : v \in Target.values[p]}, 
             {[value |-> v, delete |-> FALSE, valid |-> FALSE] : v \in Target.values[p]}, 
             {[value |-> Nil, delete |-> TRUE, valid |-> TRUE]},
             {[value |-> Nil, delete |-> TRUE, valid |-> FALSE]}}

ValidPaths ==
   UNION {{v @@ [path |-> p] : v \in ValidValues(p)} : p \in DOMAIN Target.values}

\* The set of all valid sets of changes to all targets and their paths. 
\* The set of possible changes is computed from the Target model value.
ValidChanges == 
   LET changeSets == {s \in SUBSET ValidPaths :
                        /\ \A p \in DOMAIN Target.values :
                           /\ Cardinality({v \in s : v.path = p}) <= 1}
   IN
      {c \in {Paths(s) : s \in changeSets} : DOMAIN c # {}}

\* Add change 'c' to the proposal log 
Change(c) ==
   LET index == Len(proposal) + 1
   IN  proposal' = proposal @@ 
          (index :> [type       |-> ProposalChange,
                     index      |-> index,
                     change     |-> [index  |-> index,
                                     values |-> c],
                     rollback   |-> [index  |-> 0],
                     phase      |-> ProposalInitialize,
                     state      |-> ProposalInProgress])

\* Add a rollback of proposal 'i' to the proposal log
Rollback(i) ==
   LET index == Len(proposal) + 1
   IN  proposal' = proposal @@
          (index :> [type       |-> ProposalRollback,
                     index      |-> index,
                     change     |-> [index   |-> 0],
                     rollback   |-> [index   |-> i],
                     phase      |-> ProposalInitialize,
                     state      |-> ProposalInProgress])

\* Abort aborts proposal 'i'
Abort(i) ==
   /\ proposal[i].phase # ProposalAbort
   /\ proposal[i].state # ProposalFailed
   /\ proposal' = [proposal EXCEPT ![i].phase = ProposalAbort,
                                   ![i].state = ProposalInProgress]

----

(*
Formal specification, constraints, and theorems.
*)

InitNorthbound == TRUE

NextNorthbound ==
   \/ \E c \in ValidChanges :
         Change(c)
   \/ \E i \in DOMAIN proposal :
         Rollback(i)
   \/ \E i \in DOMAIN proposal :
         Abort(i)

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 16:42:15 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:10:06 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:08:25 PST 2022 by jordanhalterman
