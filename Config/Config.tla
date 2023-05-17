------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

GenerateTestCases == FALSE

Nil == "<nil>"

Change == "Change"
Rollback == "Rollback"

ReadCommitted == "ReadCommitted"
Serializable == "Serializable"

Initialize == "Initialize"
Validate == "Validate"
Abort == "Abort"
Commit == "Commit"
Apply == "Apply"

InProgress == "InProgress"
Complete == "Complete"
Failed == "Failed"

Pending == "Pending"
Validated == "Validated"
Committed == "Committed"
Applied == "Applied"
Aborted == "Aborted"

Valid == TRUE
Invalid == FALSE

Success == "Success"
Failure == "Failure"

Node == {"node-1"}

NumTransactions == 3

Target == [
   target1 |-> [
      persistent |-> FALSE,
      values |-> [
         path1 |-> {"value1", "value2"}]]]

----

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

LOCAL Transaction == INSTANCE Transaction

LOCAL Proposal == INSTANCE Proposal

LOCAL Configuration == INSTANCE Configuration

LOCAL Mastership == INSTANCE Mastership

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
         
----

RequestChange(i, c) ==
   /\ Transaction!RequestChange(i, c)

RequestRollback(i, j) ==
   /\ Transaction!RequestRollback(i, j)

SetMaster(n, t) ==
   /\ Mastership!SetMaster(n, t)
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

UnsetMaster(t) ==
   /\ Mastership!UnsetMaster(t)
   /\ UNCHANGED <<transaction, proposal, configuration, target>>

ReconcileTransaction(n, t) ==
   /\ Transaction!ReconcileTransaction(n, t)
   /\ GenerateTestCases => Transaction!Test!Log([node |-> n, index |-> t])

ReconcileProposal(n, t, i) ==
   /\ Proposal!ReconcileProposal(n, t, i)
   /\ UNCHANGED <<transaction>>
   /\ GenerateTestCases => Proposal!Test!Log([node |-> n, target |-> t, index |-> i])

ReconcileConfiguration(n, c) ==
   /\ Configuration!ReconcileConfiguration(n, c)
   /\ UNCHANGED <<transaction, proposal>>
   /\ GenerateTestCases => Configuration!Test!Log([node |-> n, target |-> c])

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ transaction = [i \in {} |->
                       [type   |-> Change,
                        phase  |-> Initialize,
                        state  |-> InProgress,
                        status |-> Pending]]
   /\ proposal = [t \in DOMAIN Target |->
                    [i \in {} |-> 
                       [phase |-> Initialize,
                        state |-> InProgress]]]
   /\ configuration = [t \in DOMAIN Target |-> 
                         [state  |-> InProgress,
                          config |-> 
                            [index  |-> 0,
                             term   |-> 0,
                             values |-> 
                                [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]]],
                          proposal  |-> [index |-> 0],
                          commit    |-> [index |-> 0],
                          target    |-> 
                            [index  |-> 0,
                             term   |-> 0,
                             values |-> 
                               [path \in {} |-> 
                                  [path    |-> path,
                                   value   |-> Nil,
                                   index   |-> 0,
                                   deleted |-> FALSE]]]]]
   /\ target = [t \in DOMAIN Target |-> 
                  [path \in {} |-> 
                     [value |-> Nil]]]
   /\ mastership = [t \in DOMAIN Target |-> [master |-> Nil, term |-> 0]]

Next ==
   \/ \E i \in 1..NumTransactions :
         \E c \in ValidChanges : 
            RequestChange(i, c)
   \/ \E i \in 1..NumTransactions :
         \E j \in DOMAIN transaction :
            RequestRollback(i, j)
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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Order ==
   \A t \in DOMAIN proposal :
      \A i \in DOMAIN proposal[t] :
         /\ /\ proposal[t][i].phase = Commit
            /\ proposal[t][i].state = InProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = Commit
                  /\ proposal[t][j].state = Complete
         /\ /\ proposal[t][i].phase = Apply
            /\ proposal[t][i].state = InProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = Apply
                  /\ proposal[t][j].state = Complete

Consistency == 
   \A t \in DOMAIN target :
      LET 
          \* Compute the transaction indexes that have been applied to the target
          targetIndexes == {i \in DOMAIN transaction : 
                               /\ i \in DOMAIN proposal[t]
                               /\ proposal[t][i].phase = Apply
                               /\ proposal[t][i].state = Complete
                               /\ t \in transaction[i].targets
                               /\ ~\E j \in DOMAIN transaction :
                                     /\ j > i
                                     /\ transaction[j].type = Rollback
                                     /\ transaction[j].rollback = i
                                     /\ transaction[j].phase = Apply
                                     /\ transaction[j].state = Complete}
          \* Compute the set of paths in the target that have been updated by transactions
          appliedPaths   == UNION {DOMAIN proposal[t][i].change.values : i \in targetIndexes}
          \* Compute the highest index applied to the target for each path
          pathIndexes    == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                                    \A j \in targetIndexes :
                                          /\ i >= j 
                                          /\ p \in DOMAIN proposal[t][i].change.values]
          \* Compute the expected target configuration based on the last indexes applied
          \* to the target for each path.
          expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[t][pathIndexes[p]].change.values[p]]
      IN 
          target[t] = expectedConfig

Isolation ==
   \A i \in DOMAIN transaction :
      /\ /\ transaction[i].phase = Commit
         /\ transaction[i].state = InProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = Commit
      /\ /\ transaction[i].phase = Apply
         /\ transaction[i].state = InProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = Apply

Safety == [](Order /\ Consistency /\ Isolation)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN transaction
   /\ transaction[i].phase \in {Apply, Abort}
   /\ transaction[i].state = Complete

Termination ==
   \A i \in 1..NumTransactions : Terminated(i)

Liveness == <>Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Thu Feb 10 15:59:15 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
