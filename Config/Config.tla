------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

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

\* Phase constants
CONSTANTS
   Initialize,
   Validate,
   Abort,
   Commit,
   Apply

Phase ==
   {Initialize,
    Validate,
    Abort,
    Commit,
    Apply}

\* Status constants
CONSTANTS
   InProgress,
   Complete,
   Failed

State == 
   {InProgress,
    Complete,
    Failed}

\* State constants
CONSTANTS
   Pending,
   Validated,
   Committed,
   Applied,
   Aborted

Status ==
   {Pending,
    Validated,
    Committed,
    Applied,
    Aborted}

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
   Target == 
      [target1 |-> 
         [persistent |-> FALSE,
          values |-> [
            path1 |-> {"value1", "value2"},
            path2 |-> {"value2", "value3"}]],
      target2 |-> 
         [persistent |-> TRUE,
          values |-> [
            path2 |-> {"value3", "value4"},
            path3 |-> {"value4", "value5"}]]]
*)
CONSTANT Target

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
       
   TYPE Phase ::= phase \in
      {Initialize,
       Validate,
       Abort,
       Commit,
       Apply}

   TYPE State ::= state \in 
      {InProgress,
       Complete,
       Failed}

   TYPE Status ::= status \in 
      {Pending,
       Validated,
       Committed,
       Applied,
       Aborted}
   
   TYPE Isolation ::= isolation \in
      {ReadCommitted, 
       Serializable}

   TYPE Transaction == 
      [type      ::= type \in Type,
       isolation ::= isolation \in Isolation
       change    ::= 
         [target \in SUBSET (DOMAIN Target) |-> 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       rollback  ::= index \in Nat,
       targets   ::= targets \in SUBSET (DOMAIN Target)
       phase     ::= phase \in Phase,
       state     ::= state \in State,
       status    ::= status \in Status]
   
   TYPE Proposal == 
      [type       ::= type \in Type,
       change     ::= 
         [index  ::= index \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       rollback   ::= 
         [index  ::= index \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target].values) |-> 
               [value  ::= value \in STRING, 
                delete ::= delete \in BOOLEAN]]],
       dependency ::= [index \in Nat],
       phase      ::= phase \in Phase,
       state      ::= state \in State]
   
   TYPE Configuration == 
      [config    ::= 
         [index  ::= index \in Nat,
          term   ::= term \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target]) |-> 
               [value   ::= value \in STRING, 
                index   ::= index \in Nat,
                deleted ::= delete \in BOOLEAN]]],
       proposal ::= [index ::= index \in Nat],
       commit   ::= [index ::= index \in Nat],
       target   ::= 
         [index  ::= index \in Nat,
          term   ::= term \in Nat,
          values ::= 
            [path \in SUBSET (DOMAIN Target[target]) |-> 
               [value   ::= value \in STRING, 
                index   ::= index \in Nat,
                deleted ::= delete \in BOOLEAN]]],
       state    ::= state \in State]
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

Transaction   == INSTANCE Transaction
Proposal      == INSTANCE Proposal
Configuration == INSTANCE Configuration
Southbound    == INSTANCE Southbound
Northbound    == INSTANCE Northbound

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ Transaction!Init
   /\ Proposal!Init
   /\ Configuration!Init
   /\ Northbound!Init
   /\ Southbound!Init

Next ==
   \/ /\ Transaction!Next
      /\ UNCHANGED <<configuration, target, mastership>>
   \/ /\ Proposal!Next
      /\ UNCHANGED <<transaction>>
   \/ /\ Configuration!Next
      /\ UNCHANGED <<transaction, proposal>>
   \/ /\ Northbound!Next
      /\ UNCHANGED <<proposal, configuration, target, mastership>>
   \/ /\ Southbound!Next
      /\ UNCHANGED <<transaction, proposal, configuration>>

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
   \A i \in 1..Len(transaction) : Terminated(i)

Liveness == <>Termination

THEOREM Spec => Liveness

----

(*
Type assumptions.
*)

ASSUME Nil \in STRING

ASSUME \A phase \in Phase : phase \in STRING

ASSUME \A state \in State : state \in STRING

ASSUME \A status \in Status : status \in STRING

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

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 08:03:14 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
