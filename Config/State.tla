------------------------------- MODULE State -------------------------------

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

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 07:51:01 PST 2022 by jordanhalterman
\* Created Sun Feb 20 07:50:39 PST 2022 by jordanhalterman
