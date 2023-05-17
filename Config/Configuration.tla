------------------------------- MODULE Configuration -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Status constants
CONSTANTS
   InProgress,
   Complete,
   Failed

State == 
   {InProgress,
    Complete,
    Failed}

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

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masterships
VARIABLE mastership

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].state # Complete
         /\ configuration' = [configuration EXCEPT ![t].state = Complete]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ \/ mastership[t].term > configuration[t].config.term
            \/ /\ mastership[t].term = configuration[t].config.term
               /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].config.term = mastership[t].term,
                                                   ![t].state       = InProgress]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].state = InProgress
         /\ mastership[t].term = configuration[t].config.term
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].target.values]
         /\ configuration' = [configuration EXCEPT ![t].target.term = mastership[t].term,
                                                   ![t].state       = Complete]
   /\ UNCHANGED <<mastership>>

=============================================================================
