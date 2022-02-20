--------------------------- MODULE Configuration ---------------------------

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Status constants
CONSTANTS
   InProgress,
   Complete,
   Failed

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

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masterships
VARIABLE mastership

----

LOCAL InitState ==
   [configurations |-> configuration,
    targets        |-> target,
    masterships    |-> mastership]

LOCAL NextState ==
   [configurations |-> configuration',
    targets        |-> target',
    masterships    |-> mastership']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Configuration",
   InitState <- InitState,
   NextState <- NextState

----

(*
This section models the Configuration reconciler.
*)

Reconcile(n, t) ==
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

----

(*
Formal specification, constraints, and theorems.
*)

Init == 
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
   /\ Trace!Init

Next == 
   \/ \E n \in Node :
         \E t \in DOMAIN configuration :
            Trace!Step("Reconcile", Reconcile(n, t), [node |-> n, target |-> t])

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 08:17:49 PST 2022 by jordanhalterman
\* Created Sun Feb 20 02:21:04 PST 2022 by jordanhalterman
