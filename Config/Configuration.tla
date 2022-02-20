--------------------------- MODULE Configuration ---------------------------

EXTENDS Southbound

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* Status constants
CONSTANTS
   ConfigurationInProgress,
   ConfigurationComplete,
   ConfigurationFailed

\* A record of per-target configurations
VARIABLE configuration

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

ReconcileConfiguration(n, t) ==
   /\ \/ /\ Target[t].persistent
         /\ configuration[t].state # ConfigurationComplete
         /\ configuration' = [configuration EXCEPT ![t].state = ConfigurationComplete]
         /\ UNCHANGED <<target>>
      \/ /\ ~Target[t].persistent
         /\ \/ mastership[t].term > configuration[t].config.term
            \/ /\ mastership[t].term = configuration[t].config.term
               /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].config.term = mastership[t].term,
                                                   ![t].state       = ConfigurationInProgress]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].state = ConfigurationInProgress
         /\ mastership[t].term = configuration[t].config.term
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].target.values]
         /\ configuration' = [configuration EXCEPT ![t].target.term = mastership[t].term,
                                                   ![t].state       = ConfigurationComplete]
   /\ UNCHANGED <<mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ configuration = [t \in DOMAIN Target |-> 
                         [state  |-> ConfigurationInProgress,
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

NextConfiguration == 
   \/ \E n \in Node :
         \E t \in DOMAIN configuration :
            Trace!Step("Reconcile", ReconcileConfiguration(n, t), [node |-> n, target |-> t])

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:02:19 PST 2022 by jordanhalterman
\* Created Sun Feb 20 02:21:04 PST 2022 by jordanhalterman
