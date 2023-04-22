--------------------------- MODULE Configurations ---------------------------

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
   Module    <- "Configurations",
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
         /\ \/ mastership[t].term > configuration[t].committed.term
            \/ /\ mastership[t].term = configuration[t].committed.term
               /\ mastership[t].master = Nil
         /\ configuration' = [configuration EXCEPT ![t].committed.term = mastership[t].term,
                                                   ![t].state          = ConfigurationInProgress]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration[t].state = ConfigurationInProgress
         /\ mastership[t].term = configuration[t].committed.term
         /\ mastership[t].master = n
         /\ target' = [target EXCEPT ![t] = configuration[t].applied.values]
         /\ configuration' = [configuration EXCEPT ![t].applied.term = mastership[t].term,
                                                   ![t].state        = ConfigurationComplete]
   /\ UNCHANGED <<mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ configuration = [t \in DOMAIN Target |-> 
                         [state  |-> ConfigurationInProgress,
                          index     |-> 0,
                          committed |-> 
                            [index  |-> 0,
                             term   |-> 0,
                             values |-> 
                                [path \in {} |-> 
                                   [path    |-> path,
                                    value   |-> Nil,
                                    index   |-> 0,
                                    deleted |-> FALSE]]],
                          proposed  |-> [index |-> 0],
                          applied   |-> 
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
\* Last modified Fri Apr 21 12:46:55 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:07:49 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:06:55 PST 2022 by jordanhalterman
