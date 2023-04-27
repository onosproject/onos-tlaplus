--------------------------- MODULE Configuration ---------------------------

EXTENDS Mastership

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* Status constants
CONSTANTS
   ConfigurationInProgress,
   ConfigurationComplete,
   ConfigurationFailed

CONSTANT TraceConfiguration

\* A record of per-target configurations
VARIABLE configuration

----

LOCAL InitState ==
   [configuration |-> configuration,
    target        |-> target,
    mastership    |-> mastership,
    nodes         |-> node]

LOCAL NextState ==
   [configuration |-> configuration',
    target        |-> target',
    mastership    |-> mastership',
    nodes         |-> node']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Configuration",
   InitState <- InitState,
   NextState <- NextState,
   Enabled   <- TraceConfiguration

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n) ==
   /\ mastership.master = n
   /\ \/ /\ configuration.state # ConfigurationInProgress
         /\ configuration.apply.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.state = ConfigurationInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.state = ConfigurationInProgress
         /\ configuration.apply.term < mastership.term
         /\ node[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.apply.values]
         /\ configuration' = [configuration EXCEPT !.apply.term        = mastership.term,
                                                   !.apply.incarnation = target.incarnation,
                                                   !.state             = ConfigurationComplete]
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ configuration = [
         state  |-> ConfigurationInProgress,
         commit |-> [
            index    |-> 0,
            target   |-> 0,
            revision |-> 0,
            term     |-> 0,
            values   |-> [
               path \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]],
         apply  |-> [
            index       |-> 0,
            target      |-> 0,
            revision    |-> 0,
            term        |-> 0,
            incarnation |-> 0,
            values      |-> [
               path \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]]]
   /\ Trace!Init

NextConfiguration == 
   \/ \E n \in Nodes :
         Trace!Step(ReconcileConfiguration(n), [node |-> n])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 12:46:55 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:07:49 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:06:55 PST 2022 by jordanhalterman
