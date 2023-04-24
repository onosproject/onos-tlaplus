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
   [configurations |-> configuration,
    targets        |-> target,
    masterships    |-> mastership,
    nodes          |-> node]

LOCAL NextState ==
   [configurations |-> configuration',
    targets        |-> target',
    masterships    |-> mastership',
    nodes          |-> node']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Configurations",
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
         /\ configuration.applied.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.state = ConfigurationInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.state = ConfigurationInProgress
         /\ configuration.applied.term < mastership.term
         /\ node[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.applied.values]
         /\ configuration' = [configuration EXCEPT !.applied.term = mastership.term,
                                                   !.state        = ConfigurationComplete]
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ configuration = [
         state     |-> ConfigurationInProgress,
         committed |-> [
            index    |-> 0,
            revision |-> 0,
            term     |-> 0,
            values   |-> [
               path \in {} |-> [
                  path    |-> path,
                   value   |-> Nil,
                   index   |-> 0,
                   deleted |-> FALSE]]],
         applied   |-> [
            index    |-> 0,
            revision |-> 0,
            term     |-> 0,
            values   |-> [
               path \in {} |-> [
                  path    |-> path,
                  value   |-> Nil,
                  index   |-> 0,
                  deleted |-> FALSE]]]]
   /\ Trace!Init

NextConfiguration == 
   \/ \E n \in Node :
         Trace!Step(ReconcileConfiguration(n), [node |-> n])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 12:46:55 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:07:49 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:06:55 PST 2022 by jordanhalterman
