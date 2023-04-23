--------------------------- MODULE Configurations ---------------------------

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

ReconcileConfiguration(n) ==
   /\ mastership.master = n
   /\ \/ /\ configuration.state # ConfigurationInProgress
         /\ configuration.applied.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.state = ConfigurationInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.state = ConfigurationInProgress
         /\ configuration.applied.term < mastership.term
         /\ conn[n].state = Connected
         /\ target.state = Alive
         /\ target' = [target EXCEPT !.values = configuration.applied.values]
         /\ configuration' = [configuration EXCEPT !.applied.term = mastership.term,
                                                   !.state        = ConfigurationComplete]
   /\ UNCHANGED <<mastership, conn>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ configuration = [
         state  |-> ConfigurationInProgress,
         index     |-> 0,
         committed |-> [
            index  |-> 0,
            term   |-> 0,
            values |-> [
               path \in {} |-> [
                  path    |-> path,
                   value   |-> Nil,
                   index   |-> 0,
                   deleted |-> FALSE]]],
        proposed  |-> [index |-> 0],
        applied   |-> [
           index  |-> 0,
           term   |-> 0,
           values |-> [
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
