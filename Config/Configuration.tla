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

CONSTANT LogConfiguration

ASSUME LogConfiguration \in BOOLEAN 

\* A record of per-target configurations
VARIABLE configuration

----

LOCAL CurrentState ==
   [configuration |-> configuration,
    target        |-> target,
    mastership    |-> mastership,
    nodes         |-> node]

LOCAL SuccessorState ==
   [configuration |-> configuration',
    target        |-> target',
    mastership    |-> mastership',
    nodes         |-> node']

LOCAL Log == INSTANCE Log WITH
   File           <- "Configuration.log",
   CurrentState   <- CurrentState,
   SuccessorState <- SuccessorState,
   Enabled        <- LogConfiguration

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n) ==
   /\ mastership.master = n
   /\ \/ /\ configuration.status # ConfigurationInProgress
         /\ configuration.apply.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.status = ConfigurationInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.status = ConfigurationInProgress
         /\ configuration.apply.term < mastership.term
         /\ node[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.apply.values]
         /\ configuration' = [configuration EXCEPT !.apply.term   = mastership.term,
                                                   !.apply.target = target.incarnation,
                                                   !.status        = ConfigurationComplete]
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitConfiguration == 
   /\ Log!Init
   /\ configuration = [
         status |-> ConfigurationInProgress,
         commit |-> [
            proposal |-> 0,
            index    |-> 0,
            term     |-> 0,
            values   |-> [
               path \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]],
         apply  |-> [
            proposal |-> 0,
            index    |-> 0,
            term     |-> 0,
            target   |-> 0,
            values   |-> [
               path \in {} |-> [
                  index |-> 0,
                  value |-> Nil]]]]

NextConfiguration == 
   \/ \E n \in Nodes :
         Log!Action(ReconcileConfiguration(n), [node |-> n])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 12:46:55 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:07:49 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:06:55 PST 2022 by jordanhalterman
