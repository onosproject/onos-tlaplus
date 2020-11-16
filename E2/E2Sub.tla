------------------------------- MODULE E2Sub -------------------------------

(*
The E2Sub module specifies the E2Sub service API, state, and controllers.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of an E2Sub nodes
CONSTANT Nodes

\* Indicates a subscription being created
CONSTANT PhaseCreate

\* Indicates a subscription being deleted
CONSTANT PhaseDelete

\* Indicates a phase is pending
CONSTANT StatusPending

\* Indicates a phase is complete
CONSTANT StatusComplete

\* An empty value
CONSTANT Nil

----

\* The set of all subscriptions
VARIABLE subscriptions

\* The set of all subscription tasks
VARIABLE subscriptionTasks

vars == <<subscriptions, subscriptionTasks>>

----

----

Init ==
    /\ subscriptions = [s \in {} |-> [phase |-> Nil, status |-> Nil]]
    /\ subscriptionTasks = [s \in {} |-> [phase |-> Nil, status |-> Nil]]

Next == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:17:31 PST 2020 by jordanhalterman
\* Created Sun Nov 15 10:27:16 PST 2020 by jordanhalterman
