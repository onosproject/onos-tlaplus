-------------------------------- MODULE Topo --------------------------------

(*
The Topo module specifies the topology service API, state, and controllers.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of topology nodes
CONSTANT Nodes

\* An empty value
CONSTANT Nil

----

\* The domain of entities in the toplology
VARIABLE entities

\* The domain of relations in the topology
VARIABLE relations

vars == <<entities, relations>>

----

----

Init ==
   /\ entities = [e \in {} |-> [props |-> Nil]]
   /\ relations = [r \in {} |-> [props |-> Nil]]

Next == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:17:39 PST 2020 by jordanhalterman
\* Created Sun Nov 15 10:27:27 PST 2020 by jordanhalterman
