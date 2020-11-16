------------------------------- MODULE E2App -------------------------------

(*
The E2App module models an E2 application.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all nodes
CONSTANT Nodes

----

vars == <<>>

----

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:21:28 PST 2020 by jordanhalterman
\* Created Sun Nov 15 12:07:41 PST 2020 by jordanhalterman
