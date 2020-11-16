-------------------------------- MODULE E2T --------------------------------

(*
The E2T module specifies the E2T service API, state, and controllers.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all E2T nodes
CONSTANT Nodes

----

vars == <<>>

----

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:17:21 PST 2020 by jordanhalterman
\* Created Sun Nov 15 10:27:06 PST 2020 by jordanhalterman
