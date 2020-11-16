------------------------------- MODULE E2Node -------------------------------

(*
The E2Node module specifies the E2 node client and E2AP protocol.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all E2 nodes
CONSTANT Nodes

----

vars == <<>>

----

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:18:09 PST 2020 by jordanhalterman
\* Created Sun Nov 15 10:59:11 PST 2020 by jordanhalterman
