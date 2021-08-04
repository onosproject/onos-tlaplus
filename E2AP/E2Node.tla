------------------------------- MODULE E2Node -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, Messages

\* The set of all E2 nodes
CONSTANT Node

----

SendE2SetupRequest(n, c) ==
    /\ Send(c, [type |-> E2SetupRequest])
    /\ UNCHANGED <<>>

HandleE2SetupResponse(n, c, m) ==
    /\ Receive(c)
    /\ UNCHANGED <<>>

HandleMessage(c, m) ==
    /\ \/ /\ m.type = E2SetupRequest
          /\ HandleE2SetupResponse(connections[c].e2node, c, m)
    /\ UNCHANGED <<>>

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 17:02:35 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 10:00:09 PDT 2021 by jordanhalterman
