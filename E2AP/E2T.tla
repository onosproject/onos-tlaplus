-------------------------------- MODULE E2T --------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, Messages

\* The set of all E2T instances
CONSTANT Instance

----

HandleE2SetupRequest(n, c, m) ==
    /\ Reply(c, [type |-> E2SetupResponse])
    /\ UNCHANGED <<>>

HandleMessage(c, m) ==
    /\ \/ /\ m.type = E2SetupRequest
          /\ HandleE2SetupRequest(connections[c].e2tnode, c, m)
    /\ UNCHANGED <<>>

----

Next ==
    \/ \E c \in connections : 
       /\ Len(messages[c]) > 0 
       /\ HandleMessage(c, messages[c])

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 17:06:10 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:56:24 PDT 2021 by jordanhalterman
