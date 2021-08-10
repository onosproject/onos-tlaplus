-------------------------------- MODULE E2AP --------------------------------

EXTENDS App, E2T, E2Node

----

Init ==
    /\ InitAppVars
    /\ InitE2TVars
    /\ InitNBVars
    /\ InitE2NodeVars
    /\ InitSBVars

Next ==
    \/ AppNext
    \/ NBNext
    \/ E2TNext
    \/ SBNext
    \/ E2NodeNext

=============================================================================
\* Modification History
\* Last modified Tue Aug 10 03:51:57 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:32:11 PDT 2021 by jordanhalterman
