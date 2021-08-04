-------------------------------- MODULE E2AP --------------------------------

EXTENDS App, RIC, E2Node

----

Init ==
    /\ InitAppVars
    /\ InitRICVars
    /\ InitNBVars
    /\ InitE2NodeVars
    /\ InitSBVars

Next ==
    \/ AppNext
    \/ NBNext
    \/ RICNext
    \/ SBNext
    \/ E2NodeNext

=============================================================================
\* Modification History
\* Last modified Tue Aug 03 18:54:13 PDT 2021 by jordanhalterman
\* Created Mon Jul 26 09:32:11 PDT 2021 by jordanhalterman
