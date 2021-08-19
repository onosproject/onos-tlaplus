------------------------------- MODULE Clock -------------------------------

LOCAL INSTANCE Naturals

\* The current time
VARIABLE time

----

Tick ==
   /\ time' = time + 1
   
Time == time

----

Init ==
   /\ time = 0

Next ==
   \/ Tick

=============================================================================
\* Modification History
\* Last modified Thu Aug 19 01:15:56 PDT 2021 by jordanhalterman
\* Created Thu Aug 19 01:03:10 PDT 2021 by jordanhalterman
