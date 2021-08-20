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
\* Last modified Fri Aug 20 02:19:09 PDT 2021 by jordanhalterman
\* Created Fri Aug 20 02:18:01 PDT 2021 by jordanhalterman
