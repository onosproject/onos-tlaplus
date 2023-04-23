----------------------------- MODULE Southbound -----------------------------

EXTENDS Target

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* A connected state
CONSTANT Connected

\* A disconnected state
CONSTANT Disconnected

\* The state of the connection to the target
VARIABLE conn

----

(*
This section models target states.
*)

Connect ==
   /\ conn.state # Connected
   /\ target.state = Alive
   /\ conn' = [conn EXCEPT !.id = conn.id + 1,
                           !.state = Connected]
   /\ UNCHANGED <<target>>

Disconnect ==
   /\ conn.state = Connected
   /\ conn' = [conn EXCEPT !.state = Disconnected]
   /\ UNCHANGED <<target>>

----

InitSouthbound ==
   /\ conn = [id |-> 0, state |-> Disconnected]

NextSouthbound ==
   \/ Connect
   \/ Disconnect

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
