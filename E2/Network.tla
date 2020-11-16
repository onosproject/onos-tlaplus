------------------------------ MODULE Network ------------------------------

(*
The Network module models the behavior intra-cluster communication channels
over gRPC.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* An empty value
CONSTANT Nil

----

\* The domain of all active channels
VARIABLE channels

\* The current channel ID
VARIABLE channelId

vars == <<channels, channelId>>

----

\* Opens a channel from the given source to the given destination
OpenChannel(src, dest) ==
   /\ channelId' = channelId + 1
   /\ channels' = [channels EXCEPT ![channelId'] = [src |-> src, dest |-> dest, msgs |-> <<>>]]

\* Closes a channel by ID
CloseChannel(c) ==
   /\ channels' = [i \in DOMAIN channels \cap {c} |-> channels[i]]

----

Init ==
   /\ channelId = 0
   /\ channels = [c \in {} |-> [source |-> Nil, dest |-> Nil, msgs |-> <<>>]]

Next == 
   \/ \E c \in DOMAIN channels : CloseChannel(c)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Nov 15 18:21:01 PST 2020 by jordanhalterman
\* Created Sun Nov 15 11:08:57 PST 2020 by jordanhalterman
