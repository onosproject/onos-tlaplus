------------------------------- MODULE Trace -------------------------------

\* The Trace module logs model traces to a JSON file.

LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE Json

LOCAL INSTANCE TLC

CONSTANT Enabled

CONSTANT File

CONSTANT Depth

VARIABLE trace

Add(action, context) ==
   /\ Enabled
   /\ Len(trace) < Depth
   /\ trace' = Append(trace, [action |-> action, context |-> context])

Log(filename) ==
   /\ Enabled
   /\ Len(trace) > 0
   /\ JsonSerialize(File, trace)

Init ==
   /\ trace = <<>>

=============================================================================
\* Modification History
\* Last modified Thu Sep 30 11:59:31 PDT 2021 by jordanhalterman
\* Created Mon Sep 27 16:28:49 PDT 2021 by jordanhalterman
