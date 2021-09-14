----------------------------- MODULE Messaging -----------------------------

LOCAL INSTANCE Naturals

LOCAL INSTANCE TLC

VARIABLE messages

LOCAL WithMessage(m, msgs) ==
   IF m \in DOMAIN msgs THEN
      [msgs EXCEPT ![m] = msgs[m] + 1]
   ELSE
      msgs @@ (m :> 1)

LOCAL WithoutMessage(m, msgs) ==
   IF m \in DOMAIN msgs THEN
      [msgs EXCEPT ![m] = msgs[m] - 1]
   ELSE
      msgs

Send(m) ==
   /\ messages' = WithMessage(m, messages)

Discard(m) ==
   /\ messages' = WithoutMessage(m, messages)

Handle(h(_)) ==
   /\ \E m \in messages : h(m)

Receive(request) ==
   /\ messages' = WithoutMessage(request, messages)

Reply(response) ==
   /\ messages' = WithMessage(response, messages')

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 16:41:19 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 16:41:17 PDT 2021 by jordanhalterman
