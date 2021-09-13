-------------------------------- MODULE API --------------------------------

VARIABLE conns

gRPC == INSTANCE gRPC WITH
   Nil <- "<nil>",
   OK <- "OK",
   Error <- "Error",
   Unknown <- "Unknown",
   Canceled <- "Canceled",
   NotFound <- "NotFound",
   AlreadyExists <- "AlreadyExists",
   Unauthorized <- "Unauthorized",
   Forbidden <- "Forbidden",
   Conflict <- "Conflict",
   Invalid <- "Invalid",
   Unavailable <- "Unavailable",
   NotSupported <- "NotSupported",
   Timeout <- "Timeout",
   Internal <- "Internal"

Init ==
   /\ gRPC!Init

Next ==
   /\ gRPC!Next

=============================================================================
\* Modification History
\* Last modified Mon Sep 13 15:12:27 PDT 2021 by jordanhalterman
\* Created Mon Sep 13 03:26:39 PDT 2021 by jordanhalterman
