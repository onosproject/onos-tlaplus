-------------------------------- MODULE gNMI --------------------------------


LOCAL INSTANCE Naturals

LOCAL INSTANCE Sequences

LOCAL INSTANCE FiniteSets

LOCAL INSTANCE TLC

CONSTANT Nil

CONSTANT OK, Error

VARIABLE conns

LOCAL gRPC == INSTANCE gRPC

vars == <<conns>>

=============================================================================
\* Modification History
\* Last modified Tue Jan 11 23:48:55 PST 2022 by jordanhalterman
\* Created Tue Jan 11 23:46:02 PST 2022 by jordanhalterman
