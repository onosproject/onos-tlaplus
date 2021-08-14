-------------------------------- MODULE API --------------------------------

CONSTANTS OK, Error

VARIABLES e2apServers, e2apConns

e2apApiVars == <<e2apServers, e2apConns>>

VARIABLES e2tServers, e2tConns

e2tApiVars == <<e2tServers, e2tConns>>

VARIABLES topoServers, topoConns

topoApiVars == <<topoServers, topoConns>>

API == INSTANCE Protocols

=============================================================================
\* Modification History
\* Last modified Sat Aug 14 12:13:12 PDT 2021 by jordanhalterman
\* Created Fri Aug 13 01:24:02 PDT 2021 by jordanhalterman
