------------------------------- MODULE Log -------------------------------

INSTANCE Naturals

INSTANCE Sequences

LOCAL INSTANCE IOUtils

LOCAL INSTANCE Json

CONSTANT Enabled

CONSTANT File

CONSTANT CurrState

CONSTANT SuccState

FormatOpts == 
   [format      |-> "TXT",
    charset     |-> "UTF-8",
    openOptions |-> <<"WRITE", "CREATE", "APPEND">>]

Init ==
   /\ IOExec(<<"rm", "-f", File>>).exitValue = 0

Log(context) ==
   Enabled => 
      LET currState == [k \in {k \in DOMAIN CurrState : DOMAIN CurrState[k] # {}} |-> CurrState[k]]
          succState == [k \in {k \in DOMAIN SuccState : DOMAIN SuccState[k] # {}} |-> SuccState[k]]
          record    == [context   |-> context,
                        currState |-> currState, 
                        succState |-> [k \in {k \in DOMAIN succState : k \in DOMAIN currState => 
                                                    currState[k] # succState[k]} |-> succState[k]]]
      IN Serialize(ToJsonObject(record) \o "\n", File, FormatOpts).exitValue = 0

Action(action, context) ==
   /\ action
   /\ Log(context)

ASSUME Enabled \in BOOLEAN

=============================================================================
\* Modification History
\* Last modified Mon Feb 21 01:49:57 PST 2022 by jordanhalterman
\* Created Sun Feb 20 01:18:19 PST 2022 by jordanhalterman
