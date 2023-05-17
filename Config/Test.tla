------------------------------- MODULE Test -------------------------------

INSTANCE Naturals

INSTANCE Sequences

LOCAL INSTANCE IOUtils

LOCAL INSTANCE Json

CONSTANT File

CONSTANT CurrState

CONSTANT SuccState

FormatOpts == 
   [format      |-> "TXT",
    charset     |-> "UTF-8",
    openOptions |-> <<"WRITE", "CREATE", "APPEND">>]

Delete ==
   /\ IOExec(<<"rm", "-f", File>>).exitValue = 0

Log(context) ==
   LET 
      currState == [k \in {k \in DOMAIN CurrState : DOMAIN CurrState[k] # {}} |-> CurrState[k]]
      succState == [k \in {k \in DOMAIN SuccState : DOMAIN SuccState[k] # {}} |-> SuccState[k]]
      record    == [context   |-> context,
                    currState |-> currState, 
                    succState |-> [k \in {k \in DOMAIN succState : k \in DOMAIN currState => 
                                             currState[k] # succState[k]} |-> succState[k]]]
   IN Serialize(ToJsonObject(record) \o "\n", File, FormatOpts).exitValue = 0

=============================================================================
