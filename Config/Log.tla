------------------------------- MODULE Log -------------------------------

INSTANCE Naturals

INSTANCE Sequences

LOCAL INSTANCE IOUtils

LOCAL INSTANCE Json

CONSTANT Enabled

CONSTANT File

CONSTANT CurrentState

CONSTANT SuccessorState

FormatOpts == 
   [format      |-> "TXT",
    charset     |-> "UTF-8",
    openOptions |-> <<"WRITE", "CREATE", "APPEND">>]

Init ==
   /\ IOExec(<<"rm", "-f", File>>).exitValue = 0

Log(context) ==
   Enabled => 
      LET currentState   == [k \in {k \in DOMAIN CurrentState : DOMAIN CurrentState[k] # {}} |-> CurrentState[k]]
          successorState == [k \in {k \in DOMAIN SuccessorState : DOMAIN SuccessorState[k] # {}} |-> SuccessorState[k]]
          record         == [context        |-> context,
                             currentState   |-> currentState, 
                             successorState |-> [k \in {k \in DOMAIN successorState : k \in DOMAIN currentState => 
                                                    currentState[k] # successorState[k]} |-> successorState[k]]]
      IN Serialize(ToJsonObject(record) \o "\n", File, FormatOpts).exitValue = 0

Action(action, context) ==
   /\ action
   /\ action => Log(context)

ASSUME Enabled \in BOOLEAN

=============================================================================
\* Modification History
\* Last modified Mon Feb 21 01:49:57 PST 2022 by jordanhalterman
\* Created Sun Feb 20 01:18:19 PST 2022 by jordanhalterman
