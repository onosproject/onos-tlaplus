------------------------------- MODULE Log -------------------------------

INSTANCE Naturals

INSTANCE Sequences

LOCAL IOUtils == INSTANCE IOUtils

LOCAL Json == INSTANCE Json

CONSTANT Enabled

CONSTANT File

CONSTANT CurrentState

CONSTANT SuccessorState

FormatOpts == 
   [format      |-> "TXT",
    charset     |-> "UTF-8",
    openOptions |-> <<"WRITE", "CREATE", "APPEND">>]

Init ==
   /\ IOUtils!IOExec(<<"rm", "-f", File>>).exitValue = 0

Log(context) ==
   Enabled => 
      LET current   == [k \in {k \in DOMAIN CurrentState : DOMAIN CurrentState[k] # {}} |-> CurrentState[k]]
          successor == [k \in {k \in DOMAIN SuccessorState : DOMAIN SuccessorState[k] # {}} |-> SuccessorState[k]]
          record    == [context   |-> context,
                        current   |-> current, 
                        successor |-> [k \in {k \in DOMAIN successor : k \in DOMAIN current => current[k] # successor[k]} |-> successor[k]]]
      IN /\ IOUtils!Serialize(Json!ToJsonObject(record), File, FormatOpts).exitValue = 0
         /\ IOUtils!Serialize("\n", File, FormatOpts).exitValue = 0

Action(action, context) ==
   /\ action
   /\ action => Log(context)

ASSUME Enabled \in BOOLEAN

=============================================================================
\* Modification History
\* Last modified Mon Feb 21 01:49:57 PST 2022 by jordanhalterman
\* Created Sun Feb 20 01:18:19 PST 2022 by jordanhalterman
