------------------------------- MODULE Trace -------------------------------

CONSTANT Enabled

CONSTANT Module

CONSTANT InitState

CONSTANT NextState

INSTANCE Naturals

Init ==
   LET IOUtils == INSTANCE IOUtils
   IN
      LET ret == IOUtils!IOExecTemplate(<<"rm", "%s.log">>, <<Module>>)
      IN  TRUE

Log(context) ==
   IF Enabled THEN
      LET IOUtils == INSTANCE IOUtils
          Json    == INSTANCE Json
      IN
          LET init  == [k \in {k \in DOMAIN InitState : DOMAIN InitState[k] # {}} |-> InitState[k]]
              next  == [k \in {k \in DOMAIN NextState : DOMAIN NextState[k] # {}} |-> NextState[k]]
              trace == [context |-> context,
                          init    |-> init, 
                          next    |-> [k \in {k \in DOMAIN next : k \notin DOMAIN init \/ next[k] # init[k]} |-> next[k]]]
              ret   == IOUtils!IOExecTemplate(<<"/bin/sh", "-c", "echo '%s' >> %s.log">>, <<Json!ToJsonObject(trace), Module>>)
          IN ret.exitValue = 0
   ELSE TRUE

Step(action, context) ==
   /\ action
   /\ action => Log(context)

ASSUME Enabled \in BOOLEAN

=============================================================================
\* Modification History
\* Last modified Mon Feb 21 01:49:57 PST 2022 by jordanhalterman
\* Created Sun Feb 20 01:18:19 PST 2022 by jordanhalterman
