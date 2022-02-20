------------------------------- MODULE Trace -------------------------------

CONSTANT Module

CONSTANT InitState

CONSTANT NextState

Init ==
   LET IOUtils == INSTANCE IOUtils
   IN
      LET ret == IOUtils!IOExecTemplate(<<"rm", "%s.log">>, <<Module>>)
      IN  TRUE

Log(name, args) ==
   LET IOUtils == INSTANCE IOUtils
       Json    == INSTANCE Json
   IN
      LET init  == InitState
          next  == NextState
          trace == [action |-> name, 
                    args   |-> args,
                    init   |-> init, 
                    next   |-> [k \in {k \in DOMAIN next : next[k] # init[k]} |-> next[k]]]
          ret   == IOUtils!IOExecTemplate(<<"/bin/sh", "-c", "echo '%s' >> %s.log">>, <<Json!ToJsonObject(trace), Module>>)
      IN ret.exitValue = 0

Step(name, action, args) ==
   /\ action
   /\ action => Log(name, args)

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 08:00:38 PST 2022 by jordanhalterman
\* Created Sun Feb 20 01:18:19 PST 2022 by jordanhalterman
