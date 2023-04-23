----------------------------- MODULE Target -----------------------------

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

(*
Target is the set of all targets and their possible paths and values.

Example:
   Target == [
      values |-> [
         path1 |-> {"value1", "value2"},
         path2 |-> {"value3"}]
*)
CONSTANT Target

\* Represents a target running state
CONSTANT Alive

\* Represents a target not running state
CONSTANT Dead

\* A record of target states
VARIABLE target

----

Start ==
   /\ target.state = Dead
   /\ target' = [target EXCEPT !.instance = target.instance + 1,
                               !.state = Alive]

Stop ==
   /\ target.state = Alive
   /\ target' = [target EXCEPT !.state  = Dead,
                               !.values = [p \in {} |-> [value |-> Nil]]]

----

(*
Formal specification, constraints, and theorems.
*)

InitTarget ==
   /\ target = [instance |-> 0, state |-> Dead, values |-> [p \in {} |-> [value |-> Nil]]]

NextTarget ==
   \/ Start
   \/ Stop

----

ASSUME /\ \A p \in DOMAIN Target.values :
             IsFiniteSet(Target.values[p])

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:09:52 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:13:26 PST 2022 by jordanhalterman
