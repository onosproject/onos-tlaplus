------------------------------- MODULE Debug -------------------------------

INSTANCE Naturals

INSTANCE TLC

VARIABLE count

VARIABLE terminated

vars == <<count, terminated>>

Limit == 3

Init ==
   /\ count = 0
   /\ terminated = FALSE

Increment == 
   /\ count' = count + 1
   /\ IF count' = Limit THEN 
         terminated' = FALSE
      ELSE 
         UNCHANGED <<terminated>>

Next ==
   /\ Increment

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

LimitConstraint == count <= Limit

Termination == <>(terminated)

Liveness == Termination

=============================================================================
