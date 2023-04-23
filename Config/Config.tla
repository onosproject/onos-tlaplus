------------------------------- MODULE Config -------------------------------

EXTENDS 
   Northbound, 
   Proposals, 
   Configurations, 
   Mastership,
   Southbound,
   Target

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

vars == <<proposal, configuration, mastership, target>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ InitNorthbound
   /\ InitProposal
   /\ InitConfiguration
   /\ InitMastership
   /\ InitSouthbound
   /\ InitTarget

Next ==
   \/ /\ NextNorthbound
      /\ UNCHANGED <<configuration, mastership, conn, target>>
   \/ /\ NextProposal
      /\ UNCHANGED <<mastership, conn>>
   \/ /\ NextConfiguration
      /\ UNCHANGED <<proposal, conn>>
   \/ /\ NextMastership
      /\ UNCHANGED <<proposal, configuration, conn, target>>
   \/ /\ NextSouthbound
      /\ UNCHANGED <<proposal, configuration, mastership>>
   \/ /\ NextTarget
      /\ UNCHANGED <<proposal, configuration, mastership, conn>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Order ==
   \A t \in DOMAIN proposal :
      \A i \in DOMAIN proposal[t] :
         /\ /\ proposal[t][i].phase = ProposalCommit
            /\ proposal[t][i].state = ProposalInProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = ProposalCommit
                  /\ proposal[t][j].state = ProposalComplete
         /\ /\ proposal[t][i].phase = ProposalApply
            /\ proposal[t][i].state = ProposalInProgress
            => ~\E j \in DOMAIN proposal[t] :
                  /\ j > i
                  /\ proposal[t][j].phase = ProposalApply
                  /\ proposal[t][j].state = ProposalComplete

Consistency == 
   \A t \in DOMAIN proposal :
      LET 
          \* Compute the transaction indexes that have been applied to the target
          targetIndexes == {i \in DOMAIN proposal[t] :
                               /\ proposal[t][i].phase = ProposalApply
                               /\ proposal[t][i].state = ProposalComplete
                               /\ ~\E j \in DOMAIN proposal[t] :
                                     /\ j > i
                                     /\ proposal[t][j].type = ProposalRollback
                                     /\ proposal[t][j].rollback.index = i
                                     /\ proposal[t][j].phase = ProposalApply
                                     /\ proposal[t][j].state = ProposalComplete}
          \* Compute the set of paths in the target that have been updated by transactions
          appliedPaths == UNION {DOMAIN proposal[t][i].change.values : i \in targetIndexes}
          \* Compute the highest index applied to the target for each path
          pathIndexes  == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                                    \A j \in targetIndexes :
                                          /\ i >= j 
                                          /\ p \in DOMAIN proposal[t][i].change.values]
          \* Compute the expected target configuration based on the last indexes applied
          \* to the target for each path.
          expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[t][pathIndexes[p]].change.values[p]]
      IN 
          target[t] = expectedConfig

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminated(t, i) ==
   /\ i \in DOMAIN proposal[t]
   /\ proposal[t][i].phase \in {ProposalApply, ProposalAbort}
   /\ proposal[t][i].state = ProposalComplete

Termination ==
   \A t \in DOMAIN proposal :
      \A i \in 1..Len(proposal[t]) :
         Terminated(t, i)

Liveness == <>Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 18:30:03 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:32:07 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
