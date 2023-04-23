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
   \A i \in DOMAIN proposal :
       /\ /\ proposal[i].phase = ProposalCommit
          /\ proposal[i].state = ProposalInProgress
          => ~\E j \in DOMAIN proposal :
               /\ j > i
               /\ proposal[j].phase = ProposalCommit
               /\ proposal[j].state = ProposalComplete
       /\ /\ proposal[i].phase = ProposalApply
          /\ proposal[i].state = ProposalInProgress
          => ~\E j \in DOMAIN proposal :
               /\ j > i
               /\ proposal[j].phase = ProposalApply
               /\ proposal[j].state = ProposalComplete

Consistency == 
   LET 
      \* Compute the transaction indexes that have been applied to the target
      targetIndexes == {i \in DOMAIN proposal :
                           /\ proposal[i].phase = ProposalApply
                           /\ proposal[i].state = ProposalComplete
                           /\ ~\E j \in DOMAIN proposal :
                                 /\ j > i
                                 /\ proposal[j].type = ProposalRollback
                                 /\ proposal[j].rollback.index = i
                                 /\ proposal[j].phase = ProposalApply
                                 /\ proposal[j].state = ProposalComplete}
      \* Compute the set of paths in the target that have been updated by transactions
      appliedPaths == UNION {DOMAIN proposal[i].change.values : i \in targetIndexes}
      \* Compute the highest index applied to the target for each path
      pathIndexes  == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                          \A j \in targetIndexes :
                             /\ i >= j 
                             /\ p \in DOMAIN proposal[i].change.values]
      \* Compute the expected target configuration based on the last indexes applied
      \* to the target for each path.
      expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[pathIndexes[p]].change.values[p]]
   IN 
      target = expectedConfig

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN proposal
   /\ proposal[i].phase \in {ProposalApply, ProposalAbort}
   /\ proposal[i].state = ProposalComplete

Termination ==
   \A i \in 1..Len(proposal) :
      Terminated(i)

Liveness == <>Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 18:30:03 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:32:07 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
