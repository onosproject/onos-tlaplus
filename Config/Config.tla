------------------------------- MODULE Config -------------------------------

EXTENDS 
   Northbound, 
   Transaction, 
   Proposal, 
   Configuration, 
   Southbound

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

vars == <<transaction, proposal, configuration, mastership, target>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ InitTransaction
   /\ InitProposal
   /\ InitConfiguration
   /\ InitNorthbound
   /\ InitSouthbound

Next ==
   \/ /\ NextTransaction
      /\ UNCHANGED <<configuration, target, mastership>>
   \/ /\ NextProposal
      /\ UNCHANGED <<transaction>>
   \/ /\ NextConfiguration
      /\ UNCHANGED <<transaction, proposal>>
   \/ /\ NextNorthbound
      /\ UNCHANGED <<proposal, configuration, target, mastership>>
   \/ /\ NextSouthbound
      /\ UNCHANGED <<transaction, proposal, configuration>>

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
   \A t \in DOMAIN target :
      LET 
          \* Compute the transaction indexes that have been applied to the target
          targetIndexes == {i \in DOMAIN transaction : 
                               /\ i \in DOMAIN proposal[t]
                               /\ proposal[t][i].phase = ProposalApply
                               /\ proposal[t][i].state = ProposalComplete
                               /\ t \in transaction[i].targets
                               /\ ~\E j \in DOMAIN transaction :
                                     /\ j > i
                                     /\ transaction[j].type = TransactionRollback
                                     /\ transaction[j].rollback = i
                                     /\ transaction[j].phase = TransactionApply
                                     /\ transaction[j].state = TransactionComplete}
          \* Compute the set of paths in the target that have been updated by transactions
          appliedPaths   == UNION {DOMAIN proposal[t][i].change.values : i \in targetIndexes}
          \* Compute the highest index applied to the target for each path
          pathIndexes    == [p \in appliedPaths |-> CHOOSE i \in targetIndexes : 
                                    \A j \in targetIndexes :
                                          /\ i >= j 
                                          /\ p \in DOMAIN proposal[t][i].change.values]
          \* Compute the expected target configuration based on the last indexes applied
          \* to the target for each path.
          expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[t][pathIndexes[p]].change.values[p]]
      IN 
          target[t] = expectedConfig

Isolation ==
   \A i \in DOMAIN transaction :
      /\ /\ transaction[i].phase = TransactionCommit
         /\ transaction[i].state = TransactionInProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = TransactionCommit
      /\ /\ transaction[i].phase = TransactionApply
         /\ transaction[i].state = TransactionInProgress
         /\ transaction[i].isolation = Serializable
         => ~\E j \in DOMAIN transaction : 
               /\ j > i
               /\ transaction[j].targets \cap transaction[i].targets # {}
               /\ transaction[j].phase = TransactionApply

Safety == [](Order /\ Consistency /\ Isolation)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN transaction
   /\ transaction[i].phase \in {TransactionApply, TransactionAbort}
   /\ transaction[i].state = TransactionComplete

Termination ==
   \A i \in 1..Len(transaction) : Terminated(i)

Liveness == <>Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Sun Feb 20 09:10:53 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
