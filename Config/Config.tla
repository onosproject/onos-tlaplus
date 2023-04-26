------------------------------- MODULE Config -------------------------------

EXTENDS 
   Northbound, 
   Proposal, 
   Configuration, 
   Mastership,
   Southbound

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

Next ==
   \/ /\ NextNorthbound
      /\ UNCHANGED <<>>
   \/ /\ NextProposal
      /\ UNCHANGED <<>>
   \/ /\ NextConfiguration
      /\ UNCHANGED <<proposal>>
   \/ /\ NextMastership
      /\ UNCHANGED <<proposal, configuration>>
   \/ /\ NextSouthbound
      /\ UNCHANGED <<proposal, configuration, mastership>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Order ==
   \A i \in DOMAIN proposal :
      /\ proposal[i].type = ProposalChange 
      /\ proposal[i].phase = ProposalApply 
      /\ proposal[i].state \in {ProposalComplete, ProposalFailed} 
      => \A j \in DOMAIN proposal : 
            j < i => 
               /\ proposal[j].phase = ProposalCommit => proposal[j].state = ProposalFailed
               /\ proposal[j].phase = ProposalApply => proposal[j].state \in {ProposalComplete, ProposalFailed}

IsConsistent(indexes, values) ==
   LET 
      \* Compute the set of paths in the target that have been updated by transactions
      appliedPaths == UNION {DOMAIN proposal[i].change.values : i \in indexes}
      \* Compute the highest index applied to the target for each path
      pathIndexes  == [p \in appliedPaths |-> CHOOSE i \in indexes : 
                          \A j \in indexes :
                             /\ i >= j 
                             /\ p \in DOMAIN proposal[i].change.values]
      \* Compute the expected target configuration based on the last indexes applied
      \* to the target for each path.
      expectedConfig == [p \in DOMAIN pathIndexes |-> proposal[pathIndexes[p]].change.values[p]]
      \* Compute the actual configuration by converting missing path values to Nil
      actualConfig == [p \in DOMAIN expectedConfig |-> IF p \in DOMAIN values THEN values[p] ELSE [value |-> Nil]]
   IN
      actualConfig # expectedConfig => ~(PrintT(indexes)/\PrintT(appliedPaths)/\PrintT(pathIndexes)/\PrintT(expectedConfig)/\PrintT(actualConfig))

Consistency == 
   /\ LET indexes == {i \in DOMAIN proposal : /\ \/ /\ proposal[i].type = ProposalChange
                                                    /\ proposal[i].phase = ProposalCommit
                                                    /\ proposal[i].state = ProposalComplete
                                                 \/ proposal[i].phase = ProposalApply
                                              /\ ~\E j \in DOMAIN proposal :
                                                      /\ j > i
                                                      /\ proposal[j].type = ProposalRollback
                                                      /\ proposal[j].rollback.index = i
                                                      /\ proposal[j].phase = ProposalCommit
                                                      /\ proposal[j].state = ProposalComplete}
      IN IsConsistent(indexes, configuration.committed.values)
   /\ LET indexes == {i \in DOMAIN proposal : /\ proposal[i].type = ProposalChange
                                              /\ proposal[i].phase = ProposalApply
                                              /\ proposal[i].state = ProposalComplete
                                              /\ ~\E j \in DOMAIN proposal :
                                                      /\ j > i
                                                      /\ proposal[j].type = ProposalRollback
                                                      /\ proposal[j].rollback.index = i
                                                      /\ proposal[j].phase = ProposalApply
                                                      /\ proposal[j].state = ProposalComplete}
      IN IsConsistent(indexes, configuration.applied.values)

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminated(i) ==
   /\ i \in DOMAIN proposal
   /\ \/ /\ proposal[i].phase = ProposalApply
         /\ proposal[i].state = ProposalComplete
      \/ proposal[i].state = ProposalFailed

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
