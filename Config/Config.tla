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

vars == <<proposal, configuration, mastership, node, target>>

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

Spec == Init /\ [][Next]_vars /\ WF_vars(NextProposal)

IsCommittedChange(i) ==
   /\ proposal[i].state = ProposalChange
   /\ \/ /\ proposal[i].change.phase = ProposalCommit
         /\ proposal[i].change.status = ProposalFailed
      \/ proposal[i].change.phase = ProposalApply

IsAppliedChange(i) ==
   /\ proposal[i].state = ProposalChange
   /\ proposal[i].change.phase = ProposalApply
   /\ proposal[i].change.status = ProposalComplete


IsCommittedRollback(i) ==
   /\ proposal[i].state = ProposalRollback
   /\ \/ /\ proposal[i].change.phase = ProposalCommit
         /\ proposal[i].change.status = ProposalFailed
      \/ proposal[i].change.phase = ProposalApply

IsAppliedRollback(i) ==
   /\ proposal[i].state = ProposalRollback
   /\ \/ proposal[i].rollback.phase = ProposalCommit
      \/ /\ proposal[i].rollback.phase = ProposalApply
         /\ proposal[i].rollback.status \in {ProposalPending, ProposalComplete}

Order ==
   \A i \in DOMAIN proposal :
      /\ IsCommittedChange(i) =>
         \A j \in DOMAIN proposal : j < i =>
            /\ proposal[j].state = ProposalChange => IsCommittedChange(j)
            /\ proposal[j].state = ProposalRollback => IsCommittedRollback(j)
      /\ IsAppliedChange(i) =>
         \A j \in DOMAIN proposal : j < i =>
            /\ proposal[j].state = ProposalChange => IsAppliedChange(j)
            /\ proposal[j].state = ProposalRollback => IsAppliedRollback(j)

Consistency ==
   /\ target.running 
   /\ configuration.state = ConfigurationComplete
   /\ configuration.apply.incarnation = target.incarnation
   => \A i \in DOMAIN proposal :
         IsAppliedChange(i) =>
            \A p \in DOMAIN proposal[i].change.values :
               /\ ~\E j \in DOMAIN proposal : 
                     /\ j > i 
                     /\ proposal[j].change.phase = ProposalApply
                     /\ proposal[j].change.status = ProposalComplete
                     /\ proposal[j].rollback.phase = ProposalApply
                        => proposal[j].rollback.status # ProposalComplete
                     /\ p \in DOMAIN proposal[j].change.values 
               => /\ p \in DOMAIN target.values 
                  /\ target.values[p].value = proposal[i].change.values[p].value
                  /\ target.values[p].index = proposal[i].change.values[p].index

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Terminates(i) ==
   /\ proposal[i].state = ProposalChange ~>
      /\ proposal[i].change.phase = ProposalApply
      /\ proposal[i].change.status = ProposalComplete
   /\ proposal[i].state = ProposalRollback ~>
      /\ proposal[i].rollback.phase = ProposalApply
      /\ proposal[i].rollback.status = ProposalComplete

Termination ==
   \A i \in 1..NumProposals : Terminates(i)

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 18:30:03 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:32:07 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
