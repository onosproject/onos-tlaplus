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

Spec == 
   /\ Init
   /\ [][Next]_vars 
   /\ \A i \in 1..NumProposals : WF_vars(Change(i) \/ Rollback(i))
   /\ \A n \in Nodes, i \in 1..NumProposals : WF_vars(ReconcileProposal(n, i))
   /\ \A n \in Nodes : WF_<<configuration, mastership, node, target>>(ReconcileConfiguration(n))
   /\ \A n \in Nodes : WF_<<mastership, node, target>>(ReconcileMastership(n))
   /\ \A n \in Nodes : WF_<<node, target>>(Connect(n) \/ Disconnect(n))
   /\ WF_<<target>>(Start)
   /\ WF_<<target>>(Stop)

Order ==
    \A i \in DOMAIN proposal :
      /\ proposal[i].change.commit \in {ProposalInProgress, ProposalAborted} => 
         ~\E j \in DOMAIN proposal :
            /\ j < i
            /\ proposal[j].change.commit \in {ProposalPending, ProposalInProgress}
      /\ proposal[i].change.commit = ProposalComplete =>
         ~\E j \in DOMAIN proposal :
            /\ j < i
            /\ proposal[j].change.commit \in {ProposalPending, ProposalInProgress}
      /\ proposal[i].change.apply \in {ProposalInProgress, ProposalAborted} => 
         ~\E j \in DOMAIN proposal :
            /\ j < i
            /\ \/ proposal[j].change.apply \in {ProposalPending, ProposalInProgress}
               \/ /\ proposal[j].change.apply = ProposalFailed
                  /\ proposal[j].rollback.apply \notin ProposalDone
      /\ proposal[i].change.apply = ProposalComplete =>
         ~\E j \in DOMAIN proposal :
            /\ j < i
            /\ \/ proposal[j].change.apply \in {ProposalPending, ProposalInProgress}
               \/ /\ proposal[j].change.apply = ProposalFailed
                  /\ proposal[j].rollback.apply \notin ProposalDone
      /\ proposal[i].rollback.commit = ProposalInProgress =>
         \A j \in DOMAIN proposal : j > i /\ proposal[j].phase = ProposalRollback => 
            proposal[j].change.commit \in ProposalDone

Consistency ==
   /\ target.running 
   /\ configuration.status = ConfigurationComplete
   /\ configuration.apply.target = target.incarnation
   => \A i \in DOMAIN proposal :
         /\ proposal[i].change.apply = ProposalComplete 
         /\ proposal[i].rollback.apply # ProposalComplete
         => \A p \in DOMAIN proposal[i].change.values :
               /\ ~\E j \in DOMAIN proposal : 
                     /\ j > i 
                     /\ proposal[i].change.apply = ProposalComplete 
                     /\ proposal[i].rollback.apply # ProposalComplete
               => /\ p \in DOMAIN target.values 
                  /\ target.values[p].value = proposal[i].change.values[p].value
                  /\ target.values[p].index = proposal[i].change.values[p].index

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Termination ==
   \A i \in 1..NumProposals :
      /\ proposal[i].phase = ProposalChange ~>
         /\ proposal[i].change.commit \in ProposalDone
         /\ proposal[i].change.apply \in ProposalDone
      /\ proposal[i].phase = ProposalRollback ~>
         /\ proposal[i].rollback.commit \in ProposalDone
         /\ proposal[i].rollback.apply \in ProposalDone

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 18:30:03 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:32:07 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
