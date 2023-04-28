----------------------------- MODULE Proposal -----------------------------

EXTENDS Configuration, Mastership

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

LOCAL INSTANCE TLCExt

----

CONSTANT NumProposals

ASSUME NumProposals \in Nat 

\* Transaction type constants
CONSTANTS
   ProposalChange,
   ProposalRollback

\* Phase constants
CONSTANTS
   ProposalCommit,
   ProposalApply

\* Status constants
CONSTANTS
   ProposalPending,
   ProposalInProgress,
   ProposalComplete,
   ProposalAborted,
   ProposalFailed

CONSTANT LogProposal

ASSUME LogProposal \in BOOLEAN 

\* A record of per-target proposals
VARIABLE proposal

----

LOCAL CurrentState == [
   proposals     |-> [i \in {i \in DOMAIN proposal : proposal[i].phase # Nil} |-> proposal[i]],
   configuration |-> configuration,
   target        |-> target,
   mastership    |-> mastership,
   nodes         |-> node]

LOCAL SuccessorState == [
   proposals     |-> [i \in {i \in DOMAIN proposal' : proposal'[i].phase # Nil} |-> proposal'[i]],
   configuration |-> configuration',
   target        |-> target',
   mastership    |-> mastership',
   nodes         |-> node']

LOCAL Log == INSTANCE Log WITH
   File           <- "Proposal.log",
   CurrentState   <- CurrentState,
   SuccessorState <- SuccessorState,
   Enabled        <- LogProposal

----

ProposalDone == {ProposalComplete, ProposalAborted, ProposalFailed}

\* Commit a change to the configuration.
\* A change can be committed once all prior changes have been committed.
\* If a prior change is being rolled back, the rollback must complete
\* before the change can be committed. Changes must be committed in
\* sequential order.
\* Once a change commit is in progress, the change must be committed or
\* failed before it can be applied or rolled back.
CommitChange(n, i) == 
   /\ \/ /\ proposal[i].change.commit = ProposalPending
         \* To apply a change, the prior change must have been committed. Additionally, 
         \* the configuration's applied index must match the proposed index to prevent
         \* commits while a prior change is still being rolled back.
         /\ i-1 \in DOMAIN proposal => proposal[i-1].change.commit \in ProposalDone
         /\ configuration.commit.index = configuration.commit.proposal
         /\ \/ /\ proposal[i].rollback.commit # ProposalPending
               /\ configuration' = [configuration EXCEPT !.commit.proposal = i]
               /\ proposal' = [proposal EXCEPT ![i].change.commit  = ProposalInProgress,
                                               ![i].rollback.index = configuration.commit.index]
            \/ /\ proposal[i].rollback.commit = ProposalPending
               /\ configuration' = [configuration EXCEPT !.commit.proposal = i,
                                                         !.commit.index    = i]
               /\ proposal' = [proposal EXCEPT ![i].change.commit  = ProposalAborted,
                                               ![i].rollback.index = configuration.commit.index]
      \/ /\ proposal[i].change.commit = ProposalInProgress
         \* If all the change values are valid, record the changes required to roll
         \* back the proposal and the index to which the rollback changes
         \* will roll back the configuration.
         /\ \/ LET rollbackIndex  == configuration.commit.index
                   rollbackValues == [p \in DOMAIN proposal[i].change.values |-> 
                                        IF p \in DOMAIN configuration.commit.values THEN
                                           configuration.commit.values[p]
                                        ELSE
                                           [index |-> 0, value |-> Nil]]
                   changeValues   == [p \in DOMAIN proposal[i].change.values |->
                                        proposal[i].change.values[p] @@ [index |-> i]]
               IN /\ configuration' = [configuration EXCEPT !.commit.index  = i,
                                                            !.commit.values = changeValues]
                  /\ proposal' = [proposal EXCEPT ![i].change.values   = changeValues,
                                                  ![i].rollback.values = rollbackValues,
                                                  ![i].change.commit   = ProposalComplete]
            \/ /\ configuration' = [configuration EXCEPT !.commit.index = i]
               /\ proposal' = [proposal EXCEPT ![i].change.commit = ProposalFailed]
   /\ UNCHANGED <<target>>

\* Apply a change to the target.
\* A change can be applied once all prior changes have been applied.
\* If a prior change failed being applied, it must be rolled back before
\* any subsequent change can be applied.
ApplyChange(n, i) == 
   /\ \/ /\ proposal[i].change.apply = ProposalPending
         \* To apply a change, the change must have been committed and the prior 
         \* change applied. Additionally, the configuration's applied index must
         \* match the proposed index to prevent applies while a prior change is 
         \* still being rolled back.
         /\ i-1 \in DOMAIN proposal => proposal[i-1].change.apply \in ProposalDone
         /\ configuration.apply.index = configuration.apply.proposal
         \* The change cannot be applied until the commit is complete.
         /\ \/ /\ proposal[i].change.commit = ProposalComplete
               /\ \/ /\ proposal[i].rollback.apply # ProposalPending
                     /\ configuration' = [configuration EXCEPT !.apply.proposal = i]
                     /\ proposal' = [proposal EXCEPT ![i].change.apply = ProposalInProgress]
                  \/ /\ proposal[i].rollback.apply = ProposalPending
                     /\ configuration' = [configuration EXCEPT !.apply.proposal = i,
                                                               !.apply.index    = i]
                     /\ proposal' = [proposal EXCEPT ![i].change.apply = ProposalAborted]
            \/ /\ proposal[i].change.commit \in {ProposalAborted, ProposalFailed}
               /\ configuration' = [configuration EXCEPT !.apply.proposal = i,
                                                         !.apply.index    = i]
               /\ proposal' = [proposal EXCEPT ![i].change.apply = ProposalAborted]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[i].change.apply = ProposalInProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.apply.term = mastership.term
         \* Verify the node's connection to the target.
         /\ node[n].connected
         /\ mastership.conn = node[n].incarnation
         /\ target.running
         /\ node[n].target = target.incarnation
         \* Model successful and failed target update requests.
         /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values @@ target.values]
               /\ LET values == proposal[i].change.values @@ configuration.apply.values
                  IN configuration' = [configuration EXCEPT !.apply.index  = i,
                                                            !.apply.target = target.incarnation,
                                                            !.apply.values = values]
               /\ proposal' = [proposal EXCEPT ![i].change.apply = ProposalComplete]
            \* If the proposal could not be applied, mark it failed but do not update the
            \* last applied index. The proposal must be rolled back before new proposals
            \* can be applied to the configuration/target.
            \/ /\ proposal' = [proposal EXCEPT ![i].change.apply = ProposalFailed]
               /\ UNCHANGED <<configuration, target>>

\* Commit a rollback to the configuration.
\* A change can be rolled back once all subsequent, non-pending changes have been 
\* rolled back.
CommitRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.commit = ProposalPending
         /\ configuration.commit.proposal = i
         /\ configuration.commit.index = i
         /\ i+1 \in DOMAIN proposal => proposal[i+1].rollback.commit = ProposalComplete
            \* If the change is committed, it cannot be rolled back until both the 
            \* commit proposal and the commit index match the proposal's index.
            \* This ensures this is the proposal is the last committed to the
            \* configuration.
         /\ \/ /\ proposal[i].change.commit = ProposalComplete
               /\ configuration' = [configuration EXCEPT !.commit.proposal = proposal[i].rollback.index]
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = ProposalInProgress]
            \* If the change commit failed, we still have to wait until the
            \* commit proposal and index match this proposal index, but we can
            \* complete the rollback directly from there since it failed validation
            \* and therefore was never applied to the configuration.
            \/ /\ proposal[i].change.commit = ProposalFailed
               /\ configuration' = [configuration EXCEPT !.commit.proposal = proposal[i].rollback.index,
                                                         !.commit.index    = proposal[i].rollback.index]
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = ProposalComplete]
            \* If the change commit was aborted, the rollback can be completed once the
            \* configuration's commit proposal and index match this proposal's rollback
            \* index, indicating all subsequent changes have been rolled back.
            \/ /\ proposal[i].change.commit = ProposalAborted
               /\ configuration' = [configuration EXCEPT !.commit.proposal = proposal[i].rollback.index,
                                                         !.commit.index    = proposal[i].rollback.index]
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = ProposalComplete]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[i].rollback.commit = ProposalInProgress
         /\ LET index  == proposal[i].rollback.index
                values == proposal[i].rollback.values @@ configuration.commit.values
            IN /\ configuration' = [configuration EXCEPT !.commit.index  = index,
                                                         !.commit.values = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = ProposalComplete]
   /\ UNCHANGED <<target>>

\* Commit a rollback to the target.
\* A change can be rolled back once all subsequent, non-pending changes have been 
\* rolled back.
ApplyRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.apply = ProposalPending
         /\ i+1 \in DOMAIN proposal => proposal[i+1].rollback.apply = ProposalComplete
         \* The rollback cannot be applied until the commit is complete.
         /\ proposal[i].rollback.commit = ProposalComplete
            \* If the change is applied, it cannot be rolled back until both the 
            \* apply proposal and the apply index match the proposal's index.
            \* This ensures this is the proposal is the last applied to the
            \* configuration.
         /\ \/ /\ proposal[i].change.apply = ProposalComplete
               /\ configuration.apply.proposal = i
               /\ configuration.apply.index = i
               /\ configuration' = [configuration EXCEPT !.apply.proposal = proposal[i].rollback.index]
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = ProposalInProgress]
            \* Rollbacks must be applied for failures to account for races that may 
            \* or may not have resulted in changes applying to a target.
            \* If the change commit failed, we have to wait until the applied
            \* proposal patches this proposal index and the applied index matches
            \* this proposal's rollback index before transitioning to the in-progress 
            \* state. Update the configuration's applied proposal to the rollback
            \* index and the applied index to this proposal's index to block other
            \* proposals until this rollback is complete.
            \/ /\ proposal[i].change.apply = ProposalFailed
               /\ configuration.apply.proposal = i
               /\ configuration.apply.index = proposal[i].rollback.index
               /\ configuration' = [configuration EXCEPT !.apply.proposal = proposal[i].rollback.index,
                                                         !.apply.index    = i]
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = ProposalInProgress]
            \* If the change apply was aborted, the rollback can be completed once the
            \* configuration's applied proposal and index match this proposal's rollback
            \* index, indicating all subsequent changes have been rolled back.
            \/ /\ proposal[i].change.apply = ProposalAborted
               /\ configuration.apply.proposal = i
               /\ configuration.apply.index = i
               /\ configuration' = [configuration EXCEPT !.apply.proposal = proposal[i].rollback.index,
                                                         !.apply.index    = proposal[i].rollback.index]
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = ProposalComplete]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[i].rollback.apply = ProposalInProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.apply.term = mastership.term
         \* Verify the node's connection to the target.
         /\ node[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
         /\ LET index  == proposal[i].rollback.index
                values == proposal[i].rollback.values @@ configuration.apply.values
            IN configuration' = [configuration EXCEPT !.apply.index  = index,
                                                      !.apply.values = values]
         /\ proposal' = [proposal EXCEPT ![i].rollback.apply = ProposalComplete]

ReconcileProposal(n, i) ==
   /\ mastership.master = n
   /\ \/ /\ proposal[i].change.commit \notin ProposalDone
         /\ CommitChange(n, i)
      \/ /\ proposal[i].change.apply \notin ProposalDone
         /\ ApplyChange(n, i)
      \/ /\ proposal[i].rollback.commit \notin ProposalDone
         /\ CommitRollback(n, i)
      \/ /\ proposal[i].rollback.apply \notin ProposalDone
         /\ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitProposal == 
   /\ Log!Init
   /\ proposal = [
         i \in 1..NumProposals |-> [
            phase    |-> Nil,
            change   |-> [
               values |-> [p \in {} |-> [index |-> 0, value |-> Nil]],
               commit |-> Nil,
               apply  |-> Nil],
            rollback |-> [
               index  |-> 0,
               values |-> [p \in {} |-> [index |-> 0, value |-> Nil]],
               commit |-> Nil,
               apply  |-> Nil]]]

NextProposal == 
   \/ \E n \in Nodes :
         \E i \in DOMAIN proposal :
            Log!Action(ReconcileProposal(n, i), [node |-> n, index |-> i])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 19:15:11 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:24:12 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:07:16 PST 2022 by jordanhalterman
