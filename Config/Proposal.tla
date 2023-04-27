----------------------------- MODULE Proposal -----------------------------

EXTENDS Configuration, Mastership

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

CONSTANT NumProposals

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
   ProposalFailed

CONSTANT TraceProposal

\* A record of per-target proposals
VARIABLE proposal

----

LOCAL InitState == [
   proposals     |-> [i \in {i \in DOMAIN proposal : proposal[i].state # Nil} |-> proposal[i]],
   configuration |-> configuration,
   target        |-> target,
   mastership    |-> mastership,
   nodes         |-> node]

LOCAL NextState == [
   proposals     |-> [i \in {i \in DOMAIN proposal' : proposal'[i].state # Nil} |-> proposal'[i]],
   configuration |-> configuration',
   target        |-> target',
   mastership    |-> mastership',
   nodes         |-> node']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Proposal",
   InitState <- InitState,
   NextState <- NextState,
   Enabled   <- TraceProposal

----

\* Commit a change to the configuration.
\* A change can be committed once all prior changes have been committed.
\* If a prior change is being rolled back, the rollback must complete
\* before the change can be committed. Changes must be committed in
\* sequential order.
\* Once a change commit is in progress, the change must be committed or
\* failed before it can be applied or rolled back.
CommitChange(n, i) == 
   /\ \/ /\ proposal[i].change.status = ProposalPending
         \* To commit a change, the commit index must be the prior index,
         \* and the target commit index must match the commit revision.
         /\ configuration.commit.index = i-1
         /\ configuration.commit.revision = configuration.commit.target
         /\ configuration' = [configuration EXCEPT !.commit.index  = i,
                                                   !.commit.target = i]
         /\ proposal' = [proposal EXCEPT ![i].change.status = ProposalInProgress]
      \/ /\ proposal[i].change.status = ProposalInProgress
         \* If all the change values are valid, record the changes required to roll
         \* back the proposal and the index to which the rollback changes
         \* will roll back the configuration.
         /\ \/ LET rollbackRevision == configuration.commit.revision
                   rollbackValues   == [p \in DOMAIN proposal[i].change.values |-> 
                                          IF p \in DOMAIN configuration.commit.values THEN
                                             configuration.commit.values[p]
                                          ELSE
                                             [index |-> 0, value |-> Nil]]
                   changeValues     == [p \in DOMAIN proposal[i].change.values |->
                                          proposal[i].change.values[p] @@ [index |-> i]]
               IN /\ configuration' = [configuration EXCEPT !.commit.revision = i,
                                                            !.commit.values   = changeValues]
                  /\ proposal' = [proposal EXCEPT ![i].change.values     = changeValues,
                                                  ![i].change.phase      = ProposalApply,
                                                  ![i].change.status     = ProposalPending,
                                                  ![i].rollback.revision = rollbackRevision,
                                                  ![i].rollback.values   = rollbackValues]
            \/ /\ configuration' = [configuration EXCEPT !.commit.revision = i]
               /\ proposal' = [proposal EXCEPT ![i].change.status = ProposalFailed]
   /\ UNCHANGED <<target>>

\* Apply a change to the target.
\* A change can be applied once all prior changes have been applied.
\* If a prior change failed being applied, it must be rolled back before
\* any subsequent change can be applied.
ApplyChange(n, i) == 
   /\ \/ /\ proposal[i].change.status = ProposalPending
         \* To apply a change, the apply index must be the prior index.
         /\ configuration.apply.index = i-1
         /\ configuration.apply.revision = configuration.apply.target
         /\ configuration' = [configuration EXCEPT !.apply.index  = i,
                                                   !.apply.target = i]
         /\ proposal' = [proposal EXCEPT ![i].change.status = ProposalInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[i].change.status = ProposalInProgress
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
                  IN configuration' = [configuration EXCEPT !.apply.revision    = i,
                                                            !.apply.incarnation = target.incarnation,
                                                            !.apply.values      = values]
               /\ proposal' = [proposal EXCEPT ![i].change.status = ProposalComplete]
            \* If the proposal could not be applied, mark it failed but do not update the
            \* last applied index. The proposal must be rolled back before new proposals
            \* can be applied to the configuration/target.
            \/ /\ proposal' = [proposal EXCEPT ![i].change.status = ProposalFailed]
               /\ UNCHANGED <<configuration, target>>

\* Commit a rollback to the configuration.
\* A change can be rolled back once all subsequent, non-pending changes have been 
\* rolled back.
CommitRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.status = ProposalPending
         /\ configuration.commit.target = i
         /\ configuration.commit.revision = i
         /\ configuration' = [configuration EXCEPT !.commit.target = proposal[i].rollback.revision]
         /\ proposal' = [proposal EXCEPT ![i].rollback.status = ProposalInProgress]
      \/ /\ proposal[i].rollback.status = ProposalInProgress
         /\ LET revision == proposal[i].rollback.revision
                values   == proposal[i].rollback.values
            IN /\ configuration' = [configuration EXCEPT !.commit.revision = revision,
                                                         !.commit.values   = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.phase  = ProposalApply,
                                               ![i].rollback.status = ProposalPending]
   /\ UNCHANGED <<target>>

\* Commit a rollback to the target.
\* A change can be rolled back once all subsequent, non-pending changes have been 
\* rolled back.
ApplyRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.status = ProposalPending
         /\ configuration.apply.target = i
         /\ configuration.apply.revision = i
         /\ configuration' = [configuration EXCEPT !.apply.target = proposal[i].rollback.revision]
         /\ proposal' = [proposal EXCEPT ![i].rollback.status = ProposalInProgress]
         /\ UNCHANGED <<target>>
      \/ /\ proposal[i].rollback.status = ProposalInProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.apply.term = mastership.term
         \* Verify the node's connection to the target.
         /\ node[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
         /\ LET revision == proposal[i].rollback.revision
                values   == proposal[i].rollback.values @@ configuration.apply.values
            IN configuration' = [configuration EXCEPT !.apply.revision = revision,
                                                      !.apply.values   = values]
         /\ proposal' = [proposal EXCEPT ![i].rollback.status = ProposalComplete]

ReconcileProposal(n, i) ==
   /\ mastership.master = n
   /\ \/ /\ proposal[i].state = ProposalChange
         /\ \/ /\ proposal[i].change.phase = ProposalCommit
               /\ CommitChange(n, i)
            \/ /\ proposal[i].change.phase = ProposalApply
               /\ ApplyChange(n, i)
      \/ /\ proposal[i].state = ProposalRollback
         /\ \/ /\ proposal[i].rollback.phase = ProposalCommit
               /\ CommitRollback(n, i)
            \/ /\ proposal[i].rollback.phase = ProposalApply
               /\ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitProposal == 
   /\ proposal = [
         i \in 1..NumProposals |-> [
            state    |-> Nil,
            change   |-> [
               values |-> [p \in {} |-> [index |-> 0, value |-> Nil]],
               phase  |-> Nil,
               status |-> Nil],
            rollback |-> [
               revision |-> 0,
               values   |-> [p \in {} |-> [index |-> 0, value |-> Nil]],
               phase    |-> Nil,
               status   |-> Nil]]]
   /\ Trace!Init

NextProposal == 
   \/ \E n \in Nodes :
         \E i \in DOMAIN proposal :
            Trace!Step(ReconcileProposal(n, i), [node |-> n, index |-> i])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 19:15:11 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:24:12 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:07:16 PST 2022 by jordanhalterman
