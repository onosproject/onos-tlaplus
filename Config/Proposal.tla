----------------------------- MODULE Proposal -----------------------------

EXTENDS Configuration, Mastership

INSTANCE Naturals

INSTANCE FiniteSets

LOCAL INSTANCE TLC

----

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
   ProposalInProgress,
   ProposalComplete,
   ProposalFailed

CONSTANT TraceProposal

\* A record of per-target proposals
VARIABLE proposal

----

LOCAL InitState == [
   proposals      |-> proposal,
   configurations |-> configuration,
   targets        |-> target,
   masterships    |-> mastership,
   nodes          |-> node]

LOCAL NextState == [
   proposals      |-> proposal',
   configurations |-> configuration',
   targets        |-> target',
   masterships    |-> mastership',
   nodes          |-> node']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Proposals",
   InitState <- InitState,
   NextState <- NextState,
   Enabled   <- TraceProposal

----

\* Reconcile a proposal
ReconcileProposal(n, i) ==
   \* Only the master can process proposals for the target.
   /\ mastership.master = n
      \* While in the Commit state, commit the proposed changes to the configuration.
   /\ \/ /\ proposal[i].phase = ProposalCommit
         /\ \/ /\ proposal[i].state = ProposalInProgress
               \* Only commit the proposal if the prior proposal has already been committed.
               /\ configuration.committed.index = i-1
                  \* For Change proposals validate the set of requested changes.
               /\ \/ /\ proposal[i].type = ProposalChange
                        \* If all the change values are valid, record the changes required to roll
                        \* back the proposal and the revision to which the rollback changes
                        \* will roll back the configuration.
                     /\ \/ LET rollbackRevision == configuration.committed.revision
                               rollbackValues   == [p \in DOMAIN proposal[i].change.values |-> 
                                                      IF p \in DOMAIN configuration.committed.values THEN
                                                         configuration.committed.values[p]
                                                      ELSE
                                                         [delete |-> TRUE]]
                               changeValues     == [p \in DOMAIN proposal[i].change.values |->
                                                      proposal[i].change.values[p] @@ [index |-> i]]
                           IN /\ configuration' = [configuration EXCEPT !.committed.revision = i,
                                                                        !.committed.values   = changeValues]
                              /\ proposal' = [proposal EXCEPT ![i].change = [
                                                                 revision |-> i,
                                                                 values   |-> changeValues],
                                                              ![i].rollback = [
                                                                 revision |-> rollbackRevision,
                                                                 values   |-> rollbackValues],
                                                              ![i].state = ProposalComplete]
                        \* A proposal can fail validation at this point, in which case the proposal
                        \* is marked failed.
                        \/ /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
                           /\ UNCHANGED <<configuration>>
                  \* For Rollback proposals, validate the rollback changes which are
                  \* proposal being rolled back.
                  \/ /\ proposal[i].type = ProposalRollback
                        \* Rollbacks can only be performed on Change type proposals.
                     /\ \/ /\ proposal[proposal[i].rollback.index].type = ProposalChange
                              \* Only roll back the change if it's the lastest change made
                              \* to the configuration based on the configuration revision.
                           /\ \/ /\ configuration.committed.revision = proposal[i].rollback.index
                                 \* Record the changes required to roll back the target proposal and the index to 
                                 \* which the configuration is being rolled back.
                                 /\ LET changeRevision == proposal[proposal[i].rollback.index].rollback.revision
                                        changeValues   == proposal[proposal[i].rollback.index].rollback.values
                                    IN /\ configuration' = [configuration EXCEPT !.committed.revision = changeRevision,
                                                                                 !.committed.values   = changeValues]
                                       /\ proposal' = [proposal EXCEPT ![i].change = [
                                                                          revision |-> changeRevision,
                                                                          values   |-> changeValues],
                                                                       ![i].state  = ProposalComplete]
                              \* If the Rollback target is not the most recent change to the configuration,
                              \* fail validation for the proposal.
                              \/ /\ configuration.committed.revision # proposal[i].rollback.index
                                 /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
                                 /\ UNCHANGED <<configuration>>
                        \* If a Rollback proposal is attempting to roll back another Rollback,
                        \* fail validation for the proposal.
                        \/ /\ proposal[proposal[i].rollback.index].type = ProposalRollback
                           /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
                           /\ UNCHANGED <<configuration>>
               /\ UNCHANGED <<target>>
            \* Once the proposal is committed, update the configuration's commit index
            \* and move to the apply phase.
            \/ /\ proposal[i].state = ProposalComplete
               /\ configuration' = [configuration EXCEPT !.committed.index = i]
               /\ proposal' = [proposal EXCEPT ![i].phase = ProposalApply,
                                               ![i].state = ProposalInProgress]
               /\ UNCHANGED <<target>>
            \* If the proposal fails, mark the configuration applied for the proposal index.
            \/ /\ proposal[i].state = ProposalFailed
               /\ \/ /\ configuration.committed.index = i-1
                     /\ configuration' = [configuration EXCEPT !.committed.index = i]
                  \/ /\ configuration.applied.index = i-1
                     /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ UNCHANGED <<proposal, target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[i].phase = ProposalApply
            \* For the proposal to be applied, the node must be connected to a running target.
         /\ \/ /\ proposal[i].state = ProposalInProgress
               \* Verify the applied index is the previous proposal index to ensure
               \* changes are applied to the target in order.
               /\ configuration.applied.index = i-1
               \* Verify the applied term is the current mastership term to ensure the
               \* configuration has been synchronized following restarts.
               /\ configuration.applied.term = mastership.term
               \* Verify the node's connection to the target.
               /\ node[n].connected
               /\ target.running
               \* Model successful and failed target update requests.
               /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values]
                     /\ LET revision == proposal[i].change.revision
                            values   == proposal[i].change.values @@ configuration.applied.values
                        IN configuration' = [configuration EXCEPT !.applied.index    = i,
                                                                  !.applied.revision = revision,
                                                                  !.applied.values   = values]
                     /\ proposal' = [proposal EXCEPT ![i].state = ProposalComplete]
                  \* If the proposal could not be applied, update the configuration's applied index
                  \* and mark the proposal Failed.
                  \/ /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
                     /\ UNCHANGED <<configuration, target>>
            \* Once the proposal is applied, update the configuration's applied index.
            \/ /\ proposal[i].state = ProposalComplete
               /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ UNCHANGED <<proposal, target>>
            \* If the proposal fails, mark the configuration applied for the proposal index.
            \/ /\ proposal[i].state = ProposalFailed
               /\ configuration.applied.index = i-1
               /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ UNCHANGED <<proposal, target>>
   /\ UNCHANGED <<mastership, node>>

----

(*
Formal specification, constraints, and theorems.
*)

InitProposal == 
   /\ proposal = [
         i \in {} |-> [
            type     |-> ProposalChange,
            change   |-> [
               revision |-> 0,
               values   |-> [p \in {} |-> [index |-> 0, value |-> Nil, delete |-> FALSE]]],
            rollback |-> [
               index    |-> 0, 
               revision |-> 0,
               values   |-> [p \in {} |-> [index |-> 0, value |-> Nil, delete |-> FALSE]]],
            phase    |-> ProposalCommit,
            state    |-> ProposalInProgress]]
   /\ Trace!Init

NextProposal == 
   \/ \E n \in Node :
         \E i \in DOMAIN proposal :
            Trace!Step(ReconcileProposal(n, i), [node |-> n, index |-> i])

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 19:15:11 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:24:12 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:07:16 PST 2022 by jordanhalterman
