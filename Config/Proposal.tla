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
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                     /\ \/ LET rollbackIndex  == configuration.committed.revision
                               rollbackValues == [p \in DOMAIN proposal[i].change.values |-> 
                                                     IF p \in DOMAIN configuration.committed.values THEN
                                                        configuration.committed.values[p]
                                                     ELSE
                                                        [index |-> 0, value |-> Nil]]
                               changeValues   == [p \in DOMAIN proposal[i].change.values |->
                                                     proposal[i].change.values[p] @@ [index |-> i]]
                           IN /\ configuration' = [configuration EXCEPT !.committed.index    = i,
                                                                        !.committed.revision = i,
                                                                        !.committed.values   = changeValues]
                              /\ proposal' = [proposal EXCEPT ![i].change = [
                                                                 index  |-> i,
                                                                 values |-> changeValues],
                                                              ![i].rollback = [
                                                                 index  |-> rollbackIndex,
                                                                 values |-> rollbackValues],
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
                              \* Only roll back the change if it's the latest change made
                              \* to the configuration based on the configuration index.
                           /\ \/ /\ configuration.committed.revision = proposal[i].rollback.index
                                 \* Record the changes required to roll back the target proposal and the index to 
                                 \* which the configuration is being rolled back.
                                 /\ LET changeIndex  == proposal[proposal[i].rollback.index].rollback.index
                                        changeValues == proposal[proposal[i].rollback.index].rollback.values
                                       \* Note: these two changes must be implemented as an atomic, idempotent update.
                                       \* Implementations should check if the configuration has already been updated and 
                                       \* skip the configuration update if the committed index is >= the proposal index.
                                    IN /\ configuration' = [configuration EXCEPT !.committed.index    = i,
                                                                                 !.committed.revision = changeIndex,
                                                                                 !.committed.values   = changeValues]
                                       /\ proposal' = [proposal EXCEPT ![i].change = [
                                                                          index  |-> changeIndex,
                                                                          values |-> changeValues],
                                                                       ![i].state  = ProposalComplete]
                              \* If the Rollback target is not the most recent change to the configuration,
                              \* fail validation for the proposal.
                              \/ /\ configuration.committed.revision # proposal[i].rollback.index
                                 \* Note: these two changes must be implemented as an atomic, idempotent update.
                                 \* Implementations should check if the configuration has already been updated and 
                                 \* skip the configuration update if the committed index is >= the proposal index.
                                 /\ configuration' = [configuration EXCEPT !.committed.index = i]
                                 /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
                        \* If a Rollback proposal is attempting to roll back another Rollback,
                        \* fail validation for the proposal.
                        \/ /\ proposal[proposal[i].rollback.index].type = ProposalRollback
                           \* Note: these two changes must be implemented as an atomic, idempotent update.
                           \* Implementations should check if the configuration has already been updated and 
                           \* skip the configuration update if the committed index is >= the proposal index.
                           /\ configuration' = [configuration EXCEPT !.committed.index = i]
                           /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
               /\ UNCHANGED <<target>>
            \* Once the proposal is committed, update the configuration's commit index
            \* and move to the apply phase.
            \/ /\ proposal[i].state = ProposalComplete
               /\ proposal' = [proposal EXCEPT ![i].phase = ProposalApply,
                                               ![i].state = ProposalInProgress]
               /\ UNCHANGED <<configuration, target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[i].phase = ProposalApply
         /\ configuration.applied.index = i-1
         /\ proposal[i].state = ProposalInProgress
         \* Process the proposal once the prior proposal has been applied.
         /\ i-1 \in DOMAIN proposal =>
               \/ /\ proposal[i-1].phase = ProposalCommit
                  /\ proposal[i-1].state = ProposalFailed
               \/ /\ proposal[i-1].phase = ProposalApply
                  /\ proposal[i-1].state \in {ProposalComplete, ProposalFailed}
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ node[n].connected
         /\ target.running
         \* Model successful and failed target update requests.
         /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values]
               \* Note: these two changes must be implemented as an atomic, idempotent update.
               \* Implementations should check if the configuration has already been updated and 
               \* skip the configuration update if the applied index is >= the proposal index.
               /\ LET index  == proposal[i].change.index
                      values == proposal[i].change.values @@ configuration.applied.values
                  IN configuration' = [configuration EXCEPT !.applied.index    = i,
                                                            !.applied.revision = index,
                                                            !.applied.values   = values]
               /\ proposal' = [proposal EXCEPT ![i].state = ProposalComplete]
            \* If the proposal could not be applied, update the configuration's applied index
            \* and mark the proposal Failed.
            \* Note: these two changes must be implemented as an atomic, idempotent update.
            \* Implementations should check if the configuration has already been updated and 
            \* skip the configuration update if the applied index is >= the proposal index.
            \/ /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
               /\ UNCHANGED <<target>>
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
               index  |-> 0,
               values |-> [p \in {} |-> [index |-> 0, value |-> Nil, delete |-> FALSE]]],
            rollback |-> [
               index  |-> 0,
               values |-> [p \in {} |-> [index |-> 0, value |-> Nil, delete |-> FALSE]]],
            phase    |-> ProposalCommit,
            state    |-> ProposalInProgress]]
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
