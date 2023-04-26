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
   proposals     |-> proposal,
   configuration |-> configuration,
   target        |-> target,
   mastership    |-> mastership,
   nodes         |-> node]

LOCAL NextState == [
   proposals     |-> proposal',
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

CommitChange(n, i) == 
   \* Change proposals cannot be validated and committed until the prior index has
   \* been validated and committed and the configuration values updated.
   /\ configuration.committed.index = i-1
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
                                             ![i].phase  = ProposalApply,
                                             ![i].state  = ProposalInProgress]
      \* A proposal can fail validation at this point, in which case the proposal
      \* is marked failed.
      \/ /\ configuration' = [configuration EXCEPT !.committed.index = i]
         /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
   /\ UNCHANGED <<target>>

CommitRollback(n, i) == 
   \* Rollbacks can only be done on change type proposals.
   /\ \/ /\ proposal[proposal[i].rollback.index].type = ProposalChange
         \* If the change is the latest made to the configuration, roll it back.
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
                                                      ![i].phase  = ProposalApply,
                                                      ![i].state  = ProposalInProgress]
            \* If the change has not yet been committed to the configuration, abort it.
            \/ /\ configuration.committed.revision < proposal[i].rollback.index
               /\ proposal' = [proposal EXCEPT ![i].state = ProposalComplete,
                                               ![proposal[i].rollback.index].state = ProposalFailed]
               /\ UNCHANGED <<configuration>>
            \* If another change needs to be rolled back before this change can be,
            \* fail the rollback.
            \/ /\ configuration.committed.revision > proposal[i].rollback.index
               /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
               /\ UNCHANGED <<configuration>>
      \* If a Rollback proposal is attempting to roll back another Rollback,
      \* fail validation for the proposal.
      \/ /\ proposal[proposal[i].rollback.index].type = ProposalRollback
         /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
         /\ UNCHANGED <<configuration>>
   /\ UNCHANGED <<target>>

ApplyChange(n, i) == 
   \* Change proposals cannot be applied until the prior index has
   \* been applied and the configuration's applied index updated.
   /\ configuration.applied.index = i-1
   \* Verify the applied term is the current mastership term to ensure the
   \* configuration has been synchronized following restarts.
   /\ configuration.applied.term = mastership.term
   \* Verify the node's connection to the target.
   /\ node[n].connected
   /\ target.running
   \* Model successful and failed target update requests.
   /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values]
         /\ LET index  == proposal[i].change.index
                values == proposal[i].change.values @@ configuration.applied.values
            IN configuration' = [configuration EXCEPT !.applied.index    = i,
                                                      !.applied.revision = index,
                                                      !.applied.values   = values]
         /\ proposal' = [proposal EXCEPT ![i].state = ProposalComplete]
      \* If the proposal could not be applied, mark it failed but do not update the
      \* last applied index. The proposal must be rolled back before new proposals
      \* can be applied to the configuration/target.
      \/ /\ configuration' = [configuration EXCEPT !.applied.index = i]
         /\ proposal' = [proposal EXCEPT ![i].state = ProposalFailed]
         /\ UNCHANGED <<target>>

ApplyRollback(n, i) == 
   \* Verify the applied term is the current mastership term to ensure the
   \* configuration has been synchronized following restarts.
   /\ configuration.applied.term = mastership.term
   \* Verify the node's connection to the target.
   /\ node[n].connected
   /\ target.running
   \* The target change cannot be rolled back until it has been applied.
   /\ configuration.applied.revision = proposal[i].rollback.index
   /\ target' = [target EXCEPT !.values = proposal[i].change.values]
   /\ LET index  == proposal[i].change.index
          values == proposal[i].change.values @@ configuration.applied.values
      IN configuration' = [configuration EXCEPT !.applied.index    = i,
                                                !.applied.revision = index,
                                                !.applied.values   = values]
   /\ proposal' = [proposal EXCEPT ![i].state = ProposalComplete]

ReconcileProposal(n, i) ==
   /\ mastership.master = n
   /\ \/ /\ proposal[i].phase = ProposalCommit
         /\ proposal[i].state = ProposalInProgress
         /\ \/ /\ proposal[i].type = ProposalChange
               /\ CommitChange(n, i)
            \/ /\ proposal[i].type = ProposalRollback
               /\ CommitRollback(n, i)
      \/ /\ proposal[i].phase = ProposalApply
         /\ proposal[i].state = ProposalInProgress
         /\ \/ /\ proposal[i].type = ProposalChange
               /\ ApplyChange(n, i)
            \/ /\ proposal[i].type = ProposalRollback
               /\ ApplyRollback(n, i)
      \* If the proposal is complete, increment the applied index in sequential order
      \* to unblock proposals in the apply phase.
      \/ /\ proposal[i].state \in {ProposalComplete, ProposalFailed}
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
