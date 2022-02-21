----------------------------- MODULE Proposals -----------------------------

EXTENDS Configurations, Southbound

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
   ProposalInitialize,
   ProposalValidate,
   ProposalAbort,
   ProposalCommit,
   ProposalApply

\* Status constants
CONSTANTS
   ProposalInProgress,
   ProposalComplete,
   ProposalFailed

CONSTANTS
   ProposalValid,
   ProposalInvalid

CONSTANTS
   ProposalSuccess,
   ProposalFailure

\* A record of per-target proposals
VARIABLE proposal

----

LOCAL InitState ==
   [proposals      |-> proposal,
    configurations |-> configuration,
    targets        |-> target,
    masterships    |-> mastership]

LOCAL NextState ==
   [proposals      |-> proposal',
    configurations |-> configuration',
    targets        |-> target',
    masterships    |-> mastership']

LOCAL Trace == INSTANCE Trace WITH
   Module    <- "Proposals",
   InitState <- InitState,
   NextState <- NextState

----

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].phase = ProposalInitialize
         /\ proposal[t][i].state = ProposalInProgress
         /\ proposal' = [proposal EXCEPT ![t] = 
               [proposal[t] EXCEPT ![i].state = ProposalComplete,
                                   ![i].dependency.index = configuration[t].proposal.index]]
         /\ configuration' = [configuration EXCEPT ![t].proposal.index = i]
         /\ UNCHANGED <<target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].phase = ProposalValidate
         /\ proposal[t][i].state = ProposalInProgress
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
            \* For Change proposals validate the set of requested changes.
         /\ \/ /\ proposal[t][i].type = ProposalChange
               /\ LET rollbackIndex  == configuration[t].config.index
                      rollbackValues == [p \in DOMAIN proposal[t][i].change.values |-> 
                                           IF p \in DOMAIN configuration[t].config.values THEN
                                              configuration[t].config.values[p]
                                           ELSE
                                              [delete |-> TRUE]]
                  \* Model validation successes and failures with Valid and Invalid results.
                  IN \E r \in {ProposalValid, ProposalInvalid} :
                        \* If the Change is Valid, record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        \/ /\ r = ProposalValid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].rollback = [index  |-> rollbackIndex,
                                                                                  values |-> rollbackValues],
                                                                 ![i].state    = ProposalComplete]]
                        \/ /\ r = ProposalInvalid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].state = ProposalFailed]]
            \* For Rollback proposals, validate the rollback changes which are
            \* proposal being rolled back.
            \/ /\ proposal[t][i].type = ProposalRollback
                  \* Rollbacks can only be performed on Change type proposals.
               /\ \/ /\ proposal[t][proposal[t][i].rollback.index].type = ProposalChange
                        \* Only roll back the change if it's the lastest change made
                        \* to the configuration based on the configuration index.
                     /\ \/ /\ configuration[t].config.index = proposal[t][i].rollback.index
                           /\ LET changeIndex    == proposal[t][proposal[t][i].rollback.index].rollback.index
                                  changeValues   == proposal[t][proposal[t][i].rollback.index].rollback.values
                                  rollbackValues == proposal[t][proposal[t][i].rollback.index].change.values
                              IN \E r \in {ProposalValid, ProposalInvalid} :
                                    \* If the Rollback is Valid, record the changes required to
                                    \* roll back the target proposal and the index to which the
                                    \* configuration is being rolled back.
                                    \/ /\ r = ProposalValid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].change = [index  |-> changeIndex,
                                                                                values |-> changeValues],
                                                                 ![i].change = [index  |-> proposal[t][i].change.index,
                                                                                values |-> changeValues],
                                                                 ![i].state  = ProposalComplete]]
                                    \/ /\ r = ProposalInvalid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                                         [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration[t].config.index # proposal[t][i].rollback.index
                           /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[t][proposal[t][i].rollback.index].type = ProposalRollback
                     /\ proposal' = [proposal EXCEPT ![t] = 
                           [proposal[t] EXCEPT ![i].state = ProposalFailed]]
         /\ UNCHANGED <<configuration, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].phase = ProposalCommit
         /\ proposal[t][i].state = ProposalInProgress
         \* Only commit the proposal if the prior proposal has already been committed.
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
         /\ configuration' = [configuration EXCEPT ![t].config.values = proposal[t][i].change.values,
                                                         ![t].config.index  = proposal[t][i].change.index,
                                                         ![t].commit.index  = i]
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
         /\ UNCHANGED <<target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[t][i].phase = ProposalApply
         /\ proposal[t][i].state = ProposalInProgress
         /\ configuration[t].target.index = proposal[t][i].dependency.index
         /\ configuration[t].target.term  = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {ProposalSuccess, ProposalFailure} :
               \/ /\ r = ProposalSuccess
                  /\ target' = [target EXCEPT ![t] = proposal[t][i].change.values @@ target[t]]
                  /\ configuration' = [configuration EXCEPT 
                                          ![t].target.index  = i,
                                          ![t].target.values = proposal[t][i].change.values 
                                             @@ configuration[t].target.values]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = ProposalFailure
                  /\ configuration' = [configuration EXCEPT ![t].target.index = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                  /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].phase = ProposalAbort
         /\ proposal[t][i].state = ProposalInProgress
            \* The commit.index will always be greater than or equal to the target.index.
            \* If only the commit.index matches the proposal's dependency.index, update
            \* the commit.index to enable commits of later proposals, but do not
            \* mark the Abort phase Complete until the target.index has been incremented.
         /\ \/ /\ configuration[t].commit.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].commit.index = i]
               /\ UNCHANGED <<proposal>>
            \* If the configuration's target.index matches the proposal's dependency.index, 
            \* update the target.index and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].commit.index >= i
               /\ configuration[t].target.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].target.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
            \* If both the configuration's commit.index and target.index match the
            \* proposal's dependency.index, update the commit.index and target.index
            \* and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].commit.index = proposal[t][i].dependency.index
               /\ configuration[t].target.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].commit.index = i,
                                                         ![t].target.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

InitProposal == 
   /\ proposal = [t \in {} |->
                    [i \in {} |-> 
                       [phase |-> ProposalInitialize,
                        state |-> ProposalInProgress]]]
   /\ Trace!Init

NextProposal == 
   \/ \E n \in Node :
         \E t \in DOMAIN proposal :
            \E i \in DOMAIN proposal[t] :
               Trace!Step("Reconcile", ReconcileProposal(n, t, i), [node |-> n, target |-> t, index |-> i])

=============================================================================
\* Modification History
\* Last modified Mon Feb 21 01:24:12 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:07:16 PST 2022 by jordanhalterman
