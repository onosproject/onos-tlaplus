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
         /\ \/ /\ proposal[t][i].state = ProposalInProgress
               /\ proposal' = [proposal EXCEPT ![t] = 
                     [proposal[t] EXCEPT ![i].state = ProposalComplete]]
               /\ configuration' = [configuration EXCEPT ![t].proposed.index = i]
               /\ UNCHANGED <<target>>
            \/ /\ proposal[t][i].state = ProposalComplete
               /\ proposal' = [proposal EXCEPT ![t] = 
                     [proposal[t] EXCEPT ![i].phase = ProposalValidate,
                                         ![i].state = ProposalInProgress]]
               /\ UNCHANGED <<configuration, target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].phase = ProposalValidate
         /\ \/ /\ proposal[t][i].state = ProposalInProgress
               /\ configuration[t].index = i-1
                  \* For Change proposals validate the set of requested changes.
               /\ \/ /\ proposal[t][i].type = ProposalChange
                     /\ LET rollbackIndex  == configuration[t].committed.index
                            rollbackValues == [p \in DOMAIN proposal[t][i].change.values |-> 
                                                 IF p \in DOMAIN configuration[t].committed.values THEN
                                                    configuration[t].committed.values[p]
                                                 ELSE
                                                    [delete |-> TRUE]]
                        \* If all the change values are valid,record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        IN 
                           \/ /\ \A p \in DOMAIN proposal[t][i].change.values : proposal[t][i].change.values[p].valid
                              /\ proposal' = [proposal EXCEPT ![t] = 
                                                [proposal[t] EXCEPT ![i].rollback = [index  |-> rollbackIndex,
                                                                                     values |-> rollbackValues],
                                                                    ![i].state    = ProposalComplete]]
                           \/ /\ \E p \in DOMAIN proposal[t][i].change.values : ~proposal[t][i].change.values[p].valid
                              /\ proposal' = [proposal EXCEPT ![t] = 
                                                [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                  \* For Rollback proposals, validate the rollback changes which are
                  \* proposal being rolled back.
                  \/ /\ proposal[t][i].type = ProposalRollback
                        \* Rollbacks can only be performed on Change type proposals.
                     /\ \/ /\ proposal[t][proposal[t][i].rollback.index].type = ProposalChange
                              \* Only roll back the change if it's the lastest change made
                              \* to the configuration based on the configuration index.
                           /\ \/ /\ configuration[t].committed.index = proposal[t][i].rollback.index
                                 /\ LET changeIndex    == proposal[t][proposal[t][i].rollback.index].rollback.index
                                        changeValues   == proposal[t][proposal[t][i].rollback.index].rollback.values
                                        rollbackValues == proposal[t][proposal[t][i].rollback.index].change.values
                                    \* Record the changes required to roll back the target proposal and the index to 
                                    \* which the configuration is being rolled back.
                                    IN /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].change = [index  |-> changeIndex,
                                                                                values |-> changeValues],
                                                                 ![i].change = [index  |-> proposal[t][i].change.index,
                                                                                values |-> changeValues],
                                                                 ![i].state  = ProposalComplete]]
                              \* If the Rollback target is not the most recent change to the configuration,
                              \* fail validation for the proposal.
                              \/ /\ configuration[t].committed.index # proposal[t][i].rollback.index
                                 /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                        \* If a Rollback proposal is attempting to roll back another Rollback,
                        \* fail validation for the proposal.
                        \/ /\ proposal[t][proposal[t][i].rollback.index].type = ProposalRollback
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                 [proposal[t] EXCEPT ![i].state = ProposalFailed]]
               /\ UNCHANGED <<configuration, target>>
            \/ /\ proposal[t][i].state = ProposalComplete
               /\ proposal' = [proposal EXCEPT ![t] = 
                     [proposal[t] EXCEPT ![i].phase = ProposalCommit,
                                         ![i].state = ProposalInProgress]]
               /\ UNCHANGED <<configuration, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].phase = ProposalCommit
         /\ \/ /\ proposal[t][i].state = ProposalInProgress
               \* Only commit the proposal if the prior proposal has already been committed.
               /\ configuration[t].index = i-1
               /\ configuration' = [configuration EXCEPT ![t].committed.values = proposal[t][i].change.values,
                                                         ![t].committed.index  = proposal[t][i].change.index,
                                                         ![t].index            = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
               /\ UNCHANGED <<target>>
            \/ /\ proposal[t][i].state = ProposalComplete
               /\ proposal' = [proposal EXCEPT ![t] = 
                     [proposal[t] EXCEPT ![i].phase = ProposalApply,
                                         ![i].state = ProposalInProgress]]
               /\ UNCHANGED <<configuration, target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[t][i].phase = ProposalApply
         /\ proposal[t][i].state = ProposalInProgress
         /\ configuration[t].applied.index = i-1
         /\ configuration[t].applied.term  = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {ProposalSuccess, ProposalFailure} :
               \/ /\ r = ProposalSuccess
                  /\ target' = [target EXCEPT ![t] = proposal[t][i].change.values @@ target[t]]
                  /\ configuration' = [configuration EXCEPT 
                                          ![t].applied.index  = i,
                                          ![t].applied.values = proposal[t][i].change.values 
                                             @@ configuration[t].applied.values]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = ProposalFailure
                  /\ configuration' = [configuration EXCEPT ![t].applied.index = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalFailed]]
                  /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].phase = ProposalAbort
         /\ proposal[t][i].state = ProposalInProgress
            \* The index will always be greater than or equal to the applied.index.
            \* If only the index matches the previous proposal index, update
            \* the index to enable commits of later proposals, but do not
            \* mark the Abort phase Complete until the applied.index has been incremented.
         /\ \/ /\ configuration[t].index = i-1
               /\ configuration' = [configuration EXCEPT ![t].index = i]
               /\ UNCHANGED <<proposal>>
            \* If the configuration's applied.index matches the previous proposal index, 
            \* update the applied.index and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].index >= i
               /\ configuration[t].applied.index = i-1
               /\ configuration' = [configuration EXCEPT ![t].applied.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
            \* If both the configuration's index and applied.index match the
            \* previous proposal index, update the index and applied.index
            \* and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].index = i-1
               /\ configuration[t].applied.index = i-1
               /\ configuration' = [configuration EXCEPT ![t].index         = i,
                                                         ![t].applied.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = ProposalComplete]]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<mastership>>

----

(*
Formal specification, constraints, and theorems.
*)

InitProposal == 
   /\ proposal = [t \in DOMAIN Target |->
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
\* Last modified Fri Apr 21 19:15:11 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:24:12 PST 2022 by jordanhalterman
\* Created Sun Feb 20 10:07:16 PST 2022 by jordanhalterman
