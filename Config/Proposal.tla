------------------------------- MODULE Proposal -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Transaction type constants
CONSTANTS
   Change,
   Rollback

\* Phase constants
CONSTANTS
   Initialize,
   Validate,
   Abort,
   Commit,
   Apply

Phase ==
   {Initialize,
    Validate,
    Abort,
    Commit,
    Apply}

\* Status constants
CONSTANTS
   InProgress,
   Complete,
   Failed

State == 
   {InProgress,
    Complete,
    Failed}

\* State constants
CONSTANTS
   Pending,
   Validated,
   Committed,
   Applied,
   Aborted

Status ==
   {Pending,
    Validated,
    Committed,
    Applied,
    Aborted}

CONSTANTS
   Valid,
   Invalid

CONSTANTS
   Success,
   Failure

\* The set of all nodes
CONSTANT Node

----

\* A record of per-target proposals
VARIABLE proposal

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masterships
VARIABLE mastership

----

\* Reconcile a proposal
ReconcileProposal(n, t, i) ==
   /\ \/ /\ proposal[t][i].phase = Initialize
         /\ proposal[t][i].state = InProgress
         /\ proposal' = [proposal EXCEPT ![t] = 
               [proposal[t] EXCEPT ![i].state = Complete,
                                   ![i].dependency.index = configuration[t].proposal.index]]
         /\ configuration' = [configuration EXCEPT ![t].proposal.index = i]
         /\ UNCHANGED <<target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[t][i].phase = Validate
         /\ proposal[t][i].state = InProgress
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
            \* For Change proposals validate the set of requested changes.
         /\ \/ /\ proposal[t][i].type = Change
               /\ LET rollbackIndex  == configuration[t].config.index
                      rollbackValues == [p \in DOMAIN proposal[t][i].change.values |-> 
                                           IF p \in DOMAIN configuration[t].config.values THEN
                                              configuration[t].config.values[p]
                                           ELSE
                                              [value  |-> Nil, 
                                               delete |-> TRUE]]
                  \* Model validation successes and failures with Valid and Invalid results.
                  IN \E r \in {Valid, Invalid} :
                        \* If the Change is Valid, record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        \/ /\ r = Valid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].rollback.index  = rollbackIndex,
                                                                 ![i].rollback.values = rollbackValues,
                                                                 ![i].state           = Complete]]
                        \/ /\ r = Invalid
                           /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].state = Failed]]
            \* For Rollback proposals, validate the rollback changes which are
            \* proposal being rolled back.
            \/ /\ proposal[t][i].type = Rollback
                  \* Rollbacks can only be performed on Change type proposals.
               /\ \/ /\ proposal[t][proposal[t][i].rollback.index].type = Change
                        \* Only roll back the change if it's the lastest change made
                        \* to the configuration based on the configuration index.
                     /\ \/ /\ configuration[t].config.index = proposal[t][i].rollback.index
                           /\ LET changeIndex    == proposal[t][proposal[t][i].rollback.index].rollback.index
                                  changeValues   == proposal[t][proposal[t][i].rollback.index].rollback.values
                                  rollbackValues == proposal[t][proposal[t][i].rollback.index].change.values
                              IN \E r \in {Valid, Invalid} :
                                    \* If the Rollback is Valid, record the changes required to
                                    \* roll back the target proposal and the index to which the
                                    \* configuration is being rolled back.
                                    \/ /\ r = Valid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                             [proposal[t] EXCEPT ![i].change.index    = changeIndex,
                                                                 ![i].change.values   = changeValues,
                                                                 ![i].rollback.values = rollbackValues,
                                                                 ![i].state           = Complete]]
                                    \/ /\ r = Invalid
                                       /\ proposal' = [proposal EXCEPT ![t] = 
                                                         [proposal[t] EXCEPT ![i].state = Failed]]
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration[t].config.index # proposal[t][i].rollback.index
                           /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Failed]]
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[t][proposal[t][i].rollback.index].type = Rollback
                     /\ proposal' = [proposal EXCEPT ![t] = 
                           [proposal[t] EXCEPT ![i].state = Failed]]
         /\ UNCHANGED <<configuration, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[t][i].phase = Commit
         /\ proposal[t][i].state = InProgress
         \* Only commit the proposal if the prior proposal has already been committed.
         /\ configuration[t].commit.index = proposal[t][i].dependency.index
         /\ configuration' = [configuration EXCEPT ![t].config.values = proposal[t][i].change.values,
                                                         ![t].config.index  = proposal[t][i].change.index,
                                                         ![t].commit.index  = i]
         /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
         /\ UNCHANGED <<target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[t][i].phase = Apply
         /\ proposal[t][i].state = InProgress
         /\ configuration[t].target.index = proposal[t][i].dependency.index
         /\ configuration[t].target.term  = mastership[t].term
         /\ mastership[t].master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                  /\ target' = [target EXCEPT ![t] = proposal[t][i].change.values @@ target[t]]
                  /\ configuration' = [configuration EXCEPT 
                                          ![t].target.index  = i,
                                          ![t].target.values = proposal[t][i].change.values 
                                             @@ configuration[t].target.values]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT ![t].target.index = i]
                  /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Failed]]
                  /\ UNCHANGED <<target>>
      \/ /\ proposal[t][i].phase = Abort
         /\ proposal[t][i].state = InProgress
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
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
            \* If both the configuration's commit.index and target.index match the
            \* proposal's dependency.index, update the commit.index and target.index
            \* and mark the proposal Complete for the Abort phase.
            \/ /\ configuration[t].commit.index = proposal[t][i].dependency.index
               /\ configuration[t].target.index = proposal[t][i].dependency.index
               /\ configuration' = [configuration EXCEPT ![t].commit.index = i,
                                                         ![t].target.index = i]
               /\ proposal' = [proposal EXCEPT ![t] = [proposal[t] EXCEPT ![i].state = Complete]]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<mastership>>

=============================================================================
