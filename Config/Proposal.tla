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
   Commit,
   Apply

Phase ==
   {Initialize,
    Validate,
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

Test == INSTANCE Test WITH 
   File      <- "Proposal.log",
   CurrState <- [
      proposals     |-> proposal,
      configuration |-> configuration,
      mastership    |-> mastership,
      target        |-> target],
   SuccState <- [
      proposals     |-> proposal',
      configuration |-> configuration',
      mastership    |-> mastership',
      target        |-> target']

----

\* Reconcile a proposal
ReconcileProposal(n, i) ==
   /\ i \in DOMAIN proposal
   /\ \/ /\ proposal[i].phase = Initialize
         /\ proposal[i].state = InProgress
         /\ proposal' = [proposal EXCEPT ![i].state = Complete]
         /\ configuration' = [configuration EXCEPT !.proposal.index = i]
         /\ UNCHANGED <<target>>
      \* While in the Validate phase, validate the proposed changes.
      \* If validation is successful, the proposal also records the changes
      \* required to roll back the proposal and the index to which to roll back.
      \/ /\ proposal[i].phase = Validate
         /\ proposal[i].state = InProgress
         /\ configuration.commit.index = i-1
            \* For Change proposals validate the set of requested changes.
         /\ \/ /\ proposal[i].type = Change
               /\ LET rollbackIndex  == configuration.config.index
                      rollbackValues == [p \in DOMAIN proposal[i].change.values |-> 
                                           IF p \in DOMAIN configuration.config.values THEN
                                              configuration.config.values[p]
                                           ELSE
                                              [value  |-> Nil, 
                                               delete |-> TRUE]]
                  \* Model validation successes and failures with Valid and Invalid results.
                  IN \E r \in {Valid, Invalid} :
                        \* If the Change is Valid, record the changes required to roll
                        \* back the proposal and the index to which the rollback changes
                        \* will roll back the configuration.
                        \/ /\ r = Valid
                           /\ proposal' = [proposal EXCEPT ![i].rollback.index  = rollbackIndex,
                                                           ![i].rollback.values = rollbackValues,
                                                           ![i].state           = Complete]
                        \/ /\ r = Invalid
                           /\ proposal' = [proposal EXCEPT ![i].state = Failed]
            \* For Rollback proposals, validate the rollback changes which are
            \* proposal being rolled back.
            \/ /\ proposal[i].type = Rollback
                  \* Rollbacks can only be performed on Change type proposals.
               /\ \/ /\ proposal[proposal[i].rollback.index].type = Change
                        \* Only roll back the change if it's the lastest change made
                        \* to the configuration based on the configuration index.
                     /\ \/ /\ configuration.config.index = proposal[i].rollback.index
                           /\ LET changeIndex    == proposal[proposal[i].rollback.index].rollback.index
                                  changeValues   == proposal[proposal[i].rollback.index].rollback.values
                                  rollbackValues == proposal[proposal[i].rollback.index].change.values
                              IN \E r \in {Valid, Invalid} :
                                    \* If the Rollback is Valid, record the changes required to
                                    \* roll back the target proposal and the index to which the
                                    \* configuration is being rolled back.
                                    \/ /\ r = Valid
                                       /\ proposal' = [proposal EXCEPT ![i].change.index    = changeIndex,
                                                                       ![i].change.values   = changeValues,
                                                                       ![i].rollback.values = rollbackValues,
                                                                       ![i].state           = Complete]
                                    \/ /\ r = Invalid
                                       /\ proposal' = [proposal EXCEPT ![i].state = Failed]
                        \* If the Rollback target is not the most recent change to the configuration,
                        \* fail validation for the proposal.
                        \/ /\ configuration.config.index # proposal[i].rollback.index
                           /\ proposal' = [proposal EXCEPT ![i].state = Failed]
                     /\ UNCHANGED <<configuration>>
                  \* If a Rollback proposal is attempting to roll back another Rollback,
                  \* fail validation for the proposal.
                  \/ /\ proposal[proposal[i].rollback.index].type = Rollback
                     /\ proposal' = [proposal EXCEPT ![i].state = Failed]
         /\ UNCHANGED <<configuration, target>>
      \* If the proposal failed, set the configuration's commit index to the proposal index.
      \/ /\ proposal[i].phase = Validate
         /\ proposal[i].state = Failed
         /\ configuration.commit.index = i-1
         /\ configuration' = [configuration EXCEPT !.commit.index = i]
         /\ UNCHANGED <<proposal, target>>
      \* While in the Commit state, commit the proposed changes to the configuration.
      \/ /\ proposal[i].phase = Commit
         /\ proposal[i].state = InProgress
         \* Only commit the proposal if the prior proposal has already been committed.
         /\ configuration.commit.index = i-1
         /\ configuration' = [configuration EXCEPT !.config.values = proposal[i].change.values,
                                                   !.config.index  = proposal[i].change.index,
                                                   !.commit.index  = i]
         /\ proposal' = [proposal EXCEPT ![i].state = Complete]
         /\ UNCHANGED <<target>>
      \* While in the Apply phase, apply the proposed changes to the target.
      \/ /\ proposal[i].phase = Apply
         /\ proposal[i].state = InProgress
         /\ configuration.target.index = i-1
         /\ configuration.target.term  = mastership.term
         /\ mastership.master = n
         \* Model successful and failed target update requests.
         /\ \E r \in {Success, Failure} :
               \/ /\ r = Success
                  /\ target' = proposal[i].change.values @@ target
                  /\ configuration' = [configuration EXCEPT 
                                          !.target.index  = i,
                                          !.target.values = proposal[i].change.values 
                                             @@ configuration.target.values]
                  /\ proposal' = [proposal EXCEPT ![i].state = Complete]
               \* If the proposal could not be applied, update the configuration's applied index
               \* and mark the proposal Failed.
               \/ /\ r = Failure
                  /\ configuration' = [configuration EXCEPT !.target.index = i]
                  /\ proposal' = [proposal EXCEPT ![i].state = Failed]
                  /\ UNCHANGED <<target>>
   /\ UNCHANGED <<mastership>>

=============================================================================
