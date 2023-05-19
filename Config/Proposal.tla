------------------------------- MODULE Proposal -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Phase constants
CONSTANTS
   Commit,
   Apply

Phase ==
   {Nil,
    Commit,
    Apply}

\* Status constants
CONSTANTS
   Pending,
   InProgress,
   Complete,
   Failed

Status == 
   {Nil,
    Pending,
    InProgress,
    Complete,
    Failed}

\* The set of all nodes
CONSTANT Node

----

\* Variables defined by other modules.
VARIABLES 
   configuration,
   mastership,
   target

\* A record of per-target proposals
VARIABLE proposal

TypeOK ==
   \A i \in DOMAIN proposal :
      /\ proposal[i].change.phase \in Phase
      /\ proposal[i].change.state \in Status
      /\ \A p \in DOMAIN proposal[i].change.values :
            /\ proposal[i].change.values[p].index \in Nat
            /\ proposal[i].change.values[p].value # Nil => 
                  proposal[i].change.values[p].value \in STRING
      /\ proposal[i].rollback.phase \in Phase
      /\ proposal[i].rollback.state \in Status
      /\ proposal[i].rollback.revision \in Nat
      /\ \A p \in DOMAIN proposal[i].rollback.values :
            /\ proposal[i].rollback.values[p].index \in Nat
            /\ proposal[i].rollback.values[p].value # Nil => 
                  proposal[i].rollback.values[p].value \in STRING

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

LOCAL Max(s) == CHOOSE i \in s : \A j \in s : i > j

----

CommitChange(n, i) ==
   /\ proposal[i].change.phase = Commit
   /\ proposal[i].change.state = InProgress
      \* If the committed index does not match the proposal index, commit the change.
   /\ \/ /\ configuration.committed.index = i-1
            \* If the change is valid, update the committed index, revision, and values.
         /\ \/ configuration' = [configuration EXCEPT !.committed.index    = i,
                                                      !.committed.revision = i,
                                                      !.committed.values   = proposal[i].change.values @@ 
                                                                                 configuration.committed.values]
            \* If the change is invalid, update only the committed index.
            \/ configuration' = [configuration EXCEPT !.committed.index = i]
         /\ UNCHANGED <<proposal>>
      \* If both the committed index and committed revision were updated, the proposal was successful.
      \/ /\ configuration.committed.index = i
         /\ configuration.committed.revision = i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Complete]
         /\ UNCHANGED <<configuration>>
      \* If the committed index was updated but the revision was not, the proposal failed validation.
      \/ /\ configuration.committed.index = i
         /\ configuration.committed.revision # i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
         /\ UNCHANGED <<configuration>>
   /\ UNCHANGED <<target>>

ApplyChange(n, i) ==
   /\ proposal[i].change.phase = Apply
   /\ proposal[i].change.state = InProgress
      \* If the applied index does not match the proposal index, apply the change.
   /\ \/ /\ configuration.applied.index = i-1
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
            \* If the change can be applied, update the index, revision, and values.
         /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index    = i,
                                                         !.applied.revision = i,
                                                         !.applied.values   = proposal[i].change.values @@
                                                                                 configuration.applied.values]
            \* If the change is invalid, update only the applied index.
            \/ configuration' = [configuration EXCEPT !.applied.index = i]
         /\ UNCHANGED <<proposal>>
      \* If the applied index and revision both match the proposal index, the change was successful.
      \/ /\ configuration.applied.index = i
         /\ configuration.applied.revision = i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Complete]
         /\ UNCHANGED <<configuration>>
      \* If the applied index matches the proposal index but the revision does not, the proposal failed.
      \/ /\ configuration.applied.index = i
         /\ configuration.applied.revision # i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
         /\ UNCHANGED <<configuration>>
   /\ UNCHANGED <<target>>

CommitRollback(n, i) ==
   /\ proposal[i].rollback.phase = Commit
   /\ proposal[i].rollback.state = InProgress
      \* If the committed revision matches the proposal revision, roll back to the previous revision.
   /\ \/ /\ configuration.committed.revision = i
         /\ configuration' = [configuration EXCEPT !.committed.revision = proposal[i].rollback.revision,
                                                   !.committed.values   = proposal[i].rollback.values @@
                                                                             configuration.committed.values]
         /\ UNCHANGED <<proposal>>
      \* If the committed index matches the rollback index, complete the rollback.
      \/ /\ configuration.committed.revision = proposal[i].rollback.revision
         /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
         /\ UNCHANGED <<configuration>>
   /\ UNCHANGED <<target>>

ApplyRollback(n, i) ==
   /\ proposal[i].rollback.phase = Apply
   /\ proposal[i].rollback.phase = InProgress
      \* If the applied revision matches the proposal revision, roll back to the previous revision.
   /\ \/ /\ configuration.applied.revision = i
         /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
         /\ configuration' = [configuration EXCEPT !.applied.revision = proposal[i].rollback.revision,
                                                   !.applied.values   = proposal[i].rollback.values @@
                                                                           configuration.applied.values]
         /\ UNCHANGED <<proposal>>
      \* If the committed index matches the rollback index, complete the rollback.
      \/ /\ configuration.committed.revision = proposal[i].rollback.revision
         /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
         /\ UNCHANGED <<configuration, target>>

\* Reconcile a proposal
ReconcileProposal(n, i) ==
   /\ i \in DOMAIN proposal
   /\ mastership.master = n
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership>>

=============================================================================
