------------------------------- MODULE Proposal -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Event constants
CONSTANTS
   Change,
   Rollback

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
   conn,
   target

\* A record of per-target proposals
VARIABLE proposal

\* A sequence of configuration changes used for model checking.
VARIABLE history

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

LOCAL CurrState == [
   proposals     |-> [i \in DOMAIN proposal |-> proposal[i] @@ [ordinal |-> i]],
   configuration |-> configuration,
   mastership    |-> mastership,
   conn          |-> conn,
   target        |-> target]

LOCAL SuccState ==
   LET
      proposals == {i \in DOMAIN proposal' : 
                        i \in DOMAIN proposal => proposal'[i] # proposal[i]}
   IN 
     [proposals |-> [i \in proposals    |-> proposal'[i] @@ [ordinal |-> i]]] @@
     (IF configuration' # configuration THEN [configuration |-> configuration'] ELSE <<>>) @@
     (IF mastership' # mastership THEN [mastership |-> mastership'] ELSE <<>>) @@
     (IF conn' # conn THEN [conn |-> conn'] ELSE <<>>) @@
     (IF target' # target THEN [target |-> target'] ELSE <<>>)

Test == INSTANCE Test WITH 
   File      <- "Proposal.log"

LOCAL Max(s) == CHOOSE i \in s : \A j \in s : i > j

----

CommitChange(n, i) ==
   /\ proposal[i].change.phase = Commit
   /\ proposal[i].change.state = InProgress
      \* If the committed index does not match the proposal index, commit the change.
   /\ \/ /\ configuration.committed.index = i-1
            \* If the change is valid, update the committed index, revision, and values.
         /\ \/ /\ configuration' = [configuration EXCEPT !.committed.index    = i,
                                                         !.committed.revision = i,
                                                         !.committed.values   = proposal[i].change.values @@ 
                                                                                   configuration.committed.values]
               /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
            \* If the change is invalid, update only the committed index.
            \/ /\ configuration' = [configuration EXCEPT !.committed.index = i]
               /\ UNCHANGED <<history>>
         /\ UNCHANGED <<proposal>>
      \* If both the committed index and committed revision were updated, the proposal was successful.
      \/ /\ configuration.committed.index = i
         /\ configuration.committed.revision = i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Complete]
         /\ UNCHANGED <<configuration, history>>
      \* If the committed index was updated but the revision was not, the proposal failed validation.
      \/ /\ configuration.committed.index = i
         /\ configuration.committed.revision # i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
         /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<target>>

ApplyChange(n, i) ==
   /\ proposal[i].change.phase = Apply
   /\ proposal[i].change.state = InProgress
      \* If the applied index does not match the proposal index, apply the change.
   /\ \/ /\ configuration.applied.index = i-1
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
            \* If the change can be applied, update the index, revision, and values.
         /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index    = i,
                                                         !.applied.revision = i,
                                                         !.applied.values   = proposal[i].change.values @@
                                                                                 configuration.applied.values]
               /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
            \* If the change is invalid, update only the applied index.
            \/ /\ configuration' = [configuration EXCEPT !.applied.index = i]
               /\ UNCHANGED <<target, history>>
         /\ UNCHANGED <<proposal>>
      \* If the applied index and revision both match the proposal index, the change was successful.
      \/ /\ configuration.applied.index = i
         /\ configuration.applied.revision = i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Complete]
         /\ UNCHANGED <<configuration, target, history>>
      \* If the applied index matches the proposal index but the revision does not, the proposal failed.
      \/ /\ configuration.applied.index = i
         /\ configuration.applied.revision # i
         /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
         /\ UNCHANGED <<configuration, target, history>>

CommitRollback(n, i) ==
   /\ proposal[i].rollback.phase = Commit
   /\ proposal[i].rollback.state = InProgress
      \* If the committed revision matches the proposal revision, roll back to the previous revision.
   /\ \/ /\ configuration.committed.revision = i
         /\ configuration' = [configuration EXCEPT !.committed.revision = proposal[i].rollback.revision,
                                                   !.committed.values   = proposal[i].rollback.values @@
                                                                             configuration.committed.values]
         /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
         /\ UNCHANGED <<proposal>>
      \* If the committed index matches the rollback index, complete the rollback.
      \/ /\ configuration.committed.revision = proposal[i].rollback.revision
         /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
         /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<target>>

ApplyRollback(n, i) ==
   /\ proposal[i].rollback.phase = Apply
   /\ proposal[i].rollback.state = InProgress
      \* If the applied revision matches the proposal revision, roll back to the previous revision.
   /\ \/ /\ configuration.applied.revision = i
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
         /\ configuration' = [configuration EXCEPT !.applied.revision = proposal[i].rollback.revision,
                                                   !.applied.values   = proposal[i].rollback.values @@
                                                                           configuration.applied.values]
         /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
         /\ UNCHANGED <<proposal>>
      \* If the committed index matches the rollback index, complete the rollback.
      \/ /\ configuration.committed.revision = proposal[i].rollback.revision
         /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
         /\ UNCHANGED <<configuration, target, history>>

\* Reconcile a proposal
ReconcileProposal(n, i) ==
   /\ i \in DOMAIN proposal
   /\ mastership.master = n
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership, conn>>

=============================================================================
