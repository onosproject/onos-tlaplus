------------------------------- MODULE Proposal -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Proposal phase constants
CONSTANTS
   Change,
   Rollback

\* Proposal phase constants
CONSTANTS 
   Commit,
   Apply

\* Status constants
CONSTANTS
   Pending,
   Complete,
   Aborted,
   Failed

Status == {Pending, Complete, Aborted, Failed}

\* The set of all nodes
CONSTANT Node

\* The set of possible paths and values
CONSTANT Path, Value

Empty == [p \in {} |-> Nil]

----

\* Variables defined by other modules.
VARIABLES 
   configuration,
   mastership,
   conn,
   target

\* A proposal log. Proposals may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE proposals

\* A sequence of configuration changes used for model checking.
VARIABLE history

TypeOK == 
   \A i \in DOMAIN proposals :
      /\ proposals[i].type \in {Change, Rollback}
      /\ proposals[i].index \in Nat
      /\ proposals[i].revision \in Nat
      /\ proposals[i].change.index \in Nat
      /\ proposals[i].change.revision \in Nat
      /\ \A p \in DOMAIN proposals[i].change.values :
            proposals[i].change.values[p] # Nil => 
               proposals[i].change.values[p] \in STRING
      /\ proposals[i].rollback.index \in Nat
      /\ proposals[i].rollback.revision \in Nat
      /\ \A p \in DOMAIN proposals[i].rollback.values :
            proposals[i].rollback.values[p] # Nil => 
               proposals[i].rollback.values[p] \in STRING
      /\ proposals[i].commit \in Status
      /\ proposals[i].apply \in Status

LOCAL State == [
   proposals     |-> proposals,
   configuration |-> configuration]

LOCAL Transitions ==
   LET
      indexes == {i \in DOMAIN proposals' : 
                     i \in DOMAIN proposals => proposals'[i] # proposals[i]}
   IN 
     [proposals |-> [i \in indexes |-> proposals'[i]]]

Test == INSTANCE Test WITH 
   File <- "Proposal.log"

----

(*

  CHANGE [index=1, revision=1,  change=(index=1, revision=1), rollback=(index=0, revision=0)] <-- Change revision 1
  CHANGE [index=2, revision=2,  change=(index=2, revision=2), rollback=(index=1, revision=1)]
  CHANGE [index=3, revision=3,  change=(index=3, revision=3), rollback=(index=2, revision=2)]
ROLLBACK [index=4, revision=3,  change=(index=2, revision=2), rollback=(index=3, revision=3)] <-- Roll back revision 3 at index 3, leading to revision 2
ROLLBACK [index=5, revision=3,  change=(index=1, revision=1), rollback=(index=2, revision=2)]
  CHANGE [index=6, revision=4,  change=(index=6, revision=4), rollback=(index=1, revision=1)]
  CHANGE [index=7, revision=5,  change=(index=7, revision=5), rollback=(index=6, revision=4)]
ROLLBACK [index=8, revision=5,  change=(index=6, revision=4), rollback=(index=7, revision=5)] <-- Roll back revision 5 at index 7, leading to revision 4
ROLLBACK [index=9, revision=5,  change=(index=1, revision=1), rollback=(index=6, revision=4)] <-- Roll back revision 4 at index 6, leading to revision 1
  CHANGE [index=10, revision=6, change=(index=10, revision=6), rollback=(index=1, revision=1)]

*)

CommitChange(n, i) ==
   /\ proposals[i].commit = Pending
   /\ i-1 \in DOMAIN proposals =>
         proposals[i-1].commit # Pending
   /\ configuration' = [configuration EXCEPT !.committed.index    = proposals[i].change.index,
                                             !.committed.revision = proposals[i].change.revision,
                                             !.committed.values   = proposals[i].change.values @@ 
                                                                        configuration.committed.values]
   /\ proposals' = [proposals EXCEPT ![i].commit = Complete]
   /\ history' = Append(history, [
                     type     |-> Change, 
                     phase    |-> Commit, 
                     revision |-> proposals[i].change.revision])
   /\ UNCHANGED <<target>>

ApplyChange(n, i) ==
   /\ proposals[i].apply = Pending
   /\ proposals[i].commit = Complete
   /\ i-1 \in DOMAIN proposals =>
         proposals[i-1].apply # Pending
   /\ \/ /\ i-1 \in DOMAIN proposals =>
               proposals[i-1].apply = Complete
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
            \* Apply to the target successfully.
         /\ \/ /\ target' = [target EXCEPT !.values = proposals[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index    = proposals[i].change.index,
                                                         !.applied.revision = proposals[i].change.revision,
                                                         !.applied.values   = proposals[i].change.values @@
                                                                                 configuration.applied.values]
               /\ proposals' = [proposals EXCEPT ![i].apply = Complete]
               /\ history' = Append(history, [
                                 type     |-> Change, 
                                 phase    |-> Apply, 
                                 revision |-> proposals[i].change.revision])
            \* Apply to the target failed.
            \/ /\ proposals' = [proposals EXCEPT ![i].apply = Failed]
               /\ UNCHANGED <<configuration, target, history>>
      \/ /\ i-1 \in DOMAIN proposals
         /\ proposals[i-1].apply \in {Aborted, Failed}
         /\ proposals' = [proposals EXCEPT ![i].apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>

ReconcileChange(n, i) ==
   /\ proposals[i].type = Change
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)

CommitRollback(n, i) ==
   /\ proposals[i].commit = Pending
   /\ i-1 \in DOMAIN proposals =>
         proposals[i-1].commit # Pending
   /\ configuration' = [configuration EXCEPT !.committed.index    = proposals[i].change.index,
                                             !.committed.revision = proposals[i].change.revision,
                                             !.committed.values   = proposals[i].change.values @@ 
                                                                        configuration.committed.values]
   /\ proposals' = [proposals EXCEPT ![i].commit = Complete]
   /\ history' = Append(history, [
                     type     |-> Rollback, 
                     phase    |-> Commit, 
                     revision |-> proposals[i].rollback.revision])
   /\ UNCHANGED <<target>>

ApplyRollback(n, i) ==
   /\ proposals[i].apply = Pending
   /\ proposals[i].commit = Complete
   /\ i-1 \in DOMAIN proposals =>
         proposals[i-1].apply # Pending
   /\ \/ /\ proposals[proposals[i].rollback.index].apply \in {Complete, Failed}
         /\ configuration.state = Complete
         /\ configuration.term = mastership.term
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = proposals[i].change.values @@ target.values]
         /\ configuration' = [configuration EXCEPT !.applied.index    = proposals[i].change.index,
                                                   !.applied.revision = proposals[i].change.revision,
                                                   !.applied.values   = proposals[i].change.values @@
                                                                           configuration.applied.values]
         /\ proposals' = [proposals EXCEPT ![i].apply = Complete]
         /\ history' = Append(history, [
                           type     |-> Rollback, 
                           phase    |-> Apply, 
                           revision |-> proposals[i].rollback.revision])
      \/ /\ proposals[proposals[i].rollback.index].apply = Aborted
         /\ proposals' = [proposals EXCEPT ![i].apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>

ReconcileRollback(n, i) ==
   /\ proposals[i].type = Rollback
   /\ \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)

ReconcileProposal(n, i) ==
   /\ i \in DOMAIN proposals
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)
   /\ UNCHANGED <<mastership, conn>>

=============================================================================
