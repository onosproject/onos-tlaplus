------------------------------- MODULE Proposal -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANTS
   None,
   Node,
   Synchronizing,
   Synchronized

VARIABLES
   configuration,
   mastership,
   conn,
   target

LOCAL Configuration == INSTANCE Configuration

----

(*
This section specifies constant parameters for the model.
*)

CONSTANT NumProposals

ASSUME NumProposals \in Nat

CONSTANTS 
   Change,
   Rollback

Event == {Change, Rollback}

ASSUME \A e \in Event : e \in STRING

CONSTANTS 
   Commit,
   Apply

Phase == {Commit, Apply}

ASSUME \A p \in Phase : p \in STRING

CONSTANTS 
   Pending, 
   InProgress,
   Complete, 
   Aborted, 
   Failed

State == {Pending, InProgress, Complete, Aborted, Failed}

Done == {Complete, Aborted, Failed}

ASSUME \A s \in State : s \in STRING

CONSTANT Path

ASSUME \A p \in Path : p \in STRING

CONSTANT Value

ASSUME \A v \in Value : v \in STRING

AllValues == Value \union {None}

VARIABLE proposal

VARIABLE history

----

(*
This section models proposal reconcilation.
*)

CommitChange(n, i) == 
   /\ \/ /\ proposal[i].change.commit = Pending
         /\ \A j \in DOMAIN proposal : j < i => 
               /\ proposal[j].change.commit \in Done
               /\ proposal[j].rollback.commit # InProgress
         /\ \/ /\ proposal[i].rollback.commit = None
               /\ proposal' = [proposal EXCEPT ![i].change.commit = InProgress]
            \/ /\ proposal[i].rollback.commit = Pending
               /\ proposal' = [proposal EXCEPT ![i].change.commit = Aborted]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].change.commit = InProgress
         \* Changes are validated during the commit phase. If a change fails validation,
         \* it will be marked failed before being applied to the configuration.
         \* If all the change values are valid, record the changes required to roll
         \* back the proposal and the index to which the rollback changes
         \* will roll back the configuration.
         /\ \/ /\ LET values == [p \in DOMAIN proposal[i].values |->
                                    [index |-> i, value |-> proposal[i].values[p]]] @@
                                        configuration.committed.values
                  IN /\ configuration' = [configuration EXCEPT !.committed.values = values]
                     /\ proposal' = [proposal EXCEPT ![i].change.commit = Complete]
                     /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
            \/ /\ proposal' = [proposal EXCEPT ![i].change.commit = Failed]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

ApplyChange(n, i) == 
   /\ \/ /\ proposal[i].change.apply = Pending
         /\ \/ /\ proposal[i].change.commit = Complete
               /\ \A j \in DOMAIN proposal : j < i =>
                     \/ /\ proposal[j].change.apply = Complete
                        /\ proposal[j].rollback.apply # InProgress
                     \/ /\ proposal[j].change.apply = Failed
                        /\ proposal[j].rollback.apply = Complete
               /\ proposal' = [proposal EXCEPT ![i].change.apply = InProgress]
            \/ /\ proposal[i].change.commit \in {Aborted, Failed}
               /\ proposal' = [proposal EXCEPT ![i].change.apply = Aborted]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ proposal[i].change.apply = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ mastership.conn = conn[n].id
         /\ target.running
         \* Model successful and failed target update requests.
         /\ \/ /\ LET values == [p \in DOMAIN proposal[i].values |-> 
                                    [index |-> i, value |-> proposal[i].values[p]]]
                  IN /\ target' = [target EXCEPT !.values = values @@ target.values]
                     /\ configuration' = [configuration EXCEPT !.applied.values = values @@ 
                                                                  configuration.applied.values]
                     /\ proposal' = [proposal EXCEPT ![i].change.apply = Complete]
                     /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
            \/ /\ proposal' = [proposal EXCEPT ![i].change.apply = Failed]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

CommitRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.commit = Pending
         /\ \A j \in DOMAIN proposal : 
               /\ j > i 
               /\ proposal[j].phase # None
               /\ proposal[j].change.commit # Pending 
               => proposal[j].rollback.commit = Complete
         /\ \/ /\ proposal[i].change.commit = Aborted
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = Complete]
            \/ /\ proposal[i].change.commit \in {Complete, Failed}
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = InProgress]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].rollback.commit = InProgress
         /\ LET changes == {j \in DOMAIN proposal : 
                              /\ j < i 
                              /\ proposal[j].change.commit = Complete 
                              /\ proposal[j].rollback.commit # Complete}
                paths   == {p \in DOMAIN configuration.committed.values : 
                              \E j \in changes : p \in DOMAIN proposal[j].values}
                indexes == [p \in paths |-> CHOOSE j \in changes : 
                              /\ p \in DOMAIN proposal[j].values
                              /\ ~\E k \in changes : k > j /\ p \in DOMAIN proposal[k].values]
                values  == [p \in DOMAIN configuration.committed.values |->
                              IF p \in paths THEN 
                                 [index |-> indexes[p], value |-> proposal[indexes[p]].values[p]]
                              ELSE 
                                 [index |-> 0, value |-> None]]
            IN 
               /\ configuration' = [configuration EXCEPT !.committed.values = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = Complete]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
   /\ UNCHANGED <<mastership, conn, target>>

ApplyRollback(n, i) == 
   /\ \/ /\ proposal[i].rollback.apply = Pending
         /\ proposal[i].rollback.commit = Complete
         /\ \A j \in DOMAIN proposal : 
               /\ j > i 
               /\ proposal[j].phase # None 
               /\ proposal[j].change.apply # Pending 
               => proposal[j].rollback.apply \in Done
         /\ \/ /\ proposal[i].change.apply = Pending
               /\ proposal' = [proposal EXCEPT ![i].change.apply   = Aborted,
                                               ![i].rollback.apply = Complete]
            \/ /\ proposal[i].change.apply \in Done
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = InProgress]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ proposal[i].rollback.apply = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ target.running
         /\ LET changes == {j \in DOMAIN proposal : 
                              /\ j < i 
                              /\ proposal[j].change.apply = Complete 
                              /\ proposal[j].rollback.apply # Complete}
                paths   == {p \in DOMAIN configuration.applied.values : 
                              \E j \in changes : p \in DOMAIN proposal[j].values}
                indexes == [p \in paths |-> CHOOSE j \in changes : 
                              /\ p \in DOMAIN proposal[j].values
                              /\ ~\E k \in changes : k > j /\ p \in DOMAIN proposal[k].values]
                values  == [p \in DOMAIN configuration.applied.values |->
                              IF p \in paths THEN 
                                 [index |-> indexes[p], value |-> proposal[indexes[p]].values[p]]
                              ELSE 
                                 [index |-> 0, value |-> None]]
            IN 
               /\ target' = [target EXCEPT !.values = values]
               /\ configuration' = [configuration EXCEPT !.applied.values = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = Complete]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
   /\ UNCHANGED <<mastership, conn>>

Reconcile(n, i) ==
   /\ mastership.master = n
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership, conn>>

----

\* Propose change at index 'i'
ProposeChange(i) ==
   /\ proposal[i].phase = None
   /\ i-1 \in DOMAIN proposal => proposal[i-1].phase # None
   /\ \E p \in Path, v \in AllValues :
         /\ proposal' = [proposal EXCEPT ![i].phase         = Change,
                                         ![i].values = (p :> v),
                                         ![i].change.commit = Pending,
                                         ![i].change.apply  = Pending]
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

\* Rollback proposed change at index 'i'
ProposeRollback(i) ==
   /\ proposal[i].phase = Change
   /\ proposal' = [proposal EXCEPT ![i].phase           = Rollback,
                                   ![i].rollback.commit = Pending,
                                   ![i].rollback.apply  = Pending]
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

----

Init ==
   /\ proposal = [
         i \in 1..NumProposals |-> [
            phase    |-> None,
            values   |-> [p \in {} |-> None],
            change   |-> [
               commit |-> None,
               apply  |-> None],
            rollback |-> [
               commit |-> None,
               apply  |-> None]]]
   /\ history = <<>>
   /\ Configuration!Init

Next ==
   \/ \E i \in DOMAIN proposal :
         \/ ProposeChange(i)
         \/ ProposeRollback(i)
   \/ \E n \in Node, i \in DOMAIN proposal : Reconcile(n, i)
   \/ /\ Configuration!Next
      /\ UNCHANGED <<proposal, history>>

=============================================================================
