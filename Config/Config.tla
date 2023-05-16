------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

(*
This section specifies constant parameters for the model.
*)

CONSTANT None

ASSUME None \in STRING

CONSTANT Node

ASSUME \A n \in Node : n \in STRING

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

CONSTANT NumProposals

ASSUME NumProposals \in Nat

----

(*
This section defines model state variables.

proposal == [
   i \in 1..Nat |-> [
      phase  |-> Phase,
      change |-> [
         values |-> Change,
         commit |-> State,
         apply  |-> State],
      rollback |-> [
         index  |-> Nat,
         values |-> Change,
         commit |-> State,
         apply  |-> State]]]

configuration == [
   committed |-> [
      index  |-> Nat,
      values |-> Change],
   applied   |-> [
      index  |-> Nat,
      values |-> Change,
      term   |-> Nat]]

mastership == [
   master |-> STRING,
   term   |-> Nat,
   conn   |-> Nat]

conn == [
   n \in Node |-> [
      id        |-> Nat,
      connected |-> BOOLEAN]]

target == [
   id      |-> Nat,
   values  |-> Change,
   running |-> BOOLEAN]
*)

VARIABLE proposal

VARIABLE configuration

VARIABLE mastership

VARIABLE conn

VARIABLE target

VARIABLE history

vars == <<proposal, configuration, mastership, conn, target, history>>

----

(*
This section models configuration target.
*)

StartTarget ==
   /\ ~target.running
   /\ target' = [target EXCEPT !.id      = target.id + 1,
                               !.running = TRUE]
   /\ UNCHANGED <<proposal, configuration, mastership, conn, history>>

StopTarget ==
   /\ target.running
   /\ target' = [target EXCEPT !.running = FALSE,
                               !.values  = [p \in {} |-> [value |-> None]]]
   /\ conn' = [n \in Node |-> [conn[n] EXCEPT !.connected = FALSE]]
   /\ UNCHANGED <<proposal, configuration, mastership, history>>

----

(*
This section models nodes connection to the configuration target.
*)

ConnectNode(n) ==
   /\ ~conn[n].connected
   /\ target.running
   /\ conn' = [conn EXCEPT ![n].id        = conn[n].id + 1,
                           ![n].connected = TRUE]
   /\ UNCHANGED <<proposal, configuration, mastership, target, history>>

DisconnectNode(n) ==
   /\ conn[n].connected
   /\ conn' = [conn EXCEPT ![n].connected = FALSE]
   /\ UNCHANGED <<proposal, configuration, mastership, target, history>>

----

(*
This section models mastership reconciliation.
*)

ReconcileMastership(n) ==
   /\ \/ /\ conn[n].connected
         /\ mastership.master = None
         /\ mastership' = [master |-> n, term |-> mastership.term + 1, conn |-> conn[n].id]
      \/ /\ ~conn[n].connected
         /\ mastership.master = n
         /\ mastership' = [mastership EXCEPT !.master = None]
   /\ UNCHANGED <<proposal, configuration, conn, target, history>>

----

(*
This section models configuration reconciliation.
*)

ReconcileConfiguration(n) ==
   /\ mastership.master = n
   /\ \/ /\ configuration.status # InProgress
         /\ configuration.applied.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.status = InProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.status = InProgress
         /\ configuration.applied.term < mastership.term
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.applied.values]
         /\ configuration' = [configuration EXCEPT !.applied.term   = mastership.term,
                                                   !.applied.target = target.id,
                                                   !.status         = Complete]
   /\ UNCHANGED <<proposal, mastership, conn, history>>

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
               /\ i-1 \in DOMAIN proposal /\ proposal[i-1].change.apply = Failed =>
                     proposal[i-1].rollback.apply = Complete
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

ReconcileProposal(n, i) ==
   /\ mastership.master = n
   /\ \/ CommitChange(n, i)
      \/ ApplyChange(n, i)
      \/ CommitRollback(n, i)
      \/ ApplyRollback(n, i)
   /\ UNCHANGED <<mastership, conn>>

----

(*
This section models changes to the proposal queue.
*)

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

(*
Formal specification, constraints, and theorems.
*)

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
   /\ configuration = [
         committed |-> [
            values |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         applied |-> [
            term   |-> 0,
            target |-> 0,
            values |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         status  |-> Pending]
   /\ mastership = [master |-> None, term |-> 0, conn |-> 0]
   /\ conn = [n \in Node |-> [id |-> 0, connected |-> FALSE]]
   /\ target = [
         id      |-> 0, 
         values  |-> [p \in {} |-> [index |-> 0, value |-> None]], 
         running |-> FALSE]
   /\ history = <<>>

Next ==
   \/ \E i \in 1..NumProposals :
         \/ ProposeChange(i)
         \/ ProposeRollback(i)
   \/ \E n \in Node, i \in DOMAIN proposal : ReconcileProposal(n, i)
   \/ \E n \in Node : ReconcileConfiguration(n)
   \/ \E n \in Node : ReconcileMastership(n)
   \/ \E n \in Node :
      \/ ConnectNode(n)
      \/ DisconnectNode(n)
   \/ StartTarget
   \/ StopTarget

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ \A i \in 1..NumProposals : WF_vars(ProposeChange(i) \/ ProposeRollback(i))
   /\ \A n \in Node, i \in 1..NumProposals : WF_vars(ReconcileProposal(n, i))
   /\ \A n \in Node : WF_<<configuration, mastership, conn, target>>(ReconcileConfiguration(n))
   /\ \A n \in Node : WF_<<mastership, conn, target>>(ReconcileMastership(n))
   /\ \A n \in Node : WF_<<conn, target>>(ConnectNode(n) \/ DisconnectNode(n))
   /\ WF_<<target>>(StartTarget)
   /\ WF_<<target>>(StopTarget)

IsOrderedChange(p, i) ==
   /\ history[i].type = Change
   /\ history[i].phase = p
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].index >= history[i].index

IsOrderedRollback(p, i) ==
   /\ history[i].type = Rollback
   /\ history[i].phase = p
   /\ ~\E j \in DOMAIN history :
         /\ j < i
         /\ history[j].type = Change
         /\ history[j].phase = p
         /\ history[j].index > history[i].index
         /\ ~\E k \in DOMAIN history :
               /\ k > j
               /\ k < i
               /\ history[k].type = Rollback
               /\ history[k].phase = p
               /\ history[k].index = history[j].index

Order ==
   /\ \A i \in DOMAIN history :
      \/ IsOrderedChange(Commit, i)
      \/ IsOrderedChange(Apply, i)
      \/ IsOrderedRollback(Commit, i)
      \/ IsOrderedRollback(Apply, i)
   /\ \A i \in DOMAIN proposal :
         /\ proposal[i].change.apply = Failed 
         /\ proposal[i].rollback.apply # Complete
         => \A j \in DOMAIN proposal : j > i => 
               proposal[j].change.apply \in {None, Pending, Aborted}

Consistency ==
   /\ target.running 
   /\ configuration.status = Complete
   /\ configuration.applied.target = target.id
   => \A i \in DOMAIN proposal :
         /\ proposal[i].change.apply = Complete
         /\ proposal[i].rollback.apply # Complete
         => \A p \in DOMAIN proposal[i].values :
               /\ ~\E j \in DOMAIN proposal : 
                     /\ j > i 
                     /\ proposal[j].change.apply = Complete
                     /\ proposal[j].rollback.apply # Complete
               => /\ p \in DOMAIN target.values 
                  /\ target.values[p].value = proposal[i].values[p]
                  /\ target.values[p].index = i

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Termination ==
   \A i \in 1..NumProposals :
      /\ proposal[i].change.commit = Pending ~>
            proposal[i].change.commit \in Done
      /\ proposal[i].change.apply = Pending ~>
            proposal[i].change.apply \in Done
      /\ proposal[i].rollback.commit = Pending ~>
            proposal[i].rollback.commit \in Done
      /\ proposal[i].rollback.apply = Pending ~>
            proposal[i].rollback.apply \in Done

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
