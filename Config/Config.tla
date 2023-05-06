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

CONSTANT NumProposals

ASSUME NumProposals \in Nat

----

(*
This section defines model state variables.

proposal == [
   i \in 1..Nat |-> [
      change |-> [
         values |-> Change,
         phase  |-> Phase,
         state  |-> State],
      rollback |-> [
         index  |-> Nat,
         values |-> Change,
         phase  |-> Phase,
         state  |-> State]]]

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
   /\ proposal[i].change.phase = Commit
   /\ \/ /\ proposal[i].change.state = Pending
         /\ proposal[i].rollback.phase = None
         /\ \A j \in DOMAIN proposal : j < i =>
               /\ \/ /\ proposal[j].change.phase = Commit
                     /\ proposal[j].change.state \in Done
                  \/ proposal[j].change.phase = Apply
               /\ proposal[j].rollback.phase # None =>
                  proposal[j].rollback.phase = Apply
         /\ proposal' = [proposal EXCEPT ![i].change.state = InProgress]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].change.state = InProgress
         \* Changes are validated during the commit phase. If a change fails validation,
         \* it will be marked failed before being applied to the configuration.
         \* If all the change values are valid, record the changes required to roll
         \* back the proposal and the index to which the rollback changes
         \* will roll back the configuration.
         /\ \/ LET rollbackIndex  == configuration.committed.index
                   rollbackValues == [p \in DOMAIN proposal[i].change.values |-> 
                                        IF p \in DOMAIN configuration.committed.values THEN
                                           configuration.committed.values[p]
                                        ELSE
                                           [index |-> 0, value |-> None]]
                   changeValues   == [p \in DOMAIN proposal[i].change.values |->
                                        proposal[i].change.values[p] @@ [index |-> i]]
               IN /\ configuration' = [configuration EXCEPT !.committed.index  = i,
                                                            !.committed.values = changeValues]
                  /\ proposal' = [proposal EXCEPT ![i].change.values   = changeValues,
                                                  ![i].rollback.values = rollbackValues,
                                                  ![i].change.phase    = Apply,
                                                  ![i].change.state    = Pending]
                  /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
            \/ /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<mastership, conn, target>>

ApplyChange(n, i) == 
   /\ proposal[i].change.phase = Apply
   /\ \/ /\ proposal[i].change.state = Pending
         /\ proposal[i].rollback.phase = None
         /\ \A j \in DOMAIN proposal : j < i =>
               \/ /\ proposal[j].change.phase = Commit
                  /\ proposal[j].rollback.state = Complete
               \/ /\ proposal[j].change.phase = Apply
                  /\ proposal[j].change.state = Complete
                  /\ proposal[j].rollback.phase = None
               \/ /\ proposal[j].change.phase = Apply
                  /\ proposal[j].change.state = Failed
                  /\ proposal[j].rollback.phase = Apply
                  /\ proposal[j].rollback.state = Complete
         /\ proposal' = [proposal EXCEPT ![i].change.state = InProgress]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ proposal[i].change.state = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ mastership.conn = conn[n].id
         /\ target.running
         \* Model successful and failed target update requests.
         /\ \/ /\ target' = [target EXCEPT !.values = proposal[i].change.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index  = i,
                                                         !.applied.values = proposal[i].change.values @@
                                                                               configuration.applied.values]
               /\ proposal' = [proposal EXCEPT ![i].change.state = Complete]
               /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
            \* If the proposal could not be applied, mark it failed but do not update the
            \* last applied index. The proposal must be rolled back before new proposals
            \* can be applied to the configuration/target.
            \/ /\ proposal' = [proposal EXCEPT ![i].change.state = Failed]
               /\ UNCHANGED <<configuration, target, history>>
   /\ UNCHANGED <<mastership, conn>>

CommitRollback(n, i) == 
   /\ proposal[i].rollback.phase = Commit
   /\ \/ /\ proposal[i].rollback.state = Pending
         /\ \A j \in DOMAIN proposal : j > i => 
               \/ /\ proposal[j].rollback.phase = Commit
                  /\ proposal[j].rollback.state \in Done
               \/ proposal[j].rollback.phase = Apply
         /\ \/ /\ proposal[i].change.phase = Commit
               /\ proposal[i].change.state = Pending
               /\ proposal' = [proposal EXCEPT ![i].change.state   = Aborted,
                                               ![i].rollback.state = Complete]
            \/ /\ proposal[i].change.phase = Commit
               /\ proposal[i].change.state \in Done
               /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
            \/ /\ proposal[i].change.phase = Apply
               /\ proposal' = [proposal EXCEPT ![i].rollback.state = InProgress]
         /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].rollback.state = InProgress
         /\ LET index  == proposal[i].rollback.index
                values == proposal[i].rollback.values @@ configuration.committed.values
            IN /\ configuration' = [configuration EXCEPT !.committed.index  = index,
                                                         !.committed.values = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.phase = Apply,
                                               ![i].rollback.state = Pending]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
   /\ UNCHANGED <<mastership, conn, target>>

ApplyRollback(n, i) == 
   /\ proposal[i].rollback.phase = Apply
   /\ \/ /\ proposal[i].rollback.state = Pending
         /\ \A j \in DOMAIN proposal : j > i =>
               /\ proposal[j].rollback.phase = Apply
               /\ proposal[j].rollback.state \in Done
         /\ \/ /\ proposal[i].change.phase = Apply
               /\ proposal[i].change.state = Pending
               /\ proposal' = [proposal EXCEPT ![i].change.state   = Aborted,
                                               ![i].rollback.state = Complete]
            \/ /\ proposal[i].change.phase = Apply
               /\ proposal[i].change.state \in Done
               /\ proposal' = [proposal EXCEPT ![i].rollback.state = InProgress]
         /\ UNCHANGED <<configuration, target, history>>
      \/ /\ proposal[i].rollback.state = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
         /\ LET index  == proposal[i].rollback.index
                values == proposal[i].rollback.values @@ configuration.applied.values
            IN 
               /\ configuration' = [configuration EXCEPT !.applied.index  = index,
                                                         !.applied.values = values]
               /\ proposal' = [proposal EXCEPT ![i].rollback.state = Complete]
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
   /\ proposal[i].change.phase = None
   /\ i-1 \in DOMAIN proposal => proposal[i-1].change.phase # None
   /\ \E p \in Path, v \in Value \union {None} :
         /\ proposal' = [proposal EXCEPT ![i].change.phase = Commit,
                                         ![i].change.state = Pending,
                                         ![i].change.values = (p :> [value |-> v])]
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

\* Rollback proposed change at index 'i'
ProposeRollback(i) ==
   /\ proposal[i].change.phase # None
   /\ proposal[i].rollback.phase = None
   /\ proposal' = [proposal EXCEPT ![i].rollback.phase = Commit,
                                   ![i].rollback.state = Pending]
   /\ UNCHANGED <<configuration, mastership, conn, target, history>>

----

(*
Formal specification, constraints, and theorems.
*)

Init ==
   /\ proposal = [
         i \in 1..NumProposals |-> [
            change   |-> [
               values |-> [p \in {} |-> [index |-> 0, value |-> None]],
               phase  |-> None,
               state  |-> None],
            rollback |-> [
               index  |-> 0,
               values |-> [p \in {} |-> [index |-> 0, value |-> None]],
               phase  |-> None,
               state  |-> None]]]
   /\ configuration = [
         committed |-> [
            index  |-> 0,
            values |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         applied |-> [
            index  |-> 0,
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
      /\ proposal[i].change.phase = Apply
      /\ proposal[i].change.state \notin {Pending, Aborted}
      => \A j \in DOMAIN proposal :
            /\ j < i
            /\ proposal[j].change.phase = Apply
            /\ proposal[j].change.state = Failed
            => /\ proposal[j].rollback.phase = Apply
               /\ proposal[j].rollback.state = Complete

Consistency ==
   /\ target.running 
   /\ configuration.status = Complete
   /\ configuration.applied.target = target.id
   => \A i \in DOMAIN proposal :
         /\ proposal[i].change.phase = Apply
         /\ proposal[i].change.state = Complete
         /\ proposal[i].rollback.state # Complete
         => \A p \in DOMAIN proposal[i].change.values :
               /\ ~\E j \in DOMAIN proposal : 
                     /\ j > i 
                     /\ proposal[i].change.phase = Apply
                     /\ proposal[i].change.state = Complete
                     /\ proposal[i].rollback.state # Complete
               => /\ p \in DOMAIN target.values 
                  /\ target.values[p].value = proposal[i].change.values[p].value
                  /\ target.values[p].index = proposal[i].change.values[p].index

Safety == [](Order /\ Consistency)

THEOREM Spec => Safety

Termination ==
   \A i \in 1..NumProposals :
      /\ proposal[i].change.phase = Commit ~>
            \/ /\ proposal[i].change.phase = Commit
               /\ proposal[i].change.state \in Done
            \/ proposal[i].change.phase = Apply
      /\ proposal[i].change.phase = Apply ~>
            /\ proposal[i].change.state \in Done
      /\ proposal[i].rollback.phase = Commit ~>
            \/ /\ proposal[i].rollback.phase = Commit
               /\ proposal[i].rollback.state \in Done
            \/ proposal[i].rollback.phase = Apply
      /\ proposal[i].rollback.phase = Apply ~>
            /\ proposal[i].rollback.state \in Done
            /\ \/ /\ proposal[i].change.phase = Commit
                  /\ proposal[i].change.state \in Done
               \/ proposal[i].change.phase = Apply

Liveness == Termination

THEOREM Spec => Liveness

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 18:30:03 PDT 2023 by jhalterm
\* Last modified Mon Feb 21 01:32:07 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
