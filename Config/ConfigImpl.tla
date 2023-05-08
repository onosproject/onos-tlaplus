------------------------------- MODULE ConfigImpl -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

(*
This section specifies constant parameters for the model.
*)

CONSTANT LogEnabled

ASSUME LogEnabled \in BOOLEAN 

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

LOCAL MastershipLog == INSTANCE Log WITH
   File      <- "Mastership.log",
   CurrState <- [
      target        |-> target,
      mastership    |-> mastership,
      conns         |-> conn],
   SuccState <- [
      target        |-> target',
      mastership    |-> mastership',
      conns         |-> conn'],
   Enabled   <- LogEnabled

LOCAL ConfigurationLog == INSTANCE Log WITH
   File      <- "Configuration.log",
   CurrState <- [
      configuration |-> configuration,
      target        |-> target,
      mastership    |-> mastership,
      conns         |-> conn],
   SuccState <- [
      configuration |-> configuration',
      target        |-> target',
      mastership    |-> mastership',
      conns         |-> conn'],
   Enabled   <- LogEnabled

LOCAL ProposalLog == INSTANCE Log WITH
   File      <- "Proposal.log",
   CurrState <- [
      proposals     |-> [i \in {i \in DOMAIN proposal : proposal[i].phase # None} |-> proposal[i]],
      configuration |-> configuration,
      target        |-> target,
      mastership    |-> mastership,
      conns         |-> conn],
   SuccState <- [
      proposals     |-> [i \in {i \in DOMAIN proposal' : proposal'[i].phase # None} |-> proposal'[i]],
      configuration |-> configuration',
      target        |-> target',
      mastership    |-> mastership',
      conns         |-> conn'],
   Enabled   <- LogEnabled

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
   \* 'index' is the current index committed to the configuration
   \* 'changeIndex' is the maximum change index committed to the configuration
   \* 'targetIndex' is the index of the proposal currently being committed
   \* targetIndex is always changed first. Once the change is committed, the
   \* changeIndex and index will be incremented to match the targetIndex. 
   \* If the index is less than the targetIndex, this indicates a rollback
   \* of a prior proposal is being processed, and the targetIndex cannot be incremented
   \* until that rollback is complete. The index represents the index to which
   \* the proposal at changeIndex + 1 rolls back.
   /\ \/ /\ proposal[i].change.commit = Pending
         /\ \/ /\ configuration.committed.changeIndex = i-1
               /\ configuration.committed.targetIndex # i
               /\ configuration.committed.index = configuration.committed.targetIndex
               /\ configuration' = [configuration EXCEPT !.committed.targetIndex = i]
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.committed.changeIndex = i-1
               /\ configuration.committed.targetIndex = i
               /\ LET rollbackIndex  == configuration.committed.index
                      rollbackValues == [p \in DOMAIN proposal[i].change.values |->
                                           IF p \in DOMAIN configuration.committed.values THEN
                                              configuration.committed.values[p]
                                           ELSE
                                              [index |-> 0, value |-> None]]
                  IN proposal' = [proposal EXCEPT ![i].change.commit   = InProgress,
                                                  ![i].rollback.index  = rollbackIndex,
                                                  ![i].rollback.values = rollbackValues]
               /\ UNCHANGED <<configuration>>
         /\ UNCHANGED <<history>>
      \/ /\ proposal[i].change.commit = InProgress
         /\ \/ /\ configuration.committed.changeIndex = i-1
               /\ \/ /\ LET values == [p \in DOMAIN proposal[i].change.values |->
                                          proposal[i].change.values[p] @@ [index |-> i]] @@
                                             configuration.committed.values
                        IN /\ configuration' = [configuration EXCEPT !.committed.index       = i,
                                                                     !.committed.changeIndex = i,
                                                                     !.committed.values      = values]
                           /\ history' = Append(history, [type |-> Change, phase |-> Commit, index |-> i])
                           /\ UNCHANGED <<proposal>>
                  \/ /\ proposal' = [proposal EXCEPT ![i].change.commit = Failed]
                     /\ UNCHANGED <<configuration, history>>
            \/ /\ configuration.committed.changeIndex >= i
               /\ proposal' = [proposal EXCEPT ![i].change.commit = Complete]
               /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].change.commit = Failed
         /\ configuration.committed.changeIndex = i-1
         /\ configuration' = [configuration EXCEPT !.committed.index       = i,
                                                   !.committed.changeIndex = i]
         /\ UNCHANGED <<proposal, history>>
   /\ UNCHANGED <<target>>

ApplyChange(n, i) == 
   \* 'index' is the current index applied to the configuration
   \* 'changeIndex' is the maximum change index applied to the configuration
   \* 'targetIndex' is the index of the proposal currently being applied
   \* targetIndex is always changed first. Once the change is applied, the
   \* changeIndex and index will be incremented to match the targetIndex. 
   \* If the index is less than the targetIndex, this indicates a rollback
   \* of a prior proposal is being processed, and the targetIndex cannot be incremented
   \* until that rollback is complete. The index represents the index to which
   \* the proposal at changeIndex + 1 rolls back.
   /\ \/ /\ proposal[i].change.apply = Pending
         /\ configuration.committed.changeIndex >= i
         /\ configuration.applied.changeIndex = i-1
         /\ \/ /\ configuration.applied.targetIndex # i
               /\ configuration.applied.index = configuration.applied.targetIndex
               /\ configuration' = [configuration EXCEPT !.applied.targetIndex = i]
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.applied.targetIndex = i
               /\ proposal' = [proposal EXCEPT ![i].change.apply = InProgress]
               /\ UNCHANGED <<configuration>>
         /\ UNCHANGED <<target, history>>
      \/ /\ proposal[i].change.apply = InProgress
         \* Verify the applied term is the current mastership term to ensure the
         \* configuration has been synchronized following restarts.
         /\ configuration.applied.term = mastership.term
         \* Verify the node's connection to the target.
         /\ conn[n].connected
         /\ mastership.conn = conn[n].id
         /\ target.running
         /\ \/ /\ configuration.applied.changeIndex = i-1
               /\ \/ /\ LET values == [p \in DOMAIN proposal[i].change.values |-> 
                                          proposal[i].change.values[p] @@ [index |-> i]]
                        IN /\ target' = [target EXCEPT !.values = values @@ target.values]
                           /\ configuration' = [configuration EXCEPT !.applied.index  = i,
                                                                     !.applied.changeIndex = i,
                                                                     !.applied.values = values @@ 
                                                                        configuration.applied.values]
                           /\ history' = Append(history, [type |-> Change, phase |-> Apply, index |-> i])
                           /\ UNCHANGED <<proposal>>
                  \/ /\ proposal' = [proposal EXCEPT ![i].change.apply = Failed]
                     /\ UNCHANGED <<configuration, target, history>>
            \/ /\ configuration.applied.changeIndex >= i
               /\ proposal' = [proposal EXCEPT ![i].change.apply = Complete]
               /\ UNCHANGED <<configuration, target, history>>
      \/ /\ proposal[i].change.apply = Failed
         /\ configuration.applied.changeIndex = i-1
         /\ configuration' = [configuration EXCEPT !.applied.index       = i,
                                                   !.applied.changeIndex = i]
         /\ UNCHANGED <<proposal, target, history>>

CommitRollback(n, i) == 
   \* 'index' is the current index committed to the configuration
   \* 'changeIndex' is the maximum change index committed to the configuration
   \* 'targetIndex' is the index of the proposal currently being committed
   \* targetIndex is always changed first. Once the rollback is committed, the
   \* index will be decremented to match the targetIndex. The next time a change
   \* is committed, the index will increase again. If the committed index is equal 
   \* to this proposal index, this proposal is the next to be rolled back. To roll
   \* back a proposal, the target index is set to the proposal's rollback index.
   \* When the rollback is committed, the committed index is set to the proposal's
   \* rollback index, thus matching the targetIndex. This unblocks new changes
   \* to be committed.
   /\ \/ /\ proposal[i].rollback.commit = Pending
         /\ configuration.committed.changeIndex >= i
         /\ configuration.committed.index = i
         /\ \/ /\ configuration.committed.targetIndex = i
               /\ configuration' = [configuration EXCEPT !.committed.targetIndex = proposal[i].rollback.index]
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.committed.targetIndex = proposal[i].rollback.index
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = InProgress]
               /\ UNCHANGED <<configuration>>
         /\ UNCHANGED <<history>>
      \/ /\ proposal[i].rollback.commit = InProgress
         /\ \/ /\ configuration.committed.index = i
               /\ configuration' = [configuration EXCEPT !.committed.index  = proposal[i].rollback.index,
                                                         !.committed.values = proposal[i].rollback.values @@ 
                                                                                 configuration.committed.values]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.committed.index # i
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = Complete]
               /\ UNCHANGED <<configuration, history>>
   /\ UNCHANGED <<target>>

ApplyRollback(n, i) == 
   \* 'index' is the current index applied to the configuration
   \* 'changeIndex' is the maximum change index applied to the configuration
   \* 'targetIndex' is the index of the proposal currently being applied
   \* targetIndex is always changed first. Once the rollback is applied, the
   \* index will be decremented to match the targetIndex. The next time a change
   \* is applied, the index will increase again. If the applied index is equal 
   \* to this proposal index, this proposal is the next to be rolled back. To roll
   \* back a proposal, the target index is set to the proposal's rollback index.
   \* When the rollback is applied, the applied index is set to the proposal's
   \* rollback index, thus matching the targetIndex. This unblocks new changes
   \* to be applied.
   /\ \/ /\ proposal[i].rollback.apply = Pending
         /\ configuration.applied.changeIndex >= i
         /\ configuration.applied.index = i
         /\ \/ /\ configuration.applied.targetIndex = i
               /\ configuration' = [configuration EXCEPT !.applied.targetIndex = proposal[i].rollback.index]
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.applied.targetIndex = proposal[i].rollback.index
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = InProgress]
               /\ UNCHANGED <<configuration>>
         /\ UNCHANGED <<target, history>>
      \/ /\ proposal[i].rollback.apply = InProgress
         /\ \/ /\ configuration.applied.index = i
               \* Verify the applied term is the current mastership term to ensure the
               \* configuration has been synchronized following restarts.
               /\ configuration.applied.term = mastership.term
               \* Verify the node's connection to the target.
               /\ conn[n].connected
               /\ target.running
               /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
               /\ configuration' = [configuration EXCEPT !.applied.index  = proposal[i].rollback.index,
                                                         !.applied.values = proposal[i].rollback.values @@ 
                                                                               configuration.applied.values]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.applied.index # i
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = Complete]
               /\ UNCHANGED <<configuration, target, history>>

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
                                         ![i].change.values = (p :> [value |-> v]),
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
            change   |-> [
               values |-> [p \in {} |-> [index |-> 0, value |-> None]],
               commit |-> None,
               apply  |-> None],
            rollback |-> [
               index  |-> 0,
               values |-> [p \in {} |-> [index |-> 0, value |-> None]],
               commit |-> None,
               apply  |-> None]]]
   /\ configuration = [
         committed |-> [
            index       |-> 0,
            changeIndex |-> 0,
            targetIndex |-> 0,
            values      |-> [p \in {} |-> [index |-> 0, value |-> None]]],
         applied |-> [
            index       |-> 0,
            changeIndex |-> 0,
            targetIndex |-> 0,
            term        |-> 0,
            target      |-> 0,
            values      |-> [p \in {} |-> [index |-> 0, value |-> None]]],
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
   \/ \E n \in Node, i \in DOMAIN proposal : 
         ProposalLog!Action(ReconcileProposal(n, i), [node |-> n, index |-> i])
   \/ \E n \in Node : 
         ConfigurationLog!Action(ReconcileConfiguration(n), [node |-> n])
   \/ \E n \in Node : 
         MastershipLog!Action(ReconcileMastership(n), [node |-> n])
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

Mapping == INSTANCE Config WITH 
   proposal <- [i \in DOMAIN proposal |-> [
      phase    |-> proposal[i].phase,
      values   |-> [p \in DOMAIN proposal[i].change.values |-> proposal[i].change.values[p].value],
      change   |-> [
         commit |-> IF /\ proposal[i].change.commit = InProgress 
                       /\ configuration.committed.changeIndex >= i
                    THEN Complete
                    ELSE proposal[i].change.commit,
         apply  |-> IF /\ proposal[i].change.apply = InProgress 
                       /\ configuration.applied.changeIndex >= i
                     THEN Complete
                     ELSE proposal[i].change.apply],
      rollback |-> [
         commit |-> IF /\ proposal[i].rollback.commit = InProgress 
                       /\ configuration.committed.index # i
                    THEN Complete
                    ELSE proposal[i].rollback.commit,
         apply  |-> IF /\ proposal[i].rollback.commit = InProgress 
                       /\ configuration.applied.index # i
                    THEN Complete
                    ELSE proposal[i].rollback.apply]]],
   configuration <- [
      committed |-> [
         values |-> configuration.committed.values],
      applied |-> [
         term   |-> configuration.applied.term,
         target |-> configuration.applied.target,
         values |-> configuration.applied.values],
      status |-> configuration.status]

Refinement == Mapping!Spec

Order == Mapping!Order

Consistency == Mapping!Consistency

Liveness == Mapping!Liveness

Sequential == Mapping!Sequential

=============================================================================
