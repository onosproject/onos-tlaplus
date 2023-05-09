------------------------------- MODULE ProposalImpl -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT LogEnabled

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

LOCAL Configuration == INSTANCE ConfigurationImpl

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

LOCAL Log == INSTANCE Log WITH
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
         /\ configuration.committed.changeIndex = i-1
         /\ \/ /\ configuration.committed.targetIndex # i
               /\ configuration.committed.index = configuration.committed.targetIndex
               /\ configuration' = [configuration EXCEPT !.committed.targetIndex = i]
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.committed.targetIndex = i
               /\ \/ /\ proposal[i].rollback.commit = None
                     /\ LET rollbackIndex  == configuration.committed.index
                            rollbackValues == [p \in DOMAIN proposal[i].change.values |->
                                                 IF p \in DOMAIN configuration.committed.values THEN
                                                    configuration.committed.values[p]
                                                 ELSE
                                                    [index |-> 0, value |-> None]]
                        IN \/ /\ proposal[i].rollback.commit = None
                              /\ proposal' = [proposal EXCEPT ![i].change.commit   = InProgress,
                                                              ![i].rollback.index  = rollbackIndex,
                                                              ![i].rollback.values = rollbackValues]
                           \/ /\ proposal[i].rollback.commit = Pending
                              /\ proposal' = [proposal EXCEPT ![i].change.commit  = Aborted,
                                                              ![i].rollback.index = rollbackIndex]
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
      \/ /\ proposal[i].change.commit \in {Aborted, Failed}
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
               /\ \/ /\ proposal[i].change.commit \in {Aborted, Failed}
                     /\ proposal' = [proposal EXCEPT ![i].change.apply = Aborted]
                  \/ /\ proposal[i].change.commit = Complete
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
               /\ \/ /\ proposal[i].change.commit # Aborted
                     /\ proposal' = [proposal EXCEPT ![i].rollback.commit = InProgress]
                  \/ /\ proposal[i].change.commit = Aborted
                     /\ proposal' = [proposal EXCEPT ![i].rollback.commit = Complete]
               /\ UNCHANGED <<configuration>>
         /\ UNCHANGED <<history>>
      \/ /\ proposal[i].rollback.commit = InProgress
         /\ \/ /\ configuration.committed.index = i
               /\ LET values == [p \in DOMAIN configuration.committed.values |-> 
                                    IF p \in DOMAIN proposal[i].rollback.values THEN
                                       proposal[i].rollback.values[p]
                                    ELSE
                                       configuration.committed.values[p]]
                  IN configuration' = [configuration EXCEPT !.committed.index  = proposal[i].rollback.index,
                                                            !.committed.values = values]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Commit, index |-> i])
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.committed.index = proposal[i].rollback.index
               /\ proposal' = [proposal EXCEPT ![i].rollback.commit = Complete]
               /\ UNCHANGED <<configuration, history>>
      \/ /\ proposal[i].rollback.commit = Complete
         /\ configuration.committed.targetIndex = proposal[i].rollback.index
         /\ configuration.committed.index # proposal[i].rollback.index
         /\ configuration' = [configuration EXCEPT !.committed.index = proposal[i].rollback.index]
         /\ UNCHANGED <<proposal, history>>
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
         /\ configuration.committed.index <= proposal[i].rollback.index
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
               /\ LET values == [p \in DOMAIN configuration.applied.values |-> 
                                    IF p \in DOMAIN proposal[i].rollback.values THEN
                                       proposal[i].rollback.values[p]
                                    ELSE
                                       configuration.applied.values[p]]
                  IN /\ target' = [target EXCEPT !.values = proposal[i].rollback.values @@ target.values]
                     /\ configuration' = [configuration EXCEPT !.applied.index  = proposal[i].rollback.index,
                                                               !.applied.values = values]
               /\ history' = Append(history, [type |-> Rollback, phase |-> Apply, index |-> i])
               /\ UNCHANGED <<proposal>>
            \/ /\ configuration.applied.index # i
               /\ proposal' = [proposal EXCEPT ![i].rollback.apply = Complete]
               /\ UNCHANGED <<configuration, target, history>>

Reconcile(n, i) ==
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
   /\ history = <<>>
   /\ Configuration!Init

Next ==
   \/ \E i \in 1..NumProposals :
         \/ ProposeChange(i)
         \/ ProposeRollback(i)
   \/ \E n \in Node, i \in DOMAIN proposal : 
         Log!Action(Reconcile(n, i), [node |-> n, index |-> i])
   \/ /\ Configuration!Next
      /\ UNCHANGED <<proposal, history>>

=============================================================================
