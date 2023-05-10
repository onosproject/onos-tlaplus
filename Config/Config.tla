------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

----

NumProposals == 3

None == "<none>"

Synchronizing == "Synchronizing"
Synchronized == "Synchronized"

Change == "Change"
Rollback == "Rollback"

Commit == "Commit"
Apply == "Apply"

Pending == "Pending"
InProgress == "InProgress"
Complete == "Complete"
Aborted == "Aborted"
Failed == "Failed"

Node == {"node1"}

Path == {"path1"}

Value == {"value1", "value2"}

VARIABLES
   proposal,
   configuration,
   mastership,
   conn,
   target,
   history

vars == <<proposal, configuration, mastership, conn, target, history>>

----

LOCAL Proposal == INSTANCE Proposal

Spec ==
   /\ Proposal!Init
   /\ [][Proposal!Next]_vars
   /\ \A i \in 1..NumProposals : WF_vars(Proposal!ProposeChange(i) \/ Proposal!ProposeRollback(i))
   /\ \A n \in Node, i \in 1..NumProposals : WF_vars(Proposal!ReconcileProposal(n, i))
   /\ \A n \in Node : WF_<<configuration, mastership, conn, target>>(Proposal!ReconcileConfiguration(n))
   /\ \A n \in Node : WF_<<mastership, conn, target>>(Proposal!ReconcileMastership(n))
   /\ \A n \in Node : WF_<<conn, target>>(Proposal!ConnectNode(n) \/ Proposal!DisconnectNode(n))
   /\ WF_<<target>>(Proposal!StartTarget)
   /\ WF_<<target>>(Proposal!StopTarget)

----

LimitMastership == 
   CASE mastership.term < 2 -> TRUE
     [] mastership.term = 2 -> mastership.master # None
     [] OTHER -> FALSE

LimitConn == 
   \A n \in DOMAIN conn : 
      CASE conn[n].id < 2 -> TRUE
        [] conn[n].id = 2 -> conn[n].connected
        [] OTHER -> FALSE

LimitTarget == 
   CASE target.id < 2 -> TRUE
     [] target.id = 2 -> target.running
     [] OTHER -> FALSE

Constraint == 
   /\ LimitMastership
   /\ LimitConn
   /\ LimitTarget

----

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

Done == {Complete, Aborted, Failed}

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
