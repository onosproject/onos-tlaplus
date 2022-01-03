------------------------------- MODULE Config -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

CONSTANT TraceEnabled, TraceDepth

\* Indicates that a configuration change is waiting to be applied to the network
CONSTANT Pending

\* Indicates that a configuration change has been applied to the network
CONSTANT Complete

\* Indicates that a configuration change failed
CONSTANT Failed

\* Indicates a change is a configuration
CONSTANT Change

\* Indicates a change is a rollback
CONSTANT Rollback

\* Indicates a device is connected
CONSTANT Connected

\* Indicates a device is disconnected
CONSTANT Disconnected

\* Indicates that an error occurred when applying a change
CONSTANT Error

\* An empty constant
CONSTANT Nil

\* The set of all nodes
CONSTANT Node

\* The set of all devices
CONSTANT Device

ASSUME Pending \in STRING
ASSUME Complete \in STRING
ASSUME Failed \in STRING
ASSUME Rollback \in STRING
ASSUME Connected \in STRING
ASSUME Disconnected \in STRING
ASSUME Error \in STRING
ASSUME Nil \in STRING

ASSUME /\ IsFiniteSet(Node) 
       /\ \A n \in Node : 
             /\ n \notin Device 
             /\ n \in STRING
ASSUME /\ IsFiniteSet(Device) 
       /\ \A d \in Device : 
             /\ d \notin Node 
             /\ d \in STRING

----

\* Per-node election state
VARIABLE leader

\* Per-node per-device election state
VARIABLE master

\* A sequence of network-wide configuration changes
\* Each change contains a record of 'changes' for each device
VARIABLE networkChanges

\* A record of sequences of device configuration changes
\* Each sequence is a list of changes in the order in which they
\* are to be applied to the device
VARIABLE deviceChanges

\* A record of device states - either Connected or Disconnected
VARIABLE deviceState

\* A count of leader changes to serve as a state constraint
VARIABLE electionCount

\* A count of configuration changes to serve as a state constraint
VARIABLE configCount

\* A count of device connection changes to serve as a state constraint
VARIABLE connectionCount

----

\* Node variables
nodeVars == <<leader, master>>

\* Configuration variables
configVars == <<networkChanges, deviceChanges>>

\* Device variables
deviceVars == <<deviceState>>

\* State constraint variables
constraintVars == <<electionCount, configCount, connectionCount>>

vars == <<nodeVars, configVars, deviceVars, constraintVars>>

----
(*
This section models leader election for control loops and for devices.
Leader election is modelled as a simple boolean indicating whether each node
is the leader for the cluster and for each device. This model implies the ordering
of leadership changes is irrelevant to the correctness of the spec.
*)

\* Set the leader for node n to l
SetNodeLeader(n, l) ==
   /\ leader' = [leader EXCEPT ![n] = n = l]
   /\ electionCount' = electionCount + 1
   /\ UNCHANGED <<master, configVars, deviceVars, configCount, connectionCount>>

\* Set the master for device d on node n to l
SetDeviceMaster(n, d, l) ==
   /\ master' = [master EXCEPT ![n] = [master[n] EXCEPT ![d] = n = l]]
   /\ electionCount' = electionCount + 1
   /\ UNCHANGED <<leader, configVars, deviceVars, configCount, connectionCount>>

----
(*
This section models the northbound API for the configuration service.
*)

\* Enqueue network configuration change c
SubmitChange(c) ==
   /\ Cardinality(DOMAIN c) > 0
   /\ networkChanges' = Append(networkChanges, [
                          phase       |-> Change,
                          changes     |-> c,
                          value       |-> Len(networkChanges),
                          state       |-> Pending,
                          incarnation |-> 0])
   /\ configCount' = configCount + 1
   /\ UNCHANGED <<nodeVars, deviceChanges, deviceVars, electionCount, connectionCount>>

RollbackChange(c) ==
   /\ networkChanges[c].phase = Change
   /\ networkChanges[c].state = Complete
   /\ networkChanges' = [networkChanges EXCEPT ![c].phase = Rollback, ![c].state = Pending]
   /\ configCount' = configCount + 1
   /\ UNCHANGED <<nodeVars, deviceChanges, deviceVars, electionCount, connectionCount>>

----

(*
This section models the NetworkChange reconciler. The reconciler reconciles network changes
when the change or one of its device changes is updated.
*)

\* Return the set of all network changes prior to the given change
PriorNetworkChanges(c) ==
   {n \in DOMAIN networkChanges : n < c}

\* Return the set of all completed device changes for network change c
NetworkCompletedChanges(c) ==
   {d \in DOMAIN networkChanges[c].changes :
      /\ c \in DOMAIN deviceChanges[d]
      /\ deviceChanges[d][c].state = Complete}

\* Return a boolean indicating whether all device changes are complete for the given network change
NetworkChangesComplete(c) ==
   Cardinality(NetworkCompletedChanges(c)) = Cardinality(DOMAIN networkChanges[c].changes)

\* Return the set of all incomplete device changes prior to network change c
PriorIncompleteDevices(c) ==
   UNION {DOMAIN networkChanges[n].changes :
             n \in {n \in PriorNetworkChanges(c) : ~NetworkChangesComplete(n)}}

\* Return the set of all devices configured by network change c
NetworkChangeDevices(c) == DOMAIN networkChanges[c].changes

\* Return a boolean indicating whether network change 'c' is complete
IsCompleteNetworkChange(c) ==
   /\ networkChanges[c].phase = Change
   /\ networkChanges[c].state = Complete

\* Return the set of all connected devices configured by network change c
ConnectedDevices(c) == {d \in DOMAIN networkChanges[c].changes : deviceState[d] = Connected}

\* Return a boolean indicating whether network change c can be applied
\* A change can be applied if its devices do not intersect with past device
\* changes that have not been applied
CanApplyNetworkChange(c) ==
   /\ Cardinality(ConnectedDevices(c) \cap NetworkChangeDevices(c)) # 0
   /\ Cardinality(NetworkChangeDevices(c) \cap PriorIncompleteDevices(c)) = 0
   /\ \/ networkChanges[c].incarnation = 0
      \/ Cardinality({d \in DOMAIN networkChanges[c].changes :
            /\ deviceChanges[d][c].incarnation = networkChanges[c].incarnation
            /\ deviceChanges[d][c].phase = Rollback
            /\ deviceChanges[d][c].state = Complete}) =
                   Cardinality(DOMAIN networkChanges[c].changes)

\* Return a boolean indicating whether a change exists for the given device
\* If the device is modified by the change, it must contain a device change
\* that's either Complete or with the same 'incarnation' as the network change.
HasDeviceChange(d, c) ==
   /\ c \in DOMAIN deviceChanges[d]
   /\ deviceChanges[d][c].incarnation = networkChanges[c].incarnation

\* Return a boolean indicating whether device changes have been propagated
\* for the given network change
HasDeviceChanges(c) ==
   Cardinality({d \in DOMAIN networkChanges[c].changes : HasDeviceChange(d, c)}) =
      Cardinality(DOMAIN networkChanges[c].changes)

\* Add or update the given device changes for the given network change.
\* If a device change already exists, update the 'incarnation' field.
CreateDeviceChange(d, c) ==
   IF d \in DOMAIN networkChanges[c].changes THEN
      IF c \in DOMAIN deviceChanges[d] THEN
         IF deviceChanges[d][c].state = Complete THEN
            deviceChanges[d]
         ELSE
            [deviceChanges[d] EXCEPT ![c].incarnation = networkChanges[c].incarnation,
                                    ![c].state = Pending]
      ELSE
         [x \in {c} |-> [
            phase       |-> networkChanges[c].phase,
            state       |-> Pending,
            value       |-> networkChanges[c].value,
            incarnation |-> networkChanges[c].incarnation]] @@ deviceChanges[d]
   ELSE
      deviceChanges[d]

\* Add or update device changes for the given network change
CreateDeviceChanges(c) ==
   deviceChanges' = [d \in DOMAIN deviceChanges |-> CreateDeviceChange(d, c)]

\* Rollback device change c for device d
RollbackDeviceChange(d, c) ==
   IF /\ c \in DOMAIN deviceChanges[d]
      /\ \/ deviceChanges[d][c].phase = Change
         \/ /\ deviceChanges[d][c].phase = Rollback
            /\ deviceChanges[d][c].state = Failed
   THEN
      [deviceChanges[d] EXCEPT ![c].phase = Rollback, ![c].state = Pending]
   ELSE
      deviceChanges[d]

\* Roll back device changes
RollbackDeviceChanges(c) ==
   deviceChanges' = [d \in DOMAIN deviceChanges |-> RollbackDeviceChange(d, c)]

\* Return a boolean indicating whether the given device change is Failed
IsFailedDeviceChange(d, c) ==
   /\ c \in DOMAIN deviceChanges[d]
   /\ deviceChanges[d][c].incarnation = networkChanges[c].incarnation
   /\ deviceChanges[d][c].state = Failed

\* Return a boolean indicating whether the given device change is Complete
IsCompleteDeviceChange(d, c) ==
   /\ c \in DOMAIN deviceChanges[d]
   /\ deviceChanges[d][c].incarnation = networkChanges[c].incarnation
   /\ deviceChanges[d][c].phase = Change
   /\ deviceChanges[d][c].state = Complete

\* Return a boolean indicating whether any device change is Failed for the given network change
HasFailedDeviceChanges(c) ==
   Cardinality({d \in DOMAIN networkChanges[c].changes :
      IsFailedDeviceChange(d, c)}) # 0

\* Return a boolean indicating whether all device changes are Complete for the given network change
DeviceChangesComplete(c) ==
   Cardinality({d \in DOMAIN networkChanges[c].changes :
      IsCompleteDeviceChange(d, c)}) =
         Cardinality(DOMAIN networkChanges[c].changes)

\* Reconcile a network change state
ReconcileNetworkChange(n, c) ==
   /\ leader[n]
   /\ networkChanges[c].state = Pending
   /\ \/ /\ ~HasDeviceChanges(c)
         /\ CreateDeviceChanges(c)
         /\ UNCHANGED <<networkChanges>>
      \/ /\ HasDeviceChanges(c)
         /\ \/ /\ networkChanges[c].phase = Change
               /\ \/ /\ CanApplyNetworkChange(c)
                     /\ networkChanges' = [networkChanges EXCEPT
                           ![c].incarnation = networkChanges[c].incarnation + 1]
                     /\ UNCHANGED <<deviceChanges>>
                  \/ /\ DeviceChangesComplete(c)
                     /\ networkChanges' = [networkChanges EXCEPT
                           ![c].state = Complete]
                     /\ UNCHANGED <<deviceChanges>>
                  \/ /\ HasFailedDeviceChanges(c)
                     /\ RollbackDeviceChanges(c)
                     /\ UNCHANGED <<networkChanges>>
            \* TODO
            \/ /\ networkChanges[c].phase = Rollback
               /\ networkChanges' = [networkChanges EXCEPT
                      ![c].state = Complete]
               /\ UNCHANGED <<deviceChanges>>
   /\ UNCHANGED <<nodeVars, deviceVars, constraintVars>>

----

(*
This section models the DeviceChange reconciler.
*)

ReconcileDeviceChange(n, d, c) ==
   /\ master[n][d]
   /\ deviceChanges[d][c].state = Pending
   /\ deviceChanges[d][c].incarnation > 0
   /\ \/ /\ deviceState[d] = Connected
         /\ deviceChanges' = [deviceChanges EXCEPT
               ![d] = [deviceChanges[d] EXCEPT ![c].state = Complete]]
      \/ /\ deviceState[d] = Disconnected
         /\ deviceChanges' = [deviceChanges EXCEPT
               ![d] = [deviceChanges[d] EXCEPT ![c].state = Failed]]
   /\ UNCHANGED <<nodeVars, networkChanges, deviceVars, constraintVars>>

----
(*
This section models device states. Devices begin in the Disconnected state and can only
be configured while in the Connected state.
*)

\* Set device d state to Connected
ConnectDevice(d) ==
   /\ deviceState' = [deviceState EXCEPT ![d] = Connected]
   /\ connectionCount' = connectionCount + 1
   /\ UNCHANGED <<nodeVars, configVars, electionCount, configCount>>

\* Set device d state to Disconnected
DisconnectDevice(d) ==
   /\ deviceState' = [deviceState EXCEPT ![d] = Disconnected]
   /\ connectionCount' = connectionCount + 1
   /\ UNCHANGED <<nodeVars, configVars, electionCount, configCount>>

----
(*
Init and next state predicates
*)

Init ==
   /\ leader = [n \in Node |-> FALSE]
   /\ master = [n \in Node |-> [d \in Device |-> FALSE]]
   /\ networkChanges = <<>>
   /\ deviceChanges = [d \in Device |-> [x \in {} |-> [phase |-> Change, state |-> Pending]]]
   /\ deviceState = [d \in Device |-> Disconnected]
   /\ electionCount = 0
   /\ configCount = 0
   /\ connectionCount = 0

Next ==
   \/ \E d \in SUBSET Device :
         SubmitChange([x \in d |-> 1])
   \/ \E c \in DOMAIN networkChanges :
         RollbackChange(c)
   \/ \E n \in Node :
         \E l \in Node :
            SetNodeLeader(n, l)
   \/ \E n \in Node :
         \E d \in Device :
            \E l \in Node :
               SetDeviceMaster(n, d, l)
   \/ \E n \in Node :
         \E c \in DOMAIN networkChanges :
            ReconcileNetworkChange(n, c)
   \/ \E n \in Node :
         \E d \in Device :
            \E c \in DOMAIN deviceChanges[d] :
               ReconcileNetworkChange(n, c)
   \/ \E n \in Node :
         \E d \in Device :
            \E c \in DOMAIN deviceChanges[d] :
               ReconcileDeviceChange(n, d, c)
   \/ \E d \in Device :
         ConnectDevice(d)
   \/ \E d \in Device :
         DisconnectDevice(d)

TraceNext ==
   \/ Next
   \/ /\ ~ENABLED Next
      /\ UNCHANGED <<vars>>

Spec == Init /\ [][TraceNext]_vars

Inv == \A c1 \in DOMAIN networkChanges :
          \A c2 \in DOMAIN networkChanges :
             LET d1 == DOMAIN networkChanges[c1].changes
                 s1 == networkChanges[c1].state
                 d2 == DOMAIN networkChanges[c2].changes
                 s2 == networkChanges[c2].state
             IN
                (c1 > c2 /\ d1 \in SUBSET d2 /\ s1 = Complete) => s2 = Complete

Term == <>(\A c \in DOMAIN networkChanges : IsCompleteNetworkChange(c))

=============================================================================
\* Modification History
\* Last modified Mon Jan 03 01:43:02 PST 2022 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
