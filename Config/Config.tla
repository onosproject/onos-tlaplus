------------------------------- MODULE Config -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

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

\* The set of all nodes
CONSTANT Node

\* The set of all devices
CONSTANT Device

\* An empty constant
CONSTANT Nil

\* Per-node election state
VARIABLE leader

\* Per-node per-device election state
VARIABLE master

\* A sequence of network-wide configuration changes
\* Each change contains a record of 'changes' for each device
VARIABLE networkChange

\* A record of sequences of device configuration changes
\* Each sequence is a list of changes in the order in which they
\* are to be applied to the device
VARIABLE deviceChange

\* A record of device states - either Available or Unavailable
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
configVars == <<networkChange, deviceChange>>

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
    /\ networkChange' = Append(networkChange, [
                            phase       |-> Change,
                            changes     |-> c,
                            value       |-> Len(networkChange),
                            state       |-> Pending,
                            incarnation |-> 0])
    /\ configCount' = configCount + 1
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, electionCount, connectionCount>>

RollbackChange(c) ==
    /\ networkChange[c].phase = Change
    /\ networkChange[c].state = Complete
    /\ networkChange' = [networkChange EXCEPT ![c].phase = Rollback, ![c].state = Pending]
    /\ configCount' = configCount + 1
    /\ UNCHANGED <<nodeVars, deviceChange, deviceVars, electionCount, connectionCount>>

----

(*
This section models the NetworkChange reconciler. The reconciler reconciles network changes
when the change or one of its device changes is updated.
*)

\* Return the set of all network changes prior to the given change
PriorNetworkChanges(c) ==
    {n \in DOMAIN networkChange : n < c}

\* Return the set of all completed device changes for network change c
NetworkCompletedChanges(c) ==
    {d \in DOMAIN networkChange[c].changes :
        /\ c \in DOMAIN deviceChange[d]
        /\ deviceChange[d][c].state = Complete}

\* Return a boolean indicating whether all device changes are complete for the given network change
NetworkChangesComplete(c) ==
    Cardinality(NetworkCompletedChanges(c)) = Cardinality(DOMAIN networkChange[c].changes)

\* Return the set of all incomplete device changes prior to network change c
PriorIncompleteDevices(c) ==
    UNION {DOMAIN networkChange[n].changes :
               n \in {n \in PriorNetworkChanges(c) : ~NetworkChangesComplete(n)}}

\* Return the set of all devices configured by network change c
NetworkChangeDevices(c) == DOMAIN networkChange[c].changes

\* Return the set of all connected devices configured by network change c
ConnectedDevices(c) == {d \in DOMAIN networkChange[c].changes : deviceState[d] = Connected}

\* Return a boolean indicating whether network change c can be applied
\* A change can be applied if its devices do not intersect with past device
\* changes that have not been applied
CanApplyNetworkChange(c) ==
    /\ Cardinality(ConnectedDevices(c) \cap NetworkChangeDevices(c)) # 0
    /\ Cardinality(NetworkChangeDevices(c) \cap PriorIncompleteDevices(c)) = 0
    /\ \/ networkChange[c].incarnation = 0
       \/ Cardinality({d \in DOMAIN networkChange[c].changes :
             /\ deviceChange[d][c].incarnation = networkChange[c].incarnation
             /\ deviceChange[d][c].phase = Rollback
             /\ deviceChange[d][c].state = Complete}) =
                   Cardinality(DOMAIN networkChange[c].changes)

\* Return a boolean indicating whether a change exists for the given device
\* If the device is modified by the change, it must contain a device change
\* that's either Complete or with the same 'incarnation' as the network change.
HasDeviceChange(d, c) ==
    /\ c \in DOMAIN deviceChange[d]
    /\ deviceChange[d][c].incarnation = networkChange[c].incarnation

\* Return a boolean indicating whether device changes have been propagated
\* for the given network change
HasDeviceChanges(c) ==
    Cardinality({d \in DOMAIN networkChange[c].changes : HasDeviceChange(d, c)}) =
       Cardinality(DOMAIN networkChange[c].changes)

\* Add or update the given device changes for the given network change.
\* If a device change already exists, update the 'incarnation' field.
CreateDeviceChange(d, c) ==
    IF Cardinality(DOMAIN deviceChange[d]) = 0 THEN
        [x \in {c} |-> [
                    phase       |-> networkChange[c].phase,
                    state       |-> Pending,
                    value       |-> networkChange[c].value,
                    incarnation |-> networkChange[c].incarnation]]
    ELSE
        IF d \in DOMAIN networkChange[c].changes THEN
            IF c \in DOMAIN deviceChange[d] THEN
                IF deviceChange[d][c].state = Complete THEN
                    deviceChange[d][c]
                ELSE
                    [deviceChange[d] EXCEPT ![c].incarnation = networkChange[c].incarnation,
                                            ![c].state = Pending]
            ELSE
                [x \in {c} |-> [
                    phase       |-> networkChange[c].phase,
                    state       |-> Pending,
                    value       |-> networkChange[c].value,
                    incarnation |-> networkChange[c].incarnation]] @@ deviceChange[d]
        ELSE
            deviceChange[d]

\* Add or update device changes for the given network change
CreateDeviceChanges(c) ==
    deviceChange' = [d \in DOMAIN deviceChange |-> CreateDeviceChange(d, c)]

\* Rollback device change c for device d
RollbackDeviceChange(d, c) ==
    IF /\ c \in DOMAIN deviceChange[d]
       /\ \/ deviceChange[d][c].phase = Change
          \/ /\ deviceChange[d][c].phase = Rollback
             /\ deviceChange[d][c].state = Failed
    THEN
        [deviceChange[d] EXCEPT ![c].phase = Rollback, ![c].state = Pending]
    ELSE
        deviceChange[d]

\* Roll back device changes
RollbackDeviceChanges(c) ==
    deviceChange' = [d \in DOMAIN deviceChange |-> RollbackDeviceChange(d, c)]

\* Return a boolean indicating whether the given device change is Failed
IsFailedDeviceChange(d, c) ==
    /\ c \in DOMAIN deviceChange[d]
    /\ deviceChange[d][c].incarnation = networkChange[c].incarnation
    /\ deviceChange[d][c].state = Failed

\* Return a boolean indicating whether the given device change is Complete
IsCompleteDeviceChange(d, c) ==
    /\ c \in DOMAIN deviceChange[d]
    /\ deviceChange[d][c].incarnation = networkChange[c].incarnation
    /\ deviceChange[d][c].phase = Change
    /\ deviceChange[d][c].state = Complete

\* Return a boolean indicating whether any device change is Failed for the given network change
HasFailedDeviceChanges(c) ==
    Cardinality({d \in DOMAIN networkChange[c].changes :
        IsFailedDeviceChange(d, c)}) # 0

\* Return a boolean indicating whether all device changes are Complete for the given network change
DeviceChangesComplete(c) ==
    Cardinality({d \in DOMAIN networkChange[c].changes :
       IsCompleteDeviceChange(d, c)}) =
          Cardinality(DOMAIN networkChange[c].changes)

\* Reconcile a network change state
ReconcileNetworkChange(n, c) ==
    /\ leader[n]
    /\ networkChange[c].state = Pending
    /\ \/ /\ ~HasDeviceChanges(c)
          /\ CreateDeviceChanges(c)
          /\ UNCHANGED <<networkChange>>
       \/ /\ HasDeviceChanges(c)
          /\ \/ /\ networkChange[c].phase = Change
                /\ \/ /\ CanApplyNetworkChange(c)
                      /\ networkChange' = [networkChange EXCEPT
                            ![c].incarnation = networkChange[c].incarnation + 1]
                      /\ UNCHANGED <<deviceChange>>
                   \/ /\ DeviceChangesComplete(c)
                      /\ networkChange' = [networkChange EXCEPT
                            ![c].state = Complete]
                      /\ UNCHANGED <<deviceChange>>
                   \/ /\ HasFailedDeviceChanges(c)
                      /\ RollbackDeviceChanges(c)
                      /\ UNCHANGED <<networkChange>>
             \* TODO
             \/ /\ networkChange[c].phase = Rollback
                /\ networkChange' = [networkChange EXCEPT
                       ![c].state = Complete]
                /\ UNCHANGED <<deviceChange>>
    /\ UNCHANGED <<nodeVars, deviceVars, constraintVars>>

----

(*
This section models the DeviceChange reconciler.
*)

ReconcileDeviceChange(n, d, c) ==
    /\ master[n][d]
    /\ deviceChange[d][c].state = Pending
    /\ deviceChange[d][c].incarnation > 0
    /\ \/ /\ deviceState[d] = Connected
          /\ deviceChange' = [deviceChange EXCEPT
                ![d] = [deviceChange[d] EXCEPT ![c].state = Complete]]
       \/ /\ deviceState[d] = Disconnected
          /\ deviceChange' = [deviceChange EXCEPT
                ![d] = [deviceChange[d] EXCEPT ![c].state = Failed]]
    /\ UNCHANGED <<nodeVars, networkChange, deviceVars, constraintVars>>

----
(*
This section models device states. Devices begin in the Unavailable state and can only
be configured while in the Available state.
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
    /\ networkChange = <<>>
    /\ deviceChange = [d \in Device |-> [x \in {} |-> [phase |-> Change, state |-> Pending]]]
    /\ deviceState = [d \in Device |-> Disconnected]
    /\ electionCount = 0
    /\ configCount = 0
    /\ connectionCount = 0

Next ==
    \/ \E d \in SUBSET Device :
          SubmitChange([x \in d |-> 1])
    \/ \E c \in DOMAIN networkChange :
          RollbackChange(c)
    \/ \E n \in Node :
          \E l \in Node :
             SetNodeLeader(n, l)
    \/ \E n \in Node :
          \E d \in Device :
             \E l \in Node :
                SetDeviceMaster(n, d, l)
    \/ \E n \in Node :
          \E c \in DOMAIN networkChange :
             ReconcileNetworkChange(n, c)
    \/ \E n \in Node :
          \E d \in Device :
             \E c \in DOMAIN deviceChange[d] :
                ReconcileNetworkChange(n, c)
    \/ \E n \in Node :
          \E d \in Device :
             \E c \in DOMAIN deviceChange[d] :
                ReconcileDeviceChange(n, d, c)
    \/ \E d \in Device :
          ConnectDevice(d)
    \/ \E d \in Device :
          DisconnectDevice(d)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Sep 22 13:23:25 PDT 2021 by jordanhalterman
\* Created Wed Sep 22 13:22:32 PDT 2021 by jordanhalterman
