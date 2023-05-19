------------------------------- MODULE Mastership -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* The set of possible master nodes
CONSTANT Node

----

\* A record of target masterships
VARIABLE mastership

TypeOK ==
   /\ mastership.term \in Nat
   /\ mastership.master # Nil => mastership.master \in Node

----

(*
This section models mastership for the configuration service.

Mastership is used primarily to track the lifecycle of individual
configuration targets and react to state changes on the southbound.
Each target is assigned a master from the Node set, and masters
can be unset when the target disconnects.
*)

\* Set node n as the master for target t
SetMaster(n) ==
   /\ mastership.master # n
   /\ mastership' = [mastership EXCEPT !.term   = mastership.term + 1,
                                       !.master = n]

UnsetMaster ==
   /\ mastership.master # Nil
   /\ mastership' = [mastership EXCEPT !.master = Nil]

=============================================================================
