------------------------------- MODULE Mastership -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

----

\* An empty constant
CONSTANT Nil

\* The set of possible master nodes
CONSTANT Node

----

\* Variables defined by other modules.
VARIABLES 
   conn

\* A record of target masterships
VARIABLE mastership

TypeOK ==
   /\ mastership.term \in Nat
   /\ mastership.master # Nil => mastership.master \in Node
   /\ mastership.conn \in Nat

Test == INSTANCE Test WITH 
   File      <- "Mastership.log",
   CurrState <- [
      mastership |-> mastership,
      conn       |-> conn],
   SuccState <- [
      mastership |-> mastership',
      conn       |-> conn']

----

(*
This section models mastership for the configuration service.

Mastership is used primarily to track the lifecycle of individual
configuration targets and react to state changes on the southbound.
Each target is assigned a master from the Node set, and masters
can be unset when the target disconnects.
*)

ReconcileMastership(n) ==
   /\ \/ /\ conn[n].connected
         /\ mastership.master = Nil
         /\ mastership' = [
               master |-> n, 
               term   |-> mastership.term + 1,
               conn   |-> conn[n].id]
      \/ /\ \/ ~conn[n].connected
            \/ conn[n].id # mastership.conn
         /\ mastership.master = n
         /\ mastership' = [mastership EXCEPT !.master = Nil]
   /\ UNCHANGED <<conn>>

=============================================================================