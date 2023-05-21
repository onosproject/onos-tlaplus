------------------------------- MODULE Configuration -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Status constants
CONSTANTS
   Pending,
   InProgress,
   Complete

Status == 
   {Pending,
    InProgress,
    Complete}

----

\* Variables defined by other modules.
VARIABLES 
   mastership,
   conn,
   target

\* A record of per-target configurations
VARIABLE configuration

TypeOK ==
   /\ configuration.state \in Status
   /\ configuration.term \in Nat
   /\ configuration.committed.index \in Nat
   /\ configuration.committed.revision \in Nat
   /\ \A p \in DOMAIN configuration.committed.values :
         /\ configuration.committed.values[p].index \in Nat
         /\ configuration.committed.values[p].value # Nil =>
               configuration.committed.values[p].value \in STRING
   /\ configuration.applied.index \in Nat
   /\ configuration.applied.revision \in Nat
   /\ configuration.applied.target \in Nat
   /\ \A p \in DOMAIN configuration.applied.values :
         /\ configuration.applied.values[p].index \in Nat
         /\ configuration.applied.values[p].value # Nil =>
               configuration.applied.values[p].value \in STRING

LOCAL CurrState == [
   configuration |-> configuration,
   mastership    |-> mastership,
   conn          |-> conn,
   target        |-> target]

LOCAL SuccState ==
   <<>> @@
   (IF configuration' # configuration THEN [configuration |-> configuration'] ELSE <<>>) @@
   (IF mastership' # mastership THEN [mastership |-> mastership'] ELSE <<>>) @@
   (IF conn' # conn THEN [conn |-> conn'] ELSE <<>>) @@
   (IF target' # target THEN [target |-> target'] ELSE <<>>)

Test == INSTANCE Test WITH 
   File <- "Configuration.log"

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n) ==
   /\ \/ /\ configuration.state = Pending
         /\ configuration.term = mastership.term
         /\ mastership.master = n
         /\ configuration' = [configuration EXCEPT !.state = InProgress]
         /\ UNCHANGED <<target>>
      \/ /\ configuration.state = InProgress
         /\ configuration.term = mastership.term
         /\ mastership.master = n
         /\ conn[n].id = mastership.conn
         /\ conn[n].connected
         /\ target.running
         /\ target' = [target EXCEPT !.values = configuration.applied.values]
         /\ configuration' = [configuration EXCEPT !.state = Complete,
                                                   !.applied.target = target.id]
      \/ /\ configuration.term < mastership.term
         /\ configuration' = [configuration EXCEPT !.state = Pending,
                                                   !.term  = mastership.term]
         /\ UNCHANGED <<target>>
   /\ UNCHANGED <<mastership, conn>>

=============================================================================
