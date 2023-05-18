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
   InProgress,
   Complete,
   Failed

State == 
   {InProgress,
    Complete,
    Failed}

----

\* A record of per-target configurations
VARIABLE configuration

\* A record of target states
VARIABLE target

\* A record of target masterships
VARIABLE mastership

Test == INSTANCE Test WITH 
   File      <- "Configuration.log",
   CurrState <- [
      configuration |-> configuration,
      mastership    |-> mastership,
      target        |-> target],
   SuccState <- [
      configuration |-> configuration',
      mastership    |-> mastership',
      target        |-> target']

----

(*
This section models the Configuration reconciler.
*)

ReconcileConfiguration(n) ==
   /\ \/ /\ \/ mastership.term > configuration.config.term
            \/ /\ mastership.term = configuration.config.term
               /\ mastership.master = Nil
         /\ configuration' = [configuration EXCEPT !.config.term = mastership.term,
                                                   !.state       = InProgress]                                          
         /\ UNCHANGED <<target>>
      \/ /\ configuration.state = InProgress
         /\ mastership.term = configuration.config.term
         /\ mastership.master = n
         /\ target' = configuration.target.values
         /\ configuration' = [configuration EXCEPT !.target.term = mastership.term,
                                                   !.state       = Complete]
   /\ UNCHANGED <<mastership>>

=============================================================================
