----------------------------- MODULE Northbound -----------------------------

EXTENDS Proposal

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT Changes

\* Add change 'c' to the proposal log 
Change(c) ==
   /\ proposal' = Append(proposal, [type     |-> ProposalChange,
                                    change   |-> [values |-> [
                                       p \in DOMAIN c |-> [value |-> c[p]]]],
                                    rollback |-> [index  |-> 0],
                                    phase    |-> ProposalCommit,
                                    state    |-> ProposalInProgress])
   /\ UNCHANGED <<configuration, mastership, node, target>>

\* Add a rollback of proposal 'i' to the proposal log
Rollback(i) ==
   /\ proposal' = Append(proposal, [type     |-> ProposalRollback,
                                    change   |-> [index |-> 0],
                                    rollback |-> [index |-> i],
                                    phase    |-> ProposalCommit,
                                    state    |-> ProposalInProgress])
   /\ UNCHANGED <<configuration, mastership, node, target>>

----

(*
Formal specification, constraints, and theorems.
*)

InitNorthbound == TRUE

NextNorthbound ==
   \/ \E c \in Changes :
         Change(c)
   \/ \E i \in DOMAIN proposal :
         Rollback(i)

----

ASSUME \A c \in Changes :
          /\ Cardinality(DOMAIN c) > 0
          /\ \A p \in DOMAIN c : c[p] \in STRING
                

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 16:42:15 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:10:06 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:08:25 PST 2022 by jordanhalterman
