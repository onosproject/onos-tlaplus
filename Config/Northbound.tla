----------------------------- MODULE Northbound -----------------------------

EXTENDS Proposal

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

LOCAL INSTANCE TLC

----

CONSTANT Changes

\* Add change 'c' to the proposal log 
Change(i) ==
   /\ proposal[i].phase = Nil
   /\ i-1 \in DOMAIN proposal => proposal[i-1].phase # Nil
   /\ \E c \in Changes :
         /\ proposal' = [proposal EXCEPT ![i] = [phase    |-> ProposalChange,
                                                 change   |-> [
                                                    values |-> [p \in DOMAIN c |-> [value |-> c[p]]],
                                                    commit   |-> ProposalPending,
                                                    apply    |-> ProposalPending],
                                                 rollback |-> [
                                                    index  |-> 0,
                                                    values |-> [p \in {} |-> [value |-> Nil]],
                                                    commit |-> Nil,
                                                    apply  |-> Nil]]]
   /\ UNCHANGED <<configuration, mastership, node, target>>

\* Add a rollback of proposal 'i' to the proposal log
Rollback(i) ==
   /\ proposal[i].phase = ProposalChange
   /\ proposal' = [proposal EXCEPT ![i].phase = ProposalRollback,
                                   ![i].rollback.commit = ProposalPending,
                                   ![i].rollback.apply  = ProposalPending]
   /\ UNCHANGED <<configuration, mastership, node, target>>

----

(*
Formal specification, constraints, and theorems.
*)

InitNorthbound == TRUE

NextNorthbound ==
   \E i \in 1..NumProposals : 
      \/ Change(i)
      \/ Rollback(i)

----

ASSUME \A c \in Changes :
          /\ Cardinality(DOMAIN c) > 0
          /\ \A p \in DOMAIN c : c[p] \in STRING
                

=============================================================================
\* Modification History
\* Last modified Fri Apr 21 16:42:15 PDT 2023 by jhalterm
\* Last modified Sun Feb 20 10:10:06 PST 2022 by jordanhalterman
\* Created Sun Feb 20 03:08:25 PST 2022 by jordanhalterman
