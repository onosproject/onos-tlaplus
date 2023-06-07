------------------------------- MODULE Transaction -------------------------------

INSTANCE Naturals

INSTANCE FiniteSets

INSTANCE Sequences

INSTANCE TLC

----

\* An empty constant
CONSTANT Nil

\* Transaction phase constants
CONSTANTS
   Change,
   Rollback

\* Proposal phase constants
CONSTANTS 
   Commit,
   Apply

\* Status constants
CONSTANTS
   Pending,
   Complete,
   Aborted,
   Failed

Status == {Pending, Complete, Aborted, Failed}

\* The set of all nodes
CONSTANT Node

\* The set of possible paths and values
CONSTANT Path, Value

Empty == [p \in {} |-> Nil]

----

\* Variables defined by other modules.
VARIABLES 
   proposals,
   configuration

\* A transaction log. Transactions may either request a set
\* of changes to a set of targets or rollback a prior change.
VARIABLE transactions

TypeOK == 
   \A i \in DOMAIN transactions :
      /\ transactions[i].index \in Nat
      /\ transactions[i].phase \in {Change, Rollback}
      /\ transactions[i].change \in Nat
      /\ transactions[i].rollback \in Nat
      /\ \A p \in DOMAIN transactions[i].values :
            transactions[i].values[p] # Nil => transactions[i].values[p] \in STRING

LOCAL State == [
   transactions  |-> transactions,
   proposals     |-> proposals,
   configuration |-> configuration]

LOCAL Transitions ==
   LET
      txIndexes   == {i \in DOMAIN transactions' : 
                           i \in DOMAIN transactions => transactions'[i] # transactions[i]}
      propIndexes == {i \in DOMAIN proposals' : 
                           i \in DOMAIN proposals => proposals'[i] # proposals[i]}
   IN [transactions |-> [i \in txIndexes   |-> transactions'[i]],
       proposals    |-> [i \in propIndexes |-> proposals'[i]]]

Test == INSTANCE Test WITH 
   File <- "Transaction.log"

----

\* Add a change for revision 'i' to the transaction log
AppendChange(i) ==
   /\ Len(transactions) = i-1
   /\ \E p \in Path, v \in Value :
         /\ transactions' = Append(transactions, [
                              index    |-> Len(transactions)+1,
                              phase    |-> Change,
                              values   |-> (p :> v),
                              change   |-> 0,
                              rollback |-> 0])
   /\ UNCHANGED <<proposals, configuration>>

\* Add a rollback of revision 'i' to the transaction log
RollbackChange(i) ==
   /\ i \in DOMAIN transactions 
   /\ transactions[i].phase = Change
   /\ transactions' = [transactions EXCEPT ![i].phase = Rollback]
   /\ UNCHANGED <<proposals, configuration>>

----

ReconcileChange(n, i) ==
   /\ transactions[i].phase = Change
   /\ transactions[i].change = 0
   /\ \/ /\ Len(proposals) = 0
         /\ i = 1
      \/ /\ Len(proposals) > 0
         /\ proposals[Len(proposals)].revision = i-1
         /\ proposals[Len(proposals)].commit = Complete
   /\ LET proposal == [
         type |-> Change,
         index |-> Len(proposals)+1,
         revision |-> i,
         change   |-> [
            index    |-> Len(proposals)+1,
            revision |-> i,
            values   |-> transactions[i].values],
         rollback |-> [
            index    |-> IF Len(proposals) > 0 THEN proposals[Len(proposals)].change.index ELSE 0,
            revision |-> IF Len(proposals) > 0 THEN proposals[Len(proposals)].change.revision ELSE 0,
            values   |-> [
               p \in DOMAIN transactions[i].values |-> 
                  IF p \in DOMAIN configuration.committed.values THEN 
                     configuration.committed.values[p]
                  ELSE Nil]],
         commit   |-> Pending,
         apply    |-> Pending]
      IN
         /\ proposals' = Append(proposals, proposal)
         /\ transactions' = [transactions EXCEPT ![i].change = Len(proposals')]
   /\ UNCHANGED <<configuration>>

ReconcileRollback(n, i) ==
   /\ transactions[i].phase = Rollback
   /\ Len(proposals) > 0
   /\ LET lastProposal == proposals[Len(proposals)]
      IN /\ lastProposal.change.revision = i
         /\ lastProposal.commit = Complete
         /\ LET proposal == [
               type     |-> Rollback,
               index    |-> Len(proposals)+1,
               revision |-> lastProposal.revision,
               change   |-> [
                  index    |-> proposals[lastProposal.change.index].rollback.index,
                  revision |-> proposals[lastProposal.change.index].rollback.revision,
                  values   |-> proposals[lastProposal.change.index].rollback.values],
               rollback |-> [
                  index    |-> lastProposal.change.index,
                  revision |-> i,
                  values   |-> Empty],
               commit   |-> Pending,
               apply    |-> Pending]
            IN /\ proposals' = Append(proposals, proposal)
               /\ transactions' = [transactions EXCEPT ![i].rollback = Len(proposals')]
   /\ UNCHANGED <<configuration>>

ReconcileTransaction(n, i) ==
   /\ i \in DOMAIN transactions
   /\ \/ ReconcileChange(n, i)
      \/ ReconcileRollback(n, i)

=============================================================================
