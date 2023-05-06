---- MODULE MC ----
EXTENDS Config, TLC

const_Path ==
    {"path1"}

const_Value ==
    {"value1", "value2"}

const_Node == 
   {"node1"}

const_LogEnabled == TRUE

const_NumProposals == 3

const_None == "<none>"

const_Change == "Change"

const_Rollback == "Rollback"

const_Commit == "Commit"

const_Apply == "Apply"

const_Pending == "Pending"

const_InProgress == "InProgress"

const_Complete == "Complete"

const_Aborted == "Aborted"

const_Failed == "Failed"

(*
constraint_mastership == 
   mastership.term <= 2
*)

constraint_mastership == 
   CASE mastership.term < 2 -> TRUE
     [] mastership.term = 2 -> mastership.master # None
     [] OTHER -> FALSE

(*
constraint_conn == 
   \A n \in DOMAIN conn : conn[n].id <= 2

*)

constraint_conn == 
   \A n \in DOMAIN conn : 
      CASE conn[n].id < 2 -> TRUE
        [] conn[n].id = 2 -> conn[n].connected
        [] OTHER -> FALSE

(*
constraint_target == 
   target.id <= 2

*)

constraint_target == 
   CASE target.id < 2 -> TRUE
     [] target.id = 2 -> target.running
     [] OTHER -> FALSE

=============================================================================
\* Modification History
\* Created Fri Apr 21 19:16:11 PDT 2023 by jhalterm
