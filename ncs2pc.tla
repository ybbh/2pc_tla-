-------------------------------- MODULE ncs2pc --------------------------------
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)

EXTENDS Bags, TLC


CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  tmACK,         \* The set of RMs from which the TM has received $"ACK"$
                 \* messages.          
  msgs           
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)

Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
  (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
  (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
  (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  [type : {"Prepared", "ACK", "Commit", "Abort", "End"}, rm : RM, tm : RM]

TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "to abort", "aborted", "ended"}]
  /\ tmPrepared \in [RM -> SUBSET RM]
  /\ tmACK \in [RM -> SUBSET RM]
  \*/\ rmStatus \in [RM -> {"right", "error"}]
  \*/\ msgs \subseteq Message

TPInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmPrepared   = [rm \in RM |-> {}]
  /\ tmACK = [rm \in RM |-> {}]
  /\ msgs = {}
  \*/\ rmStatus = [rm \in RM |-> "right"]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm, tm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  LET msg == [type |-> "Prepared", rm |-> rm, tm |-> tm] IN
  /\ msg \in msgs
  /\ msgs' = msgs \ {msg}
  /\ tmPrepared' = [tmPrepared EXCEPT ![tm] = @ \cup {rm}]
  /\ UNCHANGED <<rmState, tmACK>>

TMRecovery(tm) == 
  (*************************************************************************)
  (* Transaction manager $tm$ crush recovery.                                       *)
  (*************************************************************************)
  /\ tmPrepared' = [tmPrepared EXCEPT ![tm] = {}]
  /\ tmACK' = [tmACK EXCEPT ![tm] = {}]
  /\ UNCHANGED <<rmState, msgs>>
  
TMRcvNo(rm, tm) ==
  (*************************************************************************)
  (* The TM receives a $"No"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  LET msg_to_remove == [type |-> "No", rm |-> rm, tm |-> tm] 
      msg_to_add == [type : {"Abort"}, rm : RM, tm : {tm}]
  IN
  /\ msg_to_remove \in msgs
  /\ rmState' = [rmState EXCEPT ![tm] = "aborted"]
  /\ msgs' = (msgs \ {msg_to_remove}) \cup msg_to_add
  /\ UNCHANGED <<tmPrepared, tmACK>>
  
TMCommit(tm) ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmPrepared[tm] = RM
  /\ LET msg == [type : {"Commit"}, rm : RM, tm : {tm}] IN
        msgs' = msgs \cup msg \*TODO
  /\ UNCHANGED <<rmState, tmPrepared, tmACK>>

TMPrepare(tm) ==
  (*************************************************************************)
  (* The TM prepare the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ LET msg == [type : {"Prepare"}, rm : RM, tm : {tm}] IN
        msgs' = msgs \cup msg
  /\ UNCHANGED <<rmState, tmPrepared, tmACK>>
  
TMRcvACK(rm, tm) ==
  (*************************************************************************)
  (* The TM receives a $"ACK"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  LET msg == [type |-> "ACK", rm |-> rm, tm |-> tm] IN
  /\ msg \in msgs
  /\ msgs' = msgs \ {msg}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMEnd(tm) ==
  (*************************************************************************)
  (* The TM send $"End"$ the transaction iff every RM has sent a $"ACK"$   *)
  (* commit message.                                                       *)
  (*************************************************************************)
  /\ tmACK[tm] = RM
  /\ LET msg == [type : {"End"}, rm : RM, tm : {tm}] IN
        msgs' = msgs \cup msg \*TODO
  /\ UNCHANGED <<rmState, tmPrepared, tmACK>>

TMAbort(tm) ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ rmState[tm] = "to abort"
  /\ rmState' = [rmState EXCEPT ![tm] = "aborted"]
  /\ LET msg == [type : {"Abort"}, rm : RM, tm : {tm}] IN
        msgs' = msgs \cup msg \*TODO
  /\ UNCHANGED <<tmPrepared, tmACK>>

RMRecovery(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ crush recovery.                                       *)
  (*************************************************************************)
  /\ CASE rmState[rm] = "prepared"
     -> /\ msgs' = msgs  \cup [type : {"Prepare"}, rm : RM, tm : {rm}]
        /\ UNCHANGED <<rmState>>
     [] rmState[rm] = "committed"
     -> /\ msgs' = msgs  \cup [type : {"Commit"}, rm : RM, tm : {rm}]
        /\ UNCHANGED <<rmState>>
     [] OTHER 
     -> /\ rmState' =  [rmState EXCEPT ![rm] = "aborted"]
        /\ UNCHANGED <<msgs>>
  /\ UNCHANGED <<tmPrepared, tmACK>>
  
RMRcvPrepare(rm, tm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  LET msg == [type |-> "Prepare", rm |-> rm , tm |-> tm] IN
  /\ msg \in msgs
  /\ IF rmState[rm] = "working" THEN
        rmState' = [rmState EXCEPT ![rm] = "prepared"]
     ELSE UNCHANGED rmState
  /\ IF rmState[rm] = "aborted" \/ rmState[rm] = "to abort" THEN
        msgs' = (msgs \ {msg}) \cup {[type |-> "No", rm |-> rm, tm |-> tm]}
     ELSE
        msgs' = (msgs \ {msg}) \cup {[type |-> "Prepared", rm |-> rm, tm |-> tm]}
  /\ UNCHANGED <<tmPrepared, tmACK>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "to abort"]
  /\ UNCHANGED <<tmPrepared, tmACK, msgs>>

RMRcvCommitMsg(rm, tm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  LET msg == [type |-> "Commit", rm |-> rm , tm |-> tm] IN
  /\ msg \in msgs
  /\ msgs' = (msgs \ {msg}) \cup {[type |-> "ACK", rm |-> rm , tm |-> tm]}
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmPrepared, tmACK>>

RMRcvAbortMsg(rm, tm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  LET msg == [type |-> "Abort", rm |-> rm , tm |-> tm] IN  
  /\ msg \in msgs
  /\ msgs' = msgs \ {msg}
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmPrepared, tmACK>>

RMRcvEndMsg(rm, tm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to end.                     *)
  (*************************************************************************)
  LET msg == [type |-> "End", rm |-> rm , tm |-> tm] IN
  /\ msg \in msgs
  /\ rmState[rm] = "committed"
  /\ msg' = msgs \ {msg}
  /\ rmState' = [rmState EXCEPT ![rm] = "ended"]
  /\ UNCHANGED <<tmPrepared, tmACK>>


TPNext ==
  \E tm \in RM:
      \/ TMCommit(tm)
      \/ TMPrepare(tm)
      \/ TMAbort(tm)
      \/ TMRecovery(tm)
      \/ RMRecovery(tm)
      \/ \E rm \in RM: 
           \/ TMRcvPrepared(rm, tm) 
           \/ TMRcvNo(rm, tm)
           \/ RMRcvPrepare(rm, tm) 
           \/ RMChooseToAbort(rm)
           \/ RMRcvCommitMsg(rm, tm) 
           \/ RMRcvAbortMsg(rm, tm)

(***************************************************************************)
(* We now assert invariance properties of the specification.               *)
(***************************************************************************)
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ (\/ rmState[rm2] = "committed"
                             \/ rmState[rm2] = "ended")
                             
(***************************************************************************)
(* The complete state of NPS2PC will be $ended$.                           *)
(***************************************************************************)
TCEnd ==
    \/ \A rm \in RM : /\ rmState[rm] = "aborted"
    \/ \A rm \in RM : /\ rmState[rm] = "ended"
-----------------------------------------------------------------------------
TPSpec == /\ TPInit 
          /\ [][TPNext]_<<rmState, tmPrepared, tmACK, msgs>>
          /\ \A rm \in RM: 
                WF_<<rmState, tmPrepared, tmACK, msgs>>(
                      \/ RMRecovery(rm)
                      \/ TMRecovery(rm))
                      
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

THEOREM TPSpec => []TPTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------


THEOREM TPSpec =>  TCConsistent

THEOREM TPSpec =>  <> TCEnd
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states, in a little over a    *)
(* minute on a 1 GHz PC.                                                   *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Fri May 03 22:01:46 CST 2019 by ybbh
\* Last modified Fri May 03 19:56:34 CST 2019 by ybbh
\* Last modified Mon Apr 22 20:51:41 CST 2019 by ybbh
\* Created Mon Mar 18 15:48:50 CST 2019 by ybbh
