----------------------------- MODULE l2plot -----------------------------

(* EXAMPLE

TMId ->
{300}

RMId ->
{100, 200}

Key ->
{1, 2}

InvalidId ->
0

TxnId ->
{1000, 2000, 3000}

ALLTxns ->
{[txnId |-> 1000,
  tmId |-> 300,
  access |-> {[op |-> "read", siteId |-> 200, key |-> 1],
              [op |-> "write", siteId |-> 100, key |-> 1]}],
 [txnId |-> 2000,
  tmId |-> 300,
  access |-> {[op |-> "read", siteId |-> 200, key |-> 1],
              [op |-> "read", siteId |-> 100, key |-> 1]}],
  [txnId |-> 3000,
  tmId |-> 300,
  access |-> {[op |-> "write", siteId |-> 200, key |-> 1]}]
}

*)

EXTENDS Bags, FiniteSets, Integers, Naturals, Sequences, TLC

CONSTANTS    AllTxns            \* transaction structure
CONSTANTS    InvalidId          \* an invalid id
CONSTANTS    Key                \* keys on each resrc manager site
CONSTANTS    RMId               \* resource manager id
CONSTANTS    TMId               \* transaction manager id
CONSTANTS    TxnId              \* transation id set


VARIABLE rm
VARIABLE tm
VARIABLE data
VARIABLE locks
VARIABLE messages
VARIABLE txns
VARIABLE history

SiteId == RMId \union TMId

variables == <<data, history, locks, messages, rm, tm, txns>>

ReadOperation == [
    op : "read",
    rmId : RMId,
    key : Key
]

WriteOperation == [
    op : "read",
    rmId : RMId,
    key : Key
]

TMState == {
    "initial",
    "working",
    "collecting",
    "committed",
    "aborted",
    "finished"
}

TState == {
    "initial",
    "working",
    "committed",
    "aborted"
}

RMState == {
    "initial",
    "working",
    "prepared",
    "to abort", \* the transaction will be aborted for some reason...
    "committed",
    "aborted"
}

LockState == {
    "lock",
    "unlock"
}

Command == {
    \* TM --> RM
    "begin",
    "read",
    "commit",
    "prepare",
    "try commit",
    "release",           \* TM tell RM, lock can be released

    \* RM --> TM
    "vote no",
    "vote yes",
    "aborted",           \* aborted ack
    "committed"          \* committed ack
}


TxnOp == {
    "begin",
    "read",
    "write",
    "abort",
    "commit"
}

TxnEventOp == [
    seq : Nat,
    txnId : TxnId,
    op : TxnOp,
    siteId : SiteId,
    key : Key \cup {InvalidId}
]

Message == [
    src : SiteId,       \* the site who send the message
    dest : SiteId,      \* which site the message send to
    cmd : Command,      \* message cmd
    txnId : TxnId       \* transaction id
]

MessageInit(src, dest, cmd, txnId)  ==
    [
        src |-> src,
        dest |-> dest,
        cmd |-> cmd,
        txnId |-> txnId
    ]

ResourceManager == [
    txnState : RMState,
    lockState : LockState,
    readSet : SUBSET Key,               \* read key set
    writeSet : SUBSET Key,              \* write key set
    depOut : SUBSET TxnId,              \* out dependency
    depIn : SUBSET TxnId                \* in dependency
]

TransactionManager == [
    txnState : TMState,       \* the transaction state
    rmIdSet : SUBSET RMId
]

Tuple == [
    txnId : TxnId \union {InvalidId}   \* who writes this tuple
]

Lock == [
    txnId : TxnId,
    rmId : RMId,
    key : Key
]

ResourceManagerInit(txnState) ==
    [
        txnState |-> txnState,
        lockState |-> "lock",
        readSet |-> {},
        writeSet |-> {},
        depOut |-> {},
        depIn |-> {}
    ]

TransactionManagerInit(txnState) ==
    [
        txnState |-> txnState,
        rmIdSet |-> {}
    ]

TypeInv ==
    /\ rm \in [RMId -> [TxnId -> ResourceManager]]
    /\ tm \in [TMId -> [TxnId -> TransactionManager]]
    /\ data \in [RMId -> [Key -> Tuple]]
    /\ locks \in Lock
    /\ messages \in Message
    /\ txns = [id \in TxnId |-> BOOLEAN]
    /\ history \in TxnEventOp

Init ==
    /\ tm = [t \in TMId |-> [txn \in TxnId |-> TransactionManagerInit("initial")]]
    /\ rm = [r \in RMId |-> [txn \in TxnId |-> ResourceManagerInit("initial")]]
    /\ data = [id \in RMId |-> [ key \in Key |-> InvalidId ]]
    /\ locks = {}
    /\ messages = {}
    /\ txns = [id \in TxnId |-> FALSE]
    /\ history = {}

-----------------------------------------------------------------------------------------

PrintIf(out, val, pred) ==
    IF pred THEN
        Print(<<out, val>>, TRUE)
    ELSE TRUE

Ascii(char) == \* TODO... some errors ?
     96 + CHOOSE i \in 1 .. 62 :
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"[i] = char

Less(s1, s2) == \* TODO ..., compare a string ...
    LET l1 == Len(s1)
        l2 == Len(s2)
        lm == IF l1 <= l2 THEN l1 ELSE l2
    IN
    \/ \E n \in 1..lm:
        /\ Ascii(s1[n]) < Ascii(s2[n])
        /\ \/ \E i \in 1..n - 1:
                Ascii(s1[i]) = Ascii(s2[i])
           \/ n = 1
    \/ /\ \A i \in 1..lm:
            Ascii(s1[i]) = Ascii(s2[i])
       /\ l1 < l2

---------------------------------------------
\* work on RM

RMBegin(txnId, rmId, tmId) ==
    /\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "begin"
                     /\ msg.txnId = txnId
    /\ rm[rmId][txnId].txnState = "initial"
    /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "working"]
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "begin",
                        siteId |-> rmId,
                        key |-> InvalidId]}
    /\ UNCHANGED <<data, locks, messages, tm, txns>>

DeadlockPrevent(txnId, rmId, key) ==
    /\ ~ \E lock \in locks:
        /\ lock.txnId = txnId
        /\ lock.rmId >= rmId
        /\ lock.key >= key

RMRead(txnId, rmId, key) ==
    LET in == data[rmId][key]
        rlock == [
                    txnId |-> txnId,
                    rmId |-> rmId,
                    key |-> key
                 ]
    IN
    /\ rm[rmId][txnId].txnState = "working"
    /\ rm[rmId][txnId].lockState = "lock"
    /\ DeadlockPrevent(txnId, rmId, key)
    /\ ~ \E l \in locks : /\ l.key = key
                          /\ l.rmId = rmId
                          /\ l.txnId # txnId
    /\ IF in = InvalidId THEN
        /\ rm' = [rm EXCEPT ![rmId][txnId].depIn = @ \union {in},
                            ![rmId][txnId].writeSet = @ \union {key} ]
       ELSE
        /\ rm' = [rm EXCEPT ![rmId][txnId].depIn = @ \union {in},
                            ![rmId][in].depOut = @ \union {txnId},
                            ![rmId][txnId].writeSet = @ \union {key} ]
    /\ locks' = locks \union {rlock}
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "read",
                        siteId |-> rmId,
                        key |-> key]}
    /\ UNCHANGED <<data, messages, tm, txns>>

RMWrite(txnId, rmId, key) ==
    LET in == data[rmId][key]
        wlock == [
                    txnId |-> txnId,
                    rmId |-> rmId,
                    key |-> key
                 ]
    IN
    /\ rm[rmId][txnId].txnState = "working"
    /\ rm[rmId][txnId].lockState = "lock"
    /\ DeadlockPrevent(txnId, rmId, key)
    /\ ~ \E l \in locks : /\ l.key = key
                          /\ l.rmId = rmId
                          /\ l.txnId # txnId
    /\ IF in = InvalidId THEN
        /\ rm' = [rm EXCEPT ![rmId][txnId].depIn = @ \union {in},
                            ![rmId][txnId].writeSet = @ \union {key} ]
       ELSE
        /\ rm' = [rm EXCEPT ![rmId][txnId].depIn = @ \union {in},
                            ![rmId][in].depOut = @ \union {txnId},
                            ![rmId][txnId].writeSet = @ \union {key} ]
    /\ data' = [data EXCEPT ![rmId][key] = txnId]
    /\ locks' = locks \union {wlock}
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "write",
                        siteId |-> rmId,
                        key |-> key]}
    /\ UNCHANGED <<messages, tm, txns>>

RMPrepare(txnId, rmId, tmId) ==
    /\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "prepare"
                     /\ msg.txnId = txnId
    /\ \/ ( /\ rm[rmId][txnId].txnState = "working"
            /\ ~ \E txn \in rm[rmId][txnId].depIn :
                        /\ txn # InvalidId
                        /\ rm[rmId][txn].txnState # "committed"
            /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "prepared"]
            /\ messages' = messages \cup
                        {[
                            src |-> rmId,
                            dest |-> tmId,
                            cmd |-> "vote yes",
                            txnId |-> txnId
                        ]}
          )
       \/ ( /\ ( \/ rm[rmId][txnId].txnState = "to abort"
                 \/ \E txn \in rm[rmId][txnId].depIn :
                        /\ txn # InvalidId
                        /\ rm[rmId][txn].txnState \in { "aborted", "to abort"}
               )
            /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "to abort"]
            /\ messages' = messages \cup
                        {[
                            src |-> rmId,
                            dest |-> tmId,
                            cmd |-> "vote no",
                            txnId |-> txnId
                        ]}
           )
    /\ UNCHANGED <<data, history, locks, tm, txns>>

RMAbort(txnId, rmId, tmId) ==
    LET writeSet == rm[rmId][txnId].writeSet
        toRelease == { l \in locks : /\ l.txnId = txnId
                                     /\ l.rmId = rmId
                     }
    IN
    /\ \* a distributed transaction
       \/ /\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "abort"
                     /\ msg.txnId = txnId
          /\ rm[rmId][txnId].txnState \in {"prepared", "to abort"}
       \* or a local transaction
       \/ /\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "try commit"
                     /\ msg.txnId = txnId
          /\ rm[rmId][txnId].txnState = "to abort"
    /\ \A t \in rm[rmId][txnId].depOut:
          rm[rmId][txnId].txnState = "aborted"
    /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "aborted",
                        ![rmId][txnId].depIn = {},
                        ![rmId][txnId].depOut = {} ]
    /\ data' = [data EXCEPT ![rmId] =
                    [key \in Key |-> IF key \in writeSet
                                     THEN InvalidId
                                     ELSE data[rmId][key]]]
    /\ locks' = locks \ toRelease
    /\ messages' = messages \cup
                {[
                    src |-> rmId,
                    dest |-> tmId,
                    cmd |-> "aborted",
                    txnId |-> txnId
                ]}
    /\ history' = history \union {[
                seq |-> Cardinality(history),
                txnId |-> txnId,
                op |-> "abort",
                siteId |-> rmId,
                key |-> InvalidId]}
    /\ UNCHANGED <<tm, txns>>

RMCommit(txnId, rmId, tmId) ==
    LET writeSet == rm[rmId][txnId].writeSet
        toRelease == { l \in locks : /\ l.txnId = txnId
                                     /\ l.rmId = rmId
                     }
    IN
    /\ \* a global transaction
       \/ (/\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "commit"
                     /\ msg.txnId = txnId
           /\ rm[rmId][txnId].txnState = "prepared")
       \* or a local transaction
       \/ (/\ \E msg \in messages :
                     /\ msg.src = tmId
                     /\ msg.dest = rmId
                     /\ msg.cmd = "try commit"
                     /\ msg.txnId = txnId
          /\ rm[rmId][txnId].txnState = "working")
    /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "committed",
                        ![rmId][txnId].depIn = {},
                        ![rmId][txnId].depOut = {}
                        ]
    /\ ~ \E txn \in rm[rmId][txnId].depIn :
                /\ txn # InvalidId
                /\ rm[rmId][txn].txnState # "committed"
    /\ data' = [data EXCEPT ![rmId] =
                    [key \in Key |-> IF key \in writeSet
                                     THEN InvalidId
                                     ELSE data[rmId][key]]]
    /\ locks' = locks \ toRelease
    /\ messages' = messages \cup
                {[
                    src |-> rmId,
                    dest |-> tmId,
                    cmd |-> "committed",
                    txnId |-> txnId
                ]}
    /\ history' = history \union {[
                seq |-> Cardinality(history),
                txnId |-> txnId,
                op |-> "commit",
                siteId |-> rmId,
                key |-> InvalidId]}
    /\ UNCHANGED <<tm, txns>>

RMRelease(txnId, rmId, tmId) ==
    LET toRelease == { l \in locks : /\ l.txnId = txnId
                                     /\ l.rmId = rmId
                     }
    IN
    /\ rm[rmId][txnId].lockState # "unlock"
    /\ \E msg \in messages :
            /\ msg.src = tmId
            /\ msg.dest = rmId
            /\ msg.cmd = "release"
            /\ msg.txnId = txnId
    /\ rm' = [rm EXCEPT ![rmId][txnId].lockState = "unlock" ]
    /\ locks' = locks \ toRelease
    /\ UNCHANGED <<history, tm, data, messages, tm, txns>>

RMChooseToAbort(txnId, rmId, tmId) ==
    /\ rm[rmId][txnId].txnState = "working"
    /\ rm' = [rm EXCEPT ![rmId][txnId].txnState = "to abort"]
    /\ UNCHANGED <<data,  history, locks, messages, tm, txns>>

---------------------------------------------------------
\* work on TM

TMBegin(txnId, tmId, rmIdSet) ==
    /\ tm[tmId][txnId].txnState = "initial"
    /\ ~ txns[txnId]
    /\ Cardinality(rmIdSet) > 0
    /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "working",
                        ![tmId][txnId].rmIdSet = rmIdSet]
    /\ txns' = [txns EXCEPT ![txnId] = TRUE]
    /\ LET msgs == {msg \in Message :
                        /\ msg.src = tmId
                        /\ msg.dest \in rmIdSet
                        /\ msg.cmd = "begin"
                        /\ msg.txnId = txnId
                   }
       IN messages' = messages \cup msgs
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "begin",
                        siteId |-> tmId,
                        key |-> InvalidId]}
    /\ UNCHANGED <<data, locks, rm>>

AccessDone(txnId) ==
    LET txn == CHOOSE t \in AllTxns : t.txnId = txnId
        access == txn.access
    IN
    \A a \in access:
        \E e \in history:
            /\ e.txnId = txnId
            /\ e.key = a.key
            /\ e.siteId = a.siteId
            /\ e.op = a.op

TMPrepare(txnId, tmId) ==
    LET rmIdSet == tm[tmId][txnId].rmIdSet
    IN
    /\ tm[tmId][txnId].txnState = "working"
    /\ AccessDone(txnId)
    /\ IF Cardinality(rmIdSet) > 1 THEN
           LET msgs == {msg \in Message :
                            /\ msg.src = tmId
                            /\ msg.dest \in rmIdSet
                            /\ msg.cmd = "prepare"
                            /\ msg.txnId = txnId
                       }
           IN messages' = messages \cup msgs
       ELSE
           /\ Cardinality(rmIdSet) = 1
           /\ LET msgs == {[
                            src |-> tmId,
                            dest |-> CHOOSE id \in rmIdSet : TRUE,
                            cmd |-> "try commit",
                            txnId |-> txnId
                       ]}
              IN messages' = messages \cup msgs
    /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "collecting"]
    /\ UNCHANGED <<data, history, locks, rm, txns>>

TMCollectingPrepared(txnId, tmId) ==
    LET rmIdSet == tm[tmId][txnId].rmIdSet
    IN
    /\ tm[tmId][txnId].txnState = "collecting"
    /\ Cardinality(rmIdSet) > 1
    /\  \/ /\ \A rmId \in rmIdSet:
              /\ \E msg \in messages :
                         /\ msg.src = rmId
                         /\ msg.dest = tmId
                         /\ msg.cmd = "vote yes"
                         /\ msg.txnId = txnId
           /\ LET msgs == {msg \in Message :
                            /\ msg.src = tmId
                            /\ msg.dest \in rmIdSet
                            /\ msg.cmd = "commit"
                            /\ msg.txnId = txnId
                       }
              IN messages' = messages \cup msgs
           /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "committed"]
           /\ UNCHANGED <<data, history, locks, rm, txns>>
        \/ /\ \E rmId \in rmIdSet:
              /\ \E msg \in messages :
                         /\ msg.src = rmId
                         /\ msg.dest = tmId
                         /\ msg.cmd = "vote no"
                         /\ msg.txnId = txnId
           /\ LET msgs == {msg \in Message :
                            /\ msg.src = tmId
                            /\ msg.dest \in rmIdSet
                            /\ msg.cmd = "abort"
                            /\ msg.txnId = txnId
                       }
              IN messages' = messages \cup msgs
           /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "aborted"]
           /\ UNCHANGED <<data, history, locks, rm, txns>>

TMCollectingCommittedACK(txnId, tmId) ==
    LET rmIdSet == tm[tmId][txnId].rmIdSet
    IN
    /\ \A rmId \in rmIdSet:
          /\ \E msg \in messages :
                     /\ msg.src = rmId
                     /\ msg.dest = tmId
                     /\ msg.cmd = "committed"
                     /\ msg.txnId = txnId
    /\ \/ (/\ tm[tmId][txnId].txnState = "committed"
           /\ Cardinality(rmIdSet) > 1
          )
       \/ (/\ tm[tmId][txnId].txnState = "collecting"
           /\ Cardinality(rmIdSet) = 1
          )
    /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "finished"]
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "commit",
                        siteId |-> tmId,
                        key |-> InvalidId]}
    /\ UNCHANGED <<data, locks, messages, rm, txns>>

TMCollectingAbortedACK(txnId, tmId) ==
    LET rmIdSet == tm[tmId][txnId].rmIdSet
    IN
    /\ \A rmId \in rmIdSet:
          /\ \E msg \in messages :
                     /\ msg.src = rmId
                     /\ msg.dest = tmId
                     /\ msg.cmd = "aborted"
                     /\ msg.txnId = txnId
    /\ \/ (/\ tm[tmId][txnId].txnState = "aborted"
           /\ Cardinality(rmIdSet) > 1
          )
       \/ (/\ tm[tmId][txnId].txnState = "collecting"
           /\ Cardinality(rmIdSet) = 1
          )
    /\ tm' = [tm EXCEPT ![tmId][txnId].txnState = "finished"]
    /\ history' = history \union {[
                        seq |-> Cardinality(history),
                        txnId |-> txnId,
                        op |-> "abort",
                        siteId |-> tmId,
                        key |-> InvalidId]}
    /\ UNCHANGED <<data, locks, messages, rm, txns>>


Next == \E txn \in AllTxns:
            LET txnId == txn.txnId
                tmId == txn.tmId
                access == txn.access
                rmIdSet == {rmId \in RMId :
                                \E acc \in access :
                                    acc.siteId = rmId}
            IN  \/ TMBegin(txnId, tmId, rmIdSet)
                \/ TMPrepare(txnId, tmId)
                \/ TMCollectingPrepared(txnId, tmId)
                \/ TMCollectingCommittedACK(txnId, tmId)
                \/ TMCollectingAbortedACK(txnId, tmId)
                \/ \E acc \in access:
                    LET rmId == acc.siteId
                        key == acc.key
                        op == acc.op
                    IN  \/ RMBegin(txnId, rmId, tmId)
                        \/ RMPrepare(txnId, rmId, tmId)
                        \/ RMCommit(txnId, rmId, tmId)
                        \/ RMAbort(txnId, rmId, tmId)
                        \/ RMChooseToAbort(txnId, rmId, tmId)
                        \/ RMRelease(txnId, rmId, tmId)
                        \/ IF op = "read" THEN
                             \/ RMRead(txnId, rmId, key)
                             \/ UNCHANGED <<variables>>
                           ELSE
                             \/ RMWrite(txnId, rmId, key)
                             \/ UNCHANGED <<variables>>

FinalState ==
    \A txnId \in TxnId:
        \A tmId \in TMId:
            tm[tmId][txnId].txnState = "finished"

Atomicity ==
    \A txnId \in TxnId:
        ~ \E r1 \in RMId, r2 \in RMId:
             \/ /\ r1 # r2
                /\ rm[r1][txnId].txnState = "aborted"
                /\ rm[r2][txnId].txnState = "committed"
             \/ /\ r1 # r2
                /\ rm[r1][txnId].txnState = "committed"
                /\ rm[r2][txnId].txnState = "aborted"

Conflict(o1, o2) ==
    LET op1 == o1.op
        op2 == o2.op
        rm1 == o1.siteId
        rm2 == o2.siteId
        key1 == o1.key
        key2 == o1.key
    IN
    /\ key1 = key2
    /\ rm1 = rm2
    /\ (\/ /\ op1 = "read"
           /\ op2 = "write"
        \/ /\ op1 = "write"
           /\ op2 = "read"
        \/ /\ op1 = "write"
           /\ op2 = "write")

Serializable ==
    ~ \E txn1 \in TxnId, txn2 \in TxnId:
        /\ txn1 # txn2
        /\ \E op1 \in history, op2 \in history:
            /\ op1.txnId = txn1
            /\ op2.txnId = txn2
            /\ Conflict(op1, op2)
            /\ op1.seq < op2.seq
        /\ \E op1 \in history, op2 \in history:
            /\ op1.txnId = txn1
            /\ op2.txnId = txn2
            /\ Conflict(op1, op2)
            /\ op1.seq > op2.seq

OrderedTermination ==
    \A op1 \in history, op2 \in history:
        IF (/\ op1.txnId # op2.txnId
            /\ op1.seq < op2.seq
            /\ op1.siteId = op2.siteId
            /\ op1.key = op2.key
            /\ op1.op = "write"
            /\ (op2.op = "write" \/ op2.op = "read"))
            /\ (~\E op \in history:
                /\ op.op = "write"
                /\ op.key = op1.key
                /\ op1.seq < op.seq
                /\ op.seq < op2.seq)
        THEN
            CASE (/\ rm[op1.siteId][op1.txnId].txnState = "aborted"
                  /\ op1.op = "write"
                  /\ op2.op = "write")
             -> (~ \E c1 \in history, c2 \in history:
                       /\ c1.seq < c2.seq
                       /\ c1.txnId = op1.txnId
                       /\ c2.txnId = op2.txnId
                       /\ c1.siteId = op1.siteId
                       /\ c2.siteId = op2.siteId
                       /\ c1.op = "abort"
                       /\ c2.op = "abort")
             [] (/\ rm[op2.siteId][op2.txnId].txnState = "committed"
                 /\ op1.op = "write"
                 /\ (op2.op = "write" \/ op2.op = "read"))
             -> (~ \E c1 \in history, c2 \in history:
                           /\ c1.seq > c2.seq
                           /\ c1.txnId = op1.txnId
                           /\ c2.txnId = op2.txnId
                           /\ c1.siteId = op1.siteId
                           /\ c2.siteId = op2.siteId
                           /\ c1.op = "commit"
                           /\ c2.op = "commit")
            [] OTHER -> TRUE
        ELSE TRUE

SOT == OrderedTermination /\ Serializable

Spec == Init /\ [][Next]_variables


=============================================================================
