---- MODULE KafkaSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Nodes

VARIABLES
    ISR, ISR_rev, leader, rev,
    log, offset,
    local_ISR, local_ISR_rev, local_rev, local_leader,
    client_log

LogData == Seq(Nat)

UnchangedCore == UNCHANGED <<ISR, ISR_rev, leader, rev>>

UnchangedLog == UNCHANGED <<log, offset>>

UnchangedLocals == UNCHANGED <<local_ISR, local_ISR_rev, local_rev, local_leader>>

TypeOK ==
    /\ ISR \subseteq Nodes
    /\ ISR_rev \in Nat
    /\ leader \in Nodes
    /\ rev \in Nat
    /\ log \in [Nodes -> LogData]
    /\ offset \in [Nodes -> [Nodes -> Nat]]
    /\ local_ISR \in [Nodes -> SUBSET Nodes]
    /\ local_ISR_rev \in [Nodes -> Nat]
    /\ local_rev \in [Nodes -> Nat]
    /\ local_leader \in [Nodes -> Nodes]
    /\ client_log \in LogData

Init ==
    /\ ISR = Nodes
    /\ ISR_rev = 1
    /\ leader \in Nodes
    /\ rev = 1
    /\ log = [n \in Nodes |-> <<>>]
    /\ offset = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ local_ISR = [n \in Nodes |-> Nodes]
    /\ local_ISR_rev = [n \in Nodes |-> 1]
    /\ local_rev = [n \in Nodes |-> 1]
    /\ local_leader = [n \in Nodes |-> leader]
    /\ client_log = <<>>

ZeroOffset == [n \in Nodes |-> 0]

AppendLog(n) ==
    /\ local_leader[n] = n
    /\ log' = [log EXCEPT ![n] = Append(@, local_rev[n])]
    /\ offset' = [offset EXCEPT ![n] = [@ EXCEPT ![n] = @ + 1]]
    /\ UnchangedCore
    /\ UnchangedLocals
    /\ UNCHANGED client_log

UpdateISR(n) ==
    /\ local_leader[n] = n
    /\ rev = local_rev[n]
    /\ \E m \in ISR\{n}: ISR' = ISR \ {m}
    /\ ISR_rev' = rev
    /\ UNCHANGED <<leader, rev>>
    /\ UnchangedLog
    /\ UnchangedLocals
    /\ UNCHANGED client_log

UpdateLeader ==
    /\ \E m \in ISR\{leader}: leader' = m
    /\ rev' = rev + 1
    /\ UNCHANGED <<ISR, ISR_rev>>
    /\ UnchangedLog
    /\ UnchangedLocals
    /\ UNCHANGED client_log

ObserveLeader(n) ==
    /\ local_rev[n] /= rev
    /\ local_leader' = [local_leader EXCEPT ![n] = leader]
    /\ local_rev' = [local_rev EXCEPT ![n] = rev]
    /\ IF leader = n
        THEN /\ offset' = [offset EXCEPT ![n] = [ZeroOffset EXCEPT ![n] = Len(log[n])]]
             /\ UNCHANGED log
        ELSE /\ UnchangedLog
    /\ UNCHANGED <<local_ISR, local_ISR_rev>>
    /\ UnchangedCore
    /\ UNCHANGED client_log

ObserveISR(n) ==
    /\ local_ISR[n] /= ISR
    /\ local_ISR' = [local_ISR EXCEPT ![n] = ISR]
    /\ local_ISR_rev' = [local_ISR_rev EXCEPT ![n] = ISR_rev]
    /\ IF ISR_rev > local_rev[n]
        THEN /\ offset' = [offset EXCEPT ![n] = [ZeroOffset EXCEPT ![n] = Len(log[n])]]
             /\ UNCHANGED log
        ELSE UnchangedLog
    /\ UNCHANGED <<local_leader, local_rev>>
    /\ UnchangedCore
    /\ UNCHANGED client_log

ReplicateLog(n, m) ==
    /\ local_leader[n] = n
    /\ n /= m
    /\ local_rev[n] >= local_rev[m]
    /\ log' = [log EXCEPT ![m] = log[n]]
    /\ offset' = [offset EXCEPT ![n] = [@ EXCEPT ![m] = Len(log[n])]]
    /\ local_rev' = [local_rev EXCEPT ![m] = local_rev[n]]
    /\ local_leader' = [local_leader EXCEPT ![m] = local_leader[n]]
    /\ UnchangedCore
    /\ UNCHANGED <<local_ISR, local_ISR_rev>>
    /\ UNCHANGED client_log

Slice(seq, n) ==
    [i \in 1..n |-> seq[i]]

NextLogElem(n) ==
    log[n][Len(client_log) + 1]

LastElem(seq) ==
    seq[Len(seq)]

ClientCanRecv(n) ==
    /\ local_leader[n] = n
    /\ n \in local_ISR[n]
    /\ \A m \in local_ISR[n]: Len(client_log) < offset[n][m]

ClientRecv(n) ==
    /\ ClientCanRecv(n)
    /\ client_log' = Append(client_log, NextLogElem(n))
    /\ UnchangedCore
    /\ UnchangedLog
    /\ UnchangedLocals

Next ==
    \/ UpdateLeader
    \/ \E n \in Nodes:
        \/ AppendLog(n)
        \/ UpdateISR(n)
        \/ ObserveLeader(n)
        \/ ObserveISR(n)
        \/ \E m \in Nodes: ReplicateLog(n, m)
        \/ ClientRecv(n)

Constraints ==
    /\ \A n \in Nodes: Len(log[n]) < 4
    /\ rev < 4

Inv ==
    /\ ISR /= {}
    /\ \A n \in ISR:
        /\ Len(log[n]) >= Len(client_log)
        /\ client_log = Slice(log[n], Len(client_log))
    \* /\ ~(client_log = <<1, 2, 2>> /\ Cardinality(ISR) = 2)
    \* /\ \A n \in Nodes: ClientCanRecv(n) =>
    \*     client_log = Slice(log[n], Len(client_log))
    \* /\ \A n \in Nodes: ClientCanRecv(n) => local_ISR[n] = Nodes
    \* /\ \A n \in Nodes: local_rev[n] < 3
    \* /\ \A n1, n2 \in Nodes:
    \*     n1 /= n2 /\ Len(log[n1]) > 2 => log[n1] /= log[n2]


Perms == Permutations(Nodes)

====