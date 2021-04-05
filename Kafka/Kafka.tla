---- MODULE Kafka ----
EXTENDS TLC, Naturals, Integers, FiniteSets, Sequences

CONSTANTS Nodes
ASSUME Nodes /= {}

VARIABLES
    core, log, offset,
    local_ISR, local_leader, local_rev,
    effective_rev,
    client_log

LogData == Seq(Nat)

Core == [leader: Nodes, ISR: SUBSET Nodes]

NullOffset == [n \in Nodes |-> -1]

TypeOK ==
    /\ core \in Seq(Core)
    /\ local_ISR \in [Nodes -> SUBSET Nodes]
    /\ local_leader \in [Nodes -> Nodes]
    /\ local_rev \in [Nodes -> Nat]
    /\ effective_rev \in [Nodes -> Nat]
    /\ log \in [Nodes -> LogData]
    /\ offset \in [Nodes -> [Nodes -> Int]]
    /\ client_log \in LogData

Init ==
    /\ \E leader \in Nodes:
        /\ core = <<[leader |-> leader, ISR |-> Nodes]>>
        /\ local_ISR = [n \in Nodes |-> Nodes]
        /\ local_leader = [n \in Nodes |-> leader]
        /\ local_rev = [n \in Nodes |-> 1]
        /\ effective_rev = [n \in Nodes |-> 1]
    /\ log = [n \in Nodes |-> <<>>]
    /\ offset = [n \in Nodes |-> [NullOffset EXCEPT ![n] = 0]]
    /\ client_log = <<>>

UnchangedLocals == UNCHANGED <<local_ISR, local_leader, local_rev, effective_rev>>
UnchangedLog == UNCHANGED <<log, offset>>

AppendLog(n) ==
    /\ local_leader[n] = n
    /\ effective_rev[n] = local_rev[n]
    /\ log' = [log EXCEPT ![n] = Append(@, local_rev[n])]
    /\ offset' = [offset EXCEPT ![n] = [@ EXCEPT ![n] = @ + 1]]
    /\ UNCHANGED core
    /\ UNCHANGED client_log
    /\ UnchangedLocals

CurrentCore == core[Len(core)]

UpdateLeader ==
    /\ \E m \in (CurrentCore.ISR \ {CurrentCore.leader}):
        core' = Append(core, [leader |-> m, ISR |-> CurrentCore.ISR])
    /\ UnchangedLog
    /\ UnchangedLocals
    /\ UNCHANGED client_log

ShrinkISR(n) ==
    /\ local_leader[n] = n
    /\ Len(core) = local_rev[n]
    /\ \E m \in CurrentCore.ISR\{n}:
        core' = Append(core, [leader |-> CurrentCore.leader, ISR |-> CurrentCore.ISR \ {m}])
    /\ UnchangedLog
    /\ UnchangedLocals
    /\ UNCHANGED client_log

ExtendISR(n) ==
    /\ local_leader[n] = n
    /\ Len(core) = local_rev[n]
    /\ \E m \in Nodes \ CurrentCore.ISR:
        /\ \A k \in local_ISR[n]: offset[n][k] >= 0
        /\ \E k \in local_ISR[n]: offset[n][k] <= offset[n][m]
        /\ core' = Append(core, [leader |-> CurrentCore.leader, ISR |-> CurrentCore.ISR \union {m}])
        /\ local_ISR' = [local_ISR EXCEPT ![n] = local_ISR[n] \union {m}]
    /\ UnchangedLog
    /\ UNCHANGED <<local_rev, local_leader, effective_rev>>
    /\ UNCHANGED client_log

NextCore(n) == core[local_rev[n] + 1]

UpdateEffectiveRev(n) ==
    IF local_rev[n] = effective_rev[n]
        THEN effective_rev' = [effective_rev EXCEPT ![n] = @ + 1]
        ELSE UNCHANGED effective_rev

WatchCore(n) ==
    /\ local_rev[n] < Len(core)
    /\ local_leader' = [local_leader EXCEPT ![n] = NextCore(n).leader]
    /\ local_ISR' = [local_ISR EXCEPT ![n] = NextCore(n).ISR]
    /\ local_rev' = [local_rev EXCEPT ![n] = @ + 1]
    /\ UpdateEffectiveRev(n)
    /\ IF NextCore(n).leader /= local_leader[n]
        THEN /\ offset' = [offset EXCEPT ![n] = [NullOffset EXCEPT ![n] = Len(log[n])]]
             /\ UNCHANGED log
        ELSE UnchangedLog
    /\ UNCHANGED core
    /\ UNCHANGED client_log

NearestCommon(a, b) ==
    LET
        logA == <<0>> \o a
        logB == <<0>> \o b
    IN
        (CHOOSE i \in 1..Len(logA):
            /\ i <= Len(logB)
            /\ \A j \in 1..i: logA[j] = logB[j]
            /\ \/ i = Len(logA)
               \/ i = Len(logB)
               \/ logA[i + 1] /= logB[i + 1]) - 1

Slice(seq, n) ==
    [i \in 1..n |-> seq[i]]

ReplicateLog(n, m) ==
    /\ n /= m
    /\ local_leader[n] = n
    /\ local_leader[m] = n
    /\ effective_rev[n] >= effective_rev[m]
    /\ LET last == NearestCommon(log[n], log[m]) IN
        /\ Len(log[n]) > last
        /\ log' = [log EXCEPT ![m] = Slice(log[n], last + 1)]
        /\ offset' = [offset EXCEPT ![n] = [@ EXCEPT ![m] = last + 1]]
    /\ effective_rev' = [effective_rev EXCEPT ![m] = effective_rev[n]]
    /\ UNCHANGED core
    /\ UNCHANGED <<local_leader, local_ISR, local_rev>>
    /\ UNCHANGED client_log

ClientCanRecv(n) ==
    /\ local_leader[n] = n
    /\ n \in local_ISR[n]
    /\ \A m \in local_ISR[n]: Len(client_log) < offset[n][m]

NextLogElem(n) ==
    log[n][Len(client_log) + 1]

ClientRecv(n) ==
    /\ ClientCanRecv(n)
    /\ client_log' = Append(client_log, NextLogElem(n))
    /\ UNCHANGED core
    /\ UnchangedLog
    /\ UnchangedLocals

Next ==
    \/ UpdateLeader
    \/ \E n \in Nodes:
        \/ AppendLog(n)
        \/ WatchCore(n)
        \/ ShrinkISR(n)
        \/ ExtendISR(n)
        \/ \E m \in Nodes: ReplicateLog(n, m)
        \/ ClientRecv(n)

Constraints ==
    /\ \A n \in Nodes: Len(log[n]) < 4
    /\ Len(core) < 5

Inv ==
    /\ \A i \in 1..Len(core): core[i].ISR /= {}
    /\ \A n \in CurrentCore.ISR:
        /\ Len(log[n]) >= Len(client_log)
        /\ client_log = Slice(log[n], Len(client_log))
    \* /\ Cardinality(CurrentCore.ISR) >= 2
    \* /\ \A m, n \in Nodes: (m /= n /\ Len(log[n]) > 0) => Len(log[m]) = 0

Perms == Permutations(Nodes)

Tung == NearestCommon(<<1, 1, 2, 2>>, <<1, 1, 2, 2>>)

====