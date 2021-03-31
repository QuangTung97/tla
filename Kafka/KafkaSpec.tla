---- MODULE KafkaSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Nodes

VARIABLES
    ISR, leader, rev, log, offset, other_rev,
    local_ISR, local_rev, local_leader,
    client_log

LogData == Seq(Nat)

UnchangedLocals == UNCHANGED <<local_ISR, local_rev, local_leader>>

TypeOK ==
    /\ ISR \subseteq Nodes
    /\ leader \in Nodes
    /\ rev \in Nat
    /\ log \in [Nodes -> LogData]
    /\ offset \in [Nodes -> [Nodes -> Nat]]
    /\ other_rev \in [Nodes -> [Nodes -> Nat]]
    /\ local_ISR \in [Nodes -> SUBSET Nodes]
    /\ local_rev \in [Nodes -> Nat]
    /\ local_leader \in [Nodes -> Nodes]
    /\ client_log \in LogData

Init ==
    /\ ISR = Nodes
    /\ leader \in Nodes
    /\ rev = 1
    /\ log = [n \in Nodes |-> <<>>]
    /\ offset = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ other_rev = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ local_ISR = [n \in Nodes |-> Nodes]
    /\ local_rev = [n \in Nodes |-> 1]
    /\ local_leader = [n \in Nodes |-> leader]
    /\ client_log = <<>>

AppendLog(n) ==
    /\ local_leader[n] = n
    /\ log' = [log EXCEPT ![n] = Append(@, local_rev[n])]
    /\ offset' = [offset EXCEPT ![n] = [@ EXCEPT ![n] = @ + 1]]
    /\ UNCHANGED <<ISR, leader, rev, other_rev>>
    /\ UnchangedLocals
    /\ UNCHANGED client_log

UpdateISR(n) ==
    /\ local_leader[n] = n
    /\ rev = local_rev[n]
    /\ \E m \in ISR\{n}: ISR' = ISR \ {m}
    /\ UNCHANGED <<leader, rev, log, offset, other_rev>>
    /\ UnchangedLocals
    /\ UNCHANGED client_log

UpdateLeader ==
    /\ \E m \in ISR\{leader}: leader' = m
    /\ rev' = rev + 1
    /\ UNCHANGED <<ISR, log, offset, other_rev>>
    /\ UnchangedLocals
    /\ UNCHANGED client_log

ObserveLeader(n) ==
    /\ local_rev[n] /= rev
    /\ local_leader' = [local_leader EXCEPT ![n] = leader]
    /\ local_rev' = [local_rev EXCEPT ![n] = rev]
    /\ other_rev' = [other_rev EXCEPT ![n] = [@ EXCEPT ![n] = rev]]
    /\ UNCHANGED <<ISR, leader, rev, log, offset, local_ISR>>
    /\ UNCHANGED client_log

ObserveISR(n) ==
    /\ local_ISR[n] /= ISR
    /\ local_ISR' = [local_ISR EXCEPT ![n] = ISR]
    /\ UNCHANGED <<ISR, leader, rev, log, offset, other_rev, local_leader, local_rev>>
    /\ UNCHANGED client_log

ZeroOffset == [n \in Nodes |-> 0]

ReplicateLog(n, m) ==
    /\ local_leader[n] = n
    /\ n /= m
    /\ local_rev[n] >= local_rev[m]
    /\ log' = [log EXCEPT ![m] = log[n]]
    /\ offset' = [offset EXCEPT
        ![n] = [@ EXCEPT ![m] = Len(log[n])], ![m] = ZeroOffset]
    /\ other_rev' = [other_rev EXCEPT
        ![n] = [@ EXCEPT ![m] = local_rev[n]], ![m] = ZeroOffset]
    /\ local_rev' = [local_rev EXCEPT ![m] = local_rev[n]]
    /\ local_leader' = [local_leader EXCEPT ![m] = local_leader[n]]
    /\ UNCHANGED <<ISR, leader, rev>>
    /\ UNCHANGED local_ISR
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
    /\ \A m \in local_ISR[n]:
        /\ Len(client_log) < offset[n][m]
        /\ other_rev[n][m] = local_rev[n]

ClientRecv(n) ==
    /\ ClientCanRecv(n)
    /\ client_log' = Append(client_log, NextLogElem(n))
    /\ UNCHANGED <<ISR, leader, rev, log, offset, other_rev>>
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
    \* /\ ~(client_log = <<1, 2, 3>> /\ Cardinality(ISR) < 3)
    \* /\ \A n \in Nodes: ClientCanRecv(n) =>
    \*     client_log = Slice(log[n], Len(client_log))
    \* /\ \A n \in Nodes: ClientCanRecv(n) => local_ISR[n] = Nodes
    \* /\ \A n \in Nodes: local_rev[n] < 3
    \* /\ \A n1, n2 \in Nodes:
    \*     n1 /= n2 /\ Len(log[n1]) > 2 => log[n1] /= log[n2]


Perms == Permutations(Nodes)

====