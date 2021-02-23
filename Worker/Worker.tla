---- MODULE Worker ----
EXTENDS Naturals, TLC
CONSTANTS Worker, etcd, nil

ASSUME
    /\ Worker /= {}
    /\ ~(etcd \in Worker)
    /\ ~(nil \in Worker)

(*--algorithm Worker
variables
    leader = nil,
    db_sequence = 0,
    last_sent_seq = 0,
    service_seq = 0;

process etcdServer = etcd
begin
StartEtcd:
    while TRUE do
        leader := nil;
    end while;
end process;

process worker \in Worker
variables
    local_leader = nil,
    local_last_sent_seq = 0,
    local_db_sequence = 0;

begin
StartWorker:
    while TRUE do
        either await local_leader = nil;
        SetLeader:
            if leader = nil then
                leader := self;
            end if;
        or await leader /= local_leader;
        GetLeader:
            local_leader := leader;
        or await local_last_sent_seq = 0;
        GetLastSentSeq:
            local_last_sent_seq := last_sent_seq;
        or await local_leader = self;
        RecvEvent:
            db_sequence := db_sequence + 1;
        or await local_leader = self;
        GetSequence:
            local_db_sequence := db_sequence;

            if local_db_sequence > local_last_sent_seq then
            SendEvents:
                if service_seq < local_db_sequence then
                    service_seq := local_db_sequence;
                end if;
            SetSequence:
                if last_sent_seq < local_db_sequence then
                    last_sent_seq := local_db_sequence;
                    local_last_sent_seq := local_db_sequence;
                else
                    local_last_sent_seq := 0;
                end if;
            end if;

        end either;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "9170ef57" /\ chksum(tla) = "a29ea975")
VARIABLES leader, db_sequence, last_sent_seq, service_seq, pc, local_leader, 
          local_last_sent_seq, local_db_sequence

vars == << leader, db_sequence, last_sent_seq, service_seq, pc, local_leader, 
           local_last_sent_seq, local_db_sequence >>

ProcSet == {etcd} \cup (Worker)

Init == (* Global variables *)
        /\ leader = nil
        /\ db_sequence = 0
        /\ last_sent_seq = 0
        /\ service_seq = 0
        (* Process worker *)
        /\ local_leader = [self \in Worker |-> nil]
        /\ local_last_sent_seq = [self \in Worker |-> 0]
        /\ local_db_sequence = [self \in Worker |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = etcd -> "StartEtcd"
                                        [] self \in Worker -> "StartWorker"]

StartEtcd == /\ pc[etcd] = "StartEtcd"
             /\ leader' = nil
             /\ pc' = [pc EXCEPT ![etcd] = "StartEtcd"]
             /\ UNCHANGED << db_sequence, last_sent_seq, service_seq, 
                             local_leader, local_last_sent_seq, 
                             local_db_sequence >>

etcdServer == StartEtcd

StartWorker(self) == /\ pc[self] = "StartWorker"
                     /\ \/ /\ local_leader[self] = nil
                           /\ pc' = [pc EXCEPT ![self] = "SetLeader"]
                        \/ /\ leader /= local_leader[self]
                           /\ pc' = [pc EXCEPT ![self] = "GetLeader"]
                        \/ /\ local_last_sent_seq[self] = 0
                           /\ pc' = [pc EXCEPT ![self] = "GetLastSentSeq"]
                        \/ /\ local_leader[self] = self
                           /\ pc' = [pc EXCEPT ![self] = "RecvEvent"]
                        \/ /\ local_leader[self] = self
                           /\ pc' = [pc EXCEPT ![self] = "GetSequence"]
                     /\ UNCHANGED << leader, db_sequence, last_sent_seq, 
                                     service_seq, local_leader, 
                                     local_last_sent_seq, local_db_sequence >>

SetLeader(self) == /\ pc[self] = "SetLeader"
                   /\ IF leader = nil
                         THEN /\ leader' = self
                         ELSE /\ TRUE
                              /\ UNCHANGED leader
                   /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                   /\ UNCHANGED << db_sequence, last_sent_seq, service_seq, 
                                   local_leader, local_last_sent_seq, 
                                   local_db_sequence >>

GetLeader(self) == /\ pc[self] = "GetLeader"
                   /\ local_leader' = [local_leader EXCEPT ![self] = leader]
                   /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                   /\ UNCHANGED << leader, db_sequence, last_sent_seq, 
                                   service_seq, local_last_sent_seq, 
                                   local_db_sequence >>

GetLastSentSeq(self) == /\ pc[self] = "GetLastSentSeq"
                        /\ local_last_sent_seq' = [local_last_sent_seq EXCEPT ![self] = last_sent_seq]
                        /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                        /\ UNCHANGED << leader, db_sequence, last_sent_seq, 
                                        service_seq, local_leader, 
                                        local_db_sequence >>

RecvEvent(self) == /\ pc[self] = "RecvEvent"
                   /\ db_sequence' = db_sequence + 1
                   /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                   /\ UNCHANGED << leader, last_sent_seq, service_seq, 
                                   local_leader, local_last_sent_seq, 
                                   local_db_sequence >>

GetSequence(self) == /\ pc[self] = "GetSequence"
                     /\ local_db_sequence' = [local_db_sequence EXCEPT ![self] = db_sequence]
                     /\ IF local_db_sequence'[self] > local_last_sent_seq[self]
                           THEN /\ pc' = [pc EXCEPT ![self] = "SendEvents"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                     /\ UNCHANGED << leader, db_sequence, last_sent_seq, 
                                     service_seq, local_leader, 
                                     local_last_sent_seq >>

SendEvents(self) == /\ pc[self] = "SendEvents"
                    /\ IF service_seq < local_db_sequence[self]
                          THEN /\ service_seq' = local_db_sequence[self]
                          ELSE /\ TRUE
                               /\ UNCHANGED service_seq
                    /\ pc' = [pc EXCEPT ![self] = "SetSequence"]
                    /\ UNCHANGED << leader, db_sequence, last_sent_seq, 
                                    local_leader, local_last_sent_seq, 
                                    local_db_sequence >>

SetSequence(self) == /\ pc[self] = "SetSequence"
                     /\ IF last_sent_seq < local_db_sequence[self]
                           THEN /\ last_sent_seq' = local_db_sequence[self]
                                /\ local_last_sent_seq' = [local_last_sent_seq EXCEPT ![self] = local_db_sequence[self]]
                           ELSE /\ local_last_sent_seq' = [local_last_sent_seq EXCEPT ![self] = 0]
                                /\ UNCHANGED last_sent_seq
                     /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                     /\ UNCHANGED << leader, db_sequence, service_seq, 
                                     local_leader, local_db_sequence >>

worker(self) == StartWorker(self) \/ SetLeader(self) \/ GetLeader(self)
                   \/ GetLastSentSeq(self) \/ RecvEvent(self)
                   \/ GetSequence(self) \/ SendEvents(self)
                   \/ SetSequence(self)

Next == etcdServer
           \/ (\E self \in Worker: worker(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

NilWorker == Worker \union {nil}

TypeOK ==
    /\ leader \in NilWorker
    /\ db_sequence \in Nat
    /\ last_sent_seq \in Nat
    /\ service_seq \in Nat
    /\ local_leader \in [Worker -> NilWorker]

Inv ==
    /\ last_sent_seq <= db_sequence
    /\ service_seq <= db_sequence
    /\ \A w \in Worker: pc[w] = "SendEvents" => service_seq >= local_last_sent_seq[w]

Limit ==
    /\ service_seq /= 4

Perms == Permutations(Worker)

Constraints ==
    /\ db_sequence =< 4

====
