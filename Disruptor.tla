----------------------------- MODULE Disruptor -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS keys

GetFirstSequence(s, size) ==
    IF size >= Len(s)
    THEN s
    ELSE [i \in 1..size |-> s[i]]
    
DrainSequence(s, size) ==
    IF size >= Len(s)
    THEN <<>>
    ELSE [i \in 1..(Len(s) - size) |-> s[i + size]]

cache_size == 2
sequence_range == 3
buffer_size == 2
nil == "nil"

(*--algorithm disruptor
variables
    cache = <<>>,
    store = <<>>,
    channel = <<>>,
    sequence = 0,
    buffer = <<>>,
    current = nil,
    tmp_sequence = 0,
    changeset = <<>>;
    
define
    TypeOK ==
        /\ sequence \in Nat
    
    MinKey == CHOOSE k \in DOMAIN cache: (\A k1 \in DOMAIN cache: cache[k1] >= cache[k])
    CacheDelete(key) == [k \in (DOMAIN cache \ {key}) |-> cache[k]]
    CachePut(key, v) ==
        IF (key \in DOMAIN cache) \/ (Cardinality(DOMAIN cache) < cache_size)
        THEN (key :> v) @@ cache
        ELSE (key :> v) @@ CacheDelete(MinKey)
        
    GetStore(key) == IF key \in DOMAIN store THEN store[key] ELSE 0
        
    Latest ==
        IF Len(buffer) /= 0
        THEN IF Head(buffer).key \notin DOMAIN cache
            THEN IF Head(buffer).snapshot >= tmp_sequence + 1 - sequence_range
                THEN Head(buffer).value = GetStore(Head(buffer).key)
                ELSE TRUE
            ELSE TRUE
        ELSE TRUE
end define;

process sender \in 2..5
variables 
    local_sequence = 0,
    key \in keys,
    value = 0;
begin
GetSequence:
    local_sequence := sequence;
GetValue:
    value := GetStore(key);
Send:
    channel := Append(channel, [key |-> key, snapshot |-> local_sequence, value |-> value]);
end process;

process main = 1
begin
Loop:
    while TRUE do
        await Len(channel) /= 0;
        buffer := GetFirstSequence(channel, buffer_size);
        channel := DrainSequence(channel, buffer_size);
        tmp_sequence := sequence;
        changeset := <<>>;
Processing:
        while Len(buffer) /= 0 do
CheckValid:
            current := Head(buffer);
            buffer := Tail(buffer);
            
            if current.snapshot >= tmp_sequence + 1 - sequence_range then
                cache := CachePut(current.key, tmp_sequence + 1);
                changeset := (current.key :> tmp_sequence + 1) @@ changeset;
                tmp_sequence := tmp_sequence + 1;
            end if;    
        end while;
StoreData:
        store := changeset @@ store;
SetSequence:
        sequence := tmp_sequence;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "6550c00f" /\ chksum(tla) = "db41e6fc")
VARIABLES cache, store, channel, sequence, buffer, current, tmp_sequence, 
          changeset, pc

(* define statement *)
TypeOK ==
    /\ sequence \in Nat

MinKey == CHOOSE k \in DOMAIN cache: (\A k1 \in DOMAIN cache: cache[k1] >= cache[k])
CacheDelete(key) == [k \in (DOMAIN cache \ {key}) |-> cache[k]]
CachePut(key, v) ==
    IF (key \in DOMAIN cache) \/ (Cardinality(DOMAIN cache) < cache_size)
    THEN (key :> v) @@ cache
    ELSE (key :> v) @@ CacheDelete(MinKey)

GetStore(key) == IF key \in DOMAIN store THEN store[key] ELSE 0

Latest ==
    IF Len(buffer) /= 0
    THEN IF Head(buffer).key \notin DOMAIN cache
        THEN IF Head(buffer).snapshot >= tmp_sequence + 1 - sequence_range
            THEN Head(buffer).value = GetStore(Head(buffer).key)
            ELSE TRUE
        ELSE TRUE
    ELSE TRUE

VARIABLES local_sequence, key, value

vars == << cache, store, channel, sequence, buffer, current, tmp_sequence, 
           changeset, pc, local_sequence, key, value >>

ProcSet == (2..5) \cup {1}

Init == (* Global variables *)
        /\ cache = <<>>
        /\ store = <<>>
        /\ channel = <<>>
        /\ sequence = 0
        /\ buffer = <<>>
        /\ current = nil
        /\ tmp_sequence = 0
        /\ changeset = <<>>
        (* Process sender *)
        /\ local_sequence = [self \in 2..5 |-> 0]
        /\ key \in [2..5 -> keys]
        /\ value = [self \in 2..5 |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 2..5 -> "GetSequence"
                                        [] self = 1 -> "Loop"]

GetSequence(self) == /\ pc[self] = "GetSequence"
                     /\ local_sequence' = [local_sequence EXCEPT ![self] = sequence]
                     /\ pc' = [pc EXCEPT ![self] = "GetValue"]
                     /\ UNCHANGED << cache, store, channel, sequence, buffer, 
                                     current, tmp_sequence, changeset, key, 
                                     value >>

GetValue(self) == /\ pc[self] = "GetValue"
                  /\ value' = [value EXCEPT ![self] = GetStore(key[self])]
                  /\ pc' = [pc EXCEPT ![self] = "Send"]
                  /\ UNCHANGED << cache, store, channel, sequence, buffer, 
                                  current, tmp_sequence, changeset, 
                                  local_sequence, key >>

Send(self) == /\ pc[self] = "Send"
              /\ channel' = Append(channel, [key |-> key[self], snapshot |-> local_sequence[self], value |-> value[self]])
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << cache, store, sequence, buffer, current, 
                              tmp_sequence, changeset, local_sequence, key, 
                              value >>

sender(self) == GetSequence(self) \/ GetValue(self) \/ Send(self)

Loop == /\ pc[1] = "Loop"
        /\ Len(channel) /= 0
        /\ buffer' = GetFirstSequence(channel, buffer_size)
        /\ channel' = DrainSequence(channel, buffer_size)
        /\ tmp_sequence' = sequence
        /\ changeset' = <<>>
        /\ pc' = [pc EXCEPT ![1] = "Processing"]
        /\ UNCHANGED << cache, store, sequence, current, local_sequence, key, 
                        value >>

Processing == /\ pc[1] = "Processing"
              /\ IF Len(buffer) /= 0
                    THEN /\ pc' = [pc EXCEPT ![1] = "CheckValid"]
                    ELSE /\ pc' = [pc EXCEPT ![1] = "StoreData"]
              /\ UNCHANGED << cache, store, channel, sequence, buffer, current, 
                              tmp_sequence, changeset, local_sequence, key, 
                              value >>

CheckValid == /\ pc[1] = "CheckValid"
              /\ current' = Head(buffer)
              /\ buffer' = Tail(buffer)
              /\ IF current'.snapshot >= tmp_sequence + 1 - sequence_range
                    THEN /\ cache' = CachePut(current'.key, tmp_sequence + 1)
                         /\ changeset' = (current'.key :> tmp_sequence + 1) @@ changeset
                         /\ tmp_sequence' = tmp_sequence + 1
                    ELSE /\ TRUE
                         /\ UNCHANGED << cache, tmp_sequence, changeset >>
              /\ pc' = [pc EXCEPT ![1] = "Processing"]
              /\ UNCHANGED << store, channel, sequence, local_sequence, key, 
                              value >>

StoreData == /\ pc[1] = "StoreData"
             /\ store' = changeset @@ store
             /\ pc' = [pc EXCEPT ![1] = "SetSequence"]
             /\ UNCHANGED << cache, channel, sequence, buffer, current, 
                             tmp_sequence, changeset, local_sequence, key, 
                             value >>

SetSequence == /\ pc[1] = "SetSequence"
               /\ sequence' = tmp_sequence
               /\ pc' = [pc EXCEPT ![1] = "Loop"]
               /\ UNCHANGED << cache, store, channel, buffer, current, 
                               tmp_sequence, changeset, local_sequence, key, 
                               value >>

main == Loop \/ Processing \/ CheckValid \/ StoreData \/ SetSequence

Next == main
           \/ (\E self \in 2..5: sender(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Thu Feb 04 13:37:42 ICT 2021 by teko
\* Created Thu Feb 04 09:40:08 ICT 2021 by teko
