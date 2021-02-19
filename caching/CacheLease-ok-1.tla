----------------------------- MODULE CacheLease -----------------------------
EXTENDS Integers
CONSTANTS Client

(*--algorithm cache_lease
variables db_value = 10, cache_value = 0, cache_lease = 0, lease_seq = 0;

define
    TypeOK ==
        /\ db_value \in Nat
        /\ cache_value \in Nat \/ cache_value = -1
end define;

process client \in Client
variables new_value = 0, get_value = 0, get_lease = 0;
begin
Start:
    either
        db_value := db_value + 1;
        new_value := db_value;
    SetCache:
        cache_value := 0;
        cache_lease := 0;
    or
        get_value := cache_value;
        if cache_value = 0 /\ cache_lease = 0 then
            lease_seq := lease_seq + 1;
            cache_lease := lease_seq;
            get_lease := cache_lease;
        end if;
        
        if get_value = 0 /\ get_lease > 0 then
        GetDB:
            get_value := db_value;
        SetBackCache:
            if cache_lease = get_lease then
                cache_value := get_value;
                cache_lease := 0;
            end if;
        end if;
    or
    LRUDelete:
        cache_value := 0;
    end either;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "b6004b36" /\ chksum(tla) = "2f9ccbaa")
VARIABLES db_value, cache_value, cache_lease, lease_seq, pc

(* define statement *)
TypeOK ==
    /\ db_value \in Nat
    /\ cache_value \in Nat \/ cache_value = -1

VARIABLES new_value, get_value, get_lease

vars == << db_value, cache_value, cache_lease, lease_seq, pc, new_value, 
           get_value, get_lease >>

ProcSet == (Client)

Init == (* Global variables *)
        /\ db_value = 10
        /\ cache_value = 0
        /\ cache_lease = 0
        /\ lease_seq = 0
        (* Process client *)
        /\ new_value = [self \in Client |-> 0]
        /\ get_value = [self \in Client |-> 0]
        /\ get_lease = [self \in Client |-> 0]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ \/ /\ db_value' = db_value + 1
                     /\ new_value' = [new_value EXCEPT ![self] = db_value']
                     /\ pc' = [pc EXCEPT ![self] = "SetCache"]
                     /\ UNCHANGED <<cache_lease, lease_seq, get_value, get_lease>>
                  \/ /\ get_value' = [get_value EXCEPT ![self] = cache_value]
                     /\ IF cache_value = 0 /\ cache_lease = 0
                           THEN /\ lease_seq' = lease_seq + 1
                                /\ cache_lease' = lease_seq'
                                /\ get_lease' = [get_lease EXCEPT ![self] = cache_lease']
                           ELSE /\ TRUE
                                /\ UNCHANGED << cache_lease, lease_seq, 
                                                get_lease >>
                     /\ IF get_value'[self] = 0 /\ get_lease'[self] > 0
                           THEN /\ pc' = [pc EXCEPT ![self] = "GetDB"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED <<db_value, new_value>>
                  \/ /\ pc' = [pc EXCEPT ![self] = "LRUDelete"]
                     /\ UNCHANGED <<db_value, cache_lease, lease_seq, new_value, get_value, get_lease>>
               /\ UNCHANGED cache_value

SetCache(self) == /\ pc[self] = "SetCache"
                  /\ cache_value' = 0
                  /\ cache_lease' = 0
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << db_value, lease_seq, new_value, get_value, 
                                  get_lease >>

GetDB(self) == /\ pc[self] = "GetDB"
               /\ get_value' = [get_value EXCEPT ![self] = db_value]
               /\ pc' = [pc EXCEPT ![self] = "SetBackCache"]
               /\ UNCHANGED << db_value, cache_value, cache_lease, lease_seq, 
                               new_value, get_lease >>

SetBackCache(self) == /\ pc[self] = "SetBackCache"
                      /\ IF cache_lease = get_lease[self]
                            THEN /\ cache_value' = get_value[self]
                                 /\ cache_lease' = 0
                            ELSE /\ TRUE
                                 /\ UNCHANGED << cache_value, cache_lease >>
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << db_value, lease_seq, new_value, 
                                      get_value, get_lease >>

LRUDelete(self) == /\ pc[self] = "LRUDelete"
                   /\ cache_value' = 0
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << db_value, cache_lease, lease_seq, new_value, 
                                   get_value, get_lease >>

client(self) == Start(self) \/ SetCache(self) \/ GetDB(self)
                   \/ SetBackCache(self) \/ LRUDelete(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Client: client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Fri Feb 19 16:53:20 ICT 2021 by teko
\* Created Fri Feb 19 15:25:18 ICT 2021 by teko
