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
    UpdateDB:
        db_value := db_value + 1;
        new_value := db_value;
        either
        SetCache:
            if cache_value /= 0 /\ new_value > cache_value then
                cache_value := new_value;
                cache_lease := 0;
            else
                cache_value := 0;
                cache_lease := 0;
            end if;
        or
        InvalidateCache:
            cache_value := 0;
            cache_lease := 0;
        end either;
    or
    GetCache:
        get_value := cache_value;
        if cache_value = 0 /\ cache_lease = 0 then
            lease_seq := lease_seq + 1;
            cache_lease := lease_seq;
            get_lease := cache_lease;
        end if;
        
        if get_value = 0 /\ get_lease > 0 then
        GetDB:
            get_value := db_value;
            
            either
            SetBackCache:
                if cache_lease = get_lease then
                    cache_value := get_value;
                    cache_lease := 0;
                end if;
            or
                skip;
            end either;
        end if;
    or
    LRUDelete:
        cache_value := 0;
        cache_lease := 0;
    end either;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "968fc170" /\ chksum(tla) = "1f84f8bf")
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
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "UpdateDB"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "GetCache"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "LRUDelete"]
               /\ UNCHANGED << db_value, cache_value, cache_lease, lease_seq, 
                               new_value, get_value, get_lease >>

UpdateDB(self) == /\ pc[self] = "UpdateDB"
                  /\ db_value' = db_value + 1
                  /\ new_value' = [new_value EXCEPT ![self] = db_value']
                  /\ \/ /\ pc' = [pc EXCEPT ![self] = "SetCache"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "InvalidateCache"]
                  /\ UNCHANGED << cache_value, cache_lease, lease_seq, 
                                  get_value, get_lease >>

SetCache(self) == /\ pc[self] = "SetCache"
                  /\ IF cache_value /= 0 /\ new_value[self] > cache_value
                        THEN /\ cache_value' = new_value[self]
                             /\ cache_lease' = 0
                        ELSE /\ cache_value' = 0
                             /\ cache_lease' = 0
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << db_value, lease_seq, new_value, get_value, 
                                  get_lease >>

InvalidateCache(self) == /\ pc[self] = "InvalidateCache"
                         /\ cache_value' = 0
                         /\ cache_lease' = 0
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << db_value, lease_seq, new_value, 
                                         get_value, get_lease >>

GetCache(self) == /\ pc[self] = "GetCache"
                  /\ get_value' = [get_value EXCEPT ![self] = cache_value]
                  /\ IF cache_value = 0 /\ cache_lease = 0
                        THEN /\ lease_seq' = lease_seq + 1
                             /\ cache_lease' = lease_seq'
                             /\ get_lease' = [get_lease EXCEPT ![self] = cache_lease']
                        ELSE /\ TRUE
                             /\ UNCHANGED << cache_lease, lease_seq, get_lease >>
                  /\ IF get_value'[self] = 0 /\ get_lease'[self] > 0
                        THEN /\ pc' = [pc EXCEPT ![self] = "GetDB"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << db_value, cache_value, new_value >>

GetDB(self) == /\ pc[self] = "GetDB"
               /\ get_value' = [get_value EXCEPT ![self] = db_value]
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "SetBackCache"]
                  \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
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
                   /\ cache_lease' = 0
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << db_value, lease_seq, new_value, get_value, 
                                   get_lease >>

client(self) == Start(self) \/ UpdateDB(self) \/ SetCache(self)
                   \/ InvalidateCache(self) \/ GetCache(self)
                   \/ GetDB(self) \/ SetBackCache(self) \/ LRUDelete(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Client: client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Inv == (\A c \in Client: pc[c] = "Done") /\ cache_value /= 0 => cache_value = db_value

Inv2 == cache_value = 0 \/ cache_lease = 0

THEOREM Spec => Inv

THEOREM Spec => Inv2

=============================================================================
\* Modification History
\* Last modified Mon Feb 22 17:43:41 ICT 2021 by teko
\* Created Fri Feb 19 15:25:18 ICT 2021 by teko
