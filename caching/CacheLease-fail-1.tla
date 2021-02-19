----------------------------- MODULE CacheLease -----------------------------
EXTENDS Integers
CONSTANTS Client

(*--algorithm cache_lease
variables db_value = 10, cache_value = 0;

define
    Leasing == -1
    
    TypeOK ==
        /\ db_value \in Nat
        /\ cache_value \in Nat \/ cache_value = -1
end define;

process client \in Client
variables new_value = 0, get_value = 0;
begin
Start:
    either
        db_value := db_value + 1;
        new_value := db_value;
    SetCache:
        cache_value := 0;
    or
        get_value := cache_value;
        if get_value = 0 then
            cache_value := Leasing;
        end if;
        
        if get_value = 0 then
        GetDB:
            get_value := db_value;
        SetBackCache:
            if cache_value = Leasing then
                cache_value := get_value;
            end if;
        end if;
    or
        (* delete cache *)
        cache_value := 0;
    end either;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "660bc6bb" /\ chksum(tla) = "5a360b07")
VARIABLES db_value, cache_value, pc

(* define statement *)
Leasing == -1

TypeOK ==
    /\ db_value \in Nat
    /\ cache_value \in Nat \/ cache_value = -1

VARIABLES new_value, get_value

vars == << db_value, cache_value, pc, new_value, get_value >>

ProcSet == (Client)

Init == (* Global variables *)
        /\ db_value = 10
        /\ cache_value = 0
        (* Process client *)
        /\ new_value = [self \in Client |-> 0]
        /\ get_value = [self \in Client |-> 0]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ \/ /\ db_value' = db_value + 1
                     /\ new_value' = [new_value EXCEPT ![self] = db_value']
                     /\ pc' = [pc EXCEPT ![self] = "SetCache"]
                     /\ UNCHANGED <<cache_value, get_value>>
                  \/ /\ get_value' = [get_value EXCEPT ![self] = cache_value]
                     /\ IF get_value'[self] = 0
                           THEN /\ cache_value' = Leasing
                           ELSE /\ TRUE
                                /\ UNCHANGED cache_value
                     /\ IF get_value'[self] = 0
                           THEN /\ pc' = [pc EXCEPT ![self] = "GetDB"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED <<db_value, new_value>>
                  \/ /\ cache_value' = 0
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED <<db_value, new_value, get_value>>

SetCache(self) == /\ pc[self] = "SetCache"
                  /\ cache_value' = 0
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << db_value, new_value, get_value >>

GetDB(self) == /\ pc[self] = "GetDB"
               /\ get_value' = [get_value EXCEPT ![self] = db_value]
               /\ pc' = [pc EXCEPT ![self] = "SetBackCache"]
               /\ UNCHANGED << db_value, cache_value, new_value >>

SetBackCache(self) == /\ pc[self] = "SetBackCache"
                      /\ IF cache_value = Leasing
                            THEN /\ cache_value' = get_value[self]
                            ELSE /\ TRUE
                                 /\ UNCHANGED cache_value
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << db_value, new_value, get_value >>

client(self) == Start(self) \/ SetCache(self) \/ GetDB(self)
                   \/ SetBackCache(self)

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
\* Last modified Fri Feb 19 16:26:30 ICT 2021 by teko
\* Created Fri Feb 19 15:25:18 ICT 2021 by teko
