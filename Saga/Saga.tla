---- MODULE Saga ----
EXTENDS TLC

CONSTANTS server, Worker
ASSUME
    /\ Worker /= {}
    /\ ~(server \in Worker)

RemoteValue == {"init", "accepted", "cancelled", "aborted"}
Status == {"init", "requesting", "force-aborted"}
LocalValue == {"init", "ok"}

(*--algorithm Saga
variables
    remote_value = "init",
    status = "init",
    local_value = "init";

process serverProc = server

begin
StartRequest:
    status := "requesting";
RPC:
    either
        if remote_value = "init" then
            remote_value := "accepted";
        else
            goto Done;
        end if;
    or
        if remote_value = "init" then
            remote_value := "cancelled";
        end if;
        either
            goto Done;
        or
            goto ServerDBWriteAborted;
        end either;
    or
        goto Done;
    end either;
DBWrite:
    if status = "requesting" then
        either
            local_value := "ok";
            status := "init";
            goto Done;
        or
            goto ServerRPCAbort;
        end either;
    end if;

ServerRPCAbort:
    remote_value := "aborted";

ServerDBWriteAborted:
    status := "init";
end process;

process worker \in Worker
begin
StartWorker:
    while TRUE do
    CheckStatus:
        if status = "init" then
            goto StartWorker;
        elsif status = "waiting-aborted" then
            goto AbortSaga;
        end if;

    WorkerRPC:
        if remote_value = "init" then
            either
                remote_value := "cancelled";
                goto DBWriteAborted;
            or
                remote_value := "accepted";
            end either;
        elsif remote_value \in {"cancelled", "aborted"} then
            goto DBWriteAborted;
        end if;

    WorkerWaitAbort:
        if status = "requesting" then
            status := "force-aborted";
            goto AbortSaga;
        else
            goto StartWorker;
        end if;

    AbortSaga:
        remote_value := "aborted";

    DBWriteAborted:
        either
            status := "init";
            goto Done;
        or
            goto StartWorker;
        end either;
    end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "fc8daae4" /\ chksum(tla) = "98305ed5")
VARIABLES remote_value, status, local_value, pc

vars == << remote_value, status, local_value, pc >>

ProcSet == {server} \cup (Worker)

Init == (* Global variables *)
        /\ remote_value = "init"
        /\ status = "init"
        /\ local_value = "init"
        /\ pc = [self \in ProcSet |-> CASE self = server -> "StartRequest"
                                        [] self \in Worker -> "StartWorker"]

StartRequest == /\ pc[server] = "StartRequest"
                /\ status' = "requesting"
                /\ pc' = [pc EXCEPT ![server] = "RPC"]
                /\ UNCHANGED << remote_value, local_value >>

RPC == /\ pc[server] = "RPC"
       /\ \/ /\ IF remote_value = "init"
                   THEN /\ remote_value' = "accepted"
                        /\ pc' = [pc EXCEPT ![server] = "DBWrite"]
                   ELSE /\ pc' = [pc EXCEPT ![server] = "Done"]
                        /\ UNCHANGED remote_value
          \/ /\ IF remote_value = "init"
                   THEN /\ remote_value' = "cancelled"
                   ELSE /\ TRUE
                        /\ UNCHANGED remote_value
             /\ \/ /\ pc' = [pc EXCEPT ![server] = "Done"]
                \/ /\ pc' = [pc EXCEPT ![server] = "ServerDBWriteAborted"]
          \/ /\ pc' = [pc EXCEPT ![server] = "Done"]
             /\ UNCHANGED remote_value
       /\ UNCHANGED << status, local_value >>

DBWrite == /\ pc[server] = "DBWrite"
           /\ IF status = "requesting"
                 THEN /\ \/ /\ local_value' = "ok"
                            /\ status' = "init"
                            /\ pc' = [pc EXCEPT ![server] = "Done"]
                         \/ /\ pc' = [pc EXCEPT ![server] = "ServerRPCAbort"]
                            /\ UNCHANGED <<status, local_value>>
                 ELSE /\ pc' = [pc EXCEPT ![server] = "ServerRPCAbort"]
                      /\ UNCHANGED << status, local_value >>
           /\ UNCHANGED remote_value

ServerRPCAbort == /\ pc[server] = "ServerRPCAbort"
                  /\ remote_value' = "aborted"
                  /\ pc' = [pc EXCEPT ![server] = "ServerDBWriteAborted"]
                  /\ UNCHANGED << status, local_value >>

ServerDBWriteAborted == /\ pc[server] = "ServerDBWriteAborted"
                        /\ status' = "init"
                        /\ pc' = [pc EXCEPT ![server] = "Done"]
                        /\ UNCHANGED << remote_value, local_value >>

serverProc == StartRequest \/ RPC \/ DBWrite \/ ServerRPCAbort
                 \/ ServerDBWriteAborted

StartWorker(self) == /\ pc[self] = "StartWorker"
                     /\ pc' = [pc EXCEPT ![self] = "CheckStatus"]
                     /\ UNCHANGED << remote_value, status, local_value >>

CheckStatus(self) == /\ pc[self] = "CheckStatus"
                     /\ IF status = "init"
                           THEN /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                           ELSE /\ IF status = "waiting-aborted"
                                      THEN /\ pc' = [pc EXCEPT ![self] = "AbortSaga"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "WorkerRPC"]
                     /\ UNCHANGED << remote_value, status, local_value >>

WorkerRPC(self) == /\ pc[self] = "WorkerRPC"
                   /\ IF remote_value = "init"
                         THEN /\ \/ /\ remote_value' = "cancelled"
                                    /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                                 \/ /\ remote_value' = "accepted"
                                    /\ pc' = [pc EXCEPT ![self] = "WorkerWaitAbort"]
                         ELSE /\ IF remote_value \in {"cancelled", "aborted"}
                                    THEN /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "WorkerWaitAbort"]
                              /\ UNCHANGED remote_value
                   /\ UNCHANGED << status, local_value >>

WorkerWaitAbort(self) == /\ pc[self] = "WorkerWaitAbort"
                         /\ IF status = "requesting"
                               THEN /\ status' = "force-aborted"
                                    /\ pc' = [pc EXCEPT ![self] = "AbortSaga"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                                    /\ UNCHANGED status
                         /\ UNCHANGED << remote_value, local_value >>

AbortSaga(self) == /\ pc[self] = "AbortSaga"
                   /\ remote_value' = "aborted"
                   /\ pc' = [pc EXCEPT ![self] = "DBWriteAborted"]
                   /\ UNCHANGED << status, local_value >>

DBWriteAborted(self) == /\ pc[self] = "DBWriteAborted"
                        /\ \/ /\ status' = "init"
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "StartWorker"]
                              /\ UNCHANGED status
                        /\ UNCHANGED << remote_value, local_value >>

worker(self) == StartWorker(self) \/ CheckStatus(self) \/ WorkerRPC(self)
                   \/ WorkerWaitAbort(self) \/ AbortSaga(self)
                   \/ DBWriteAborted(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == serverProc
           \/ (\E self \in Worker: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOK ==
    /\ remote_value \in RemoteValue
    /\ status \in Status
    /\ local_value \in LocalValue

Inv ==
    /\ local_value = "ok" =>
        /\ status = "init"
        /\ remote_value = "accepted"
        /\ (\A w \in Worker: pc[w] /= "Done")

InvAbortAfterAccepted ==
    /\ \A w \in Worker: pc[w] = "AbortSaga" => remote_value = "accepted" \/ remote_value = "aborted"

AcceptCanAfterAbort ==
    /\ \A w \in Worker: pc[w] = "WorkerRPC" => remote_value /= "aborted"

Completed ==
    /\ pc[server] = "Done" /\ (\E w \in Worker: pc[w] = "Done") =>
        status = "init" /\ (remote_value = "cancelled"  \/ remote_value = "aborted")

Term1 == local_value /= "ok"

Term2 == ~(\A p \in ProcSet: pc[p] = "Done")

Term3 == ~(pc[server] = "Done" /\ \E w \in Worker: pc[w] = "Done")

Perms == Permutations(Worker)

====
