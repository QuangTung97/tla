---- MODULE SagaSpec ----
EXTENDS TLC

CONSTANTS RemoteService
ASSUME RemoteService /= {}

VARIABLES db_value, state, remote_state

vars == <<db_value, state, remote_state>>

init == "init"
committed == "committed"
requesting == "requesting"
force_aborting == "force_aborting"
aborted == "aborted"
accepted == "accepted"
rejected == "rejected"

State == {init, requesting, force_aborting, committed, aborted}

RemoteState == {init, accepted, rejected, aborted}

TypeOK ==
    /\ db_value \in {init, committed}
    /\ state \in State
    /\ remote_state \in [RemoteService -> RemoteState]

Init ==
    /\ db_value = init
    /\ state = init
    /\ remote_state = [s \in RemoteService |-> init]

Termination ==
    /\ \/ state = aborted /\ (\A s \in RemoteService: remote_state[s] = aborted)
       \/ state = committed /\ (\A s \in RemoteService: remote_state[s] = accepted)
    /\ UNCHANGED <<db_value, state, remote_state>>

Requesting ==
    /\ state = init
    /\ state' = requesting
    /\ UNCHANGED <<db_value, remote_state>>

RemoteAccept(s) ==
    /\ state = requesting
    /\ remote_state[s] = init
    /\ remote_state' = [remote_state EXCEPT ![s] = accepted]
    /\ UNCHANGED <<db_value, state>>
    
RemoteReject(s) ==
    /\ state = requesting
    /\ remote_state[s] = init
    /\ remote_state' = [remote_state EXCEPT ![s] = rejected]
    /\ UNCHANGED <<db_value, state>>

Commit ==
    /\ state = requesting
    /\ \A s \in RemoteService: remote_state[s] = accepted
    /\ state' = committed
    /\ db_value' = committed
    /\ UNCHANGED remote_state

WorkerForceAborting ==
    /\ \A s \in RemoteService: remote_state[s] = accepted
    /\ state = requesting
    /\ state' = force_aborting
    /\ UNCHANGED <<db_value, remote_state>>

Finished == {accepted, rejected, aborted}

WorkerCompensateRemote(s) ==
    /\ \A rs \in RemoteService: remote_state[rs] /= init
    /\ \/ \E rs \in RemoteService: remote_state[rs] = rejected \/ remote_state[rs] = aborted
       \/ state = force_aborting
    /\ remote_state[s] /= aborted
    /\ remote_state' = [remote_state EXCEPT ![s] = aborted]
    /\ UNCHANGED <<db_value, state>>

WorkerAbort ==
    /\ \A s \in RemoteService: remote_state[s] = aborted
    /\ state /= aborted
    /\ state' = aborted
    /\ UNCHANGED <<db_value, remote_state>>

RemoteServiceActions ==
    \E s \in RemoteService: RemoteAccept(s) \/ RemoteReject(s) \/ WorkerCompensateRemote(s)

Next ==
    \/ Requesting
    \/ RemoteServiceActions
    \/ Commit
    \/ WorkerForceAborting
    \/ WorkerAbort
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(WorkerForceAborting) /\ WF_vars(WorkerAbort) /\ WF_vars(RemoteServiceActions)

Inv == db_value = committed => state = committed /\ (\A s \in RemoteService: remote_state[s] = accepted)

NotAbortedAfterInit ==
    \A s \in RemoteService: remote_state[s] = init /\ remote_state'[s] /= init => remote_state'[s] = accepted \/ remote_state'[s] = rejected

NotAbortedAfterInitProperty == [][NotAbortedAfterInit]_vars

Terminated ==
    \/ state = init /\ (\A s \in RemoteService: remote_state[s] = init)
    \/ state = aborted /\ (\A s \in RemoteService: remote_state[s] = aborted)
    \/ state = committed /\ (\A s \in RemoteService: remote_state[s] = accepted)

EventuallyTerminated == <> Terminated

====
