------------------------- MODULE SeqLock -------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS 
    Fixed   \* FALSE = vulnerable (asynchronous uncoordinated persistence)
            \* TRUE  = mitigated (cache line flushes: flush c, flush x1, flush x2)

ASSUME Fixed \in BOOLEAN

(* --algorithm PersistentMemorySeqlock
variables
    \* Persistent Memory (survives power outages and system crashes)
    pm_c = 0,
    pm_x1 = 0,
    pm_x2 = 0,

    \* Volatile Memory / Cache line states
    c = 0,
    x1 = 0,
    x2 = 0,

    \* Secret data classification: h = 1 (high sensitive), h = 0 (low)
    h \in {0, 1},

    \* System crash / power outage flag
    crashed = FALSE,

    \* Public output channel observed by external observer / calling environment
    out = << >>,

    \* Auxiliary timing variables
    t = 0,
    T_start = 0,
    t_prime = 0;

fair process Writer = 1
variables r0_w = 0;
begin
wr0: \* Public entry point
    T_start := t;
    t := t + 1;
    out := Append(out, "WR_START");

wr1: \* r0 := [c]; [c] := r0 + 1 (c becomes odd: write transaction began)
    r0_w := c;
    c := r0_w + 1;
    t := t + 1;
    if Fixed then
        \* Mitigation: flush c persists the odd counter before data writes
        pm_c := c;
    end if;

wr2: \* [x1] := r1 (write data: x1 := h)
    x1 := h;
    t := t + 1;
    if Fixed then
        skip;
    else
        \* Vulnerable: store to x1 can persist asynchronously out of order
        either
            pm_x1 := x1;
        or
            skip;
        end either;
    end if;

wr3: \* [x2] := r2 (write classification tag: x2 := h)
    x2 := h;
    t := t + 1;
    if Fixed then
        \* Mitigation: flush x1; flush x2 ensures data and tag persist before c
        pm_x1 := x1;
        pm_x2 := x2;
    else
        \* Vulnerable: store to x2 may lag in volatile buffer
        either
            pm_x2 := x2;
        or
            skip;
        end either;
    end if;

wr4: \* r0 := [c]; [c] := r0 + 1 (c becomes even: write transaction committed)
    r0_w := c;
    c := r0_w + 1;
    t := t + 1;
    \* In both modes, the final store to c is persisted
    pm_c := c;

wr_exit:
    t := t + 1;
    out := Append(out, "WR_DONE");
end process;

fair process CrashRecovery = 2
begin
crash_event:
    \* A power outage occurs non-deterministically during or after writes
    await pc[1] \in {"wr2", "wr3", "wr4", "wr_exit"};
    crashed := TRUE;
    t := t + 1;
    \* Reboot from Persistent Memory: volatile cache is wiped, restored from PM
    c := pm_c;
    x1 := pm_x1;
    x2 := pm_x2;
    out := Append(out, "CRASH_REBOOT");
end process;

fair process Reader = 3
variables r0_r = 0, r1 = 0, r2 = 0, r3 = 0;
begin
rd0: \* Start block: wait for reboot and check if counter c is even
    await crashed;
    t := t + 1;
    r0_r := c;
    if r0_r % 2 = 0 then
        goto rd1;
    else
        goto rd_inconsistent;
    end if;

rd1: \* Check security flag x2
    r2 := x2;
    t := t + 1;
    if r2 = 1 then
        goto rd2;
    else
        goto rd3;
    end if;

rd2: \* High data detected: read suppressed, clear r1, return 0
    r1 := 0;
    t := t + 1;
    t_prime := t;
    out := Append(out, "SUPPRESSED_HIGH");
    goto rd_done;

rd3: \* Low data expected: read x1, re-read c to ensure atomicity
    r1 := x1;
    r3 := c;
    t := t + 1;
    if r3 = r0_r then
        t_prime := t;
        out := Append(out, r1);
        goto rd_done;
    else
        goto rd0;
    end if;

rd_inconsistent:
    t_prime := t;
    out := Append(out, "ABORT_ODD_C");

rd_done:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cc85ff0" /\ chksum(tla) = "c692bd23")
VARIABLES pc, pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, out, t, T_start, 
          t_prime, r0_w, r0_r, r1, r2, r3

vars == << pc, pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, out, t, T_start, 
           t_prime, r0_w, r0_r, r1, r2, r3 >>

ProcSet == {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ pm_c = 0
        /\ pm_x1 = 0
        /\ pm_x2 = 0
        /\ c = 0
        /\ x1 = 0
        /\ x2 = 0
        /\ h \in {0, 1}
        /\ crashed = FALSE
        /\ out = << >>
        /\ t = 0
        /\ T_start = 0
        /\ t_prime = 0
        (* Process Writer *)
        /\ r0_w = 0
        (* Process Reader *)
        /\ r0_r = 0
        /\ r1 = 0
        /\ r2 = 0
        /\ r3 = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "wr0"
                                        [] self = 2 -> "crash_event"
                                        [] self = 3 -> "rd0"]

wr0 == /\ pc[1] = "wr0"
       /\ T_start' = t
       /\ t' = t + 1
       /\ out' = Append(out, "WR_START")
       /\ pc' = [pc EXCEPT ![1] = "wr1"]
       /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, t_prime, 
                       r0_w, r0_r, r1, r2, r3 >>

wr1 == /\ pc[1] = "wr1"
       /\ r0_w' = c
       /\ c' = r0_w' + 1
       /\ t' = t + 1
       /\ IF Fixed
             THEN /\ pm_c' = c'
             ELSE /\ TRUE
                  /\ pm_c' = pm_c
       /\ pc' = [pc EXCEPT ![1] = "wr2"]
       /\ UNCHANGED << pm_x1, pm_x2, x1, x2, h, crashed, out, T_start, t_prime, 
                       r0_r, r1, r2, r3 >>

wr2 == /\ pc[1] = "wr2"
       /\ x1' = h
       /\ t' = t + 1
       /\ IF Fixed
             THEN /\ TRUE
                  /\ pm_x1' = pm_x1
             ELSE /\ \/ /\ pm_x1' = x1'
                     \/ /\ TRUE
                        /\ pm_x1' = pm_x1
       /\ pc' = [pc EXCEPT ![1] = "wr3"]
       /\ UNCHANGED << pm_c, pm_x2, c, x2, h, crashed, out, T_start, t_prime, 
                       r0_w, r0_r, r1, r2, r3 >>

wr3 == /\ pc[1] = "wr3"
       /\ x2' = h
       /\ t' = t + 1
       /\ IF Fixed
             THEN /\ pm_x1' = x1
                  /\ pm_x2' = x2'
             ELSE /\ \/ /\ pm_x2' = x2'
                     \/ /\ TRUE
                        /\ pm_x2' = pm_x2
                  /\ pm_x1' = pm_x1
       /\ pc' = [pc EXCEPT ![1] = "wr4"]
       /\ UNCHANGED << pm_c, c, x1, h, crashed, out, T_start, t_prime, r0_w, 
                       r0_r, r1, r2, r3 >>

wr4 == /\ pc[1] = "wr4"
       /\ r0_w' = c
       /\ c' = r0_w' + 1
       /\ t' = t + 1
       /\ pm_c' = c'
       /\ pc' = [pc EXCEPT ![1] = "wr_exit"]
       /\ UNCHANGED << pm_x1, pm_x2, x1, x2, h, crashed, out, T_start, t_prime, 
                       r0_r, r1, r2, r3 >>

wr_exit == /\ pc[1] = "wr_exit"
           /\ t' = t + 1
           /\ out' = Append(out, "WR_DONE")
           /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, T_start, 
                           t_prime, r0_w, r0_r, r1, r2, r3 >>

Writer == wr0 \/ wr1 \/ wr2 \/ wr3 \/ wr4 \/ wr_exit

crash_event == /\ pc[2] = "crash_event"
               /\ pc[1] \in {"wr2", "wr3", "wr4", "wr_exit"}
               /\ crashed' = TRUE
               /\ t' = t + 1
               /\ c' = pm_c
               /\ x1' = pm_x1
               /\ x2' = pm_x2
               /\ out' = Append(out, "CRASH_REBOOT")
               /\ pc' = [pc EXCEPT ![2] = "Done"]
               /\ UNCHANGED << pm_c, pm_x1, pm_x2, h, T_start, t_prime, r0_w, 
                               r0_r, r1, r2, r3 >>

CrashRecovery == crash_event

rd0 == /\ pc[3] = "rd0"
       /\ crashed
       /\ t' = t + 1
       /\ r0_r' = c
       /\ IF r0_r' % 2 = 0
             THEN /\ pc' = [pc EXCEPT ![3] = "rd1"]
             ELSE /\ pc' = [pc EXCEPT ![3] = "rd_inconsistent"]
       /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, out, T_start, 
                       t_prime, r0_w, r1, r2, r3 >>

rd1 == /\ pc[3] = "rd1"
       /\ r2' = x2
       /\ t' = t + 1
       /\ IF r2' = 1
             THEN /\ pc' = [pc EXCEPT ![3] = "rd2"]
             ELSE /\ pc' = [pc EXCEPT ![3] = "rd3"]
       /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, out, T_start, 
                       t_prime, r0_w, r0_r, r1, r3 >>

rd2 == /\ pc[3] = "rd2"
       /\ r1' = 0
       /\ t' = t + 1
       /\ t_prime' = t'
       /\ out' = Append(out, "SUPPRESSED_HIGH")
       /\ pc' = [pc EXCEPT ![3] = "rd_done"]
       /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, T_start, 
                       r0_w, r0_r, r2, r3 >>

rd3 == /\ pc[3] = "rd3"
       /\ r1' = x1
       /\ r3' = c
       /\ t' = t + 1
       /\ IF r3' = r0_r
             THEN /\ t_prime' = t'
                  /\ out' = Append(out, r1')
                  /\ pc' = [pc EXCEPT ![3] = "rd_done"]
             ELSE /\ pc' = [pc EXCEPT ![3] = "rd0"]
                  /\ UNCHANGED << out, t_prime >>
       /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, T_start, 
                       r0_w, r0_r, r2 >>

rd_inconsistent == /\ pc[3] = "rd_inconsistent"
                   /\ t_prime' = t
                   /\ out' = Append(out, "ABORT_ODD_C")
                   /\ pc' = [pc EXCEPT ![3] = "rd_done"]
                   /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, 
                                   t, T_start, r0_w, r0_r, r1, r2, r3 >>

rd_done == /\ pc[3] = "rd_done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![3] = "Done"]
           /\ UNCHANGED << pm_c, pm_x1, pm_x2, c, x1, x2, h, crashed, out, t, 
                           T_start, t_prime, r0_w, r0_r, r1, r2, r3 >>

Reader == rd0 \/ rd1 \/ rd2 \/ rd3 \/ rd_inconsistent \/ rd_done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Writer \/ CrashRecovery \/ Reader
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Writer)
        /\ WF_vars(CrashRecovery)
        /\ WF_vars(Reader)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(* ============================================================================= *)
(* FUNCTIONAL LAYER & TYPE SAFETY                                                *)
(* ============================================================================= *)

TypeOK ==
    /\ pm_c \in Nat
    /\ pm_x1 \in {0, 1}
    /\ pm_x2 \in {0, 1}
    /\ c \in Nat
    /\ x1 \in {0, 1}
    /\ x2 \in {0, 1}
    /\ h \in {0, 1}
    /\ crashed \in BOOLEAN
    /\ t \in Nat
    /\ T_start \in Nat
    /\ t_prime \in Nat
    /\ r0_w \in Nat
    /\ r0_r \in Nat
    /\ r1 \in {0, 1}
    /\ r2 \in {0, 1}
    /\ r3 \in Nat
    /\ out \in Seq({"WR_START", "WR_DONE", "CRASH_REBOOT", "SUPPRESSED_HIGH", "ABORT_ODD_C", 0, 1})
    /\ pc[1] \in {"wr0", "wr1", "wr2", "wr3", "wr4", "wr_exit", "Done"}
    /\ pc[2] \in {"crash_event", "Done"}
    /\ pc[3] \in {"rd0", "rd1", "rd2", "rd3", "rd_inconsistent", "rd_done", "Done"}

ReaderTerminated == pc[3] = "Done"

(* ============================================================================= *)
(* PERSISTENT MEMORY GUARANTEE PREDICATE G                                       *)
(* When counter c is even, x2 = 1 if and only if x1 contains high sensitive data *)
(* ============================================================================= *)

G_Guarantee == 
    (c % 2 = 0) => (x2 = 1 <=> (h = 1 /\ (pc[1] \in {"wr4", "wr_exit"} \/ crashed)))

(* ============================================================================= *)
(* VALUE-DEPENDENT NON-INTERFERENCE / INFORMATION LEAK CHECK                     *)
(* Under secure execution, the reader must NEVER return high sensitive data (1) *)
(* through the low return channel. If it returns 1, the secret leaked!           *)

(* Fails when Fixed = FALSE (witnessing the persistent memory information leak). *)
(* Passes when Fixed = TRUE  (proving flush instructions eliminate the leak).   *)
(* ============================================================================= *)

NoInformationLeak == 
    \A k \in 1..Len(out):
        (out[k] = 1) => (h = 0)

(* ============================================================================= *)
(* LEAKY ASSERTION (FLOYD-HOARE ATTACKER DEDUCTION)                              *)
(* An observer monitoring the reader's low output channel after a crash can       *)
(* soundly infer the high secret h = 1 if the value 1 is observed:              *)
(* ============================================================================= *)

LA_PersistentLeak == 
    (~Fixed /\ crashed /\ ReaderTerminated /\ (\E k \in 1..Len(out): out[k] = 1)) => (h = 1)

=================================================================================
