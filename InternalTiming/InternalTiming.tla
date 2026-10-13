------------------------------ MODULE InternalTiming ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Delta_lo,  \* observation faster than this (or equal) => attacker concludes h = 0
          Delta_hi  \* observation at least this slow => attacker concludes h = 1

(* --algorithm InternalTiming

variables
    l = 0,          \* Shared public variable l
    h2 = 0,         \* Secret variable h2
    h \in {0, 1},   \* Secret variable h (TLC explores both 0 and 1)
    turn = 1,       \* Deterministic round-robin scheduler token
    done1 = FALSE,  \* Process T1 termination status
    done2 = FALSE,  \* Process T2 termination status
    t = 0,          \* Auxiliary global clock variable
    T_start = 0,    \* Time T recorded at entry public point
    t_prime = 0,    \* Time t' recorded at exit public point
    out = <<"START">>; \* Public output channel (entry public event)

process T1 = 1
begin
    l1: await turn = 1;
        t := t + 1;
        if h = 1 then
            turn := IF ~done2 THEN 2 ELSE 1;
            goto l2;
        else
            turn := IF ~done2 THEN 2 ELSE 1;
            goto l4;
        end if;
    l2: await turn = 1;
        h2 := 2 * h2 + l;
        t := t + 1;
        turn := IF ~done2 THEN 2 ELSE 1;
    l3: await turn = 1;
        skip;
        t := t + 1;
        turn := IF ~done2 THEN 2 ELSE 1;
        goto l5;
    l4: await turn = 1;
        skip;
        t := t + 1;
        turn := IF ~done2 THEN 2 ELSE 1;
    l5: await turn = 1;
        l := 1;
        out := Append(out, "1");
        t := t + 1;
        turn := IF ~done2 THEN 2 ELSE 1;
    l_exit:
        await turn = 1;
        done1 := TRUE;
        t := t + 1;
        if done2 then
            t_prime := t;
            out := Append(out, "END");
        end if;
        turn := 2;
end process;

process T2 = 2
begin
    m1: await turn = 2;
        skip;
        t := t + 1;
        turn := IF ~done1 THEN 1 ELSE 2;
    m2: await turn = 2;
        skip;
        t := t + 1;
        turn := IF ~done1 THEN 1 ELSE 2;
    m3: await turn = 2;
        l := 0;
        out := Append(out, "0");
        t := t + 1;
        turn := IF ~done1 THEN 1 ELSE 2;
    m_exit:
        await turn = 2;
        done2 := TRUE;
        t := t + 1;
        if done1 then
            t_prime := t;
            out := Append(out, "END");
        end if;
        turn := 1;
end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "cbdc3780" /\ chksum(tla) = "9be72aa0")
VARIABLES pc, l, h2, h, turn, done1, done2, t, T_start, t_prime, out

vars == << pc, l, h2, h, turn, done1, done2, t, T_start, t_prime, out >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ l = 0
        /\ h2 = 0
        /\ h \in {0, 1}
        /\ turn = 1
        /\ done1 = FALSE
        /\ done2 = FALSE
        /\ t = 0
        /\ T_start = 0
        /\ t_prime = 0
        /\ out = <<"START">>
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "l1"
                                        [] self = 2 -> "m1"]

l1 == /\ pc[1] = "l1"
      /\ turn = 1
      /\ t' = t + 1
      /\ IF h = 1
            THEN /\ turn' = IF ~done2 THEN 2 ELSE 1
                 /\ pc' = [pc EXCEPT ![1] = "l2"]
            ELSE /\ turn' = IF ~done2 THEN 2 ELSE 1
                 /\ pc' = [pc EXCEPT ![1] = "l4"]
      /\ UNCHANGED << l, h2, h, done1, done2, T_start, t_prime, out >>

l2 == /\ pc[1] = "l2"
      /\ turn = 1
      /\ h2' = 2 * h2 + l
      /\ t' = t + 1
      /\ turn' = IF ~done2 THEN 2 ELSE 1
      /\ pc' = [pc EXCEPT ![1] = "l3"]
      /\ UNCHANGED << l, h, done1, done2, T_start, t_prime, out >>

l3 == /\ pc[1] = "l3"
      /\ turn = 1
      /\ TRUE
      /\ t' = t + 1
      /\ turn' = IF ~done2 THEN 2 ELSE 1
      /\ pc' = [pc EXCEPT ![1] = "l5"]
      /\ UNCHANGED << l, h2, h, done1, done2, T_start, t_prime, out >>

l4 == /\ pc[1] = "l4"
      /\ turn = 1
      /\ TRUE
      /\ t' = t + 1
      /\ turn' = IF ~done2 THEN 2 ELSE 1
      /\ pc' = [pc EXCEPT ![1] = "l5"]
      /\ UNCHANGED << l, h2, h, done1, done2, T_start, t_prime, out >>

l5 == /\ pc[1] = "l5"
      /\ turn = 1
      /\ l' = 1
      /\ out' = Append(out, "1")
      /\ t' = t + 1
      /\ turn' = IF ~done2 THEN 2 ELSE 1
      /\ pc' = [pc EXCEPT ![1] = "l_exit"]
      /\ UNCHANGED << h2, h, done1, done2, T_start, t_prime >>

l_exit == /\ pc[1] = "l_exit"
          /\ turn = 1
          /\ done1' = TRUE
          /\ t' = t + 1
          /\ IF done2
                THEN /\ t_prime' = t'
                     /\ out' = Append(out, "END")
                ELSE /\ TRUE
                     /\ UNCHANGED << t_prime, out >>
          /\ turn' = 2
          /\ pc' = [pc EXCEPT ![1] = "Done"]
          /\ UNCHANGED << l, h2, h, done2, T_start >>

T1 == l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l_exit

m1 == /\ pc[2] = "m1"
      /\ turn = 2
      /\ TRUE
      /\ t' = t + 1
      /\ turn' = IF ~done1 THEN 1 ELSE 2
      /\ pc' = [pc EXCEPT ![2] = "m2"]
      /\ UNCHANGED << l, h2, h, done1, done2, T_start, t_prime, out >>

m2 == /\ pc[2] = "m2"
      /\ turn = 2
      /\ TRUE
      /\ t' = t + 1
      /\ turn' = IF ~done1 THEN 1 ELSE 2
      /\ pc' = [pc EXCEPT ![2] = "m3"]
      /\ UNCHANGED << l, h2, h, done1, done2, T_start, t_prime, out >>

m3 == /\ pc[2] = "m3"
      /\ turn = 2
      /\ l' = 0
      /\ out' = Append(out, "0")
      /\ t' = t + 1
      /\ turn' = IF ~done1 THEN 1 ELSE 2
      /\ pc' = [pc EXCEPT ![2] = "m_exit"]
      /\ UNCHANGED << h2, h, done1, done2, T_start, t_prime >>

m_exit == /\ pc[2] = "m_exit"
          /\ turn = 2
          /\ done2' = TRUE
          /\ t' = t + 1
          /\ IF done1
                THEN /\ t_prime' = t'
                     /\ out' = Append(out, "END")
                ELSE /\ TRUE
                     /\ UNCHANGED << t_prime, out >>
          /\ turn' = 1
          /\ pc' = [pc EXCEPT ![2] = "Done"]
          /\ UNCHANGED << l, h2, h, done1, T_start >>

T2 == m1 \/ m2 \/ m3 \/ m_exit

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == T1 \/ T2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(* ============================================================================= *)
(* FUNCTIONAL LAYER *)
(* ============================================================================= *)

TypeOK ==
    /\ l \in {0, 1}
    /\ h2 \in Nat
    /\ h \in {0, 1}
    /\ turn \in {1, 2}
    /\ done1 \in BOOLEAN
    /\ done2 \in BOOLEAN
    /\ t \in Nat
    /\ T_start \in Nat
    /\ t_prime \in Nat
    /\ out \in Seq({"START", "END", "0", "1"})
    /\ pc[1] \in {"l1", "l2", "l3", "l4", "l5", "l_exit", "Done"}
    /\ pc[2] \in {"m1", "m2", "m3", "m_exit", "Done"}

Terminated == pc[1] = "Done" /\ pc[2] = "Done"

\* Functional correctness postcondition
FunctionalPost == Terminated => (h2 = 0 /\ done1 /\ done2)

(* ============================================================================= *)
(* OBSERVATION LAYER *)
(* ============================================================================= *)

Observed == Terminated
Delta    == t_prime - T_start

(* ============================================================================= *)
(* CALIBRATION (Execution time per secret state) *)
(* ============================================================================= *)

Calib0 == (Observed /\ h = 0) => Delta = Delta_lo
Calib1 == (Observed /\ h = 1) => Delta = Delta_hi

(* ============================================================================= *)
(* LEAKY ASSERTIONS (Attacker deductions - SOUND on InternalTiming) *)
(* ============================================================================= *)

\* Timing leaky assertions: elapsed execution time Delta uniquely determinizes secret h
LA_Time_Low  == (Observed /\ Delta <= Delta_lo) => h = 0
LA_Time_High == (Observed /\ Delta >= Delta_hi) => h = 1
LA_Timing    == Observed => ((Delta >= Delta_hi) <=> (h = 1))

(* ============================================================================= *)
(* SECURITY PROPERTIES (EXPECTED TO FAIL; counterexample = leak witness) *)
(* ============================================================================= *)

\* Timing noninterference / constant-time property (FAILS: h=0 gives 8, h=1 gives 9)
NoTimingLeak == Observed => (Delta = Delta_lo)
ConstantTime == Observed => (Delta = Delta_lo)

=============================================================================
