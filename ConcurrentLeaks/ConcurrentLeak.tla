------------------------------ MODULE ConcurrentLeak ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Delta_lo,  \* observation faster than this  => attacker concludes h=0
          Delta_hi  \* observation at least this slow => attacker concludes h=1

(* --algorithm ConcurrentLeak

variables
    sem = 1,        \* Shared semaphore (initialized to 1)
    v = 0,          \* Shared variable v
    h \in {0, 1},   \* Secret variable (TLC explores both h=0 and h=1)
    t = 0,          \* Auxiliary global clock variable
    T_start = 0,    \* Time T recorded at l0 (entry public point)
    t_prime = 0,    \* Time t' recorded at l7 (exit public point)
    out = << >>;    \* public output channel

\* Process T1 = 1 Left box of Figure 1
process T1 = 1
begin
    T1_1: await sem > 0;
          sem := sem - 1;
          t := t + 1;
    T1_2: out := Append (out, "a"); \* Simulating print('a')
          t := t + 1;
    T1_3: v := v + 1;
          t := t + 1;
    T1_4: out := Append (out, "b"); \* Simulating print('b')
          t := t + 1; 
    T1_5: sem := sem + 1;
          t := t + 1;
end process;

\* Process T2 (Right box / Figure 2 with auxiliary time variables)
process T2 = 2
begin
    l0: T_start := t; \* Record entry time T at print('c')
        out := Append(out, "c"); \* Executing print('c')
        t := t + 1;   
    l1: if h = 1 then
    l2:     await sem > 0;
            sem := sem - 1;
            t := t + 1;
    l4:     v := v + 2;
            t := t + 1;
    l5:     sem := sem + 1;
            t := t + 1;
        else
    l6:     skip;     \* Path when h = 0
            t := t + 1;
        end if;
    l7: t_prime := t; \* Record exit time t' right before print('d')
        out := Append(out, "d"); \* Executing print('d')
        t := t + 1;   
end process;  
    
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e1a62806" /\ chksum(tla) = "610d2fe0")
VARIABLES pc, sem, v, h, t, T_start, t_prime, out

vars == << pc, sem, v, h, t, T_start, t_prime, out >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ sem = 1
        /\ v = 0
        /\ h \in {0, 1}
        /\ t = 0
        /\ T_start = 0
        /\ t_prime = 0
        /\ out = << >>
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "T1_1"
                                        [] self = 2 -> "l0"]

T1_1 == /\ pc[1] = "T1_1"
        /\ sem > 0
        /\ sem' = sem - 1
        /\ t' = t + 1
        /\ pc' = [pc EXCEPT ![1] = "T1_2"]
        /\ UNCHANGED << v, h, T_start, t_prime, out >>

T1_2 == /\ pc[1] = "T1_2"
        /\ out' = Append (out, "a")
        /\ t' = t + 1
        /\ pc' = [pc EXCEPT ![1] = "T1_3"]
        /\ UNCHANGED << sem, v, h, T_start, t_prime >>

T1_3 == /\ pc[1] = "T1_3"
        /\ v' = v + 1
        /\ t' = t + 1
        /\ pc' = [pc EXCEPT ![1] = "T1_4"]
        /\ UNCHANGED << sem, h, T_start, t_prime, out >>

T1_4 == /\ pc[1] = "T1_4"
        /\ out' = Append (out, "b")
        /\ t' = t + 1
        /\ pc' = [pc EXCEPT ![1] = "T1_5"]
        /\ UNCHANGED << sem, v, h, T_start, t_prime >>

T1_5 == /\ pc[1] = "T1_5"
        /\ sem' = sem + 1
        /\ t' = t + 1
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << v, h, T_start, t_prime, out >>

T1 == T1_1 \/ T1_2 \/ T1_3 \/ T1_4 \/ T1_5

l0 == /\ pc[2] = "l0"
      /\ T_start' = t
      /\ out' = Append(out, "c")
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "l1"]
      /\ UNCHANGED << sem, v, h, t_prime >>

l1 == /\ pc[2] = "l1"
      /\ IF h = 1
            THEN /\ pc' = [pc EXCEPT ![2] = "l2"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "l6"]
      /\ UNCHANGED << sem, v, h, t, T_start, t_prime, out >>

l2 == /\ pc[2] = "l2"
      /\ sem > 0
      /\ sem' = sem - 1
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "l4"]
      /\ UNCHANGED << v, h, T_start, t_prime, out >>

l4 == /\ pc[2] = "l4"
      /\ v' = v + 2
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "l5"]
      /\ UNCHANGED << sem, h, T_start, t_prime, out >>

l5 == /\ pc[2] = "l5"
      /\ sem' = sem + 1
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "l7"]
      /\ UNCHANGED << v, h, T_start, t_prime, out >>

l6 == /\ pc[2] = "l6"
      /\ TRUE
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "l7"]
      /\ UNCHANGED << sem, v, h, T_start, t_prime, out >>

l7 == /\ pc[2] = "l7"
      /\ t_prime' = t
      /\ out' = Append(out, "d")
      /\ t' = t + 1
      /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << sem, v, h, T_start >>

T2 == l0 \/ l1 \/ l2 \/ l4 \/ l5 \/ l6 \/ l7

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == T1 \/ T2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(* FUNTIONAL LAYER *)
T1Crit == {"T1_2", "T1_3", "T1_4", "T1_5"} \* T1 holds semaphore for 4 units of time
T2Crit == {"l4", "l5"} \* T2 holds semaphore for 2 units of time

TypeOK ==
    /\ sem \in {0, 1}
    /\ v \in Nat
    /\ h \in {0, 1}
    /\ t \in Nat
    /\ T_start \in Nat
    /\ t_prime \in Nat
    /\ out \in Seq ({"a","b","c","d"})

\*Global Invariant I : semaphore  = 1 mius number of holder (=> mutual exclusion)
(* If both the threads held a semaphore the sum would be sem + 2 = 1, forcing sem = -1, which is impossible because await sem > 0  guards every decreament.
 At most one thread is ever in the critical region. *)
 GlobalInv ==  sem + (IF pc[1] \in T1Crit THEN  1 ELSE 0)
                   + (IF pc[2] \in T2Crit THEN  1 ELSE 0) = 1 

(* Functional Specification:
  * {P} T1 || T2 {Q} : checks that
  * if initially sem=1, v=0, we end up in a state where:
  *   - termination has occurred (both threads done),
  *   - 'v' equals 1 + 2*h (correct value based on secret),
  *   - semaphore is back to 1 (released for reuse).
  * TLC verifies this using the functional postcondition FunctionalPost. *)

Terminated == (pc[1] = "Done" /\ pc[2] = "Done")
FunctionalPost == Terminated => (v = 1 + 2*h /\ sem = 1 ) \* {P} T1||T2 {Q}

(* OBSERVATION LAYER *)

Observed == pc[2] = "Done" \* both public points l0 and l7 are "Done"
Delta == t_prime - T_start \* what timing observer measures

Pos(x) == IF \E i \in 1..Len(out) : out[i] = x THEN 
             CHOOSE i \in 1..Len(out) : out[i] = x 
             ELSE Len(out) + 1


ACDB == Pos("a") < Pos("c") /\ Pos("c") < Pos("d") /\ Pos("d") < Pos("b")


(* LEAKY ASSERTIONS *)
LA_Low == (Observed /\ Delta < Delta_lo) => h = 0
LA_High == (Observed /\ Delta >= Delta_hi) => h = 1
LA_Trace == ACDB => h=0 \* the acdb leak


\* ---- Calibration: bounds on Delta per secret value (documents noise k) ----
Calib0 == (Observed /\ h = 0) => Delta \in 2..7   \* 2 own ticks + 0..5 ticks of T1
Calib1 == (Observed /\ h = 1) => Delta \in 4..9   \* 4 own ticks + 0..5 ticks of T1

\* ---- Security properties: EXPECTED TO FAIL; counterexample = leak witness --
NoTimingLeak == Observed => (Delta >= Delta_lo /\ Delta < Delta_hi)
NoOrderLeak  == ~ACDB


LA_Single == Observed => ((Delta < Delta_lo => h = 0) /\ (Delta >= Delta_lo => h = 1))
        
        
=============================================================================
