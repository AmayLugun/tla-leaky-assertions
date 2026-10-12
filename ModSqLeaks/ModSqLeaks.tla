------------------------------ MODULE ModSqLeaks ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N, Y0, BITS, MulCost, SqCost, PrintCost, Fixed, Threshold
\* Threshold = number of 1-bits that separates "fast" from "slow" keys
ASSUME /\ N > 1 /\ N < 46340 /\ Y0 \in 0..(N - 1)
       /\ BITS > 0 /\ MulCost > 0 /\ SqCost > 0 /\ PrintCost > 0
       /\ Fixed \in BOOLEAN /\ Threshold \in 0..BITS

Bits == 0..(BITS - 1)
Zero == [j \in Bits |-> 0]
Ones == [j \in Bits |-> 1]
Alt  == [j \in Bits |-> (j + 1) % 2]
One  == [j \in Bits |-> IF j = 0 THEN 1 ELSE 0]
SecretSet == IF BITS <= 8 THEN [Bits -> {0, 1}] ELSE {Zero, Ones, Alt, One}

RECURSIVE SumTo(_, _)
SumTo(f, n) == IF n = 0 THEN 0 ELSE f[n-1] + SumTo(f, n-1)
HW(f) == SumTo(f, BITS)

RECURSIVE PowBits(_, _, _)
PowBits(b, f, j) ==
  IF j >= BITS THEN 1
  ELSE ((IF f[j] = 1 THEN b ELSE 1) * PowBits((b * b) % N, f, j + 1)) % N

RECURSIVE Pow2(_, _)
Pow2(b, m) == IF m = 0 THEN b ELSE Pow2((b * b) % N, m - 1)

IterFixed == 3 + SqCost                       \* l1(1)+l3(SqCost)+l4(1)+l5(1)
Base      == PrintCost + BITS * IterFixed     \* elapsed time with zero 1-bits
Delta_t   == Base + MulCost * Threshold       \* the paper's threshold

(* --algorithm ModExpLeak
variables
    K \in SecretSet,           \* secret key: TLC explores every key in the set
    k = K,                     \* working copy (shifted right each round)
    y = Y0,                    \* public base
    r = 1,                     \* result accumulator
    i = 0,                     \* loop counter
    t = 0,                     \* auxiliary global clock
    T_start = 0,               \* time T at entry public point (print START)
    t_prime = 0,               \* time t' at exit public point (print END)
    out = <<>>;                \* what the public observer sees

begin
  l0: T_start := t;                       \* record entry time T
      out := Append(out, "START");        \* print("START")
      t := t + PrintCost;
  l1: while i < BITS do
        t := t + 1;                       \* if (k % 2 == 1)  <- secret branch
        if Fixed \/ k[0] = 1 then
  l2:     r := IF k[0] = 1 THEN (r * y) % N ELSE r;   \* r = r*y % n
          t := t + MulCost;               \* extra time (every round if Fixed)
        end if;
  l3:   y := (y * y) % N;                 \* y = y*y % n
        t := t + SqCost;
  l4:   k := [j \in Bits |-> IF j + 1 < BITS THEN k[j + 1] ELSE 0];  \* k >>= 1
        t := t + 1;
  l5:   i := i + 1;                       \* i++ and loop test
        t := t + 1;
      end while;
  l6: t_prime := t;                       \* record exit time t'
      out := Append(out, "END");          \* print("END")
      t := t + PrintCost;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f40be59e" /\ chksum(tla) = "cd3f16dd")
VARIABLES pc, K, k, y, r, i, t, T_start, t_prime, out

vars == << pc, K, k, y, r, i, t, T_start, t_prime, out >>

Init == (* Global variables *)
        /\ K \in SecretSet
        /\ k = K
        /\ y = Y0
        /\ r = 1
        /\ i = 0
        /\ t = 0
        /\ T_start = 0
        /\ t_prime = 0
        /\ out = <<>>
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ T_start' = t
      /\ out' = Append(out, "START")
      /\ t' = t + PrintCost
      /\ pc' = "l1"
      /\ UNCHANGED << K, k, y, r, i, t_prime >>

l1 == /\ pc = "l1"
      /\ IF i < BITS
            THEN /\ t' = t + 1
                 /\ IF Fixed \/ k[0] = 1
                       THEN /\ pc' = "l2"
                       ELSE /\ pc' = "l3"
            ELSE /\ pc' = "l6"
                 /\ t' = t
      /\ UNCHANGED << K, k, y, r, i, T_start, t_prime, out >>

l3 == /\ pc = "l3"
      /\ y' = (y * y) % N
      /\ t' = t + SqCost
      /\ pc' = "l4"
      /\ UNCHANGED << K, k, r, i, T_start, t_prime, out >>

l4 == /\ pc = "l4"
      /\ k' = [j \in Bits |-> IF j + 1 < BITS THEN k[j + 1] ELSE 0]
      /\ t' = t + 1
      /\ pc' = "l5"
      /\ UNCHANGED << K, y, r, i, T_start, t_prime, out >>

l5 == /\ pc = "l5"
      /\ i' = i + 1
      /\ t' = t + 1
      /\ pc' = "l1"
      /\ UNCHANGED << K, k, y, r, T_start, t_prime, out >>

l2 == /\ pc = "l2"
      /\ r' = (IF k[0] = 1 THEN (r * y) % N ELSE r)
      /\ t' = t + MulCost
      /\ pc' = "l3"
      /\ UNCHANGED << K, k, y, i, T_start, t_prime, out >>

l6 == /\ pc = "l6"
      /\ t_prime' = t
      /\ out' = Append(out, "END")
      /\ t' = t + PrintCost
      /\ pc' = "Done"
      /\ UNCHANGED << K, k, y, r, i, T_start >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l3 \/ l4 \/ l5 \/ l2 \/ l6
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

Elapsed == t_prime - T_start
Finished == pc = "Done"

TypeOK ==
  /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","Done"}
  /\ i \in 0..BITS /\ r \in 0..(N - 1) /\ y \in 0..(N - 1) /\ t >= 0

\* Loop invariant, part A: r * y^k is conserved
FuncInv == pc \in {"l1","l6","Done"} =>
  (r * PowBits(y, k, 0)) % N = PowBits(Y0, K, 0)

\* Loop invariant, part B (strengthening): ties k and y to i and K
ShiftInv == pc \in {"l1","l6","Done"} =>
  /\ y = Pow2(Y0, i)
  /\ \A j \in Bits : k[j] = IF j + i < BITS THEN K[j + i] ELSE 0

LoopInv == FuncInv /\ ShiftInv
Correct == Finished => r = PowBits(Y0, K, 0)

TimeInv == pc \in {"l1","l6"} =>
  t = PrintCost + i * IterFixed
      + (IF Fixed THEN i * MulCost ELSE MulCost * SumTo(K, i))

\* Leaky assertion, in the paper's  [t' - T >= Delta_t  =>  h = ...]  shape
LeakyAssertion == (~Fixed /\ Finished) =>
  /\ (Elapsed >= Delta_t) <=> (HW(K) >= Threshold)    \* threshold form (Fig. 2)
  /\ HW(K) = (Elapsed - Base) \div MulCost            \* exact form

\* Security check: finish time must not depend on the secret.
\* Equivalent to the twin test against the all-zero key.
ExpectedTime == Base + (IF Fixed THEN BITS * MulCost ELSE 0)
ConstantTime == Finished => Elapsed = ExpectedTime

=============================================================================
