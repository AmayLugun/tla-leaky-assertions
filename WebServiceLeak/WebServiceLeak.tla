------------------------------ MODULE WebServiceLeak ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    LookupCost,      \* Time simulating database user lookup (e.g., 1)
    HashCost,        \* Time simulating cryptographic password hash (e.g., 10)
    Fixed,           \* Countermeasure toggle: FALSE = vulnerable, TRUE = dummy hash mitigation
    Threshold        \* Observer threshold to distinguish fast vs slow response (e.g., 5)

ASSUME /\ LookupCost > 0 
       /\ HashCost > 0 
       /\ Fixed \in BOOLEAN
       /\ Threshold > LookupCost /\ Threshold <= (LookupCost + HashCost)

(* --algorithm WebServerLogin
variables 
    \* The secrets the server is trying to protect
    valid_user \in {TRUE, FALSE}, 
    password_match \in {TRUE, FALSE},
    
    \* Publicly observable variables and auxiliary timing variables
    t = 0, 
    T_start = 0,        \* Time T recorded at l0 (entry public point)
    t_prime = 0,        \* Time t' recorded at l_exit (exit public point)
    out = << >>,        \* Public output channel observed by attacker
    result = "";

fair process LoginHandler = 1
begin
l0: \* Entry public point: HTTP request received
    T_start := t;
    out := Append(out, "REQ");

Lookup:
    \* Simulating the database lookup time
    t := t + LookupCost;
    
    if ~valid_user then
        if Fixed then
            \* Mitigation: compute dummy hash so execution time is balanced
            goto DummyHash;
        else
            \* Vulnerable path: skip hashing, go straight to error
            goto OutputError;
        end if;
    else
        goto HashPassword;
    end if;

HashPassword:
    \* Valid user path: compute cryptographic hash
    t := t + HashCost;
    
    if ~password_match then
        goto OutputError;
    else
        result := "success";
        goto l_exit;
    end if;

DummyHash:
    \* Constant-time countermeasure: compute dummy hash for non-existent user
    t := t + HashCost;
    goto OutputError;

OutputError:
    \* Both invalid users and invalid passwords return the exact same error message
    result := "error message";
    goto l_exit;

l_exit:
    \* Exit public point: HTTP response dispatched
    t_prime := t;
    out := Append(out, result);
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a417e2df" /\ chksum(tla) = "f48dc11a")
VARIABLES pc, valid_user, password_match, t, T_start, t_prime, out, result

vars == << pc, valid_user, password_match, t, T_start, t_prime, out, result >>

ProcSet == {1}

Init == (* Global variables *)
        /\ valid_user \in {TRUE, FALSE}
        /\ password_match \in {TRUE, FALSE}
        /\ t = 0
        /\ T_start = 0
        /\ t_prime = 0
        /\ out = << >>
        /\ result = ""
        /\ pc = [self \in ProcSet |-> "l0"]

l0 == /\ pc[1] = "l0"
      /\ T_start' = t
      /\ out' = Append(out, "REQ")
      /\ pc' = [pc EXCEPT ![1] = "Lookup"]
      /\ UNCHANGED << valid_user, password_match, t, t_prime, result >>

Lookup == /\ pc[1] = "Lookup"
          /\ t' = t + LookupCost
          /\ IF ~valid_user
                THEN /\ IF Fixed
                           THEN /\ pc' = [pc EXCEPT ![1] = "DummyHash"]
                           ELSE /\ pc' = [pc EXCEPT ![1] = "OutputError"]
                ELSE /\ pc' = [pc EXCEPT ![1] = "HashPassword"]
          /\ UNCHANGED << valid_user, password_match, T_start, t_prime, out, result >>

HashPassword == /\ pc[1] = "HashPassword"
                /\ t' = t + HashCost
                /\ IF ~password_match
                      THEN /\ pc' = [pc EXCEPT ![1] = "OutputError"]
                           /\ UNCHANGED result
                      ELSE /\ result' = "success"
                           /\ pc' = [pc EXCEPT ![1] = "l_exit"]
                /\ UNCHANGED << valid_user, password_match, T_start, t_prime, out >>

DummyHash == /\ pc[1] = "DummyHash"
             /\ t' = t + HashCost
             /\ pc' = [pc EXCEPT ![1] = "OutputError"]
             /\ UNCHANGED << valid_user, password_match, T_start, t_prime, out, result >>

OutputError == /\ pc[1] = "OutputError"
               /\ result' = "error message"
               /\ pc' = [pc EXCEPT ![1] = "l_exit"]
               /\ UNCHANGED << valid_user, password_match, t, T_start, t_prime, out >>

l_exit == /\ pc[1] = "l_exit"
          /\ t_prime' = t
          /\ out' = Append(out, result)
          /\ pc' = [pc EXCEPT ![1] = "Done"]
          /\ UNCHANGED << valid_user, password_match, t, T_start, result >>

LoginHandler == l0 \/ Lookup \/ HashPassword \/ DummyHash \/ OutputError \/ l_exit

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == LoginHandler
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(* ============================================================================= *)
(* FUNCTIONAL LAYER *)
(* ============================================================================= *)

Terminated == pc[1] = "Done"
Observed   == Terminated
Delta      == t_prime - T_start
Elapsed    == Delta

TypeOK ==
    /\ valid_user \in BOOLEAN
    /\ password_match \in BOOLEAN
    /\ t \in Nat
    /\ T_start \in Nat
    /\ t_prime \in Nat
    /\ result \in {"", "success", "error message"}
    /\ out \in Seq({"REQ", "success", "error message"})
    /\ pc[1] \in {"l0", "Lookup", "HashPassword", "DummyHash", "OutputError", "l_exit", "Done"}

\* Functional correctness postcondition
FunctionalCorrect == Observed =>
    (result = "success" <=> (valid_user /\ password_match))

FunctionalPost == FunctionalCorrect

(* ============================================================================= *)
(* OBSERVATION & AUXILIARY TIME LAYER (Paper Section IV.A & Definition 2)       *)
(* 1. Public Entry Statement at l0: records T_start := t, emits out = <<"REQ">>  *)
(* 2. Public Exit Statement at l_exit: records t_prime := t, emits out = Append   *)
(* 3. Auxiliary Elapsed Time: Delta == t_prime - T_start                        *)
(* ============================================================================= *)

\* Canonical secret h representation (h = 1 represents valid user existence)
h == IF valid_user THEN 1 ELSE 0

\* Calibration constants for fast (h = 0, invalid user) vs slow (h = 1, valid user) paths
Delta_lo == LookupCost
Delta_hi == LookupCost + HashCost

\* Public statement references
PublicIn  == out[1]             \* "REQ" emitted at entry public point l0
PublicOut == out[Len(out)]      \* result ("error message" / "success") emitted at exit l_exit

(* ============================================================================= *)
(* CALIBRATION (Execution time per secret state)                                 *)
(* ============================================================================= *)

Calib0 == (~Fixed /\ Observed /\ result = "error message" /\ h = 0) => Delta = Delta_lo
Calib1 == (~Fixed /\ Observed /\ result = "error message" /\ h = 1) => Delta = Delta_hi

(* ============================================================================= *)
(* LEAKY ASSERTIONS AT PUBLIC CONTROL POINTS (Paper Definition 2 & Section IV.A) *)
(* In the paper (Page 33):                                                       *)
(*   [at l0]: t = T_start /\ [at l_exit]: t = t_prime /\ t' - T < Delta_t => h=0 *)
(*   [at l0]: t = T_start /\ [at l_exit]: t = t_prime /\ t' - T >= Delta_t => h=1*)
(* ============================================================================= *)

\* Leaky assertions evaluated at exit public statement l_exit:
LA_Time_Low    == (~Fixed /\ Observed /\ PublicOut = "error message" /\ Delta <= Delta_lo)  => (h = 0)
LA_Time_High   == (~Fixed /\ Observed /\ PublicOut = "error message" /\ Delta >= Delta_hi)  => (h = 1)
LA_InvalidUser == (~Fixed /\ Observed /\ PublicOut = "error message" /\ Delta < Threshold)   => (h = 0)
LA_ValidUser   == (~Fixed /\ Observed /\ PublicOut = "error message" /\ Delta >= Threshold)  => (h = 1)

\* Canonical leaky assertion in the paper's equivalence format:
LA_Timing == (~Fixed /\ Observed /\ PublicOut = "error message") =>
    ((Delta >= Threshold) <=> (h = 1))

LeakyAssertion == (~Fixed /\ Observed /\ PublicOut = "error message") =>
    /\ (Delta >= Threshold <=> (h = 1))
    /\ (Delta < Threshold  <=> (h = 0))

(* ============================================================================= *)
(* SECURITY PROPERTIES (EXPECTED TO FAIL under vulnerable mode Fixed = FALSE) *)
(* ============================================================================= *)

ExpectedErrorTime == LookupCost + HashCost

\* Non-interference: Error response time must be invariant to user validity
NoTimingLeak == (Observed /\ result = "error message") => (Delta = ExpectedErrorTime)

\* Constant-time execution across all requests
ConstantTime == Observed => (Delta = ExpectedErrorTime)

=============================================================================