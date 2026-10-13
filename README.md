# TLA+ Leaky Assertions

Formal specifications and experiments in **TLA+** and **PlusCal** modeling timing side-channel leaks and leaky assertions, verified with the **TLC** model checker.

---

## 📂 Project Structure

```text
.
├── ConcurrentLeaks/
│   ├── ConcurrentLeak.tla     # PlusCal model for concurrent timing & execution order leaks
│   └── ConcurrentLeak.cfg     # TLC model configuration
├── InternalTiming/
│   ├── InternalTiming.tla     # PlusCal model for round-robin internal timing & execution time leaks
│   └── InternalTiming.cfg     # TLC model configuration
├── InternalTimingTransformed/
│   ├── Transformed.tla        # PlusCal model for branch-padding mitigation & constant-time execution
│   └── Transformed.cfg        # TLC model configuration
├── ModSqLeaks/
│   ├── ModSqLeaks.tla         # PlusCal model for modular exponentiation leaks & countermeasures
│   └── ModSqLeaks.cfg         # TLC model configuration
├── WebServiceLeak/
│   ├── WebServiceLeak.tla     # PlusCal model for web authentication timing leaks & dummy hash mitigation
│   └── WebServiceLeak.cfg     # TLC model configuration
├── SeqLock/
│   ├── SeqLock.tla            # PlusCal model for persistent memory leaks & cache flush mitigation
│   └── SeqLock.cfg            # TLC model configuration
├── .vscode/
│   ├── settings.json          # VS Code TLC settings & file nesting
│   └── tla.code-snippets      # Boilerplate snippets for TLA+, PlusCal & CFG
├── .gitignore                 # Ignores TLC states, .out logs, .old files, and OS artifacts
└── README.md
```

---

## 📑 Specifications

### 1. `ConcurrentLeaks`
* **File**: `ConcurrentLeaks/ConcurrentLeak.tla`
* **Concept**: Models two concurrent processes ($T_1$ and $T_2$) communicating via shared memory and a semaphore. Process $T_2$ conditionally executes a critical section based on a secret variable $h \in \{0, 1\}$.
* **Key Observations**:
  * **Timing Leak**: An observer measures elapsed time ($\Delta = t' - T_{\text{start}}$) between public entry and exit points to infer the value of $h$.
  * **Order Leak**: Execution traces where output events interleave in a specific order (such as sequence trace `acdb`) definitively leak the secret state.
* **Properties Verified**:
  * `FunctionalPost`: Verifies overall system functional correctness.
  * `NoTimingLeak` / `NoOrderLeak`: Security checks that fail in the presence of side channels, producing counterexample traces that illustrate the leak.

### 2. `ModSqLeaks`
* **File**: `ModSqLeaks/ModSqLeaks.tla`
* **Concept**: Models the square-and-multiply algorithm for modular exponentiation ($y^K \pmod N$).
* **Key Observations**:
  * **Variable-Time Execution (`Fixed = FALSE`)**: Branching on secret key bits introduces execution time variance directly proportional to the key's Hamming weight ($\text{HW}(K)$).
  * **Leaky Assertion**: Verifies that elapsed execution time allows an observer to reconstruct the secret key's Hamming weight or threshold.
  * **Constant-Time Countermeasure (`Fixed = TRUE`)**: Balances the execution paths by performing operations every round, ensuring constant-time execution (`ConstantTime` invariant holds).
* **Properties Verified**:
  * `Correct`: Algorithm produces correct mathematical exponentiation.
  * `LeakyAssertion`: Formalizes the relationship between elapsed time and the secret key.
  * `ConstantTime`: Verifies execution time is independent of secret key data.

### 3. `InternalTiming`
* **File**: `InternalTiming/InternalTiming.tla`
* **Concept**: Models two concurrent threads scheduled under a deterministic round-robin scheduler. Thread 1 conditionally branches based on secret $h \in \{0, 1\}$.
* **Key Observations**:
  * **Execution Time Difference**: Unbalanced branch execution in Thread 1 introduces total execution time variations ($\Delta = 8$ for $h = 0$ vs. $\Delta = 9$ for $h = 1$).
  * **Leaky Assertion**: Elapsed execution time $\Delta$ allows an observer to directly reconstruct secret $h$ using threshold condition ($\Delta \ge 9 \iff h = 1$).
* **Properties Verified**:
  * `FunctionalPost`: Verifies system functional correctness ($h_2 = 0$ and both threads terminated).
  * `Calib0` / `Calib1`: Calibration invariants confirming execution times per secret value ($\Delta = 8$ for $h = 0$, $\Delta = 9$ for $h = 1$).
  * `LA_Timing` / `LA_Time_Low` / `LA_Time_High`: Formal leaky assertions linking elapsed execution time directly to secret $h$.
  * `NoTimingLeak` / `ConstantTime`: Security checks that fail under TLC model checking, producing counterexample traces witnessing the timing leak.

### 4. `InternalTimingTransformed`
* **File**: `InternalTimingTransformed/Transformed.tla`
* **Concept**: Applies source-level branch padding (`l4_pad: skip`) to balance execution paths across secret branches, eliminating the round-robin internal timing covert channel.
* **Key Observations**:
  * **Timing Leak Mitigation**: Balances branch steps and scheduling turns, achieving constant-time execution ($\Delta = 9$ across both $h = 0$ and $h = 1$).
* **Properties Verified**:
  * `FunctionalPost`: Verifies system functional correctness ($h_2 = 0$ and both threads terminated).
  * `ConstantTime` / `NoTimingLeak`: Verifies elapsed execution time is invariant to secret data (passes).
  * `LA_Timing`: Leaky assertion is defeated / broken by mitigation.

### 5. `WebServiceLeak`
* **File**: `WebServiceLeak/WebServiceLeak.tla`
* **Concept**: Models a **web authentication service** login endpoint susceptible to user enumeration timing attacks, and its constant-time **dummy hash** countermeasure.
* **Key Observations**:
  * **Timing Side-Channel (`Fixed = FALSE`)**: For non-existent users (`valid_user = FALSE`), the server aborts early after database lookup `Lookup` ($\Delta = \text{LookupCost} = 1$). For existing users with invalid passwords (`valid_user = TRUE`), the server computes an expensive cryptographic hash at `HashPassword` before failing ($\Delta = \text{LookupCost} + \text{HashCost} = 11$). Even though both return the exact same generic `"error message"` at `OutputError`, the time difference leaks whether the username exists.
  * **Public Program Points**: Entry public point `l0` logs incoming request `"REQ"` and records $T_{\text{start}}$. Exit public point `l_exit` returns the HTTP response (`"success"` or `"error message"`) and records exit time $t_{\text{prime}}$.
  * **Leaky Assertions**: 
    * `LeakyAssertion` / `LA_Timing`: Formally proves that observing an error response with $\Delta \ge \text{Threshold}$ (where $\text{Threshold} = 5$) is logically equivalent to the secret $h = 1$ (`valid_user = TRUE`).
    * `LA_ValidUser` / `LA_InvalidUser`: Sound external observer deductions determinizing username existence.
  * **Constant-Time Mitigation (`Fixed = TRUE`)**: Computes a dummy hash for non-existent users (`DummyHash`), balancing error response time ($\Delta = 11$) so that `NoTimingLeak` and `ConstantTime` pass.
* **Properties Verified**:
  * `FunctionalCorrect` / `FunctionalPost`: Verifies authentication logic (success occurs if and only if both username and password match).
  * `Calib0` / `Calib1`: Calibration invariants confirming execution times per secret state ($\Delta = 1$ for non-existent user, $\Delta = 11$ for existing user).
  * `LA_Timing` / `LeakyAssertion`: Formally sound deductions by an external observer.
  * `NoTimingLeak` / `ConstantTime`: Fails under vulnerable mode (yielding leak witness counterexample) and passes under mitigated mode.

### 6. `SeqLock`
* **File**: `SeqLock/SeqLock.tla`
* **Concept**: Models the **Linux `seqlock` reader-writer mechanism** running on **Intel-x86 persistent memory (PM)** under potential power outages, based on *Smith (arXiv:2606.25422v1, 2026)*.
* **Key Observations**:
  * **Asynchronous Persistency Leak (`Fixed = FALSE`)**: Stores to $x_1$ (data), $x_2$ (classification tag: 1 = high, 0 = low), and $c$ (sequence counter) reside on different cache lines. If $x_1$ and final even $c$ persist to PM while $x_2$ lags in volatile buffers before a power outage, rebooting from PM leaves an inconsistent state ($c$ even, $x_2 = 0$, but $x_1$ holds the secret). The reader then reads and outputs the high secret over the public low channel.
  * **Persistent Guarantee**: The security guarantee $G \equiv (c \pmod 2 = 0 \implies (x_2 = 1 \iff x_1 = \text{high}))$ is violated post-crash in vulnerable mode.
  * **Cache Line Flush Mitigation (`Fixed = TRUE`)**: Enforces persistence order using `flush c` after the first store to $c$, and `flush x1; flush x2` before the final increment of $c$. Across all possible crash timings, $G$ is preserved and the reader never leaks the secret.
* **Properties Verified**:
  * `G_Guarantee`: Persistent memory consistency guarantee.
  * `NoInformationLeak`: Value-dependent non-interference property (fails when `Fixed = FALSE` witnessing the leak counterexample; passes when `Fixed = TRUE`).
  * `LA_PersistentLeak`: Sound Floyd-Hoare leaky assertion confirming an external observer reading $1$ from the low output channel post-crash uniquely determines the secret $h = 1$.


---

## 🛠️ Prerequisites

1. **Java Runtime Environment (JRE)** (Java 11 or newer).
2. **VS Code / Antigravity IDE** with the [TLA+ Extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus).
   *(Alternatively: the standalone TLA+ Toolbox or `tla2tools.jar`)*.

---

## 🚀 How to Run Models

### In VS Code / Antigravity IDE (Recommended)

1. Open a specification file (e.g., `ConcurrentLeaks/ConcurrentLeak.tla` or `ModSqLeaks/ModSqLeaks.tla`).
2. Press `Cmd + Shift + P` (macOS) or `Ctrl + Shift + P` (Windows/Linux) and run:
   * **`TLA+: Check model with TLC`** (or press `F10`).
3. To re-translate PlusCal code after modifying algorithms:
   * Run **`TLA+: Translate PlusCal algorithm`**.

### From Command Line

Using `tla2tools.jar`:

```bash
# Check ConcurrentLeak
java -jar tla2tools.jar -config ConcurrentLeaks/ConcurrentLeak.cfg ConcurrentLeaks/ConcurrentLeak.tla

# Check ModSqLeaks
java -jar tla2tools.jar -config ModSqLeaks/ModSqLeaks.cfg ModSqLeaks/ModSqLeaks.tla

# Check InternalTiming
java -jar tla2tools.jar -config InternalTiming/InternalTiming.cfg InternalTiming/InternalTiming.tla

# Check InternalTimingTransformed
java -jar tla2tools.jar -config InternalTimingTransformed/Transformed.cfg InternalTimingTransformed/Transformed.tla

# Check WebServiceLeak
java -jar tla2tools.jar -config WebServiceLeak/WebServiceLeak.cfg WebServiceLeak/WebServiceLeak.tla

# Check SeqLock
java -jar tla2tools.jar -config SeqLock/SeqLock.cfg SeqLock/SeqLock.tla
```

---

## ⚡ Productivity Snippets

Built-in snippets are available in `.vscode/tla.code-snippets`:

| Prefix | File Type | Description |
| :--- | :--- | :--- |
| `tla` / `module` | `.tla` | Pure TLA+ specification boilerplate. |
| `pluscal` / `pcal` | `.tla` | PlusCal (C-syntax) algorithm template. |
| `cfg` / `tlc` | `.cfg` | Standard TLC configuration template. |
