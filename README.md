# TLA+ Leaky Assertions

Formal specifications and experiments in **TLA+** and **PlusCal** modeling timing side-channel leaks and leaky assertions, verified with the **TLC** model checker.

---

## 📂 Project Structure

```text
.
├── ConcurrentLeaks/
│   ├── ConcurrentLeak.tla     # PlusCal model for concurrent timing & execution order leaks
│   └── ConcurrentLeak.cfg     # TLC model configuration
├── ModSqLeaks/
│   ├── ModSqLeaks.tla         # PlusCal model for modular exponentiation leaks & countermeasures
│   └── ModSqLeaks.cfg         # TLC model configuration
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
```

---

## ⚡ Productivity Snippets

Built-in snippets are available in `.vscode/tla.code-snippets`:

| Prefix | File Type | Description |
| :--- | :--- | :--- |
| `tla` / `module` | `.tla` | Pure TLA+ specification boilerplate. |
| `pluscal` / `pcal` | `.tla` | PlusCal (C-syntax) algorithm template. |
| `cfg` / `tlc` | `.cfg` | Standard TLC configuration template. |
