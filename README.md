# Panama Canal Lock System Modeling and Verification (Promela / SPIN)

This repository contains formal models of a simplified **Panama Canal Lock System** created using the **Promela** modeling language and verified with the **SPIN model checker**.  
The project was developed for formal verification of concurrent systems and focuses on ensuring both **safety** and **liveness** properties.

---

## Overview

The Panama Canal Lock System allows ships to travel between sea levels by filling and emptying a series of locks. The modeled system represents:
- Ship movement through upper, middle, and lower chambers
- Water level transitions
- Mutual exclusion between lock operations
- Synchronization between ship entry, transit, and exit

The primary goals of this model were:
- To validate **deadlock freedom**
- To ensure **mutual exclusion** between critical sections (e.g., gates and water operations)
- To simulate multiple concurrent ships moving safely through the lock system

---

## Files Included

- `lock_env.pml`:  
  Basic model of a single ship moving through the lock system, with gates and water level transitions.

- `lock_env_mult2.pml`:  
  Extended version supporting multiple concurrent ships. This model includes interleaved ship behavior and is used to test mutual exclusion and fairness.

---

## Key Verification Properties

### Safety
- No two gates or locks are active simultaneously in conflicting directions.
- Water level operations only happen when gates are properly closed.

### Liveness
- Every ship that enters the lock eventually exits.
- The system avoids deadlock or livelock under typical operation.

---

## SPIN Verification

Both models were verified using **SPIN**:

- **Simulation**:  
  Used to validate intended behavior manually via animations and message sequencing.

- **Model Checking**:  
  Exhaustive verification for properties like:
  - `assert` conditions (e.g., lock state consistency)
  - `never` claims for forbidden behavior
  - `ltl` properties for eventual outcomes

---

## How to Run

1. Install **SPIN**:  
   [SPIN Tool Website](http://spinroot.com/spin/whatispin.html)

2. From terminal or command line:

```bash
spin -a lock_env.pml
gcc -o panama_model pan.c
./panama_model
