# Verified Compiler in Lean 4

This repository contains a **Lean 4 reimplementation** of Xavier Leroy’s renowned course:

> [*Proving the Correctness of a Compiler*](https://xavierleroy.org/courses/EUTypes-2019/), Xavier Leroy, Collège de France and Inria Paris

The original course presents a formal verification of a simple compiler from a simple imperative language to a low-level stack-based machine, using the Rocq proof assistant. This Lean 4 project adapts and reimplements the course showcasing Lean’s capabilities for mechanized metatheory and program verification. In particular, we make use of the recenetly added (co)inductive predicates support, as well as experimental grind tactic.

---

## 🔍 Overview

This reimplementation covers the full structure of the original course:

- `Leroy/Imp.lean`: the source language and its semantics
- `Leroy/Compil.lean`: the compiler and its correctness proofs
- `Leroy/Constprop.lean`: constant propagation optimization
- `Leroy/Deadcode.lean`: dead code elimination via liveness analysis
- `Leroy/Fixpoints.lean`: fixpoints and static analysis
- `Leroy/Sequences.lean`: definitions and lemmas about sequences of transitions.
