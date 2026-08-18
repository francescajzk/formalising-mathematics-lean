# Formalising Mathematics in Lean

A collection of formal proof projects completed as part of the
Formalising Mathematics course in the MSc Applied Mathematics programme
at Imperial College London

The projects use Lean 4 and Mathlib to formalise results from number
theory, real analysis, and combinatorial game theory.

## Projects

### 1. Bouton's Theorem for Nim

Formalisation of the game of Nim and Bouton's characterisation of
winning and losing positions.

The development includes:
- representation of Nim positions and legal moves
- recursive definitions of winning and losing positions
- nim-sums using bitwise XOR
- proof that every move from a zero nim-sum position has non-zero nim-sum
- construction of a move from any non-zero nim-sum position to one with
  zero nim-sum
- proof of Bouton's theorem: `LosingPos p ↔ NimSum p = 0`

**File:** `Projects/nim.lean`

---

### 2. Intermediate Value Theorem

A formal proof of the Intermediate Value Theorem using the supremum
construction.

The project defines continuity directly using the ε–δ definition and
proves the supporting results required for the argument.

It concludes by deriving Bolzano's theorem as a corollary.

**File:** `Projects/intermediate_value_theorem.lean`

---

### 3. Modular Cancellation

Formalisation of the modular cancellation theorem from elementary
number theory.

The project defines modular congruence and the greatest common divisor,
develops the required coprimality results, and applies Euclid's lemma to
prove the cancellation result.

**File:** `Projects/modular_cancellation.lean`
