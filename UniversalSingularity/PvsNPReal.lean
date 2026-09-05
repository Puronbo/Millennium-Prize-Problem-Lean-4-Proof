import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Language
import Mathlib.Algebra.Polynomial.Basic

/-!
# P vs NP -- bridge skeleton (honest)

P vs NP is open; it is **not resolved here**. Mathlib has no complexity classes at all,
but it does provide the deterministic polynomial-time machinery: `TM2ComputableInPolyTime`
(a `TM2` Turing machine plus a polynomial time bound) and `Language α` (a set of finite
strings). This module lifts those genuine objects into definitions of **P** and **NP** for
binary decision problems, and marks the open content with `sorry` gaps.

The classes here are the standard ones on bit strings (`Word = List Bool`):

* **P**: a problem is in P when a deterministic polytime `TM2` decides it (outputs the
  boolean answer within `p(n)` steps, `p` polynomial in the input length).
* **NP**: a problem is in NP when every accepted word has a witness of polynomial length
  that a deterministic polytime verifier checks, with the pairing encoding `w ++ [false] ++ c`.

Everything above the lifted machinery is the honest bridge boundary.
-/

namespace UniversalSingularity.PvsNPReal

/-- Words over the binary alphabet. -/
abbrev Word := List Bool

/-- A decision problem: the language of accepted (finite) binary strings. -/
abbrev Problem := Language Bool

/-- A polynomial time bound: a step-count function bounded by a polynomial. -/
def PolytimeBound (time : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n : ℕ, time n ≤ p.eval n

/-- Deterministic polytime computability of a boolean decider, via Mathlib's
`Turing.TM2ComputableInPolyTime` with the identity encoding of bit strings. The structure
carries machine data, so existence is expressed as `Nonempty`. -/
def DTMComputableInPolyTime (f : Word → Bool) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime (ea := fun w : Word => w) (eb := fun b : Bool => [b]) f)

/-- **P**: decision problems with a deterministic polytime decider. -/
def InP (L : Problem) : Prop :=
  ∃ f : Word → Bool, DTMComputableInPolyTime f ∧ ∀ w : Word, w ∈ L ↔ f w = true

/-- Deterministic polytime computability of a verifier on pairs `(word, witness)`, using
the standard pairing encoding `w ++ [false] ++ c` of two bit strings. -/
def DTMVerifierInPolyTime (V : Word × Word → Bool) : Prop :=
  Nonempty
    (Turing.TM2ComputableInPolyTime
      (ea := fun wc : Word × Word => wc.1 ++ List.cons false wc.2) (eb := fun b : Bool => [b]) V)

/-- **NP**: decision problems whose accepted words have polynomially bounded witnesses
checked by a deterministic polytime verifier. -/
def InNP (L : Problem) : Prop :=
  ∃ (V : Word × Word → Bool) (bound : ℕ → ℕ),
    DTMVerifierInPolyTime V ∧ PolytimeBound bound ∧
    ∀ w : Word, w ∈ L ↔ ∃ c : Word, c.length ≤ bound w.length ∧ V (w, c) = true

/-- **Bridge gap (P ⊆ NP).** The inclusion is classically true; a formal proof (the
decider itself as a verifier ignoring the witness, plus the encoding facts) must be built
on the machinery above. -/
theorem p_subset_np_gap : ∀ L : Problem, InP L → InNP L := by
  sorry

/-- **Bridge gap (P ≠ NP).** Whether some problem verifiable in polynomial time is not
decidable in polynomial time. Proving this settles the Clay P vs NP question. -/
theorem p_vs_np_gap : ∃ L : Problem, InNP L ∧ ¬ InP L := by
  sorry

end UniversalSingularity.PvsNPReal