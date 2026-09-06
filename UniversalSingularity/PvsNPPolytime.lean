import Mathlib.Algebra.Polynomial.BigOperators
import UniversalSingularity.PvsNPReal

/-!
# P vs NP -- verified concrete facts about the polytime bounds

This module records *genuine, fully proved* (no `sorry`) closure properties of
the polynomial step-count predicate `PolytimeBound` defined in
`UniversalSingularity.PvsNPReal`, which the bridges `InP` / `InNP` / `InNP`
are built on.

Concretely proved here:

* `polytimeBound_add`, `polytimeBound_mul` : the pointwise sum and product of two
  polytime-bounded step counts are polytime-bounded;
* `polytimeBound_const` : every constant step-count is polytime-bounded;
* `polytimeBound_of_le` : polytime-boundedness is monotone in the step count.

These are the elementary size estimates one needs when proving, e.g., that a
machine `M` combined with a machine `N` runs within the sum of their budgets.
They do **not** settle P vs NP: whether `InP ⊆ InNP` (`p_subset_np_gap`) or
`InNP ⊄ InP` (`p_vs_np_gap`) remains open in `UniversalSingularity.PvsNPReal`.
Moreover the shipped Mathlib bundle has no olean for `Mathlib.Computability.Halting`
(and the `TM2ComputableInPolyTime.comp` composition lemma is `proof_wanted` in
this Mathlib version), so no undecidability or composition content is claimed here.
-/

namespace UniversalSingularity.PvsNPPolytime

/-- The pointwise **sum** of two polytime-bounded step counts is polytime-bounded. -/
theorem polytimeBound_add {f g : ℕ → ℕ} (hf : PvsNPReal.PolytimeBound f)
    (hg : PvsNPReal.PolytimeBound g) :
    PvsNPReal.PolytimeBound (fun n => f n + g n) := by
  rcases hf with ⟨p, hp⟩
  rcases hg with ⟨q, hq⟩
  refine ⟨p + q, ?_⟩
  intro n
  calc
    f n + g n ≤ p.eval n + q.eval n := Nat.add_le_add (hp n) (hq n)
    _ = (p + q).eval n := by rw [Polynomial.eval_add]

/-- The pointwise **product** of two polytime-bounded step counts is
polytime-bounded. -/
theorem polytimeBound_mul {f g : ℕ → ℕ} (hf : PvsNPReal.PolytimeBound f)
    (hg : PvsNPReal.PolytimeBound g) :
    PvsNPReal.PolytimeBound (fun n => f n * g n) := by
  rcases hf with ⟨p, hp⟩
  rcases hg with ⟨q, hq⟩
  refine ⟨p * q, ?_⟩
  intro n
  calc
    f n * g n ≤ p.eval n * q.eval n := Nat.mul_le_mul (hp n) (hq n)
    _ = (p * q).eval n := by rw [Polynomial.eval_mul]

/-- Every **constant** step count is polytime-bounded. -/
theorem polytimeBound_const (c : ℕ) : PvsNPReal.PolytimeBound (fun _ : ℕ => c) := by
  refine ⟨Polynomial.C c, ?_⟩
  intro n
  simp

/-- Polytime-boundedness is **monotone**: a step count no larger than a
polytime-bounded one is itself polytime-bounded. -/
theorem polytimeBound_of_le {f g : ℕ → ℕ} (hg : PvsNPReal.PolytimeBound g)
    (hfg : ∀ n, f n ≤ g n) : PvsNPReal.PolytimeBound f := by
  rcases hg with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro n
  exact le_trans (hfg n) (hp n)

end UniversalSingularity.PvsNPPolytime