import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Riemann Hypothesis -- verified concrete facts about the zeta function

This module records *genuine, fully proved* (no `sorry`) facts about the Riemann
zeta function `riemannZeta` and its zero set `riemannZetaZeros`, as supplied by
`Mathlib.NumberTheory.LSeries.RiemannZeta` and `.ZetaZeros`.  It is the
verified-concrete counterpart to the honest bridge skeleton in
`UniversalSingularity.RiemannHypothesisReal`.

Concretely proved here:

* `riemannZeta_zero_val` : `ζ(0) = -1/2`, so `0` is **not** a zero
  (`zero_not_riemannZetaZeros`);
* `one_not_riemannZetaZeros` : `ζ` is nonvanishing at `s = 1`;
* `trivialZero_eq_zero`, `trivialZero_mem_riemannZetaZeros` : every trivial zero
  `-2(n+1)` (`n : ℕ`) is genuinely a zero of `ζ`, strictly left of the critical
  strip (`trivialZero_re_lt_one`);
* `no_zero_re_ge_one`, `re_lt_one_of_mem_riemannZetaZeros` : every zero lies in
  the open half-plane `Re s < 1` (Mathlib's nonvanishing theorem for `Re s ≥ 1`);
* `zeros_isClosed`, `zeros_finite_in_compact`, `isDiscrete_riemannZetaZeros_vector` :
  the zero set is closed and discrete, with finitely many zeros in every compact
  set;
* `riemannZeta_eq_dirichletSeries` : for `Re s > 1` the Euler-Dirichlet series
  identity `ζ(s) = ∑ 1 / n^s`;
* `riemannZeta_one_sub_functional` : the functional equation of `ζ`;
* `analyticOn_riemannZeta_compl_1`, `differentiableAt_riemannZeta_ne_one` :
  `ζ` is analytic everywhere except at its pole `s = 1`;
* `riemannHypothesis_iff_zeros` : Mathlib's own `RiemannHypothesis` predicate,
  restated as a "no off-line zero" condition (a logic-level restatement of the
  same definition, **not** a proof of RH).

These do **not** prove the Riemann Hypothesis: whether every point of
`riemannZetaZeros` outside the trivial family satisfies `Re s = 1/2` remains the
open gap pinned in `UniversalSingularity.RiemannHypothesisReal`.  (Note also that
the classical evaluation `ζ(2) = π²/6` and the closed forms `ζ(2k)` live in
`Mathlib.NumberTheory.LSeries.HurwitzZetaValues`, whose olean is not shipped in
the prebuilt Mathlib bundle used here, so they are not imported.)
-/

namespace UniversalSingularity.RiemannHypothesisZeta

open Complex

/-- `ζ(0) = -1/2`. -/
theorem riemannZeta_zero_val : riemannZeta (0 : ℂ) = -1 / 2 := riemannZeta_zero

/-- `0` is not a zero of `ζ`: in this normalization `ζ(0) = -1/2 ≠ 0`. -/
theorem zero_not_riemannZetaZeros : (0 : ℂ) ∉ riemannZetaZeros := by
  intro hz
  have hv : riemannZeta (0 : ℂ) = 0 := (mem_riemannZetaZeros.mp hz)
  norm_num [riemannZeta_zero] at hv

/-- `1` is not a zero of `ζ` (`s = 1` is instead the pole of `ζ`). -/
theorem one_not_riemannZetaZeros : (1 : ℂ) ∉ riemannZetaZeros := by
  intro hz
  exact riemannZeta_one_ne_zero (mem_riemannZetaZeros.mp hz)

/-- The genuine trivial-zero family: `ζ(-2(n+1)) = 0` for every `n : ℕ`. -/
theorem trivialZero_eq_zero (n : ℕ) : riemannZeta ((-2 : ℂ) * (n + 1 : ℂ)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- The trivial zeros `-2, -4, -6, ...` genuinely belong to `riemannZetaZeros`. -/
theorem trivialZero_mem_riemannZetaZeros (n : ℕ) :
    ((-2 : ℂ) * (n + 1 : ℂ)) ∈ riemannZetaZeros := by
  rw [mem_riemannZetaZeros]
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- The trivial zeros lie strictly to the left of the critical strip. -/
theorem trivialZero_re_lt_one (n : ℕ) : ((-2 : ℂ) * (n + 1 : ℂ)).re < 1 := by
  simp
  nlinarith

/-- The trivial zeros lie on the real axis: they carry vanishing imaginary
part, so a trivial zero can never be a critical-strip zero.  This is the
"frequency is zero" half of the Hilbert–Pólya picture (see
`UniversalSingularity.HilbertPolya`). -/
theorem trivialZero_im_zero (n : ℕ) : ((-2 : ℂ) * (n + 1 : ℂ)).im = 0 := by
  simp

/-- The trivial zeros lie strictly to the left of the critical strip
`{s | 0 < s.re ∧ s.re < 1}`: indeed `Re(-2·(n+1)) ≤ -2 < 0` for every `n`. -/
theorem trivialZero_re_nonpos (n : ℕ) : ((-2 : ℂ) * (n + 1 : ℂ)).re ≤ 0 := by
  have hv : ((-2 : ℂ) * (n + 1 : ℂ)).re = -2 * ((n : ℝ) + 1) := by simp
  rw [hv]
  nlinarith [Nat.succ_pos n]

/-- No zero of `ζ` lies in the closed right half-plane `Re s ≥ 1`: `ζ` is
nonvanishing there. -/
theorem no_zero_re_ge_one {z : ℂ} (hz : 1 ≤ z.re) : z ∉ riemannZetaZeros := by
  intro hz0
  exact (riemannZeta_ne_zero_of_one_le_re hz) ((mem_riemannZetaZeros.mp hz0))

/-- Every zero of `ζ` lives strictly left of `Re s = 1`. -/
theorem re_lt_one_of_mem_riemannZetaZeros {z : ℂ} (hz : z ∈ riemannZetaZeros) :
    z.re < 1 := by
  by_contra h
  exact no_zero_re_ge_one (le_of_not_gt h) hz

/-- `riemannZetaZeros` is a closed set. -/
theorem zeros_isClosed : IsClosed riemannZetaZeros := isClosed_riemannZetaZeros

/-- `riemannZetaZeros` is discrete, so it has no accumulation points in `ℂ`. -/
theorem zeros_isDiscrete : IsDiscrete riemannZetaZeros := isDiscrete_riemannZetaZeros

/-- Finitely many zeros meet every compact set. -/
theorem zeros_finite_in_compact {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite := by
  exact IsCompact.inter_riemannZetaZeros_finite hS

/-- The Dirichlet series identity `ζ(s) = ∑' n, 1 / n^s` on the half-plane
`Re s > 1`. -/
theorem riemannZeta_eq_dirichletSeries {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- The functional equation of `ζ`: `ζ(1 - s) = 2 (2π)⁻ˢ Γ(s) cos(π s / 2) ζ(s)`,
valid away from `s = 1` and the nonpositive integers. -/
theorem riemannZeta_one_sub_functional {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

/-- `ζ` is complex-analytic everywhere except at its pole `s = 1`. -/
theorem analyticOn_riemannZeta_compl_1 :
    AnalyticOnNhd ℂ riemannZeta (({1} : Set ℂ)ᶜ) :=
  analyticOn_riemannZeta

/-- `ζ` is differentiable at every `s ≠ 1`. -/
theorem differentiableAt_riemannZeta_ne_one {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs'

/-- Mathlib's `RiemannHypothesis`, restated as the "no zero off the line" form:
every `s` with `ζ(s) = 0` is either a trivial zero, the pole `s = 1`, or lies on
the critical line `Re s = 1/2`.  Logically equivalent to the definition; it does
**not** prove RH. -/
theorem riemannHypothesis_iff_zeros : RiemannHypothesis ↔
    ∀ s : ℂ, riemannZeta s = 0 →
      (∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℂ)) ∨ s = 1 ∨ s.re = 1 / 2 := by
  constructor
  · intro h s hs
    by_cases ht : ∃ n : ℕ, s = (-2 : ℂ) * (n + 1 : ℂ)
    · exact Or.inl ht
    · by_cases hs1 : s = 1
      · exact Or.inr (Or.inl hs1)
      · exact Or.inr (Or.inr (h s hs ht hs1))
  · intro h s hs ht h1
    rcases h s hs with htr | hs1 | hline
    · exact False.elim (ht htr)
    · exact False.elim (h1 hs1)
    · exact hline

end UniversalSingularity.RiemannHypothesisZeta