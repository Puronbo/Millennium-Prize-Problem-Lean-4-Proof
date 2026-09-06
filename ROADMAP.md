# Roadmap: from heuristic Q-model to real proofs

This file records the **evidence-based** state of each Millennium Prize Problem:
what Mathlib already formalizes, what is missing, and the exact milestones to
bridge each heuristic `Q` in this repo to a genuine statement/proof.

**Ground truth:** Mathlib is pinned at `leanprover/lean4:v4.33.1` (see
`lean-toolchain`). All "present/absent" claims below were verified by inspecting
files under `.lake/packages/mathlib/Mathlib`.

Legend: **LIVE** = usable infrastructure exists · **GAP** = missing dependency ·
**OPEN** = mathematically unsolved (Lean cannot supply the conclusion).

---

## Where the repo stands

- `UniversalSingularity/*.lean` — 7 heuristic `Q` models. Each proves only
  `GodForceProp a ↔ Q a = 1` (trichotomy of `≤`). No Millennium statement is
  proved.
- `UniversalSingularity/RiemannHypothesisReal.lean` — states RH on the
  genuine `riemannZetaZeros` + `riemannZeta`; 3 `gap` theorems marked `sorry`.
- `UniversalSingularity/BSDReal.lean` — states BSD on the genuine
  `WeierstrassCurve ℚ` + `WeierstrassCurve.LSeries`; 1 `gap` theorem marked `sorry`.
- `UniversalSingularity/BSD37a1.lean` — **new**: fully proved concrete
  arithmetic on the rank-one curve `37a1` (`y² + y = x³ − x`): `Δ = 37`, the
  twenty-seven nonsingular rational points `P`, `2P, ..., 27P`, `-P`, `-2P`,
  `-3P`, and `-4P`, ..., `-9P`, all explicitly integer multiples `(m : ℤ) • p`
  of the generator `P` for `-9 ≤ m ≤ 27` (the multiples `10P = (161/16, -2065/64)`
  through `27P` computed as chord sums `(n-1)P + P`), the pairwise distinctness
  (kernel-checked via `norm_num`) of the symmetric family `{0, ±P, ..., ±9P}` of
  nineteen elements and of `{0, 10P, ..., 18P}` of ten elements, the group
  relations (`2T = X`, independent `3T = 9P`, inverse pairs, more direct pair
  checks), the no-torsion forms `(n : ℕ) • p ≠ 0` and `(n : ℤ) • p ≠ 0` for
  `2 ≤ |n| ≤ 27`, the small-order no-torsion certificates for each named
  multiple `2P` through `9P` (e.g. `(n : ℕ) • (2P) = (2n : ℕ) • P ≠ 0` for
  `n ≤ 9`), and the quantified certificates `not_nsmul_p_torsion_le_27`,
  `nsmul_p_injective_le_27` and `nsmul_p_ne_zsmul_neg`. Together these give
  `2 ≤ n ≤ 27` non-torsion of `P` and the **twenty-eight** pairwise-distinct
  group elements `0`, `±P, ..., ±9P`, `10P, ..., 18P`. **Zero `sorry`s** — the
  first fully proved module in the repo. Does not prove BSD itself.
- `UniversalSingularity/HilbertPolya.lean` — states the Hilbert–Pólya
  conjecture on genuine spectral theory, plus the Riemann–von Mangoldt and
  Montgomery–Odlyzko bridge gaps; 3 `gap` theorems marked `sorry`.
- `UniversalSingularity/PoincareConjectureReal.lean` — **new**: states the
  topological and smooth 3D Poincaré conjecture on genuine manifold objects;
  topologial and smooth gaps, 2 `sorry`s.
- `UniversalSingularity/PvsNPReal.lean` — **new**: defines the classes **P**
  and **NP** on `Language Bool` from Mathlib's `Turing.TM2ComputableInPolyTime`;
  `P ≠ NP` gap, 2 `sorry`s.
- `UniversalSingularity/YangMillsReal.lean`, `NavierStokesReal.lean`,
  `HodgeConjectureReal.lean` — **new**: pin the Clay claims as documented
  placeholder bridges (Mathlib lacks gauge / PDE / Hodge machinery); 1 `sorry` each.
- `UniversalSingularity/RiemannHypothesisZeta.lean` — **new, fully proved**
  (`0` `sorry`s): the concrete zeta layer — `ζ(0) = -1/2` (so `0` is not a
  zero), nonvanishing at `s = 1` and on `Re s ≥ 1` (every zero has `Re z < 1`),
  the trivial-zero family `-2(n+1)` strictly left of the critical strip, zero
  set closed/discrete with finite intersection with every compact set, the
  Dirichlet series identity on `Re s > 1`, the functional equation, analyticity
  away from `s = 1`, and a logic-level restatement
  `riemannHypothesis_iff_zeros` of Mathlib's `RiemannHypothesis`.
- `UniversalSingularity/PoincareSphere.lean` — **new, fully proved** (`0`
  `sorry`s): `𝕊³ ⊆ ℝ⁴` is inhabited, path-connected, compact, and a smooth
  `C^∞` 3-manifold charted by `ℝ³`.
- `UniversalSingularity/YangMillsMilestone.lean` — **new, fully proved** (`0`
  `sorry`s): the Clay base `𝕊⁴ ⊆ ℝ⁵` is inhabited, path-connected, compact, and
  a smooth `C^∞` 4-manifold charted by `ℝ⁴`.
- `UniversalSingularity/PvsNPPolytime.lean` — **new, fully proved** (`0`
  `sorry`s): `PolytimeBound` is closed under pointwise `+`, pointwise `*`,
  constants, and monotone domination.
- `UniversalSingularity/BridgeIntegrity.lean` — **new, fully proved** (`0`
  `sorry`s): the Navier-Stokes and Yang-Mills placeholder skeletons visibly
  **fail** their pinned Clay statements (the `sorry` gaps are non-vacuous); the
  Hodge skeleton is deliberately **not** asserted (its stubs would make
  `HodgeConjecturePinned X` vacuously true).
- `UniversalSingularity/MassGap.lean` — the (heuristic) typeclass frame.

**Design note:** the `MassGapProblem` frame demands `Q massGapElement = 1`, but
the genuine RH/BSD parameters are naturally `0` at their distinguished points.
The two `*Real` modules therefore deliberately **do not** instantiate the
heuristic frame; they state the real mathematics directly. Keep the heuristic
models as pedagogy, but build the real proofs *outside* the MassGap frame.

---

## Per problem

### 1. Riemann Hypothesis — LIVE infra, OPEN conclusion

Present in Mathlib:
- `Mathlib.NumberTheory.LSeries.RiemannZeta` → `riemannZeta : ℂ → ℂ`,
  `completedRiemannZeta`, functional equation `completedRiemannZeta_one_sub`,
  `riemannZeta_zero`, `differentiableAt_riemannZeta`.
- `Mathlib.NumberTheory.LSeries.ZetaZeros` → `riemannZetaZeros : Set ℂ`,
  `mem_riemannZetaZeros`, `isClosed_riemannZetaZeros`, `isDiscrete_riemannZetaZeros`,
  local finiteness.

Milestones:
0. **DONE (concrete layer):** `UniversalSingularity/RiemannHypothesisZeta.lean`
   proves, with zero `sorry`s, the zeta-facts layer (values `ζ(0) = -1/2`
   non-zero, nonvanishing on `Re s ≥ 1`, trivial zeros `-2(n+1)`, Dirichlet
   series identity, functional equation, analyticity, closed/discrete zero set
   with finite intersection with every compact set) and a logic-level
   restatement `riemannHypothesis_iff_zeros` of Mathlib's `RiemannHypothesis`.
1. **LIVE ready:** classify nontrivial zeros wrt critical strip (`trivial_zero_gap` in
   `RiemannHypothesisReal.lean`). Needs a lemma that the real zeros
   `0, -1, -2, ...` are exactly the non-critical ones.
2. **GAP:** no Mathlib theorem that all zeros lie *on* `Re s = 1/2`. This *is* RH.
3. **OPEN:** proving `RiemannHypothesisFormal` (`∀ z ∈ genuineZerosZ, z.re = 1/2`)
   settles RH. Not provable by Lean alone.

Realistic near-term Lean: prove the **negation** of RH for a finite prefix via a
computational/Searle search, or formalize a classical `∃`/`∀` reformulation. Full
RH remains open.

#### 1b. Hilbert–Pólya bridge (spectral route to RH)

`UniversalSingularity/HilbertPolya.lean` concretizes the "shadow = imaginary
part, operator = real part" framing:

- **DONE (verified, 0 `sorry`s):** the "imaginary frequency axis" facts —
  `imaginaryAxis_eq_range_mul_I` (the imaginary axis *is* `I · ℝ`),
  `mul_I_re`/`mul_I_im` (`(I·γ).re = 0`, `(I·γ).im = γ`: pure frequencies carry
  no real part and their frequency is the height), `ext_mul_I_iff` (the
  frequency embedding is injective), `zero_height_from_trivial_zero` (the
  trivial zero `-2` realizes `0 ∈ zeroImagParts`), and the consistency check
  `hp_forces_height_zero` (a *real* spectrum under the pure-frequency encoding
  contains only the zero height — a genuine Hilbert-Pólya operator stores
  heights as **real** eigenvalues `γ`, not as points `I·γ`).
- `genuineZerosZ`, `zeroImagParts` — the zero *heights* (the statistical shadow).
- `HilbertPolyaConjecture` — **real Mathlib spectral theory**: a self-adjoint
  bounded operator on a Hilbert space whose spectrum is exactly
  `{ iγ | γ ∈ zeroImagParts }` (`IsSelfAdjoint`, `spectrum Complex A`).
  Self-adjointness forces the spectrum into `ℝ`, so any zero off the critical
  line would contribute a non-real height to the spectrum — a contradiction.
  This is precisely HP ⇒ RH.
- `riemannVonMangoldt` — **bridge gap**: `N(T) = (T/2π)log(T/2π) − T/2π + O(log T)`,
  the density-growth law ("gaps tighten with height").
- `montgomeryOdlyzko_bridge` — **bridge gap**: the two-point correlation of
  normalized heights matches the GUE sine kernel `1 − (sin πx/πx)²`.

Mathlib provides the spectral infrastructure (`Analysis.InnerProductSpace.Spectrum`,
`Algebra.Star.SelfAdjoint`, `Analysis.Matrix.Hermitian`). The HP operator is not
in Mathlib and HP itself remains exactly as open as RH.

### 2. BSD Conjecture — the most bridgeable genuine proof

Present in Mathlib:
- `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` → `WeierstrassCurve R`
  (fields `a₁ a₂ a₃ a₄ a₆`), point group, base-change, heights.
- `Mathlib.AlgebraicGeometry.EllipticCurve.LFunction` → 
  `WeierstrassCurve.LFunction : ArithmeticFunction ℤ` (Euler product) and the
  genuine complex L-series `WeierstrassCurve.LSeries (W) (s : ℂ) : ℂ`, both over a
  number field `K` (`[NumberField K]`).
- `Mathlib.NumberTheory.NumberField.Basic` for `NumberField ℚ`.

Milestones:
1. **DONE:** `UniversalSingularity/BSD37a1.lean` fully proves the concrete
   layer of the curve `37a1` (field set in `sampleCurve`): discriminant `Δ = 37`,
   the twenty-seven nonsingular rational points `P`, `2P, ..., 27P`, `-P`, `-2P`,
   `-3P`, `-4P, ..., -9P` (all integer multiples `(m : ℤ) • p` of `P` for
   `-9 ≤ m ≤ 27`), pairwise distinct together with the identity: the symmetric
   family `{0, ±P, ..., ±9P}` of nineteen distinct group elements,
   `{0, 10P, ..., 18P}` of ten distinct elements, and — via the quantified
   certificates `not_nsmul_p_torsion_le_27`, `nsmul_p_injective_le_27` and
   `nsmul_p_ne_zsmul_neg` — the full **twenty-eight**-element family
   `{0, ±P, ..., ±9P, 10P, ..., 18P}` pairwise distinct (so `P` is not torsion
   of any order `2 ≤ n ≤ 27`), the explicit slopes and group-law relations
   `nP` for `n = 2, ..., 9` (with `2T = X` and the independent check `3T = 9P`),
   more direct pair checks (`Q + R = P`, `Q + T = W`, `S + P = U`, `U + T = P`),
   the inverse pairs (`P + R = 0`, `Q + U = 0`, `T + S = 0`, plus `−2P = U`,
   `−3P = S`, `−S = T`), and the no-torsion forms `(n : ℕ) • p ≠ 0` and
   `(n : ℤ) • p ≠ 0` for `2 ≤ |n| ≤ 27`, giving each named multiple `2P`
   through `9P` its own small-order no-torsion certificate. Zero `sorry`s.
2. **LIVE ready (hard but finite):** compute `mordellWeilRank` for `37a1` by
   descent. This is a *real* theorem (integer rank = n), unlike the old
   placeholder.
3. **GAP:** define `ord_{s=1} L(E,s)` (order of vanishing) from `LSeries` — not
   packaged in Mathlib.
4. **OPEN:** prove `analyticRank = mordellWeilRank` for a general curve — this is BSD.

Realistic: prove a **rank-0 instance** (e.g. `L(E,1) ≠ 0 ⇒ rank = 0`) for a
specific curve once `ord` and nonvanishing lemmas are added. This is the single
finishable "real proof" left in this landscape, but still a substantial project.

### 3. Poincaré Conjecture — statable, Himalayan proof (not open)

Present in Mathlib:
- `Topology/Manifold`, `Geometry/Manifold/Instances/Sphere` (manifolds, `𝕊³`).
- `AlgebraicTopology/FundamentalGroupoid` → `FundamentalGroup`, `SimplyConnected`.
- Homology (singular + chain complexes).

Milestones:
0. **DONE (concrete layer):** `UniversalSingularity/PoincareSphere.lean` proves,
   with zero `sorry`s, that `𝕊³` is inhabited, path-connected, compact, and a
   smooth `C^∞` 3-manifold charted by `ℝ³`. Mathlib still has **no**
   `SimplyConnectedSpace 𝕊³` instance.
1. **DONE:** `PoincareConjectureReal.lean` states the topological and smooth
   statements (`PoincareConjectureTopological`, `PoincareConjectureSmooth`) on
   genuine `ChartedSpace` / `SimplyConnectedSpace` / `𝕊³` objects and proves the
   base case `𝕊³ ≃ₜ 𝕊³`. Mathlib itself only ships the claim as `proof_wanted`.
2. **GAP:** Perelman's Ricci-flow proof is not formalized (curvature flows, neck
   decomposition, collapse). Multi-thousand-lemma project. The `sorry`s
   `poincareConjectureTopological_gap` / `poincareConjectureSmooth_gap` pin this.

Conclusion is **PROVEN** (Perelman); the Lean formalization is a research-scale
program, not a quick bridge.

### 4. P vs NP — partial infra, OPEN

Present in Mathlib:
- `Computability/TuringMachine` (models, TMComputable, encoding, halting,
  reductions), `ModelTheory/Complexity`.

Milestones:
0. **DONE (concrete layer):** `UniversalSingularity/PvsNPPolytime.lean` proves,
   with zero `sorry`s, that the `PolytimeBound` predicate is closed under
   pointwise sum, pointwise product, constants, and monotone domination.
   (The shipped Mathlib bundle has no olean for `Mathlib.Computability.Halting`,
   and `TM2ComputableInPolyTime.comp` is `proof_wanted` in this Mathlib.)
1. **DONE:** `PvsNPReal.lean` defines **P** (`InP : Problem → Prop`) and **NP**
   (`InNP : Problem → Prop`) on binary decision problems, lifting Mathlib's
   `Turing.TM2ComputableInPolyTime` and `Language Bool` (polytime bounds via
   `Polynomial ℕ`).
2. **GAP:** the formal `P ⊆ NP` inclusion on this machinery
   (`p_subset_np_gap`), classically true but unproved here.
3. **OPEN:** `P ≠ NP` (`p_vs_np_gap`). Genuinely unsolved.

### 5. Yang-Mills (existence + mass gap) — GAP, OPEN

No gauge theory / rigorous Yang-Mills functional / Sobolev 4D gauge machinery in
Mathlib. Full QFT construction is the deep open part. **Not bridgeable by Lean now.**
`YangMillsReal.lean` pins the claim (`yangMillsMassGap_gap`, placeholder objects).
**DONE (base only):** `YangMillsMilestone.lean` proves, with zero `sorry`s, that
the Clay base manifold `𝕊⁴ ⊆ ℝ⁵` (`YMBase`) is inhabited, path-connected,
compact, and a smooth `C^∞` 4-manifold charted by `ℝ⁴`. All gauge-theoretic
content remains GAP/OPEN.

### 6. Navier-Stokes (existence & smoothness) — GAP, OPEN

No Sobolev spaces / Leray weak solutions / regularity in Mathlib (some ODE/evolution
and Brownian motion exist). Existence-and-smoothness is OPEN. **Not bridgeable now.**
`NavierStokesReal.lean` pins the claim (`navierStokesGlobalRegularity_gap`, placeholders).
**DONE (integrity):** `BridgeIntegrity.lean` proves, with zero `sorry`s, that the
NS placeholder skeleton `globalSmoothSolutionExists _ = false` visibly **fails**
the pinned statement (`¬ NavierStokesGlobalRegularity`), so the `sorry` gap is
non-vacuous.

### 7. Hodge Conjecture — GAP, OPEN

Some singular homology/cohomology exist, but no Hodge decomposition / Kähler
manifold machinery; the conjecture is OPEN (with known counterexamples in general
settings). **Not bridgeable now.** `HodgeConjectureReal.lean` pins the claim
(`hodgeConjecture_gap`, placeholders). **Integrity note:** the Hodge placeholder
skeleton is deliberately **not** asserted anywhere — its stubs would make
`HodgeConjecturePinned X` reduce to `∀ p, 0 = 0`, i.e. vacuously true, which
would be misleading. `BridgeIntegrity.lean` documents this decision (zero
`sorry`s).

---

## Suggested next work (real proofs, in increasing difficulty)

1. **BSD rank computation for `37a1`** — the group-law layer is DONE in
   `BSD37a1.lean`; the remaining concrete step is `mordellWeilRank` by descent.
2. **RH nontrivial-zero classification + finite counterexample search** — the
   concrete zeta layer is DONE in `RiemannHypothesisZeta.lean`; the next step
   connects it to the `riemannZetaZeros` gap in `RiemannHypothesisReal.lean`.
3. **HP spectral bridge** — pin the Hilbert–Pólya operator on a concrete Hilbert
   space (`ℓ²`, Hermite/`L²(ℝ)`, or a Sturm–Liouville operator) and prove the
   GUE pair-correlation as its spectral rigidity; HP ⇒ RH follows. Open.
4. Any attempt at the other five requires building foundational Mathlib first
   (PDE, gauge theory, Hodge theory) and/or is mathematically OPEN. The five
   `*Real` bridge modules (`PoincareConjectureReal`, `PvsNPReal`, `YangMillsReal`,
   `NavierStokesReal`, `HodgeConjectureReal`) pin exactly where those foundations
   would have to be built; the `RiemannHypothesisZeta`, `PoincareSphere`,
   `YangMillsMilestone`, `PvsNPPolytime`, and `BridgeIntegrity` milestone modules
   (all 0 `sorry`) pin the concrete layers that are already available; filling
   **any** of their `sorry` gaps is real progress.

Keep the heuristic `MassGap` modules as pedagogy. Build the real proofs in
`UniversalSingularity/*Real.lean`, outside the heuristic frame.