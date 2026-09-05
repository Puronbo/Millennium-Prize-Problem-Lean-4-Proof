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
  arithmetic on the rank-one curve `37a1` (`y² + y = x³ − x`): `Δ = 37`, eleven
  nonsingular rational points, the low multiples `nP` for `n = 2, ..., 8` (with
  `2T = X`), the inverse pairs (`P + R = 0`, `Q + U = 0`, `T + S = 0`), and no
  torsion of order `2` through `8` for the generator `P`. **Zero `sorry`s** — the
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
   eleven nonsingular rational points with their coordinates, the explicit slopes
   and group-law relations `nP` for `n = 2, ..., 8` (with `2T = X`), the inverse
   pairs (`P + R = 0`, `Q + U = 0`, `T + S = 0`), and the absence of torsion of
   order `2` through `8` for the generator `P`. Zero `sorry`s.
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

### 6. Navier-Stokes (existence & smoothness) — GAP, OPEN

No Sobolev spaces / Leray weak solutions / regularity in Mathlib (some ODE/evolution
and Brownian motion exist). Existence-and-smoothness is OPEN. **Not bridgeable now.**
`NavierStokesReal.lean` pins the claim (`navierStokesGlobalRegularity_gap`, placeholders).

### 7. Hodge Conjecture — GAP, OPEN

Some singular homology/cohomology exist, but no Hodge decomposition / Kähler
manifold machinery; the conjecture is OPEN (with known counterexamples in general
settings). **Not bridgeable now.** `HodgeConjectureReal.lean` pins the claim
(`hodgeConjecture_gap`, placeholders).

---

## Suggested next work (real proofs, in increasing difficulty)

1. **BSD rank computation for `37a1`** — the group-law layer is DONE in
   `BSD37a1.lean`; the remaining concrete step is `mordellWeilRank` by descent.
2. **RH nontrivial-zero classification + finite counterexample search** — real
   theorem, get `riemannZetaZeros` genuinely connected.
3. **HP spectral bridge** — pin the Hilbert–Pólya operator on a concrete Hilbert
   space (`ℓ²`, Hermite/`L²(ℝ)`, or a Sturm–Liouville operator) and prove the
   GUE pair-correlation as its spectral rigidity; HP ⇒ RH follows. Open.
4. Any attempt at the other five requires building foundational Mathlib first
   (PDE, gauge theory, Hodge theory) and/or is mathematically OPEN. The five
   `*Real` bridge modules (`PoincareConjectureReal`, `PvsNPReal`, `YangMillsReal`,
   `NavierStokesReal`, `HodgeConjectureReal`) pin exactly where those foundations
   would have to be built; filling **any** of their `sorry` gaps is real progress.

Keep the heuristic `MassGap` modules as pedagogy. Build the real proofs in
`UniversalSingularity/*Real.lean`, outside the heuristic frame.