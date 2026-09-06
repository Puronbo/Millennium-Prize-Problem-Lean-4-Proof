import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.PathConnected

/-!
# Yang-Mills existence and mass gap -- verified concrete facts about the base `𝕊⁴`

This module records *genuine, fully proved* (no `sorry`) facts about the unit
`4`-sphere `S4 = {x : ℝ⁵ | ‖x‖ = 1}` in `ℝ⁵`, the compact base manifold on which
the Clay Yang-Mills problem is posed.  It is the verified-concrete counterpart to
the honest bridge skeleton in `UniversalSingularity.YangMillsReal`.

Concretely proved here:

* `moduleRank_fin5` : `ℝ⁵` has (Cardinal) rank `5 > 1`;
* `isPathConnected_YMBase`, `nonempty_YMBase`, `compactSpace_YMBase` : the base
  `𝕊⁴` is path-connected, inhabited and compact;
* `chartedSpace_YMBase`, `smoothManifold_YMBase` : `𝕊⁴` is a smooth (`C^∞`)
  Hausdorff 4-manifold, charted by `ℝ⁴`.

What is **not** claimed here (honestly): since Mathlib has no gauge theory (no
principal bundles, no connections, no gauge groups, no transfer-matrix spectra),
the Yang-Mills field content -- and therefore the mass-gap assertion itself --
remains entirely at the level of the documented placeholders in
`UniversalSingularity.YangMillsReal`.
-/

open scoped Manifold ContDiff EuclideanSpace
open Metric

namespace UniversalSingularity.YangMillsMilestone

noncomputable section

/-- The unit 4-sphere `𝕊⁴ = {x : ℝ⁵ | ‖x‖ = 1}`, the base of the Clay Yang-Mills
problem. -/
noncomputable abbrev YMBase : Type := sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

/-- The Euclidean space `ℝ⁵` has rank `5 > 1`. -/
lemma moduleRank_fin5 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 5)) := by
  have h : Module.rank ℝ (EuclideanSpace ℝ (Fin 5)) = (5 : Cardinal) := by
    calc
      Module.rank ℝ (EuclideanSpace ℝ (Fin 5)) = Module.rank ℝ (Fin 5 → ℝ) := by
        exact (EuclideanSpace.equiv (Fin 5) ℝ).toLinearEquiv.rank_eq
      _ = (5 : Cardinal) := by
        rw [rank_fun']
        norm_num
  rw [h]
  norm_num

/-- `𝕊⁴` is path-connected. -/
theorem isPathConnected_YMBase : IsPathConnected (sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
  isPathConnected_sphere moduleRank_fin5 (0 : EuclideanSpace ℝ (Fin 5)) zero_le_one

/-- `𝕊⁴` is inhabited: the first standard basis vector has unit norm. -/
theorem nonempty_YMBase : Nonempty YMBase := by
  refine ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp [EuclideanSpace.single, PiLp.norm_single]⟩

/-- `𝕊⁴` is compact. -/
instance compactSpace_YMBase : CompactSpace YMBase := by
  unfold YMBase
  infer_instance

/-- `𝕊⁴` is a charted manifold, locally modelled on `ℝ⁴`. -/
instance chartedSpace_YMBase : ChartedSpace (EuclideanSpace ℝ (Fin 4)) YMBase := by
  unfold YMBase
  infer_instance

/-- `𝕊⁴` is a smooth (C∞) manifold. -/
instance smoothManifold_YMBase : IsManifold (𝓡 4) ∞ YMBase := by
  unfold YMBase
  infer_instance

end

end UniversalSingularity.YangMillsMilestone