import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.PathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Poincaré conjecture -- verified concrete facts about the 3-sphere

This module records *genuine, fully proved* (no `sorry`) facts about the unit
`3`-sphere `S3 = {x : ℝ⁴ | ‖x‖ = 1}` in the Euclidean space `ℝ⁴`, using Mathlib's
sphere/geometry instances.  It is the verified-concrete counterpart to the honest
bridge skeleton in `UniversalSingularity.PoincareConjectureReal`.

Concretely proved here:

* `moduleRank_fin4` : `ℝ⁴` has (Cardinal) rank `4 > 1`, the dimensional input
  Mathlib's `isPathConnected_sphere` requires;
* `isPathConnected_S3` : `S3` is path-connected;
* `nonempty_S3` : `S3` contains the unit basis vector `e₁ = single 0 1`;
* `compactSpace_S3`, `chartedSpace_S3`, `smoothManifold_S3` : `S3` is compact and
  a smooth (`C^∞`) Hausdorff 3-manifold, charted by `ℝ³`.

What is **not** claimed here (honestly): the deep content of the (settled)
Poincaré conjecture is that `S3` -- indeed every closed simply connected smooth
`3`-manifold -- is *simply connected* homeomorphic to `S3`.  Mathlib has the
`SimplyConnectedSpace` class but **no** instance `SimplyConnectedSpace S3`; that
statement, and its extension to arbitrary closed simply connected 3-manifolds,
remains the gap pinned in `UniversalSingularity.PoincareConjectureReal`.
-/

open scoped Manifold ContDiff EuclideanSpace
open Metric

namespace UniversalSingularity.PoincareSphere

noncomputable section

/-- The unit 3-sphere in `ℝ⁴`: `S3 = {x : ℝ⁴ | ‖x‖ = 1}`. -/
noncomputable abbrev S3 : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The Euclidean space `ℝ⁴` has rank `4 > 1`. -/
lemma moduleRank_fin4 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
  have h : Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) = (4 : Cardinal) := by
    calc
      Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) = Module.rank ℝ (Fin 4 → ℝ) := by
        exact (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv.rank_eq
      _ = (4 : Cardinal) := by
        rw [rank_fun']
        norm_num
  rw [h]
  norm_num

/-- `S3` is path-connected. -/
theorem isPathConnected_S3 : IsPathConnected (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  isPathConnected_sphere moduleRank_fin4 (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one

/-- `S3` is inhabited: the first standard basis vector has unit norm. -/
theorem nonempty_S3 : Nonempty S3 := by
  refine ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp [EuclideanSpace.single, PiLp.norm_single]⟩

/-- `S3` is compact. -/
instance compactSpace_S3 : CompactSpace S3 := by
  unfold S3
  infer_instance

/-- `S3` is a charted manifold, locally modelled on `ℝ³`. -/
instance chartedSpace_S3 : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S3 := by
  unfold S3
  infer_instance

/-- `S3` is a smooth (C∞) manifold. -/
instance smoothManifold_S3 : IsManifold (𝓡 3) ∞ S3 := by
  unfold S3
  infer_instance

end

end UniversalSingularity.PoincareSphere