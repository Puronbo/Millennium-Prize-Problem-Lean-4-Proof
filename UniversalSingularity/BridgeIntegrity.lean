import UniversalSingularity.YangMillsReal
import UniversalSingularity.NavierStokesReal

/-!
# Bridge integrity -- the placeholder skeletons are visibly non-solutions

The `*Real` bridge modules for Yang-Mills and Navier-Stokes currently pin their
Clay statements with explicit `sorry` gaps, using **documented placeholders** for
objects Mathlib does not yet have (mass gaps, PDE solution existence).

This module proves -- fully, with no `sorry` -- that those placeholders really
are placeholders: under the actual stub definitions, the pinned statements are
**not** satisfied.  So the `sorry` gaps are non-vacuous: one cannot wave away the
open content by claiming the stub already "solves" the problem.

For the Hodge bridge (`UniversalSingularity.HodgeConjectureReal`) the situation is
reversed and equally honest: its stub makes both ranks definitionally `0`, so
`HodgeConjecturePinned X` would reduce to `∀ p, 0 = 0` -- *vacuously true*.  We
deliberately do **not** publish that as a theorem here, because publishing a
name whose statement is literally the Hodge conjecture (and whose proof is mere
definitional equality of placeholders) would be misleading.
-/

namespace UniversalSingularity.BridgeIntegrity

/-- The placeholder Navier-Stokes `globalSmoothSolutionExists` is never `true`, so
the pinned Clay statement `NavierStokesGlobalRegularity` is visibly **not**
satisfied by the stub: the gap in `UniversalSingularity.NavierStokesReal` is
non-vacuous. -/
theorem not_navierStokesGlobalRegularity_placeholder :
    ¬ NavierStokesReal.NavierStokesGlobalRegularity := by
  intro h
  have hbad : (false : Bool) = true := by
    simpa [NavierStokesReal.globalSmoothSolutionExists] using h (fun _ : ℝ => 0)
  exact (by decide : (false : Bool) ≠ true) hbad

/-- The placeholder Yang-Mills `massGap` is identically `0`, so the Clay
requirement `massGap g > 0` is visibly unmet by the stub: the gap in
`UniversalSingularity.YangMillsReal` is non-vacuous. -/
theorem not_yangMillsMassGapProblem_placeholder :
    ¬ YangMillsReal.YangMillsMassGapProblem (1 : ℝ) := by
  intro h
  have hbad : (0 : ℝ) > 0 := by
    simpa [YangMillsReal.YangMillsMassGapProblem, YangMillsReal.massGap]
      using h (by norm_num : (1 : ℝ) > 0)
  exact (lt_irrefl (0 : ℝ)) hbad

end UniversalSingularity.BridgeIntegrity