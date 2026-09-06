import UniversalSingularity.MassGapTheorem
import UniversalSingularity.PvsNP
import UniversalSingularity.YangMills
import UniversalSingularity.RiemannHypothesis
import UniversalSingularity.NavierStokes
import UniversalSingularity.BSD
import UniversalSingularity.PoincareConjecture
import UniversalSingularity.HodgeConjecture
import UniversalSingularity.RiemannHypothesisZeta
import UniversalSingularity.PoincareSphere
import UniversalSingularity.YangMillsMilestone
import UniversalSingularity.PvsNPPolytime
import UniversalSingularity.BridgeIntegrity

/-
# Main file for the Millennium Prize Problems Lean 4 Q-model

This project is a **heuristic Q-model**, not a solution to any of the seven
Millennium Prize Problems (P vs NP, Yang-Mills, Riemann Hypothesis,
Navier-Stokes, BSD, Hodge, Poincaré). Those are open (or, in the case of
Poincaré, professionally settled) questions; none of them is claimed or proved
here.

What this code does establish, honestly, is a small, coherent framework: each
problem is attached a real-valued parameter `Q` and a distinguished
`massGapElement` where `Q = 1`, and the elementary real-number fact that
"`Q = 1` iff the element is in neither the virtual nor the physical sector."

In addition, five verified-concrete milestone modules (no `sorry`) pin genuine
facts about each of the non-BSD problems:

* `UniversalSingularity.RiemannHypothesisZeta` -- zeta values, the trivial-zero
  family, nonvanishing for `Re s ≥ 1`, the Dirichlet series identity, the
  functional equation, analyticity, and a logic-level restatement of RH.
* `UniversalSingularity.PoincareSphere` -- the 3-sphere `𝕊³` is inhabited,
  path-connected, compact, and a smooth 3-manifold charted by `ℝ³`.
* `UniversalSingularity.YangMillsMilestone` -- the base `𝕊⁴` of the Clay
  Yang-Mills problem is inhabited, path-connected, compact, and a smooth
  4-manifold charted by `ℝ⁴`.
* `UniversalSingularity.PvsNPPolytime` -- closure of the polytime step-bound
  predicate under sum, product, constants and monotone domination.
* `UniversalSingularity.BridgeIntegrity` -- the placeholder skeletons for
  Navier-Stokes and Yang-Mills are visibly *not* solutions, so their `sorry`
  gaps are non-vacuous.

Each module states explicitly where the corresponding Millennium claim stays
open (the `*Real` bridge files carry the `sorry` gaps).

Build with:

    lake build
-/

#check UniversalSingularity.MassGapUnificationTheorem
#check UniversalSingularity.riemannHypothesisGodForceEquivalence
