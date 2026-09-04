import UniversalSingularity.MassGapTheorem
import UniversalSingularity.PvsNP
import UniversalSingularity.YangMills
import UniversalSingularity.RiemannHypothesis
import UniversalSingularity.NavierStokes
import UniversalSingularity.BSD
import UniversalSingularity.PoincareConjecture
import UniversalSingularity.HodgeConjecture

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

Build with:

    lake build
-/

#check UniversalSingularity.MassGapUnificationTheorem
#check UniversalSingularity.riemannHypothesisGodForceEquivalence
