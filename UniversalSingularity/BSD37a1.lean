import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import UniversalSingularity.BSDReal

/-!
# BSD (Birch and Swinnerton-Dyer) -- concrete facts on the curve `37a1`

This module computes *genuine* arithmetic content about the specific rational
elliptic curve `37a1` (`y² + y = x³ - x`), using only what Mathlib's affine
elliptic-curve group law already provides.

Every theorem here is fully proved (no `sorry`): the discriminant `Δ = 37`, a
dozen rational points with their group-law relations inside
`WeierstrassCurve.Affine.Point`, and the absence of `2`/`3`/`4`-torsion for the
generator `P`.  These are *real* statements about *real* mathematics, in
contrast to the placeholder `analyticRank`/`mordellWeilRank` in
`UniversalSingularity.BSDReal`.

They do **not** prove BSD itself: the analytic rank (order of vanishing of the
L-series at `s = 1`), the Mordell-Weil rank, and their equality remain open
gaps tracked in `UniversalSingularity.BSDReal`.
-/

namespace UniversalSingularity.BSD37a1

open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

/-- The curve `37a1`: `y² + y = x³ - x`, with `Δ = 37`. -/
abbrev W : WeierstrassCurve.Affine ℚ := UniversalSingularity.BSDReal.sampleCurve

/-- The Weierstrass coefficients of `37a1`. -/
@[simp] theorem a₁_eq : W.a₁ = 0 := rfl
@[simp] theorem a₂_eq : W.a₂ = 0 := rfl
@[simp] theorem a₃_eq : W.a₃ = 1 := rfl
@[simp] theorem a₄_eq : W.a₄ = -1 := rfl
@[simp] theorem a₆_eq : W.a₆ = 0 := rfl

/-! ## The curve is genuinely an elliptic curve -/

/-- The discriminant of `37a1` is `37`. -/
theorem discriminant_eq_37 : W.Δ = 37 := by
  rw [WeierstrassCurve.Δ]
  simp [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    UniversalSingularity.BSDReal.sampleCurve]
  norm_num

/-- The discriminant is nonzero, so the curve is nonsingular. -/
theorem discriminant_ne_zero : W.Δ ≠ 0 := by
  rw [discriminant_eq_37]
  norm_num

/-- The discriminant is a unit in `ℚ`. -/
theorem isUnit_discriminant : IsUnit W.Δ := by
  rw [discriminant_eq_37]
  exact IsUnit.mk0 37 (by norm_num)

/-- `37a1` is an elliptic curve over `ℚ`. -/
instance : WeierstrassCurve.IsElliptic W :=
  ⟨isUnit_discriminant⟩

/-- The unit discriminant `Δ'` is the rational number `37`. -/
theorem unit_discriminant_eq : (W.Δ' : ℚ) = 37 := by
  rw [WeierstrassCurve.coe_Δ', discriminant_eq_37]

/-- On an elliptic curve, being an equation point and being nonsingular agree. -/
theorem equation_iff_nonsingular' {x y : ℚ} : W.Equation x y ↔ W.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular

/-! ## The points are nonsingular rational points -/

/-- `(0, 0)` lies on the curve. -/
theorem equation_P : W.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp

/-- `(0, 0)` is a nonsingular rational point. -/
theorem nonsingular_P : W.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_P
  · left
    simp

/-- `(1, 0)` lies on the curve. -/
theorem equation_Q : W.Equation 1 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp

/-- `(1, 0)` is a nonsingular rational point. -/
theorem nonsingular_Q : W.Nonsingular 1 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_Q
  · left
    simp
    norm_num

/-- `(0, -1)` lies on the curve. -/
theorem equation_R : W.Equation 0 (-1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp

/-- `(0, -1)` is a nonsingular rational point. -/
theorem nonsingular_R : W.Nonsingular 0 (-1) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_R
  · left
    simp

/-- `(-1, 0)` lies on the curve. -/
theorem equation_S : W.Equation (-1) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(-1, 0)` is a nonsingular rational point. -/
theorem nonsingular_S : W.Nonsingular (-1) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_S
  · left
    simp
    norm_num

/-- `(-1, -1)` lies on the curve. -/
theorem equation_T : W.Equation (-1) (-1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(-1, -1)` is a nonsingular rational point. -/
theorem nonsingular_T : W.Nonsingular (-1) (-1) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_T
  · left
    simp
    norm_num

/-- `(1, -1)` lies on the curve. -/
theorem equation_U : W.Equation 1 (-1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp

/-- `(1, -1)` is a nonsingular rational point. -/
theorem nonsingular_U : W.Nonsingular 1 (-1) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_U
  · left
    simp
    norm_num

/-- `(2, -3)` lies on the curve. -/
theorem equation_V : W.Equation 2 (-3) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(2, -3)` is a nonsingular rational point. -/
theorem nonsingular_V : W.Nonsingular 2 (-3) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_V
  · left
    simp
    norm_num

/-! ## The distinguished rational points -/

/-- The rational point `P = (0, 0)`. -/
def p : W.Point := Point.some 0 0 nonsingular_P

/-- The rational point `(1, 0)`. -/
def q : W.Point := Point.some 1 0 nonsingular_Q

/-- The rational point `(0, -1)`. -/
def r : W.Point := Point.some 0 (-1) nonsingular_R

/-- The rational point `(-1, 0)`. -/
def s : W.Point := Point.some (-1) 0 nonsingular_S

/-- The rational point `(-1, -1)`. -/
def t : W.Point := Point.some (-1) (-1) nonsingular_T

/-- The rational point `(1, -1)`. -/
def u : W.Point := Point.some 1 (-1) nonsingular_U

/-- The rational point `(2, -3)`. -/
def v : W.Point := Point.some 2 (-3) nonsingular_V

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem p_coords : W.nonsingularPointEquiv p =
    (Option.some ⟨⟨0, 0⟩, nonsingular_P⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold p
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_P]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem q_coords : W.nonsingularPointEquiv q =
    (Option.some ⟨⟨1, 0⟩, nonsingular_Q⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold q
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_Q]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem r_coords : W.nonsingularPointEquiv r =
    (Option.some ⟨⟨0, -1⟩, nonsingular_R⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold r
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_R]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem s_coords : W.nonsingularPointEquiv s =
    (Option.some ⟨⟨-1, 0⟩, nonsingular_S⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold s
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_S]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem t_coords : W.nonsingularPointEquiv t =
    (Option.some ⟨⟨-1, -1⟩, nonsingular_T⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold t
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_T]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem u_coords : W.nonsingularPointEquiv u =
    (Option.some ⟨⟨1, -1⟩, nonsingular_U⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold u
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_U]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem v_coords : W.nonsingularPointEquiv v =
    (Option.some ⟨⟨2, -3⟩, nonsingular_V⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold v
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_V]

/-! ## Slopes and addition coordinates

These are the explicit affine formulae for the group law, verified by
`norm_num`.  They constitute the honest computational content: the coordinates
of `P + P`, `P + Q`, `Q + Q`, and `T + P` on `37a1`.
-/

/-- `W.negY 0 0 = -1`. -/
theorem negY_00 : W.negY 0 0 = -1 := by
  rw [WeierstrassCurve.Affine.negY]
  simp

/-- `W.negY 1 0 = -1`. -/
theorem negY_10 : W.negY 1 0 = -1 := by
  rw [WeierstrassCurve.Affine.negY]
  simp

/-- `W.negY (-1) (-1) = 0`. -/
theorem negY_tt : W.negY (-1) (-1) = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  simp

/-- The tangent slope at `P` is `-1`. -/
theorem slope_pp : W.slope 0 0 0 0 = -1 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (by rw [negY_00]; norm_num : (0 : ℚ) ≠ W.negY 0 0)]
  simp

/-- The coordinate `x(P + P) = 1`. -/
theorem addX_pp : W.addX 0 0 (W.slope 0 0 0 0) = 1 := by
  rw [slope_pp]
  simp

/-- The coordinate `y(P + P) = 0`. -/
theorem addY_pp : W.addY 0 0 0 (W.slope 0 0 0 0) = 0 := by
  norm_num [slope_pp, WeierstrassCurve.Affine.addY]

/-- The secant slope through `P` and `Q` is `0`. -/
theorem slope_pq : W.slope 0 1 0 0 = 0 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 0) (x₂ := 1) (y₁ := 0) (y₂ := 0)
    (by norm_num : (0 : ℚ) ≠ 1)]
  simp

/-- The coordinate `x(P + Q) = -1`. -/
theorem addX_pq : W.addX 0 1 (W.slope 0 1 0 0) = -1 := by
  rw [slope_pq]
  simp

/-- The coordinate `y(P + Q) = -1`. -/
theorem addY_pq : W.addY 0 1 0 (W.slope 0 1 0 0) = -1 := by
  norm_num [slope_pq, WeierstrassCurve.Affine.addY]

/-- The tangent slope at `Q` is `2`. -/
theorem slope_qq : W.slope 1 1 0 0 = 2 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (by rw [negY_10]; norm_num : (0 : ℚ) ≠ W.negY 1 0)]
  simp
  norm_num

/-- The coordinate `x(Q + Q) = 2`. -/
theorem addX_qq : W.addX 1 1 (W.slope 1 1 0 0) = 2 := by
  rw [slope_qq]
  simp
  norm_num

/-- The coordinate `y(Q + Q) = -3`. -/
theorem addY_qq : W.addY 1 1 0 (W.slope 1 1 0 0) = -3 := by
  norm_num [slope_qq, WeierstrassCurve.Affine.addY]

/-- The secant slope through `T` and `P` is `1`. -/
theorem slope_tp : W.slope (-1) 0 (-1) 0 = 1 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -1) (x₂ := 0) (y₁ := -1) (y₂ := 0)
    (by norm_num : (-1 : ℚ) ≠ 0)]
  simp

/-- The coordinate `x(T + P) = 2`. -/
theorem addX_tp : W.addX (-1) 0 (W.slope (-1) 0 (-1) 0) = 2 := by
  rw [slope_tp]
  simp
  norm_num

/-- The coordinate `y(T + P) = -3`. -/
theorem addY_tp : W.addY (-1) 0 (-1) (W.slope (-1) 0 (-1) 0) = -3 := by
  norm_num [slope_tp, WeierstrassCurve.Affine.addY]

/-! ## Group-law relations on `37a1` -/

/-- `P + P = Q`; equivalently `2P = Q`. -/
theorem two_p_eq_q : p + p = q := by
  unfold p q
  rw [add_self_of_Y_ne (x₁ := 0) (y₁ := 0) (h₁ := nonsingular_P)
    (by rw [negY_00]; norm_num : (0 : ℚ) ≠ W.negY 0 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_pp, addY_pp⟩

/-- `P + Q = T`; hence `3P = T`. -/
theorem add_p_q_eq_t : p + q = t := by
  unfold p q t
  rw [add_of_X_ne (x₁ := 0) (x₂ := 1) (y₁ := 0) (y₂ := 0) (h₁ := nonsingular_P)
    (h₂ := nonsingular_Q) (by norm_num : (0 : ℚ) ≠ 1)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_pq, addY_pq⟩

/-- `Q + Q = V`; hence `4P = V`. -/
theorem two_q_eq_v : q + q = v := by
  unfold q v
  rw [add_self_of_Y_ne (x₁ := 1) (y₁ := 0) (h₁ := nonsingular_Q)
    (by rw [negY_10]; norm_num : (0 : ℚ) ≠ W.negY 1 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_qq, addY_qq⟩

/-- `T + P = V`; hence `4P = V`. -/
theorem add_t_p_eq_v : t + p = v := by
  unfold t p v
  rw [add_of_X_ne (x₁ := -1) (x₂ := 0) (y₁ := -1) (y₂ := 0) (h₁ := nonsingular_T)
    (h₂ := nonsingular_P) (by norm_num : (-1 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_tp, addY_tp⟩

/-- `3P = T`. -/
theorem three_p_eq_t : p + p + p = t := by
  rw [two_p_eq_q, add_comm (a := q) (b := p), add_p_q_eq_t]

/-- `4P = V`. -/
theorem four_p_eq_v : p + p + p + p = v := by
  rw [two_p_eq_q, add_comm (a := q) (b := p), add_p_q_eq_t, add_t_p_eq_v]

/-- `-P = (0, -1)`. -/
theorem neg_p_eq_r : -p = r := by
  unfold p r
  rw [neg_some nonsingular_P]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, negY_00⟩

/-- `-Q = (1, -1)`. -/
theorem neg_q_eq_u : -q = u := by
  unfold q u
  rw [neg_some nonsingular_Q]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, negY_10⟩

/-- `-T = (-1, 0)`. -/
theorem neg_t_eq_s : -t = s := by
  unfold t s
  rw [neg_some nonsingular_T]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, negY_tt⟩

/-- `P + (-P) = 0`. -/
theorem p_add_neg_p_eq_zero : p + -p = 0 := by
  exact add_neg_cancel p

/-! ## None of the points is the identity -/

/-- `P` is not the identity. -/
theorem p_ne_zero : p ≠ 0 :=
  some_ne_zero nonsingular_P

/-- `Q` is not the identity. -/
theorem q_ne_zero : q ≠ 0 :=
  some_ne_zero nonsingular_Q

/-- `T` is not the identity. -/
theorem t_ne_zero : t ≠ 0 :=
  some_ne_zero nonsingular_T

/-- `V` is not the identity. -/
theorem v_ne_zero : v ≠ 0 :=
  some_ne_zero nonsingular_V

/-- `2P` is not the identity. -/
theorem two_p_ne_zero : p + p ≠ 0 := by
  rw [two_p_eq_q]
  exact q_ne_zero

/-- `3P` is not the identity. -/
theorem three_p_ne_zero : p + p + p ≠ 0 := by
  rw [three_p_eq_t]
  exact t_ne_zero

/-- `4P` is not the identity. -/
theorem four_p_ne_zero : p + p + p + p ≠ 0 := by
  rw [four_p_eq_v]
  exact v_ne_zero

/-- The points `P` and `Q` are distinct. -/
theorem p_ne_q : p ≠ q := by
  intro h
  simp only [p, q] at h
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h
  norm_num at h

/-! ## There is no `2`-, `3`-, or `4`-torsion

For the generator `P`, the multiples `2P`, `3P`, `4P` are computed above and are
all distinct from the identity.
-/

/-- `P` does not have order `2`. -/
theorem not_two_torsion : p + p ≠ 0 :=
  two_p_ne_zero

/-- `P` does not have order `3`. -/
theorem not_three_torsion : p + p + p ≠ 0 :=
  three_p_ne_zero

/-- `P` does not have order `4`. -/
theorem not_four_torsion : p + p + p + p ≠ 0 :=
  four_p_ne_zero

end UniversalSingularity.BSD37a1