import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import UniversalSingularity.BSDReal

/-!
# BSD (Birch and Swinnerton-Dyer) -- concrete facts on the curve `37a1`

This module computes *genuine* arithmetic content about the specific rational
elliptic curve `37a1` (`y² + y = x³ - x`), using only what Mathlib's affine
elliptic-curve group law already provides.

Every theorem here is fully proved (no `sorry`): the discriminant `Δ = 37`,
eleven rational points with their group-law relations inside
`WeierstrassCurve.Affine.Point`, and the absence of torsion of order `2` through
`8` for the generator `P`.  These are *real* statements about *real*
mathematics, in contrast to the placeholder `analyticRank`/`mordellWeilRank` in
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

/-- `(1/4, -5/8)` lies on the curve. -/
theorem equation_W : W.Equation (1/4) (-5/8) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(1/4, -5/8)` is a nonsingular rational point. -/
theorem nonsingular_W : W.Nonsingular (1/4) (-5/8) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_W
  · left
    simp
    norm_num

/-- `(6, 14)` lies on the curve. -/
theorem equation_X : W.Equation 6 14 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(6, 14)` is a nonsingular rational point. -/
theorem nonsingular_X : W.Nonsingular 6 14 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_X
  · left
    simp
    norm_num

/-- `(-5/9, 8/27)` lies on the curve. -/
theorem equation_Y : W.Equation (-5/9) (8/27) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(-5/9, 8/27)` is a nonsingular rational point. -/
theorem nonsingular_Y : W.Nonsingular (-5/9) (8/27) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_Y
  · left
    simp
    norm_num

/-- `(21/25, -69/125)` lies on the curve. -/
theorem equation_Z : W.Equation (21/25) (-69/125) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(21/25, -69/125)` is a nonsingular rational point. -/
theorem nonsingular_Z : W.Nonsingular (21/25) (-69/125) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_Z
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

/-- The rational point `5P = (1/4, -5/8)`. -/
def w : W.Point := Point.some (1/4) (-5/8) nonsingular_W

/-- The rational point `6P = (6, 14)`. -/
def x : W.Point := Point.some 6 14 nonsingular_X

/-- The rational point `7P = (-5/9, 8/27)`. -/
def y : W.Point := Point.some (-5/9) (8/27) nonsingular_Y

/-- The rational point `8P = (21/25, -69/125)`. -/
def z : W.Point := Point.some (21/25) (-69/125) nonsingular_Z

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

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem w_coords : W.nonsingularPointEquiv w =
    (Option.some ⟨⟨1/4, -5/8⟩, nonsingular_W⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold w
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_W]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem x_coords : W.nonsingularPointEquiv x =
    (Option.some ⟨⟨6, 14⟩, nonsingular_X⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold x
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_X]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem y_coords : W.nonsingularPointEquiv y =
    (Option.some ⟨⟨-5/9, 8/27⟩, nonsingular_Y⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold y
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_Y]

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem z_coords : W.nonsingularPointEquiv z =
    (Option.some ⟨⟨21/25, -69/125⟩, nonsingular_Z⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold z
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_Z]

/-! ## Slopes and addition coordinates

These are the explicit affine formulae for the group law, verified by
`norm_num`.  They constitute the honest computational content: the coordinates
of `P + P`, `P + Q`, `Q + Q`, `T + P`, `T + T`, `V + P`, `W + P`, `X + P`, and
`Y + P` on `37a1`.
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

/-- `W.negY 0 (-1) = 0`. -/
theorem negY_0m1 : W.negY 0 (-1) = 0 := by
  rw [WeierstrassCurve.Affine.negY]
  simp

/-- `W.negY 1 (-1) = 0`. -/
theorem negY_1m1 : W.negY 1 (-1) = 0 := by
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

/-- The tangent slope at `T` is `-2`. -/
theorem slope_tt : W.slope (-1) (-1) (-1) (-1) = -2 := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (by rw [negY_tt]; norm_num : (-1 : ℚ) ≠ W.negY (-1) (-1))]
  simp
  norm_num

/-- The coordinate `x(T + T) = 6`. -/
theorem addX_tt : W.addX (-1) (-1) (W.slope (-1) (-1) (-1) (-1)) = 6 := by
  norm_num [slope_tt, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(T + T) = 14`. -/
theorem addY_tt : W.addY (-1) (-1) (-1) (W.slope (-1) (-1) (-1) (-1)) = 14 := by
  norm_num [slope_tt, WeierstrassCurve.Affine.addY]

/-- The secant slope through `V` and `P` is `-3/2`. -/
theorem slope_pv : W.slope 2 0 (-3) 0 = -3 / 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 2) (x₂ := 0) (y₁ := -3) (y₂ := 0)
    (by norm_num : (2 : ℚ) ≠ 0)]
  simp

/-- The coordinate `x(V + P) = 1/4`. -/
theorem addX_pv : W.addX 2 0 (W.slope 2 0 (-3) 0) = 1 / 4 := by
  norm_num [slope_pv, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(V + P) = -5/8`. -/
theorem addY_pv : W.addY 2 0 (-3) (W.slope 2 0 (-3) 0) = -5 / 8 := by
  norm_num [slope_pv, WeierstrassCurve.Affine.addY]

/-- The secant slope through `W` and `P` is `-5/2`. -/
theorem slope_wp : W.slope (1/4) 0 (-5/8) 0 = -5 / 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 1/4) (x₂ := 0) (y₁ := -5/8) (y₂ := 0)
    (by norm_num : (1/4 : ℚ) ≠ 0)]
  simp
  norm_num

/-- The coordinate `x(W + P) = 6`. -/
theorem addX_wp : W.addX (1/4) 0 (W.slope (1/4) 0 (-5/8) 0) = 6 := by
  norm_num [slope_wp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(W + P) = 14`. -/
theorem addY_wp : W.addY (1/4) 0 (-5/8) (W.slope (1/4) 0 (-5/8) 0) = 14 := by
  norm_num [slope_wp, WeierstrassCurve.Affine.addY]

/-- The secant slope through `X` and `P` is `7/3`. -/
theorem slope_xp : W.slope 6 0 14 0 = 7 / 3 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 6) (x₂ := 0) (y₁ := 14) (y₂ := 0)
    (by norm_num : (6 : ℚ) ≠ 0)]
  simp
  norm_num

/-- The coordinate `x(X + P) = -5/9`. -/
theorem addX_xp : W.addX 6 0 (W.slope 6 0 14 0) = -5 / 9 := by
  norm_num [slope_xp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(X + P) = 8/27`. -/
theorem addY_xp : W.addY 6 0 14 (W.slope 6 0 14 0) = 8 / 27 := by
  norm_num [slope_xp, WeierstrassCurve.Affine.addY]

/-- The secant slope through `Y` and `P` is `-8/15`. -/
theorem slope_yp : W.slope (-5/9) 0 (8/27) 0 = -8 / 15 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -5/9) (x₂ := 0) (y₁ := 8/27) (y₂ := 0)
    (by norm_num : (-5/9 : ℚ) ≠ 0)]
  simp
  norm_num

/-- The coordinate `x(Y + P) = 21/25`. -/
theorem addX_yp : W.addX (-5/9) 0 (W.slope (-5/9) 0 (8/27) 0) = 21 / 25 := by
  norm_num [slope_yp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(Y + P) = -69/125`. -/
theorem addY_yp : W.addY (-5/9) 0 (8/27) (W.slope (-5/9) 0 (8/27) 0) = -69 / 125 := by
  norm_num [slope_yp, WeierstrassCurve.Affine.addY]

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

/-- `V + P = W`; hence `5P = W`. -/
theorem add_v_p_eq_w : v + p = w := by
  unfold v p w
  rw [add_of_X_ne (x₁ := 2) (x₂ := 0) (y₁ := -3) (y₂ := 0) (h₁ := nonsingular_V)
    (h₂ := nonsingular_P) (by norm_num : (2 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_pv, addY_pv⟩

/-- `W + P = X`; hence `6P = X`. -/
theorem add_w_p_eq_x : w + p = x := by
  unfold w p x
  rw [add_of_X_ne (x₁ := 1/4) (x₂ := 0) (y₁ := -5/8) (y₂ := 0) (h₁ := nonsingular_W)
    (h₂ := nonsingular_P) (by norm_num : (1/4 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_wp, addY_wp⟩

/-- `T + T = X`; the second multiple of `T`, hence `6P = X`. -/
theorem two_t_eq_x : t + t = x := by
  unfold t x
  rw [add_self_of_Y_ne (x₁ := -1) (y₁ := -1) (h₁ := nonsingular_T)
    (by rw [negY_tt]; norm_num : (-1 : ℚ) ≠ W.negY (-1) (-1))]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_tt, addY_tt⟩

/-- `3P = T`. -/
theorem three_p_eq_t : p + p + p = t := by
  rw [two_p_eq_q, add_comm (a := q) (b := p), add_p_q_eq_t]

/-- `4P = V`. -/
theorem four_p_eq_v : p + p + p + p = v := by
  rw [two_p_eq_q, add_comm (a := q) (b := p), add_p_q_eq_t, add_t_p_eq_v]

/-- `5P = W`. -/
theorem five_p_eq_w : p + p + p + p + p = w := by
  rw [four_p_eq_v, add_v_p_eq_w]

/-- `6P = X`. -/
theorem six_p_eq_x : p + p + p + p + p + p = x := by
  rw [two_p_eq_q, add_comm (a := q) (b := p), add_p_q_eq_t, add_t_p_eq_v,
    add_v_p_eq_w, add_w_p_eq_x]

/-- `X + P = Y`; hence `7P = Y`. -/
theorem add_x_p_eq_y : x + p = y := by
  unfold x p y
  rw [add_of_X_ne (x₁ := 6) (x₂ := 0) (y₁ := 14) (y₂ := 0) (h₁ := nonsingular_X)
    (h₂ := nonsingular_P) (by norm_num : (6 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_xp, addY_xp⟩

/-- `Y + P = Z`; hence `8P = Z`. -/
theorem add_y_p_eq_z : y + p = z := by
  unfold y p z
  rw [add_of_X_ne (x₁ := -5/9) (x₂ := 0) (y₁ := 8/27) (y₂ := 0) (h₁ := nonsingular_Y)
    (h₂ := nonsingular_P) (by norm_num : (-5/9 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_yp, addY_yp⟩

/-- `7P = Y`. -/
theorem seven_p_eq_y : p + p + p + p + p + p + p = y := by
  rw [six_p_eq_x, add_x_p_eq_y]

/-- `8P = Z`. -/
theorem eight_p_eq_z : p + p + p + p + p + p + p + p = z := by
  rw [seven_p_eq_y, add_y_p_eq_z]

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

/-- `P + R = 0`, where `R = -P`. -/
theorem p_add_r_eq_zero : p + r = 0 := by
  rw [← neg_p_eq_r]
  exact p_add_neg_p_eq_zero

/-- `Q + U = 0`, where `U = -Q`. -/
theorem q_add_u_eq_zero : q + u = 0 := by
  rw [← neg_q_eq_u]
  exact add_neg_cancel q

/-- `T + S = 0`, where `S = -T`. -/
theorem t_add_s_eq_zero : t + s = 0 := by
  rw [← neg_t_eq_s]
  exact add_neg_cancel t

/-- `-R = P`. -/
theorem neg_r_eq_p : -r = p := by
  unfold r p
  rw [neg_some nonsingular_R]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, negY_0m1⟩

/-- `-U = Q`. -/
theorem neg_u_eq_q : -u = q := by
  unfold u q
  rw [neg_some nonsingular_U]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, negY_1m1⟩

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

/-- `W` is not the identity. -/
theorem w_ne_zero : w ≠ 0 :=
  some_ne_zero nonsingular_W

/-- `X` is not the identity. -/
theorem x_ne_zero : x ≠ 0 :=
  some_ne_zero nonsingular_X

/-- `Y` is not the identity. -/
theorem y_ne_zero : y ≠ 0 :=
  some_ne_zero nonsingular_Y

/-- `Z` is not the identity. -/
theorem z_ne_zero : z ≠ 0 :=
  some_ne_zero nonsingular_Z

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

/-- `5P` is not the identity. -/
theorem five_p_ne_zero : p + p + p + p + p ≠ 0 := by
  rw [five_p_eq_w]
  exact w_ne_zero

/-- `6P` is not the identity. -/
theorem six_p_ne_zero : p + p + p + p + p + p ≠ 0 := by
  rw [six_p_eq_x]
  exact x_ne_zero

/-- `7P` is not the identity. -/
theorem seven_p_ne_zero : p + p + p + p + p + p + p ≠ 0 := by
  rw [seven_p_eq_y]
  exact y_ne_zero

/-- `8P` is not the identity. -/
theorem eight_p_ne_zero : p + p + p + p + p + p + p + p ≠ 0 := by
  rw [eight_p_eq_z]
  exact z_ne_zero

/-- The points `P` and `Q` are distinct. -/
theorem p_ne_q : p ≠ q := by
  intro h
  simp only [p, q] at h
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h
  norm_num at h

/-! ## There is no torsion of order `2` through `8`

For the generator `P`, the multiples `2P`, `3P`, `4P`, `5P`, `6P`, `7P`, `8P`
are computed above and are all distinct from the identity.
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

/-- `P` does not have order `5`. -/
theorem not_five_torsion : p + p + p + p + p ≠ 0 :=
  five_p_ne_zero

/-- `P` does not have order `6`. -/
theorem not_six_torsion : p + p + p + p + p + p ≠ 0 :=
  six_p_ne_zero

/-- `P` does not have order `7`. -/
theorem not_seven_torsion : p + p + p + p + p + p + p ≠ 0 :=
  seven_p_ne_zero

/-- `P` does not have order `8`. -/
theorem not_eight_torsion : p + p + p + p + p + p + p + p ≠ 0 :=
  eight_p_ne_zero

end UniversalSingularity.BSD37a1