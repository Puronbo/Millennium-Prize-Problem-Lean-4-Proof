import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import UniversalSingularity.BSDReal

/-!
# BSD (Birch and Swinnerton-Dyer) -- concrete facts on the curve `37a1`

This module computes *genuine* arithmetic content about the specific rational
elliptic curve `37a1` (`y² + y = x³ - x`), using only what Mathlib's affine
elliptic-curve group law already provides.

Every theorem here is fully proved (no `sorry`): the discriminant `Δ = 37`,
twenty-one rational points with their group-law relations inside
`WeierstrassCurve.Affine.Point` — `P`, `2P` through `18P`, and the negatives
`-P`, `-2P`, `-3P` (with `-4P` through `-9P` recorded separately in the
symmetric family) — each of those points explicitly an integer multiple
`(m : ℤ) • p` of the generator `P` for `-9 ≤ m ≤ 18`; the pairwise
distinctness of the nineteen elements of the symmetric family
`{0, ±P, ..., ±9P}` and of `{0, 10P, ..., 18P}`; the no-torsion certificates
`(n : ℕ) • p ≠ 0` and `(n : ℤ) • p ≠ 0` for every order `2 ≤ |n| ≤ 18`; and
the resulting absence of small-order torsion for each of the named multiples
`2P` through `9P`.  These are *real* statements about *real* mathematics, in
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

/-- `(-20/49, -435/343)` lies on the curve. -/
theorem equation_A : W.Equation (-20/49) (-435/343) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `(-20/49, -435/343)` is a nonsingular rational point. -/
theorem nonsingular_A : W.Nonsingular (-20/49) (-435/343) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_A
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

/-- The rational point `9P = (-20/49, -435/343)`. -/
def a : W.Point := Point.some (-20/49) (-435/343) nonsingular_A

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

/-- The canonical equivalence records the coordinates of the rational points. -/
theorem a_coords : W.nonsingularPointEquiv a =
    (Option.some ⟨⟨-20/49, -435/343⟩, nonsingular_A⟩ :
      WithZero {xy : ℚ × ℚ // W.Nonsingular xy.fst xy.snd}) := by
  unfold a
  rw [WeierstrassCurve.Affine.nonsingularPointEquiv_some nonsingular_A]

/-! ## Slopes and addition coordinates

These are the explicit affine formulae for the group law, verified by
`norm_num`.  They constitute the honest computational content: the coordinates
of `P + P`, `P + Q`, `Q + Q`, `T + P`, `T + T`, `V + P`, `W + P`, `X + P`,
`Y + P`, and `Z + P` on `37a1`.
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

/-- The secant slope through `Z` and `P` is `-23/35`. -/
theorem slope_zp : W.slope (21/25) 0 (-69/125) 0 = -23 / 35 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 21/25) (x₂ := 0) (y₁ := -69/125) (y₂ := 0)
    (by norm_num : (21/25 : ℚ) ≠ 0)]
  simp
  norm_num

/-- The coordinate `x(Z + P) = -20/49`. -/
theorem addX_zp : W.addX (21/25) 0 (W.slope (21/25) 0 (-69/125) 0) = -20 / 49 := by
  norm_num [slope_zp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(Z + P) = -435/343`. -/
theorem addY_zp : W.addY (21/25) 0 (-69/125) (W.slope (21/25) 0 (-69/125) 0) = -435 / 343 := by
  norm_num [slope_zp, WeierstrassCurve.Affine.addY]

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

/-- `Z + P = A`; hence `9P = A`. -/
theorem add_z_p_eq_a : z + p = a := by
  unfold z p a
  rw [add_of_X_ne (x₁ := 21/25) (x₂ := 0) (y₁ := -69/125) (y₂ := 0) (h₁ := nonsingular_Z)
    (h₂ := nonsingular_P) (by norm_num : (21/25 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_zp, addY_zp⟩

/-- `7P = Y`. -/
theorem seven_p_eq_y : p + p + p + p + p + p + p = y := by
  rw [six_p_eq_x, add_x_p_eq_y]

/-- `8P = Z`. -/
theorem eight_p_eq_z : p + p + p + p + p + p + p + p = z := by
  rw [seven_p_eq_y, add_y_p_eq_z]

/-- `9P = A`. -/
theorem nine_p_eq_a : p + p + p + p + p + p + p + p + p = a := by
  rw [eight_p_eq_z, add_z_p_eq_a]

/-! ## An independent computation: `3T = 9P`

Adding `T` and `X` directly gives the same point as the nine-term chain: with
`T = 3P` and `X = 6P` the relation `T + X = 9P` is `3T = 9P`, cross-checking the
doubling `2T = X` and the multiple `9P = A` above.
-/

/-- The secant slope through `T` and `X` is `15/7`. -/
theorem slope_tx : W.slope (-1) 6 (-1) 14 = 15 / 7 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -1) (x₂ := 6) (y₁ := -1) (y₂ := 14)
    (by norm_num : (-1 : ℚ) ≠ 6)]
  norm_num

/-- The coordinate `x(T + X) = -20/49`. -/
theorem addX_tx : W.addX (-1) 6 (W.slope (-1) 6 (-1) 14) = -20 / 49 := by
  norm_num [slope_tx, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(T + X) = -435/343`. -/
theorem addY_tx : W.addY (-1) 6 (-1) (W.slope (-1) 6 (-1) 14) = -435 / 343 := by
  norm_num [slope_tx, WeierstrassCurve.Affine.addY]

/-- `T + X = A`, i.e. `3T = 9P`. -/
theorem add_t_x_eq_a : t + x = a := by
  unfold t x a
  rw [add_of_X_ne (x₁ := -1) (x₂ := 6) (y₁ := -1) (y₂ := 14) (h₁ := nonsingular_T)
    (h₂ := nonsingular_X) (by norm_num : (-1 : ℚ) ≠ 6)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_tx, addY_tx⟩

/-- `3T = 9P`. -/
theorem three_t_eq_a : t + t + t = a := by
  rw [two_t_eq_x]
  rw [add_comm]
  exact add_t_x_eq_a

/-! ## More direct pair additions

The sums `Q + R`, `Q + T`, `S + P`, and `U + T` are computed directly from the
chord-slope definition, cross-checking the identities `Q = 2P`, `R = -P`,
`T = 3P`, `S = -3P`, and `U = -2P` established above.
-/

/-- `Q + R = P`, i.e. `2P + (-P) = P`. -/
theorem q_add_r_eq_p : q + r = p := by
  unfold p q r
  rw [add_of_X_ne (x₁ := 1) (x₂ := 0) (y₁ := 0) (y₂ := -1) (h₁ := nonsingular_Q)
    (h₂ := nonsingular_R) (by norm_num : (1 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope_of_X_ne, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY]

/-- `Q + T = W`, i.e. `2P + 3P = 5P`. -/
theorem q_add_t_eq_w : q + t = w := by
  unfold q t w
  rw [add_of_X_ne (x₁ := 1) (x₂ := -1) (y₁ := 0) (y₂ := -1) (h₁ := nonsingular_Q)
    (h₂ := nonsingular_T) (by norm_num : (1 : ℚ) ≠ -1)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope_of_X_ne, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY]

/-- `S + P = U`, i.e. `-3P + P = -2P`. -/
theorem s_add_p_eq_u : s + p = u := by
  unfold p s u
  rw [add_of_X_ne (x₁ := -1) (x₂ := 0) (y₁ := 0) (y₂ := 0) (h₁ := nonsingular_S)
    (h₂ := nonsingular_P) (by norm_num : (-1 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope_of_X_ne, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY]

/-- `U + T = P`, i.e. `-2P + 3P = P`. -/
theorem u_add_t_eq_p : u + t = p := by
  unfold p u t
  rw [add_of_X_ne (x₁ := 1) (x₂ := -1) (y₁ := -1) (y₂ := -1) (h₁ := nonsingular_U)
    (h₂ := nonsingular_T) (by norm_num : (1 : ℚ) ≠ -1)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.slope_of_X_ne, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY]

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

/-- `-(2P) = U`: the negative of a multiple is the corresponding negative
multiple. -/
theorem neg_two_p_eq_u : -(p + p) = u := by
  rw [two_p_eq_q, neg_q_eq_u]

/-- `-(3P) = S`. -/
theorem neg_three_p_eq_s : -(p + p + p) = s := by
  rw [three_p_eq_t, neg_t_eq_s]

/-- `-S = T`: the negative of `-3P` is `3P`. -/
theorem neg_s_eq_t : -s = t := by
  rw [← neg_t_eq_s, neg_neg]

/-! ## The further multiples `10P` through `18P`

The nine multiples `10P, ..., 18P` are computed exactly as the earlier ones,
each as the chord sum `(n - 1)P + P` through the previously computed point and
`P`.  Together with the nineteen elements `{0, ±P, ..., ±9P}` these give
twenty-seven pairwise-distinct rational points on `37a1`.  Their main purpose
is to certify the non-vanishing `(k : ℕ) • p ≠ 0` for every `k ≤ 18`, from which
the small-order no-torsion certificates for the named multiples follow below:
for instance the claim `(2 : ℕ) • (2P) ≠ 0` is the claim `(4 : ℕ) • P ≠ 0`.
-/

/-! ### `10P` -/

/-- The secant slope through `A` and `P` is `87/28`. -/
theorem slope_ap : W.slope (-20/49) 0 (-435/343) 0 = 87 / 28 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -20/49) (x₂ := 0) (y₁ := -435/343) (y₂ := 0)
    (by norm_num : (-20/49 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(A + P) = x(10P) = 161/16`. -/
theorem addX_ap : W.addX (-20/49) 0 (W.slope (-20/49) 0 (-435/343) 0) = 161 / 16 := by
  norm_num [slope_ap, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(A + P) = y(10P) = -2065/64`. -/
theorem addY_ap : W.addY (-20/49) 0 (-435/343) (W.slope (-20/49) 0 (-435/343) 0) = -2065 / 64 := by
  norm_num [slope_ap, WeierstrassCurve.Affine.addY]

/-- `10P = (161/16, -2065/64)` lies on the curve. -/
theorem equation_b : W.Equation (161/16) (-2065/64) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `10P = (161/16, -2065/64)` is a nonsingular rational point. -/
theorem nonsingular_b : W.Nonsingular (161/16) (-2065/64) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_b
  · left
    simp
    norm_num

/-- The point `10P = (161/16, -2065/64)`. -/
def b : W.Point := Point.some (161/16) (-2065/64) nonsingular_b

/-- `A + P = B`; hence `10P = B`. -/
theorem add_a_p_eq_b : a + p = b := by
  unfold a p b
  rw [add_of_X_ne (x₁ := -20/49) (x₂ := 0) (y₁ := -435/343) (y₂ := 0) (h₁ := nonsingular_A)
    (h₂ := nonsingular_P) (by norm_num : (-20/49 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_ap, addY_ap⟩

/-- `10P = B`. -/
theorem ten_p_eq_b : p + p + p + p + p + p + p + p + p + p = b := by
  rw [nine_p_eq_a, add_a_p_eq_b]

/-! ### `11P` -/

/-- The secant slope through `B` and `P` is `-295/92`. -/
theorem slope_bp : W.slope (161/16) 0 (-2065/64) 0 = -295 / 92 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 161/16) (x₂ := 0) (y₁ := -2065/64) (y₂ := 0)
    (by norm_num : (161/16 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(B + P) = x(11P) = 116/529`. -/
theorem addX_bp : W.addX (161/16) 0 (W.slope (161/16) 0 (-2065/64) 0) = 116 / 529 := by
  norm_num [slope_bp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(B + P) = y(11P) = -3612/12167`. -/
theorem addY_bp : W.addY (161/16) 0 (-2065/64) (W.slope (161/16) 0 (-2065/64) 0) = -3612 / 12167 := by
  norm_num [slope_bp, WeierstrassCurve.Affine.addY]

/-- `11P = (116/529, -3612/12167)` lies on the curve. -/
theorem equation_c : W.Equation (116/529) (-3612/12167) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `11P = (116/529, -3612/12167)` is a nonsingular rational point. -/
theorem nonsingular_c : W.Nonsingular (116/529) (-3612/12167) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_c
  · left
    simp
    norm_num

/-- The point `11P = (116/529, -3612/12167)`. -/
def c : W.Point := Point.some (116/529) (-3612/12167) nonsingular_c

/-- `B + P = C`; hence `11P = C`. -/
theorem add_b_p_eq_c : b + p = c := by
  unfold b p c
  rw [add_of_X_ne (x₁ := 161/16) (x₂ := 0) (y₁ := -2065/64) (y₂ := 0) (h₁ := nonsingular_b)
    (h₂ := nonsingular_P) (by norm_num : (161/16 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_bp, addY_bp⟩

/-- `11P = C`. -/
theorem eleven_p_eq_c : p + p + p + p + p + p + p + p + p + p + p = c := by
  rw [ten_p_eq_b, add_b_p_eq_c]

/-! ### `12P` -/

/-- The secant slope through `C` and `P` is `-903/667`. -/
theorem slope_cp : W.slope (116/529) 0 (-3612/12167) 0 = -903 / 667 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 116/529) (x₂ := 0) (y₁ := -3612/12167) (y₂ := 0)
    (by norm_num : (116/529 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(C + P) = x(12P) = 1357/841`. -/
theorem addX_cp : W.addX (116/529) 0 (W.slope (116/529) 0 (-3612/12167) 0) = 1357 / 841 := by
  norm_num [slope_cp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(C + P) = y(12P) = 28888/24389`. -/
theorem addY_cp : W.addY (116/529) 0 (-3612/12167) (W.slope (116/529) 0 (-3612/12167) 0) = 28888 / 24389 := by
  norm_num [slope_cp, WeierstrassCurve.Affine.addY]

/-- `12P = (1357/841, 28888/24389)` lies on the curve. -/
theorem equation_d : W.Equation (1357/841) (28888/24389) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `12P = (1357/841, 28888/24389)` is a nonsingular rational point. -/
theorem nonsingular_d : W.Nonsingular (1357/841) (28888/24389) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_d
  · left
    simp
    norm_num

/-- The point `12P = (1357/841, 28888/24389)`. -/
def d : W.Point := Point.some (1357/841) (28888/24389) nonsingular_d

/-- `C + P = D`; hence `12P = D`. -/
theorem add_c_p_eq_d : c + p = d := by
  unfold c p d
  rw [add_of_X_ne (x₁ := 116/529) (x₂ := 0) (y₁ := -3612/12167) (y₂ := 0) (h₁ := nonsingular_c)
    (h₂ := nonsingular_P) (by norm_num : (116/529 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_cp, addY_cp⟩

/-- `12P = D`. -/
theorem twelve_p_eq_d : p + p + p + p + p + p + p + p + p + p + p + p = d := by
  rw [eleven_p_eq_c, add_c_p_eq_d]

/-! ### `13P` -/

/-- The secant slope through `D` and `P` is `1256/1711`. -/
theorem slope_dp : W.slope (1357/841) 0 (28888/24389) 0 = 1256 / 1711 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 1357/841) (x₂ := 0) (y₁ := 28888/24389) (y₂ := 0)
    (by norm_num : (1357/841 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(D + P) = x(13P) = -3741/3481`. -/
theorem addX_dp : W.addX (1357/841) 0 (W.slope (1357/841) 0 (28888/24389) 0) = -3741 / 3481 := by
  norm_num [slope_dp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(D + P) = y(13P) = -43355/205379`. -/
theorem addY_dp : W.addY (1357/841) 0 (28888/24389) (W.slope (1357/841) 0 (28888/24389) 0) = -43355 / 205379 := by
  norm_num [slope_dp, WeierstrassCurve.Affine.addY]

/-- `13P = (-3741/3481, -43355/205379)` lies on the curve. -/
theorem equation_e : W.Equation (-3741/3481) (-43355/205379) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `13P = (-3741/3481, -43355/205379)` is a nonsingular rational point. -/
theorem nonsingular_e : W.Nonsingular (-3741/3481) (-43355/205379) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_e
  · left
    simp
    norm_num

/-- The point `13P = (-3741/3481, -43355/205379)`. -/
def e : W.Point := Point.some (-3741/3481) (-43355/205379) nonsingular_e

/-- `D + P = E`; hence `13P = E`. -/
theorem add_d_p_eq_e : d + p = e := by
  unfold d p e
  rw [add_of_X_ne (x₁ := 1357/841) (x₂ := 0) (y₁ := 28888/24389) (y₂ := 0) (h₁ := nonsingular_d)
    (h₂ := nonsingular_P) (by norm_num : (1357/841 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_dp, addY_dp⟩

/-- `13P = E`. -/
theorem thirteen_p_eq_e : p + p + p + p + p + p + p + p + p + p + p + p + p = e := by
  rw [twelve_p_eq_d, add_d_p_eq_e]

/-! ### `14P` -/

/-- The secant slope through `E` and `P` is `1495/7611`. -/
theorem slope_ep : W.slope (-3741/3481) 0 (-43355/205379) 0 = 1495 / 7611 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -3741/3481) (x₂ := 0) (y₁ := -43355/205379) (y₂ := 0)
    (by norm_num : (-3741/3481 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(E + P) = x(14P) = 18526/16641`. -/
theorem addX_ep : W.addX (-3741/3481) 0 (W.slope (-3741/3481) 0 (-43355/205379) 0) = 18526 / 16641 := by
  norm_num [slope_ep, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(E + P) = y(14P) = -2616119/2146689`. -/
theorem addY_ep : W.addY (-3741/3481) 0 (-43355/205379) (W.slope (-3741/3481) 0 (-43355/205379) 0) = -2616119 / 2146689 := by
  norm_num [slope_ep, WeierstrassCurve.Affine.addY]

/-- `14P = (18526/16641, -2616119/2146689)` lies on the curve. -/
theorem equation_f : W.Equation (18526/16641) (-2616119/2146689) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `14P = (18526/16641, -2616119/2146689)` is a nonsingular rational point. -/
theorem nonsingular_f : W.Nonsingular (18526/16641) (-2616119/2146689) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_f
  · left
    simp
    norm_num

/-- The point `14P = (18526/16641, -2616119/2146689)`. -/
def f : W.Point := Point.some (18526/16641) (-2616119/2146689) nonsingular_f

/-- `E + P = F`; hence `14P = F`. -/
theorem add_e_p_eq_f : e + p = f := by
  unfold e p f
  rw [add_of_X_ne (x₁ := -3741/3481) (x₂ := 0) (y₁ := -43355/205379) (y₂ := 0) (h₁ := nonsingular_e)
    (h₂ := nonsingular_P) (by norm_num : (-3741/3481 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_ep, addY_ep⟩

/-- `14P = F`. -/
theorem fourteen_p_eq_f : p + p + p + p + p + p + p + p + p + p + p + p + p + p = f := by
  rw [thirteen_p_eq_e, add_e_p_eq_f]

/-! ### `15P` -/

/-- The secant slope through `F` and `P` is `-44341/40506`. -/
theorem slope_fp : W.slope (18526/16641) 0 (-2616119/2146689) 0 = -44341 / 40506 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 18526/16641) (x₂ := 0) (y₁ := -2616119/2146689) (y₂ := 0)
    (by norm_num : (18526/16641 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(F + P) = x(15P) = 8385/98596`. -/
theorem addX_fp : W.addX (18526/16641) 0 (W.slope (18526/16641) 0 (-2616119/2146689) 0) = 8385 / 98596 := by
  norm_num [slope_fp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(F + P) = y(15P) = -28076979/30959144`. -/
theorem addY_fp : W.addY (18526/16641) 0 (-2616119/2146689) (W.slope (18526/16641) 0 (-2616119/2146689) 0) = -28076979 / 30959144 := by
  norm_num [slope_fp, WeierstrassCurve.Affine.addY]

/-- `15P = (8385/98596, -28076979/30959144)` lies on the curve. -/
theorem equation_g : W.Equation (8385/98596) (-28076979/30959144) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `15P = (8385/98596, -28076979/30959144)` is a nonsingular rational point. -/
theorem nonsingular_g : W.Nonsingular (8385/98596) (-28076979/30959144) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_g
  · left
    simp
    norm_num

/-- The point `15P = (8385/98596, -28076979/30959144)`. -/
def g : W.Point := Point.some (8385/98596) (-28076979/30959144) nonsingular_g

/-- `F + P = G`; hence `15P = G`. -/
theorem add_f_p_eq_g : f + p = g := by
  unfold f p g
  rw [add_of_X_ne (x₁ := 18526/16641) (x₂ := 0) (y₁ := -2616119/2146689) (y₂ := 0) (h₁ := nonsingular_f)
    (h₂ := nonsingular_P) (by norm_num : (18526/16641 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_fp, addY_fp⟩

/-- `15P = G`. -/
theorem fifteen_p_eq_g : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = g := by
  rw [fourteen_p_eq_f, add_f_p_eq_g]

/-! ### `16P` -/

/-- The secant slope through `G` and `P` is `-217651/20410`. -/
theorem slope_gp : W.slope (8385/98596) 0 (-28076979/30959144) 0 = -217651 / 20410 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 8385/98596) (x₂ := 0) (y₁ := -28076979/30959144) (y₂ := 0)
    (by norm_num : (8385/98596 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(G + P) = x(16P) = 480106/4225`. -/
theorem addX_gp : W.addX (8385/98596) 0 (W.slope (8385/98596) 0 (-28076979/30959144) 0) = 480106 / 4225 := by
  norm_num [slope_gp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(G + P) = y(16P) = 332513754/274625`. -/
theorem addY_gp : W.addY (8385/98596) 0 (-28076979/30959144) (W.slope (8385/98596) 0 (-28076979/30959144) 0) = 332513754 / 274625 := by
  norm_num [slope_gp, WeierstrassCurve.Affine.addY]

/-- `16P = (480106/4225, 332513754/274625)` lies on the curve. -/
theorem equation_h : W.Equation (480106/4225) (332513754/274625) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `16P = (480106/4225, 332513754/274625)` is a nonsingular rational point. -/
theorem nonsingular_h : W.Nonsingular (480106/4225) (332513754/274625) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_h
  · left
    simp
    norm_num

/-- The point `16P = (480106/4225, 332513754/274625)`. -/
def h : W.Point := Point.some (480106/4225) (332513754/274625) nonsingular_h

/-- `G + P = H`; hence `16P = H`. -/
theorem add_g_p_eq_h : g + p = h := by
  unfold g p h
  rw [add_of_X_ne (x₁ := 8385/98596) (x₂ := 0) (y₁ := -28076979/30959144) (y₂ := 0) (h₁ := nonsingular_g)
    (h₂ := nonsingular_P) (by norm_num : (8385/98596 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_gp, addY_gp⟩

/-- `16P = H`. -/
theorem sixteen_p_eq_h : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = h := by
  rw [fifteen_p_eq_g, add_g_p_eq_h]

/-! ### `17P` -/

/-- The secant slope through `H` and `P` is `1058961/99385`. -/
theorem slope_hp : W.slope (480106/4225) 0 (332513754/274625) 0 = 1058961 / 99385 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 480106/4225) (x₂ := 0) (y₁ := 332513754/274625) (y₂ := 0)
    (by norm_num : (480106/4225 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(H + P) = x(17P) = -239785/2337841`. -/
theorem addX_hp : W.addX (480106/4225) 0 (W.slope (480106/4225) 0 (332513754/274625) 0) = -239785 / 2337841 := by
  norm_num [slope_hp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(H + P) = y(17P) = 331948240/3574558889`. -/
theorem addY_hp : W.addY (480106/4225) 0 (332513754/274625) (W.slope (480106/4225) 0 (332513754/274625) 0) = 331948240 / 3574558889 := by
  norm_num [slope_hp, WeierstrassCurve.Affine.addY]

/-- `17P = (-239785/2337841, 331948240/3574558889)` lies on the curve. -/
theorem equation_i : W.Equation (-239785/2337841) (331948240/3574558889) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `17P = (-239785/2337841, 331948240/3574558889)` is a nonsingular rational point. -/
theorem nonsingular_i : W.Nonsingular (-239785/2337841) (331948240/3574558889) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_i
  · left
    simp
    norm_num

/-- The point `17P = (-239785/2337841, 331948240/3574558889)`. -/
def i : W.Point := Point.some (-239785/2337841) (331948240/3574558889) nonsingular_i

/-- `H + P = I`; hence `17P = I`. -/
theorem add_h_p_eq_i : h + p = i := by
  unfold h p i
  rw [add_of_X_ne (x₁ := 480106/4225) (x₂ := 0) (y₁ := 332513754/274625) (y₂ := 0) (h₁ := nonsingular_h)
    (h₂ := nonsingular_P) (by norm_num : (480106/4225 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_hp, addY_hp⟩

/-- `17P = I`. -/
theorem seventeen_p_eq_i : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = i := by
  rw [sixteen_p_eq_h, add_h_p_eq_i]

/-! ### `18P` -/

/-- The secant slope through `I` and `P` is `-5106896/5640481`. -/
theorem slope_ip : W.slope (-239785/2337841) 0 (331948240/3574558889) 0 = -5106896 / 5640481 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -239785/2337841) (x₂ := 0) (y₁ := 331948240/3574558889) (y₂ := 0)
    (by norm_num : (-239785/2337841 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(I + P) = x(18P) = 12551561/13608721`. -/
theorem addX_ip : W.addX (-239785/2337841) 0 (W.slope (-239785/2337841) 0 (331948240/3574558889) 0) = 12551561 / 13608721 := by
  norm_num [slope_ip, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(I + P) = y(18P) = -8280062505/50202571769`. -/
theorem addY_ip : W.addY (-239785/2337841) 0 (331948240/3574558889) (W.slope (-239785/2337841) 0 (331948240/3574558889) 0) = -8280062505 / 50202571769 := by
  norm_num [slope_ip, WeierstrassCurve.Affine.addY]

/-- `18P = (12551561/13608721, -8280062505/50202571769)` lies on the curve. -/
theorem equation_j : W.Equation (12551561/13608721) (-8280062505/50202571769) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `18P = (12551561/13608721, -8280062505/50202571769)` is a nonsingular rational point. -/
theorem nonsingular_j : W.Nonsingular (12551561/13608721) (-8280062505/50202571769) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_j
  · left
    simp
    norm_num

/-- The point `18P = (12551561/13608721, -8280062505/50202571769)`. -/
def j : W.Point := Point.some (12551561/13608721) (-8280062505/50202571769) nonsingular_j

/-- `I + P = J`; hence `18P = J`. -/
theorem add_i_p_eq_j : i + p = j := by
  unfold i p j
  rw [add_of_X_ne (x₁ := -239785/2337841) (x₂ := 0) (y₁ := 331948240/3574558889) (y₂ := 0) (h₁ := nonsingular_i)
    (h₂ := nonsingular_P) (by norm_num : (-239785/2337841 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_ip, addY_ip⟩

/-- `18P = J`. -/
theorem eighteen_p_eq_j : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = j := by
  rw [seventeen_p_eq_i, add_i_p_eq_j]

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

/-- `A` is not the identity. -/
theorem a_ne_zero : a ≠ 0 :=
  some_ne_zero nonsingular_A

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

/-- `9P` is not the identity. -/
theorem nine_p_ne_zero : p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [nine_p_eq_a]
  exact a_ne_zero

/-- `10P` is not the identity. -/
theorem b_ne_zero : b ≠ 0 :=
  some_ne_zero nonsingular_b

/-- `11P` is not the identity. -/
theorem c_ne_zero : c ≠ 0 :=
  some_ne_zero nonsingular_c

/-- `12P` is not the identity. -/
theorem d_ne_zero : d ≠ 0 :=
  some_ne_zero nonsingular_d

/-- `13P` is not the identity. -/
theorem e_ne_zero : e ≠ 0 :=
  some_ne_zero nonsingular_e

/-- `14P` is not the identity. -/
theorem f_ne_zero : f ≠ 0 :=
  some_ne_zero nonsingular_f

/-- `15P` is not the identity. -/
theorem g_ne_zero : g ≠ 0 :=
  some_ne_zero nonsingular_g

/-- `16P` is not the identity. -/
theorem h_ne_zero : h ≠ 0 :=
  some_ne_zero nonsingular_h

/-- `17P` is not the identity. -/
theorem i_ne_zero : i ≠ 0 :=
  some_ne_zero nonsingular_i

/-- `18P` is not the identity. -/
theorem j_ne_zero : j ≠ 0 :=
  some_ne_zero nonsingular_j

/-- `10P` is not the identity. -/
theorem ten_p_ne_zero : p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [ten_p_eq_b]
  exact b_ne_zero

/-- `11P` is not the identity. -/
theorem eleven_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [eleven_p_eq_c]
  exact c_ne_zero

/-- `12P` is not the identity. -/
theorem twelve_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twelve_p_eq_d]
  exact d_ne_zero

/-- `13P` is not the identity. -/
theorem thirteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [thirteen_p_eq_e]
  exact e_ne_zero

/-- `14P` is not the identity. -/
theorem fourteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [fourteen_p_eq_f]
  exact f_ne_zero

/-- `15P` is not the identity. -/
theorem fifteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [fifteen_p_eq_g]
  exact g_ne_zero

/-- `16P` is not the identity. -/
theorem sixteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [sixteen_p_eq_h]
  exact h_ne_zero

/-- `17P` is not the identity. -/
theorem seventeen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [seventeen_p_eq_i]
  exact i_ne_zero

/-- `18P` is not the identity. -/
theorem eighteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [eighteen_p_eq_j]
  exact j_ne_zero

/-- The points `P` and `Q` are distinct. -/
theorem p_ne_q : p ≠ q := by
  intro h
  simp only [p, q] at h
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h
  norm_num at h

/-! ## There is no torsion of order `2` through `18`

For the generator `P`, the multiples `2P`, `3P`, `4P`, `5P`, `6P`, `7P`, `8P`,
`9P` are computed above and are all distinct from the identity; the further
multiples `10P` through `27P` extend this through `27P`.  Below, the same
facts are restated in the group-theoretic form `(n : ℕ) • p ≠ 0`, using the
`nsmul` operation of the additive group of the curve; the rewrite by
`succ_nsmul` recovers the repeated-sum notation of the `*_ne_zero` theorems,
and the orders `10` through `27` are transferred from the integer form via
`natCast_zsmul`.
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

/-- `P` does not have order `9`. -/
theorem not_nine_torsion : p + p + p + p + p + p + p + p + p ≠ 0 :=
  nine_p_ne_zero

/-- `P` does not have order `2`, in the `(n : ℕ) • p` notation. -/
theorem not_two_nsmul_torsion : (2 : ℕ) • p ≠ 0 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num,
    succ_nsmul]
  exact two_p_ne_zero

/-- `P` does not have order `3`, in the `(n : ℕ) • p` notation. -/
theorem not_three_nsmul_torsion : (3 : ℕ) • p ≠ 0 := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num,
    succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num, succ_nsmul]
  exact three_p_ne_zero

/-- `P` does not have order `4`, in the `(n : ℕ) • p` notation. -/
theorem not_four_nsmul_torsion : (4 : ℕ) • p ≠ 0 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num,
    succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num, succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num,
    succ_nsmul]
  exact four_p_ne_zero

/-- `P` does not have order `5`, in the `(n : ℕ) • p` notation. -/
theorem not_five_nsmul_torsion : (5 : ℕ) • p ≠ 0 := by
  rw [show (5 : ℕ) = 4 + 1 by norm_num, succ_nsmul, show (4 : ℕ) = 3 + 1 by norm_num,
    succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num, succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num,
    succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num, succ_nsmul]
  exact five_p_ne_zero

/-- `P` does not have order `6`, in the `(n : ℕ) • p` notation. -/
theorem not_six_nsmul_torsion : (6 : ℕ) • p ≠ 0 := by
  rw [show (6 : ℕ) = 5 + 1 by norm_num, succ_nsmul, show (5 : ℕ) = 4 + 1 by norm_num,
    succ_nsmul, show (4 : ℕ) = 3 + 1 by norm_num, succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num,
    succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num, succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num,
    succ_nsmul]
  exact six_p_ne_zero

/-- `P` does not have order `7`, in the `(n : ℕ) • p` notation. -/
theorem not_seven_nsmul_torsion : (7 : ℕ) • p ≠ 0 := by
  rw [show (7 : ℕ) = 6 + 1 by norm_num, succ_nsmul, show (6 : ℕ) = 5 + 1 by norm_num,
    succ_nsmul, show (5 : ℕ) = 4 + 1 by norm_num, succ_nsmul, show (4 : ℕ) = 3 + 1 by norm_num,
    succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num, succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num,
    succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num, succ_nsmul]
  exact seven_p_ne_zero

/-- `P` does not have order `8`, in the `(n : ℕ) • p` notation. -/
theorem not_eight_nsmul_torsion : (8 : ℕ) • p ≠ 0 := by
  rw [show (8 : ℕ) = 7 + 1 by norm_num, succ_nsmul, show (7 : ℕ) = 6 + 1 by norm_num,
    succ_nsmul, show (6 : ℕ) = 5 + 1 by norm_num, succ_nsmul, show (5 : ℕ) = 4 + 1 by norm_num,
    succ_nsmul, show (4 : ℕ) = 3 + 1 by norm_num, succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num,
    succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num, succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num,
    succ_nsmul]
  exact eight_p_ne_zero

/-- `P` does not have order `9`, in the `(n : ℕ) • p` notation. -/
theorem not_nine_nsmul_torsion : (9 : ℕ) • p ≠ 0 := by
  rw [show (9 : ℕ) = 8 + 1 by norm_num, succ_nsmul, show (8 : ℕ) = 7 + 1 by norm_num,
    succ_nsmul, show (7 : ℕ) = 6 + 1 by norm_num, succ_nsmul, show (6 : ℕ) = 5 + 1 by norm_num,
    succ_nsmul, show (5 : ℕ) = 4 + 1 by norm_num, succ_nsmul, show (4 : ℕ) = 3 + 1 by norm_num,
    succ_nsmul, show (3 : ℕ) = 2 + 1 by norm_num, succ_nsmul, show (2 : ℕ) = 1 + 1 by norm_num,
    succ_nsmul, show (1 : ℕ) = 0 + 1 by norm_num, succ_nsmul]
  exact nine_p_ne_zero

/-! ## The integer multiples of `P`

The `zsmul` operation `(n : ℤ) • p` recovers the named points for every
`n` with `-3 ≤ n ≤ 9`; in particular every one of the twelve listed points is
an integer multiple of `P` (`P`, `2P`, `3P`, `-3P`, `-2P`, and `4P` through
`9P`, together with the negatives `-P`, `-2P`, `-3P`).  The no-torsion facts
transfer to the integer form: `(n : ℤ) • p ≠ 0` for every such `n ≠ 0`.
-/

/-- `0 • P` is the identity. -/
theorem zero_zsmul_p_eq_zero : (0 : ℤ) • p = 0 := by
  simp

/-- `1 • P = P`. -/
theorem one_zsmul_p_eq_p : (1 : ℤ) • p = p := by
  simp

/-- `2 • P = Q`. -/
theorem two_zsmul_p_eq_q : (2 : ℤ) • p = q := by
  rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
  exact two_p_eq_q

/-- `3 • P = T`. -/
theorem three_zsmul_p_eq_t : (3 : ℤ) • p = t := by
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact three_p_eq_t

/-- `4 • P = V`. -/
theorem four_zsmul_p_eq_v : (4 : ℤ) • p = v := by
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact four_p_eq_v

/-- `5 • P = W`. -/
theorem five_zsmul_p_eq_w : (5 : ℤ) • p = w := by
  rw [show (5 : ℤ) = (4 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact five_p_eq_w

/-- `6 • P = X`. -/
theorem six_zsmul_p_eq_x : (6 : ℤ) • p = x := by
  rw [show (6 : ℤ) = (5 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (5 : ℤ) = (4 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact six_p_eq_x

/-- `7 • P = Y`. -/
theorem seven_zsmul_p_eq_y : (7 : ℤ) • p = y := by
  rw [show (7 : ℤ) = (6 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (6 : ℤ) = (5 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (5 : ℤ) = (4 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact seven_p_eq_y

/-- `8 • P = Z`. -/
theorem eight_zsmul_p_eq_z : (8 : ℤ) • p = z := by
  rw [show (8 : ℤ) = (7 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (7 : ℤ) = (6 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (6 : ℤ) = (5 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (5 : ℤ) = (4 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact eight_p_eq_z

/-- `9 • P = A`. -/
theorem nine_zsmul_p_eq_a : (9 : ℤ) • p = a := by
  rw [show (9 : ℤ) = (8 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (8 : ℤ) = (7 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (7 : ℤ) = (6 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (6 : ℤ) = (5 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (5 : ℤ) = (4 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (4 : ℤ) = (3 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact nine_p_eq_a

/-- `(-1) • P = R`. -/
theorem neg_one_zsmul_p_eq_r : (-1 : ℤ) • p = r := by
  rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, neg_zsmul]
  exact neg_p_eq_r

/-- `(-2) • P = U`. -/
theorem neg_two_zsmul_p_eq_u : (-2 : ℤ) • p = u := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, neg_zsmul]
  exact neg_two_p_eq_u

/-- `(-3) • P = S`. -/
theorem neg_three_zsmul_p_eq_s : (-3 : ℤ) • p = s := by
  rw [neg_zsmul]
  rw [show (3 : ℤ) = (2 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [one_zsmul]
  exact neg_three_p_eq_s

/-- `|P|` does not vanish under integer multiplication by `2`. -/
theorem two_zsmul_p_ne_zero : (2 : ℤ) • p ≠ 0 := by
  rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
  exact not_two_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `3`. -/
theorem three_zsmul_p_ne_zero : (3 : ℤ) • p ≠ 0 := by
  rw [show (3 : ℤ) = (3 : ℕ) by norm_num]
  exact not_three_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `4`. -/
theorem four_zsmul_p_ne_zero : (4 : ℤ) • p ≠ 0 := by
  rw [show (4 : ℤ) = (4 : ℕ) by norm_num]
  exact not_four_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `5`. -/
theorem five_zsmul_p_ne_zero : (5 : ℤ) • p ≠ 0 := by
  rw [show (5 : ℤ) = (5 : ℕ) by norm_num]
  exact not_five_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `6`. -/
theorem six_zsmul_p_ne_zero : (6 : ℤ) • p ≠ 0 := by
  rw [show (6 : ℤ) = (6 : ℕ) by norm_num]
  exact not_six_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `7`. -/
theorem seven_zsmul_p_ne_zero : (7 : ℤ) • p ≠ 0 := by
  rw [show (7 : ℤ) = (7 : ℕ) by norm_num]
  exact not_seven_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `8`. -/
theorem eight_zsmul_p_ne_zero : (8 : ℤ) • p ≠ 0 := by
  rw [show (8 : ℤ) = (8 : ℕ) by norm_num]
  exact not_eight_nsmul_torsion

/-- `|P|` does not vanish under integer multiplication by `9`. -/
theorem nine_zsmul_p_ne_zero : (9 : ℤ) • p ≠ 0 := by
  rw [show (9 : ℤ) = (9 : ℕ) by norm_num]
  exact not_nine_nsmul_torsion

/-- `(-1) • P` is not the identity. -/
theorem neg_one_zsmul_p_ne_zero : (-1 : ℤ) • p ≠ 0 := by
  rw [neg_zsmul]
  exact neg_ne_zero.mpr p_ne_zero

/-- `(-2) • P` is not the identity. -/
theorem neg_two_zsmul_p_ne_zero : (-2 : ℤ) • p ≠ 0 := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, neg_zsmul]
  exact neg_ne_zero.mpr not_two_nsmul_torsion

/-- `(-3) • P` is not the identity. -/
theorem neg_three_zsmul_p_ne_zero : (-3 : ℤ) • p ≠ 0 := by
  rw [show (-3 : ℤ) = -(3 : ℤ) by norm_num, neg_zsmul]
  exact neg_ne_zero.mpr not_three_nsmul_torsion

/-- `10 • P = B`. -/
theorem ten_zsmul_p_eq_b : (10 : ℤ) • p = b := by
  rw [show (10 : ℤ) = (9 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [nine_zsmul_p_eq_a, one_zsmul]
  exact add_a_p_eq_b

/-- `11 • P = C`. -/
theorem eleven_zsmul_p_eq_c : (11 : ℤ) • p = c := by
  rw [show (11 : ℤ) = (10 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [ten_zsmul_p_eq_b, one_zsmul]
  exact add_b_p_eq_c

/-- `12 • P = D`. -/
theorem twelve_zsmul_p_eq_d : (12 : ℤ) • p = d := by
  rw [show (12 : ℤ) = (11 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [eleven_zsmul_p_eq_c, one_zsmul]
  exact add_c_p_eq_d

/-- `13 • P = E`. -/
theorem thirteen_zsmul_p_eq_e : (13 : ℤ) • p = e := by
  rw [show (13 : ℤ) = (12 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twelve_zsmul_p_eq_d, one_zsmul]
  exact add_d_p_eq_e

/-- `14 • P = F`. -/
theorem fourteen_zsmul_p_eq_f : (14 : ℤ) • p = f := by
  rw [show (14 : ℤ) = (13 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [thirteen_zsmul_p_eq_e, one_zsmul]
  exact add_e_p_eq_f

/-- `15 • P = G`. -/
theorem fifteen_zsmul_p_eq_g : (15 : ℤ) • p = g := by
  rw [show (15 : ℤ) = (14 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [fourteen_zsmul_p_eq_f, one_zsmul]
  exact add_f_p_eq_g

/-- `16 • P = H`. -/
theorem sixteen_zsmul_p_eq_h : (16 : ℤ) • p = h := by
  rw [show (16 : ℤ) = (15 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [fifteen_zsmul_p_eq_g, one_zsmul]
  exact add_g_p_eq_h

/-- `17 • P = I`. -/
theorem seventeen_zsmul_p_eq_i : (17 : ℤ) • p = i := by
  rw [show (17 : ℤ) = (16 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [sixteen_zsmul_p_eq_h, one_zsmul]
  exact add_h_p_eq_i

/-- `18 • P = J`. -/
theorem eighteen_zsmul_p_eq_j : (18 : ℤ) • p = j := by
  rw [show (18 : ℤ) = (17 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [seventeen_zsmul_p_eq_i, one_zsmul]
  exact add_i_p_eq_j

/-- `10 • P` is not the identity. -/
theorem ten_zsmul_p_ne_zero : (10 : ℤ) • p ≠ 0 := by
  rw [ten_zsmul_p_eq_b]
  exact b_ne_zero

/-- `11 • P` is not the identity. -/
theorem eleven_zsmul_p_ne_zero : (11 : ℤ) • p ≠ 0 := by
  rw [eleven_zsmul_p_eq_c]
  exact c_ne_zero

/-- `12 • P` is not the identity. -/
theorem twelve_zsmul_p_ne_zero : (12 : ℤ) • p ≠ 0 := by
  rw [twelve_zsmul_p_eq_d]
  exact d_ne_zero

/-- `13 • P` is not the identity. -/
theorem thirteen_zsmul_p_ne_zero : (13 : ℤ) • p ≠ 0 := by
  rw [thirteen_zsmul_p_eq_e]
  exact e_ne_zero

/-- `14 • P` is not the identity. -/
theorem fourteen_zsmul_p_ne_zero : (14 : ℤ) • p ≠ 0 := by
  rw [fourteen_zsmul_p_eq_f]
  exact f_ne_zero

/-- `15 • P` is not the identity. -/
theorem fifteen_zsmul_p_ne_zero : (15 : ℤ) • p ≠ 0 := by
  rw [fifteen_zsmul_p_eq_g]
  exact g_ne_zero

/-- `16 • P` is not the identity. -/
theorem sixteen_zsmul_p_ne_zero : (16 : ℤ) • p ≠ 0 := by
  rw [sixteen_zsmul_p_eq_h]
  exact h_ne_zero

/-- `17 • P` is not the identity. -/
theorem seventeen_zsmul_p_ne_zero : (17 : ℤ) • p ≠ 0 := by
  rw [seventeen_zsmul_p_eq_i]
  exact i_ne_zero

/-- `18 • P` is not the identity. -/
theorem eighteen_zsmul_p_ne_zero : (18 : ℤ) • p ≠ 0 := by
  rw [eighteen_zsmul_p_eq_j]
  exact j_ne_zero

/-- `P` does not have order `10`, in the `(n : ℕ) • p` notation. -/
theorem not_ten_nsmul_torsion : (10 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact ten_zsmul_p_ne_zero

/-- `P` does not have order `11`, in the `(n : ℕ) • p` notation. -/
theorem not_eleven_nsmul_torsion : (11 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact eleven_zsmul_p_ne_zero

/-- `P` does not have order `12`, in the `(n : ℕ) • p` notation. -/
theorem not_twelve_nsmul_torsion : (12 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twelve_zsmul_p_ne_zero

/-- `P` does not have order `13`, in the `(n : ℕ) • p` notation. -/
theorem not_thirteen_nsmul_torsion : (13 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact thirteen_zsmul_p_ne_zero

/-- `P` does not have order `14`, in the `(n : ℕ) • p` notation. -/
theorem not_fourteen_nsmul_torsion : (14 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact fourteen_zsmul_p_ne_zero

/-- `P` does not have order `15`, in the `(n : ℕ) • p` notation. -/
theorem not_fifteen_nsmul_torsion : (15 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact fifteen_zsmul_p_ne_zero

/-- `P` does not have order `16`, in the `(n : ℕ) • p` notation. -/
theorem not_sixteen_nsmul_torsion : (16 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact sixteen_zsmul_p_ne_zero

/-- `P` does not have order `17`, in the `(n : ℕ) • p` notation. -/
theorem not_seventeen_nsmul_torsion : (17 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact seventeen_zsmul_p_ne_zero

/-- `P` does not have order `18`, in the `(n : ℕ) • p` notation. -/
theorem not_eighteen_nsmul_torsion : (18 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact eighteen_zsmul_p_ne_zero

/-! ## The further multiples `19P` through `27P`

Continuing the same pattern, the secant through the previous multiple and `P`
produces the next nine multiples `19P, ..., 27P`, each verified on the curve as
a nonsingular rational point.  Their significance is the certificates below:
`P` has no torsion of any order `2 ≤ n ≤ 27` (`not_*_nsmul_torsion`).
-/

/-! ### `19P` -/

/-- The secant slope through `J` and `P` is `-5415345/30283001`. -/
theorem slope_jp : W.slope (12551561/13608721) 0 (-8280062505/50202571769) 0 = -5415345 / 30283001 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 12551561/13608721) (x₂ := 0) (y₁ := -8280062505/50202571769) (y₂ := 0)
    (by norm_num : (12551561/13608721 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(J + P) = x(19P) = -59997896/67387681`. -/
theorem addX_jp : W.addX (12551561/13608721) 0 (W.slope (12551561/13608721) 0 (-8280062505/50202571769) 0) = -59997896 / 67387681 := by
  norm_num [slope_jp, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(J + P) = y(19P) = -641260644409/553185473329`. -/
theorem addY_jp : W.addY (12551561/13608721) 0 (-8280062505/50202571769) (W.slope (12551561/13608721) 0 (-8280062505/50202571769) 0) = -641260644409 / 553185473329 := by
  norm_num [slope_jp, WeierstrassCurve.Affine.addY]

/-- `19P = (-59997896/67387681, -641260644409/553185473329)` lies on the curve. -/
theorem equation_p19 : W.Equation (-59997896/67387681) (-641260644409/553185473329) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `19P = (-59997896/67387681, -641260644409/553185473329)` is a nonsingular rational point. -/
theorem nonsingular_p19 : W.Nonsingular (-59997896/67387681) (-641260644409/553185473329) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p19
  · left
    simp
    norm_num

/-- The point `19P = (-59997896/67387681, -641260644409/553185473329)`. -/
def p19 : W.Point := Point.some (-59997896/67387681) (-641260644409/553185473329) nonsingular_p19

/-- `J + P = 19P`; the secant through `J` and `P` meets the curve at `19P`. -/
theorem add_j_p_eq_p19 : j + p = p19 := by
  unfold j p p19
  rw [add_of_X_ne (x₁ := 12551561/13608721) (x₂ := 0) (y₁ := -8280062505/50202571769) (y₂ := 0) (h₁ := nonsingular_j)
    (h₂ := nonsingular_P) (by norm_num : (12551561/13608721 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_jp, addY_jp⟩

/-- `19P = P19`. -/
theorem nineteen_p_eq_p19 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p19 := by
  rw [eighteen_p_eq_j, add_j_p_eq_p19]

/-! ### `20P` -/

/-- The secant slope through `19P` and `P` is `173830481/133511176`. -/
theorem slope_p19p : W.slope (-59997896/67387681) 0 (-641260644409/553185473329) 0 = 173830481 / 133511176 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -59997896/67387681) (x₂ := 0) (y₁ := -641260644409/553185473329) (y₂ := 0)
    (by norm_num : (-59997896/67387681 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(19P + P) = x(20P) = 683916417/264517696`. -/
theorem addX_p19p : W.addX (-59997896/67387681) 0 (W.slope (-59997896/67387681) 0 (-641260644409/553185473329) 0) = 683916417 / 264517696 := by
  norm_num [slope_p19p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(19P + P) = y(20P) = -18784454671297/4302115807744`. -/
theorem addY_p19p : W.addY (-59997896/67387681) 0 (-641260644409/553185473329) (W.slope (-59997896/67387681) 0 (-641260644409/553185473329) 0) = -18784454671297 / 4302115807744 := by
  norm_num [slope_p19p, WeierstrassCurve.Affine.addY]

/-- `20P = (683916417/264517696, -18784454671297/4302115807744)` lies on the curve. -/
theorem equation_p20 : W.Equation (683916417/264517696) (-18784454671297/4302115807744) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `20P = (683916417/264517696, -18784454671297/4302115807744)` is a nonsingular rational point. -/
theorem nonsingular_p20 : W.Nonsingular (683916417/264517696) (-18784454671297/4302115807744) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p20
  · left
    simp
    norm_num

/-- The point `20P = (683916417/264517696, -18784454671297/4302115807744)`. -/
def p20 : W.Point := Point.some (683916417/264517696) (-18784454671297/4302115807744) nonsingular_p20

/-- `19P + P = 20P`; the secant through `19P` and `P` meets the curve at `20P`. -/
theorem add_p19_p_eq_p20 : p19 + p = p20 := by
  unfold p19 p p20
  rw [add_of_X_ne (x₁ := -59997896/67387681) (x₂ := 0) (y₁ := -641260644409/553185473329) (y₂ := 0) (h₁ := nonsingular_p19)
    (h₂ := nonsingular_P) (by norm_num : (-59997896/67387681 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p19p, addY_p19p⟩

/-- `20P = P20`. -/
theorem twenty_p_eq_p20 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p20 := by
  rw [nineteen_p_eq_p19, add_p19_p_eq_p20]

/-! ### `21P` -/

/-- The secant slope through `20P` and `P` is `-2288275633/1355002632`. -/
theorem slope_p20p : W.slope (683916417/264517696) 0 (-18784454671297/4302115807744) 0 = -2288275633 / 1355002632 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 683916417/264517696) (x₂ := 0) (y₁ := -18784454671297/4302115807744) (y₂ := 0)
    (by norm_num : (683916417/264517696 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(20P + P) = x(21P) = 1849037896/6941055969`. -/
theorem addX_p20p : W.addX (683916417/264517696) 0 (W.slope (683916417/264517696) 0 (-18784454671297/4302115807744) 0) = 1849037896 / 6941055969 := by
  norm_num [slope_p20p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(20P + P) = y(21P) = -318128427505160/578280195945297`. -/
theorem addY_p20p : W.addY (683916417/264517696) 0 (-18784454671297/4302115807744) (W.slope (683916417/264517696) 0 (-18784454671297/4302115807744) 0) = -318128427505160 / 578280195945297 := by
  norm_num [slope_p20p, WeierstrassCurve.Affine.addY]

/-- `21P = (1849037896/6941055969, -318128427505160/578280195945297)` lies on the curve. -/
theorem equation_p21 : W.Equation (1849037896/6941055969) (-318128427505160/578280195945297) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `21P = (1849037896/6941055969, -318128427505160/578280195945297)` is a nonsingular rational point. -/
theorem nonsingular_p21 : W.Nonsingular (1849037896/6941055969) (-318128427505160/578280195945297) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p21
  · left
    simp
    norm_num

/-- The point `21P = (1849037896/6941055969, -318128427505160/578280195945297)`. -/
def p21 : W.Point := Point.some (1849037896/6941055969) (-318128427505160/578280195945297) nonsingular_p21

/-- `20P + P = 21P`; the secant through `20P` and `P` meets the curve at `21P`. -/
theorem add_p20_p_eq_p21 : p20 + p = p21 := by
  unfold p20 p p21
  rw [add_of_X_ne (x₁ := 683916417/264517696) (x₂ := 0) (y₁ := -18784454671297/4302115807744) (y₂ := 0) (h₁ := nonsingular_p20)
    (h₂ := nonsingular_P) (by norm_num : (683916417/264517696 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p20p, addY_p20p⟩

/-- `21P = P21`. -/
theorem twenty_one_p_eq_p21 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p21 := by
  rw [twenty_p_eq_p20, add_p20_p_eq_p21]

/-! ### `22P` -/

/-- The secant slope through `21P` and `P` is `-19560282065/9471771657`. -/
theorem slope_p21p : W.slope (1849037896/6941055969) 0 (-318128427505160/578280195945297) 0 = -19560282065 / 9471771657 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 1849037896/6941055969) (x₂ := 0) (y₁ := -318128427505160/578280195945297) (y₂ := 0)
    (by norm_num : (1849037896/6941055969 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(21P + P) = x(22P) = 51678803961/12925188721`. -/
theorem addX_p21p : W.addX (1849037896/6941055969) 0 (W.slope (1849037896/6941055969) 0 (-318128427505160/578280195945297) 0) = 51678803961 / 12925188721 := by
  norm_num [slope_p21p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(21P + P) = y(22P) = 10663732503571536/1469451780501769`. -/
theorem addY_p21p : W.addY (1849037896/6941055969) 0 (-318128427505160/578280195945297) (W.slope (1849037896/6941055969) 0 (-318128427505160/578280195945297) 0) = 10663732503571536 / 1469451780501769 := by
  norm_num [slope_p21p, WeierstrassCurve.Affine.addY]

/-- `22P = (51678803961/12925188721, 10663732503571536/1469451780501769)` lies on the curve. -/
theorem equation_p22 : W.Equation (51678803961/12925188721) (10663732503571536/1469451780501769) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `22P = (51678803961/12925188721, 10663732503571536/1469451780501769)` is a nonsingular rational point. -/
theorem nonsingular_p22 : W.Nonsingular (51678803961/12925188721) (10663732503571536/1469451780501769) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p22
  · left
    simp
    norm_num

/-- The point `22P = (51678803961/12925188721, 10663732503571536/1469451780501769)`. -/
def p22 : W.Point := Point.some (51678803961/12925188721) (10663732503571536/1469451780501769) nonsingular_p22

/-- `21P + P = 22P`; the secant through `21P` and `P` meets the curve at `22P`. -/
theorem add_p21_p_eq_p22 : p21 + p = p22 := by
  unfold p21 p p22
  rw [add_of_X_ne (x₁ := 1849037896/6941055969) (x₂ := 0) (y₁ := -318128427505160/578280195945297) (y₂ := 0) (h₁ := nonsingular_p21)
    (h₂ := nonsingular_P) (by norm_num : (1849037896/6941055969 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p21p, addY_p21p⟩

/-- `22P = P22`. -/
theorem twenty_two_p_eq_p22 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p22 := by
  rw [twenty_one_p_eq_p21, add_p21_p_eq_p22]

/-! ### `23P` -/

/-- The secant slope through `22P` and `P` is `127996021072/70520945633`. -/
theorem slope_p22p : W.slope (51678803961/12925188721) 0 (10663732503571536/1469451780501769) 0 = 127996021072 / 70520945633 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 51678803961/12925188721) (x₂ := 0) (y₁ := 10663732503571536/1469451780501769) (y₂ := 0)
    (by norm_num : (51678803961/12925188721 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(22P + P) = x(23P) = -270896443865/384768368209`. -/
theorem addX_p22p : W.addX (51678803961/12925188721) 0 (W.slope (51678803961/12925188721) 0 (10663732503571536/1469451780501769) 0) = -270896443865 / 384768368209 := by
  norm_num [slope_p22p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(22P + P) = y(23P) = 66316334575107447/238670664494938073`. -/
theorem addY_p22p : W.addY (51678803961/12925188721) 0 (10663732503571536/1469451780501769) (W.slope (51678803961/12925188721) 0 (10663732503571536/1469451780501769) 0) = 66316334575107447 / 238670664494938073 := by
  norm_num [slope_p22p, WeierstrassCurve.Affine.addY]

/-- `23P = (-270896443865/384768368209, 66316334575107447/238670664494938073)` lies on the curve. -/
theorem equation_p23 : W.Equation (-270896443865/384768368209) (66316334575107447/238670664494938073) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `23P = (-270896443865/384768368209, 66316334575107447/238670664494938073)` is a nonsingular rational point. -/
theorem nonsingular_p23 : W.Nonsingular (-270896443865/384768368209) (66316334575107447/238670664494938073) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p23
  · left
    simp
    norm_num

/-- The point `23P = (-270896443865/384768368209, 66316334575107447/238670664494938073)`. -/
def p23 : W.Point := Point.some (-270896443865/384768368209) (66316334575107447/238670664494938073) nonsingular_p23

/-- `22P + P = 23P`; the secant through `22P` and `P` meets the curve at `23P`. -/
theorem add_p22_p_eq_p23 : p22 + p = p23 := by
  unfold p22 p p23
  rw [add_of_X_ne (x₁ := 51678803961/12925188721) (x₂ := 0) (y₁ := 10663732503571536/1469451780501769) (y₂ := 0) (h₁ := nonsingular_p22)
    (h₂ := nonsingular_P) (by norm_num : (51678803961/12925188721 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p22p, addY_p22p⟩

/-- `23P = P23`. -/
theorem twenty_three_p_eq_p23 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p23 := by
  rw [twenty_two_p_eq_p22, add_p22_p_eq_p23]

/-! ### `24P` -/

/-- The secant slope through `23P` and `P` is `-583313553423/1478034387145`. -/
theorem slope_p23p : W.slope (-270896443865/384768368209) 0 (66316334575107447/238670664494938073) 0 = -583313553423 / 1478034387145 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -270896443865/384768368209) (x₂ := 0) (y₁ := 66316334575107447/238670664494938073) (y₂ := 0)
    (by norm_num : (-270896443865/384768368209 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(23P + P) = x(24P) = 4881674119706/5677664356225`. -/
theorem addX_p23p : W.addX (-270896443865/384768368209) 0 (W.slope (-270896443865/384768368209) 0 (66316334575107447/238670664494938073) 0) = 4881674119706 / 5677664356225 := by
  norm_num [slope_p23p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(23P + P) = y(24P) = -8938035295591025771/13528653463047586625`. -/
theorem addY_p23p : W.addY (-270896443865/384768368209) 0 (66316334575107447/238670664494938073) (W.slope (-270896443865/384768368209) 0 (66316334575107447/238670664494938073) 0) = -8938035295591025771 / 13528653463047586625 := by
  norm_num [slope_p23p, WeierstrassCurve.Affine.addY]

/-- `24P = (4881674119706/5677664356225, -8938035295591025771/13528653463047586625)` lies on the curve. -/
theorem equation_p24 : W.Equation (4881674119706/5677664356225) (-8938035295591025771/13528653463047586625) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `24P = (4881674119706/5677664356225, -8938035295591025771/13528653463047586625)` is a nonsingular rational point. -/
theorem nonsingular_p24 : W.Nonsingular (4881674119706/5677664356225) (-8938035295591025771/13528653463047586625) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p24
  · left
    simp
    norm_num

/-- The point `24P = (4881674119706/5677664356225, -8938035295591025771/13528653463047586625)`. -/
def p24 : W.Point := Point.some (4881674119706/5677664356225) (-8938035295591025771/13528653463047586625) nonsingular_p24

/-- `23P + P = 24P`; the secant through `23P` and `P` meets the curve at `24P`. -/
theorem add_p23_p_eq_p24 : p23 + p = p24 := by
  unfold p23 p p24
  rw [add_of_X_ne (x₁ := -270896443865/384768368209) (x₂ := 0) (y₁ := 66316334575107447/238670664494938073) (y₂ := 0) (h₁ := nonsingular_p23)
    (h₂ := nonsingular_P) (by norm_num : (-270896443865/384768368209 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p23p, addY_p23p⟩

/-- `24P = P24`. -/
theorem twenty_four_p_eq_p24 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p24 := by
  rw [twenty_three_p_eq_p23, add_p23_p_eq_p24]

/-! ### `25P` -/

/-- The secant slope through `24P` and `P` is `-14409283449043/18752274905930`. -/
theorem slope_p24p : W.slope (4881674119706/5677664356225) 0 (-8938035295591025771/13528653463047586625) 0 = -14409283449043 / 18752274905930 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 4881674119706/5677664356225) (x₂ := 0) (y₁ := -8938035295591025771/13528653463047586625) (y₂ := 0)
    (by norm_num : (4881674119706/5677664356225 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(24P + P) = x(25P) = -16683000076735/61935294530404`. -/
theorem addX_p24p : W.addX (4881674119706/5677664356225) 0 (W.slope (4881674119706/5677664356225) 0 (-8938035295591025771/13528653463047586625) 0) = -16683000076735 / 61935294530404 := by
  norm_num [slope_p24p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(24P + P) = y(25P) = -588310630753491921045/487424450554237378792`. -/
theorem addY_p24p : W.addY (4881674119706/5677664356225) 0 (-8938035295591025771/13528653463047586625) (W.slope (4881674119706/5677664356225) 0 (-8938035295591025771/13528653463047586625) 0) = -588310630753491921045 / 487424450554237378792 := by
  norm_num [slope_p24p, WeierstrassCurve.Affine.addY]

/-- `25P = (-16683000076735/61935294530404, -588310630753491921045/487424450554237378792)` lies on the curve. -/
theorem equation_p25 : W.Equation (-16683000076735/61935294530404) (-588310630753491921045/487424450554237378792) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `25P = (-16683000076735/61935294530404, -588310630753491921045/487424450554237378792)` is a nonsingular rational point. -/
theorem nonsingular_p25 : W.Nonsingular (-16683000076735/61935294530404) (-588310630753491921045/487424450554237378792) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p25
  · left
    simp
    norm_num

/-- The point `25P = (-16683000076735/61935294530404, -588310630753491921045/487424450554237378792)`. -/
def p25 : W.Point := Point.some (-16683000076735/61935294530404) (-588310630753491921045/487424450554237378792) nonsingular_p25

/-- `24P + P = 25P`; the secant through `24P` and `P` meets the curve at `25P`. -/
theorem add_p24_p_eq_p25 : p24 + p = p25 := by
  unfold p24 p p25
  rw [add_of_X_ne (x₁ := 4881674119706/5677664356225) (x₂ := 0) (y₁ := -8938035295591025771/13528653463047586625) (y₂ := 0) (h₁ := nonsingular_p24)
    (h₂ := nonsingular_P) (by norm_num : (4881674119706/5677664356225 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p24p, addY_p24p⟩

/-- `25P = P25`. -/
theorem twenty_five_p_eq_p25 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p25 := by
  rw [twenty_four_p_eq_p24, add_p24_p_eq_p25]

/-! ### `26P` -/

/-- The secant slope through `25P` and `P` is `246900425658837/55100862619958`. -/
theorem slope_p25p : W.slope (-16683000076735/61935294530404) 0 (-588310630753491921045/487424450554237378792) 0 = 246900425658837 / 55100862619958 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := -16683000076735/61935294530404) (x₂ := 0) (y₁ := -588310630753491921045/487424450554237378792) (y₂ := 0)
    (by norm_num : (-16683000076735/61935294530404 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(25P + P) = x(26P) = 997454379905326/49020596163841`. -/
theorem addX_p25p : W.addX (-16683000076735/61935294530404) 0 (W.slope (-16683000076735/61935294530404) 0 (-588310630753491921045/487424450554237378792) 0) = 997454379905326 / 49020596163841 := by
  norm_num [slope_p25p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(25P + P) = y(26P) = -31636113722016288336230/343216282443844010111`. -/
theorem addY_p25p : W.addY (-16683000076735/61935294530404) 0 (-588310630753491921045/487424450554237378792) (W.slope (-16683000076735/61935294530404) 0 (-588310630753491921045/487424450554237378792) 0) = -31636113722016288336230 / 343216282443844010111 := by
  norm_num [slope_p25p, WeierstrassCurve.Affine.addY]

/-- `26P = (997454379905326/49020596163841, -31636113722016288336230/343216282443844010111)` lies on the curve. -/
theorem equation_p26 : W.Equation (997454379905326/49020596163841) (-31636113722016288336230/343216282443844010111) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `26P = (997454379905326/49020596163841, -31636113722016288336230/343216282443844010111)` is a nonsingular rational point. -/
theorem nonsingular_p26 : W.Nonsingular (997454379905326/49020596163841) (-31636113722016288336230/343216282443844010111) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p26
  · left
    simp
    norm_num

/-- The point `26P = (997454379905326/49020596163841, -31636113722016288336230/343216282443844010111)`. -/
def p26 : W.Point := Point.some (997454379905326/49020596163841) (-31636113722016288336230/343216282443844010111) nonsingular_p26

/-- `25P + P = 26P`; the secant through `25P` and `P` meets the curve at `26P`. -/
theorem add_p25_p_eq_p26 : p25 + p = p26 := by
  unfold p25 p p26
  rw [add_of_X_ne (x₁ := -16683000076735/61935294530404) (x₂ := 0) (y₁ := -588310630753491921045/487424450554237378792) (y₂ := 0) (h₁ := nonsingular_p25)
    (h₂ := nonsingular_P) (by norm_num : (-16683000076735/61935294530404 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p25p, addY_p25p⟩

/-- `26P = P26`. -/
theorem twenty_six_p_eq_p26 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p26 := by
  rw [twenty_five_p_eq_p25, add_p25_p_eq_p26]

/-! ### `27P` -/

/-- The secant slope through `26P` and `P` is `-4019888659550135/887387347933877`. -/
theorem slope_p26p : W.slope (997454379905326/49020596163841) 0 (-31636113722016288336230/343216282443844010111) 0 = -4019888659550135 / 887387347933877 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne (x₁ := 997454379905326/49020596163841) (x₂ := 0) (y₁ := -31636113722016288336230/343216282443844010111) (y₂ := 0)
    (by norm_num : (997454379905326/49020596163841 : ℚ) ≠ 0)]
  norm_num

/-- The coordinate `x(26P + P) = x(27P) = 2786836257692691/16063784753682169`. -/
theorem addX_p26p : W.addX (997454379905326/49020596163841) 0 (W.slope (997454379905326/49020596163841) 0 (-31636113722016288336230/343216282443844010111) 0) = 2786836257692691 / 16063784753682169 := by
  norm_num [slope_p26p, WeierstrassCurve.Affine.addX]

/-- The coordinate `y(26P + P) = y(27P) = -435912379274109872312968/2035972062206737347698803`. -/
theorem addY_p26p : W.addY (997454379905326/49020596163841) 0 (-31636113722016288336230/343216282443844010111) (W.slope (997454379905326/49020596163841) 0 (-31636113722016288336230/343216282443844010111) 0) = -435912379274109872312968 / 2035972062206737347698803 := by
  norm_num [slope_p26p, WeierstrassCurve.Affine.addY]

/-- `27P = (2786836257692691/16063784753682169, -435912379274109872312968/2035972062206737347698803)` lies on the curve. -/
theorem equation_p27 : W.Equation (2786836257692691/16063784753682169) (-435912379274109872312968/2035972062206737347698803) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `27P = (2786836257692691/16063784753682169, -435912379274109872312968/2035972062206737347698803)` is a nonsingular rational point. -/
theorem nonsingular_p27 : W.Nonsingular (2786836257692691/16063784753682169) (-435912379274109872312968/2035972062206737347698803) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_p27
  · left
    simp
    norm_num

/-- The point `27P = (2786836257692691/16063784753682169, -435912379274109872312968/2035972062206737347698803)`. -/
def p27 : W.Point := Point.some (2786836257692691/16063784753682169) (-435912379274109872312968/2035972062206737347698803) nonsingular_p27

/-- `26P + P = 27P`; the secant through `26P` and `P` meets the curve at `27P`. -/
theorem add_p26_p_eq_p27 : p26 + p = p27 := by
  unfold p26 p p27
  rw [add_of_X_ne (x₁ := 997454379905326/49020596163841) (x₂ := 0) (y₁ := -31636113722016288336230/343216282443844010111) (y₂ := 0) (h₁ := nonsingular_p26)
    (h₂ := nonsingular_P) (by norm_num : (997454379905326/49020596163841 : ℚ) ≠ 0)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_p26p, addY_p26p⟩

/-- `27P = P27`. -/
theorem twenty_seven_p_eq_p27 : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p = p27 := by
  rw [twenty_six_p_eq_p26, add_p26_p_eq_p27]

/-- `19P` is not the identity. -/
theorem p19_ne_zero : p19 ≠ 0 :=
  some_ne_zero nonsingular_p19

/-- `20P` is not the identity. -/
theorem p20_ne_zero : p20 ≠ 0 :=
  some_ne_zero nonsingular_p20

/-- `21P` is not the identity. -/
theorem p21_ne_zero : p21 ≠ 0 :=
  some_ne_zero nonsingular_p21

/-- `22P` is not the identity. -/
theorem p22_ne_zero : p22 ≠ 0 :=
  some_ne_zero nonsingular_p22

/-- `23P` is not the identity. -/
theorem p23_ne_zero : p23 ≠ 0 :=
  some_ne_zero nonsingular_p23

/-- `24P` is not the identity. -/
theorem p24_ne_zero : p24 ≠ 0 :=
  some_ne_zero nonsingular_p24

/-- `25P` is not the identity. -/
theorem p25_ne_zero : p25 ≠ 0 :=
  some_ne_zero nonsingular_p25

/-- `26P` is not the identity. -/
theorem p26_ne_zero : p26 ≠ 0 :=
  some_ne_zero nonsingular_p26

/-- `27P` is not the identity. -/
theorem p27_ne_zero : p27 ≠ 0 :=
  some_ne_zero nonsingular_p27

/-- `19P` is not the identity. -/
theorem nineteen_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [nineteen_p_eq_p19]
  exact p19_ne_zero

/-- `20P` is not the identity. -/
theorem twenty_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_p_eq_p20]
  exact p20_ne_zero

/-- `21P` is not the identity. -/
theorem twenty_one_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_one_p_eq_p21]
  exact p21_ne_zero

/-- `22P` is not the identity. -/
theorem twenty_two_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_two_p_eq_p22]
  exact p22_ne_zero

/-- `23P` is not the identity. -/
theorem twenty_three_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_three_p_eq_p23]
  exact p23_ne_zero

/-- `24P` is not the identity. -/
theorem twenty_four_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_four_p_eq_p24]
  exact p24_ne_zero

/-- `25P` is not the identity. -/
theorem twenty_five_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_five_p_eq_p25]
  exact p25_ne_zero

/-- `26P` is not the identity. -/
theorem twenty_six_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_six_p_eq_p26]
  exact p26_ne_zero

/-- `27P` is not the identity. -/
theorem twenty_seven_p_ne_zero : p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p + p ≠ 0 := by
  rw [twenty_seven_p_eq_p27]
  exact p27_ne_zero

/-- `19 • P = 19P`. -/
theorem nineteen_zsmul_p_eq_p19 : (19 : ℤ) • p = p19 := by
  rw [show (19 : ℤ) = (18 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [eighteen_zsmul_p_eq_j, one_zsmul]
  exact add_j_p_eq_p19

/-- `20 • P = 20P`. -/
theorem twenty_zsmul_p_eq_p20 : (20 : ℤ) • p = p20 := by
  rw [show (20 : ℤ) = (19 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [nineteen_zsmul_p_eq_p19, one_zsmul]
  exact add_p19_p_eq_p20

/-- `21 • P = 21P`. -/
theorem twenty_one_zsmul_p_eq_p21 : (21 : ℤ) • p = p21 := by
  rw [show (21 : ℤ) = (20 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_zsmul_p_eq_p20, one_zsmul]
  exact add_p20_p_eq_p21

/-- `22 • P = 22P`. -/
theorem twenty_two_zsmul_p_eq_p22 : (22 : ℤ) • p = p22 := by
  rw [show (22 : ℤ) = (21 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_one_zsmul_p_eq_p21, one_zsmul]
  exact add_p21_p_eq_p22

/-- `23 • P = 23P`. -/
theorem twenty_three_zsmul_p_eq_p23 : (23 : ℤ) • p = p23 := by
  rw [show (23 : ℤ) = (22 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_two_zsmul_p_eq_p22, one_zsmul]
  exact add_p22_p_eq_p23

/-- `24 • P = 24P`. -/
theorem twenty_four_zsmul_p_eq_p24 : (24 : ℤ) • p = p24 := by
  rw [show (24 : ℤ) = (23 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_three_zsmul_p_eq_p23, one_zsmul]
  exact add_p23_p_eq_p24

/-- `25 • P = 25P`. -/
theorem twenty_five_zsmul_p_eq_p25 : (25 : ℤ) • p = p25 := by
  rw [show (25 : ℤ) = (24 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_four_zsmul_p_eq_p24, one_zsmul]
  exact add_p24_p_eq_p25

/-- `26 • P = 26P`. -/
theorem twenty_six_zsmul_p_eq_p26 : (26 : ℤ) • p = p26 := by
  rw [show (26 : ℤ) = (25 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_five_zsmul_p_eq_p25, one_zsmul]
  exact add_p25_p_eq_p26

/-- `27 • P = 27P`. -/
theorem twenty_seven_zsmul_p_eq_p27 : (27 : ℤ) • p = p27 := by
  rw [show (27 : ℤ) = (26 : ℤ) + (1 : ℤ) by norm_num, add_zsmul]
  rw [twenty_six_zsmul_p_eq_p26, one_zsmul]
  exact add_p26_p_eq_p27

/-- `19 • P` is not the identity. -/
theorem nineteen_zsmul_p_ne_zero : (19 : ℤ) • p ≠ 0 := by
  rw [nineteen_zsmul_p_eq_p19]
  exact p19_ne_zero

/-- `20 • P` is not the identity. -/
theorem twenty_zsmul_p_ne_zero : (20 : ℤ) • p ≠ 0 := by
  rw [twenty_zsmul_p_eq_p20]
  exact p20_ne_zero

/-- `21 • P` is not the identity. -/
theorem twenty_one_zsmul_p_ne_zero : (21 : ℤ) • p ≠ 0 := by
  rw [twenty_one_zsmul_p_eq_p21]
  exact p21_ne_zero

/-- `22 • P` is not the identity. -/
theorem twenty_two_zsmul_p_ne_zero : (22 : ℤ) • p ≠ 0 := by
  rw [twenty_two_zsmul_p_eq_p22]
  exact p22_ne_zero

/-- `23 • P` is not the identity. -/
theorem twenty_three_zsmul_p_ne_zero : (23 : ℤ) • p ≠ 0 := by
  rw [twenty_three_zsmul_p_eq_p23]
  exact p23_ne_zero

/-- `24 • P` is not the identity. -/
theorem twenty_four_zsmul_p_ne_zero : (24 : ℤ) • p ≠ 0 := by
  rw [twenty_four_zsmul_p_eq_p24]
  exact p24_ne_zero

/-- `25 • P` is not the identity. -/
theorem twenty_five_zsmul_p_ne_zero : (25 : ℤ) • p ≠ 0 := by
  rw [twenty_five_zsmul_p_eq_p25]
  exact p25_ne_zero

/-- `26 • P` is not the identity. -/
theorem twenty_six_zsmul_p_ne_zero : (26 : ℤ) • p ≠ 0 := by
  rw [twenty_six_zsmul_p_eq_p26]
  exact p26_ne_zero

/-- `27 • P` is not the identity. -/
theorem twenty_seven_zsmul_p_ne_zero : (27 : ℤ) • p ≠ 0 := by
  rw [twenty_seven_zsmul_p_eq_p27]
  exact p27_ne_zero

/-- `P` does not have order `19`, in the `(n : ℕ) • p` notation. -/
theorem not_nineteen_nsmul_torsion : (19 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact nineteen_zsmul_p_ne_zero

/-- `P` does not have order `20`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_nsmul_torsion : (20 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_zsmul_p_ne_zero

/-- `P` does not have order `21`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_one_nsmul_torsion : (21 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_one_zsmul_p_ne_zero

/-- `P` does not have order `22`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_two_nsmul_torsion : (22 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_two_zsmul_p_ne_zero

/-- `P` does not have order `23`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_three_nsmul_torsion : (23 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_three_zsmul_p_ne_zero

/-- `P` does not have order `24`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_four_nsmul_torsion : (24 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_four_zsmul_p_ne_zero

/-- `P` does not have order `25`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_five_nsmul_torsion : (25 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_five_zsmul_p_ne_zero

/-- `P` does not have order `26`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_six_nsmul_torsion : (26 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_six_zsmul_p_ne_zero

/-- `P` does not have order `27`, in the `(n : ℕ) • p` notation. -/
theorem not_twenty_seven_nsmul_torsion : (27 : ℕ) • p ≠ 0 := by
  rw [← natCast_zsmul]
  exact twenty_seven_zsmul_p_ne_zero

/-! ## The negative multiples `-4P` through `-9P`

With `-1P = R`, `-2P = U`, `-3P = S` already recorded, the six remaining
negative multiples `-4P, ..., -9P` complete the symmetric family
`{0, ±P, ..., ±9P}` of nineteen multiples of `P`.
-/

/-- `-4P = (2, 2)` lies on the curve. -/
theorem equation_m4 : W.Equation 2 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-4P = (2, 2)` is a nonsingular rational point. -/
theorem nonsingular_m4 : W.Nonsingular 2 2 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m4
  · left
    simp
    norm_num

/-- The point `-4P = (2, 2)`. -/
def m4 : W.Point := Point.some 2 2 nonsingular_m4

/-- `-V = -4P = (2, 2)`. -/
theorem neg_v_eq_m4 : -v = m4 := by
  unfold v m4
  rw [neg_some nonsingular_V]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-4) • P = -4P`. -/
theorem neg_four_zsmul_p_eq_m4 : (-4 : ℤ) • p = m4 := by
  rw [neg_zsmul, four_zsmul_p_eq_v]
  exact neg_v_eq_m4

/-- `(-4) • P` is not the identity. -/
theorem neg_four_zsmul_p_ne_zero : (-4 : ℤ) • p ≠ 0 := by
  rw [neg_four_zsmul_p_eq_m4]
  exact some_ne_zero nonsingular_m4

/-- `-5P = (1/4, -3/8)` lies on the curve. -/
theorem equation_m5 : W.Equation (1 / 4) (-3 / 8) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-5P = (1/4, -3/8)` is a nonsingular rational point. -/
theorem nonsingular_m5 : W.Nonsingular (1 / 4) (-3 / 8) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m5
  · left
    simp
    norm_num

/-- The point `-5P = (1/4, -3/8)`. -/
def m5 : W.Point := Point.some (1 / 4) (-3 / 8) nonsingular_m5

/-- `-W = -5P = (1/4, -3/8)`. -/
theorem neg_w_eq_m5 : -w = m5 := by
  unfold w m5
  rw [neg_some nonsingular_W]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-5) • P = -5P`. -/
theorem neg_five_zsmul_p_eq_m5 : (-5 : ℤ) • p = m5 := by
  rw [neg_zsmul, five_zsmul_p_eq_w]
  exact neg_w_eq_m5

/-- `(-5) • P` is not the identity. -/
theorem neg_five_zsmul_p_ne_zero : (-5 : ℤ) • p ≠ 0 := by
  rw [neg_five_zsmul_p_eq_m5]
  exact some_ne_zero nonsingular_m5

/-- `-6P = (6, -15)` lies on the curve. -/
theorem equation_m6 : W.Equation 6 (-15) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-6P = (6, -15)` is a nonsingular rational point. -/
theorem nonsingular_m6 : W.Nonsingular 6 (-15) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m6
  · left
    simp
    norm_num

/-- The point `-6P = (6, -15)`. -/
def m6 : W.Point := Point.some 6 (-15) nonsingular_m6

/-- `-X = -6P = (6, -15)`. -/
theorem neg_x_eq_m6 : -x = m6 := by
  unfold x m6
  rw [neg_some nonsingular_X]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-6) • P = -6P`. -/
theorem neg_six_zsmul_p_eq_m6 : (-6 : ℤ) • p = m6 := by
  rw [neg_zsmul, six_zsmul_p_eq_x]
  exact neg_x_eq_m6

/-- `(-6) • P` is not the identity. -/
theorem neg_six_zsmul_p_ne_zero : (-6 : ℤ) • p ≠ 0 := by
  rw [neg_six_zsmul_p_eq_m6]
  exact some_ne_zero nonsingular_m6

/-- `-7P = (-5/9, -35/27)` lies on the curve. -/
theorem equation_m7 : W.Equation (-5 / 9) (-35 / 27) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-7P = (-5/9, -35/27)` is a nonsingular rational point. -/
theorem nonsingular_m7 : W.Nonsingular (-5 / 9) (-35 / 27) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m7
  · left
    simp
    norm_num

/-- The point `-7P = (-5/9, -35/27)`. -/
def m7 : W.Point := Point.some (-5 / 9) (-35 / 27) nonsingular_m7

/-- `-Y = -7P = (-5/9, -35/27)`. -/
theorem neg_y_eq_m7 : -y = m7 := by
  unfold y m7
  rw [neg_some nonsingular_Y]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-7) • P = -7P`. -/
theorem neg_seven_zsmul_p_eq_m7 : (-7 : ℤ) • p = m7 := by
  rw [neg_zsmul, seven_zsmul_p_eq_y]
  exact neg_y_eq_m7

/-- `(-7) • P` is not the identity. -/
theorem neg_seven_zsmul_p_ne_zero : (-7 : ℤ) • p ≠ 0 := by
  rw [neg_seven_zsmul_p_eq_m7]
  exact some_ne_zero nonsingular_m7

/-- `-8P = (21/25, -56/125)` lies on the curve. -/
theorem equation_m8 : W.Equation (21 / 25) (-56 / 125) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-8P = (21/25, -56/125)` is a nonsingular rational point. -/
theorem nonsingular_m8 : W.Nonsingular (21 / 25) (-56 / 125) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m8
  · left
    simp
    norm_num

/-- The point `-8P = (21/25, -56/125)`. -/
def m8 : W.Point := Point.some (21 / 25) (-56 / 125) nonsingular_m8

/-- `-Z = -8P = (21/25, -56/125)`. -/
theorem neg_z_eq_m8 : -z = m8 := by
  unfold z m8
  rw [neg_some nonsingular_Z]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-8) • P = -8P`. -/
theorem neg_eight_zsmul_p_eq_m8 : (-8 : ℤ) • p = m8 := by
  rw [neg_zsmul, eight_zsmul_p_eq_z]
  exact neg_z_eq_m8

/-- `(-8) • P` is not the identity. -/
theorem neg_eight_zsmul_p_ne_zero : (-8 : ℤ) • p ≠ 0 := by
  rw [neg_eight_zsmul_p_eq_m8]
  exact some_ne_zero nonsingular_m8

/-- `-9P = (-20/49, 92/343)` lies on the curve. -/
theorem equation_m9 : W.Equation (-20 / 49) (92 / 343) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp
  norm_num

/-- `-9P = (-20/49, 92/343)` is a nonsingular rational point. -/
theorem nonsingular_m9 : W.Nonsingular (-20 / 49) (92 / 343) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_m9
  · left
    simp
    norm_num

/-- The point `-9P = (-20/49, 92/343)`. -/
def m9 : W.Point := Point.some (-20 / 49) (92 / 343) nonsingular_m9

/-- `-A = -9P = (-20/49, 92/343)`. -/
theorem neg_a_eq_m9 : -a = m9 := by
  unfold a m9
  rw [neg_some nonsingular_A]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.negY]

/-- `(-9) • P = -9P`. -/
theorem neg_nine_zsmul_p_eq_m9 : (-9 : ℤ) • p = m9 := by
  rw [neg_zsmul, nine_zsmul_p_eq_a]
  exact neg_a_eq_m9

/-- `(-9) • P` is not the identity. -/
theorem neg_nine_zsmul_p_ne_zero : (-9 : ℤ) • p ≠ 0 := by
  rw [neg_nine_zsmul_p_eq_m9]
  exact some_ne_zero nonsingular_m9

/-! ## The named multiples have no small-order torsion

With `(k : ℕ) • p ≠ 0` for `2 ≤ k ≤ 18` in place, each of the earlier named
multiples is certified torsion-free in every order `n` that is consistent with
`18`: `(n : ℕ) • (2P) = (2n : ℕ) • P` is non-zero for `2n ≤ 18`, i.e. for
`2 ≤ n ≤ 9`; similarly `3P` for `2 ≤ n ≤ 6`, `4P` for `2 ≤ n ≤ 4`, `5P` for
`2 ≤ n ≤ 3`, and `6P`, `7P`, `8P`, `9P` for `n = 2`.  No listed point can
therefore have finite order of any of these values, the orders the geometry of
the curve (order `2` needs `3`-division polynomials, orders `3` and `5`
`5`-division polynomials, and so on) would predict below the generators bound.
-/

/-- `Q` does not have order `2`; `(2 : ℕ) • (2P) = (4 : ℕ) • P`. -/
theorem not_two_nsmul_q_torsion : (2 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_four_nsmul_torsion

/-- `Q` does not have order `3`; `(3 : ℕ) • (2P) = (6 : ℕ) • P`. -/
theorem not_three_nsmul_q_torsion : (3 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_six_nsmul_torsion

/-- `Q` does not have order `4`; `(4 : ℕ) • (2P) = (8 : ℕ) • P`. -/
theorem not_four_nsmul_q_torsion : (4 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_eight_nsmul_torsion

/-- `Q` does not have order `5`; `(5 : ℕ) • (2P) = (10 : ℕ) • P`. -/
theorem not_five_nsmul_q_torsion : (5 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_ten_nsmul_torsion

/-- `Q` does not have order `6`; `(6 : ℕ) • (2P) = (12 : ℕ) • P`. -/
theorem not_six_nsmul_q_torsion : (6 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_twelve_nsmul_torsion

/-- `Q` does not have order `7`; `(7 : ℕ) • (2P) = (14 : ℕ) • P`. -/
theorem not_seven_nsmul_q_torsion : (7 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_fourteen_nsmul_torsion

/-- `Q` does not have order `8`; `(8 : ℕ) • (2P) = (16 : ℕ) • P`. -/
theorem not_eight_nsmul_q_torsion : (8 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_sixteen_nsmul_torsion

/-- `Q` does not have order `9`; `(9 : ℕ) • (2P) = (18 : ℕ) • P`. -/
theorem not_nine_nsmul_q_torsion : (9 : ℕ) • q ≠ 0 := by
  rw [← two_p_eq_q, nsmul_add, ← add_nsmul]
  norm_num
  exact not_eighteen_nsmul_torsion

/-- `T` does not have order `2`; `(2 : ℕ) • (3P) = (6 : ℕ) • P`. -/
theorem not_two_nsmul_t_torsion : (2 : ℕ) • t ≠ 0 := by
  rw [← three_p_eq_t, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_six_nsmul_torsion

/-- `T` does not have order `3`; `(3 : ℕ) • (3P) = (9 : ℕ) • P`. -/
theorem not_three_nsmul_t_torsion : (3 : ℕ) • t ≠ 0 := by
  rw [← three_p_eq_t, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_nine_nsmul_torsion

/-- `T` does not have order `4`; `(4 : ℕ) • (3P) = (12 : ℕ) • P`. -/
theorem not_four_nsmul_t_torsion : (4 : ℕ) • t ≠ 0 := by
  rw [← three_p_eq_t, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_twelve_nsmul_torsion

/-- `T` does not have order `5`; `(5 : ℕ) • (3P) = (15 : ℕ) • P`. -/
theorem not_five_nsmul_t_torsion : (5 : ℕ) • t ≠ 0 := by
  rw [← three_p_eq_t, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_fifteen_nsmul_torsion

/-- `T` does not have order `6`; `(6 : ℕ) • (3P) = (18 : ℕ) • P`. -/
theorem not_six_nsmul_t_torsion : (6 : ℕ) • t ≠ 0 := by
  rw [← three_p_eq_t, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_eighteen_nsmul_torsion

/-- `V` does not have order `2`; `(2 : ℕ) • (4P) = (8 : ℕ) • P`. -/
theorem not_two_nsmul_v_torsion : (2 : ℕ) • v ≠ 0 := by
  rw [← four_p_eq_v, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_eight_nsmul_torsion

/-- `V` does not have order `3`; `(3 : ℕ) • (4P) = (12 : ℕ) • P`. -/
theorem not_three_nsmul_v_torsion : (3 : ℕ) • v ≠ 0 := by
  rw [← four_p_eq_v, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_twelve_nsmul_torsion

/-- `V` does not have order `4`; `(4 : ℕ) • (4P) = (16 : ℕ) • P`. -/
theorem not_four_nsmul_v_torsion : (4 : ℕ) • v ≠ 0 := by
  rw [← four_p_eq_v, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_sixteen_nsmul_torsion

/-- `W` does not have order `2`; `(2 : ℕ) • (5P) = (10 : ℕ) • P`. -/
theorem not_two_nsmul_w_torsion : (2 : ℕ) • w ≠ 0 := by
  rw [← five_p_eq_w, nsmul_add, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul, ← add_nsmul,
    ← add_nsmul]
  norm_num
  exact not_ten_nsmul_torsion

/-- `W` does not have order `3`; `(3 : ℕ) • (5P) = (15 : ℕ) • P`. -/
theorem not_three_nsmul_w_torsion : (3 : ℕ) • w ≠ 0 := by
  rw [← five_p_eq_w, nsmul_add, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul, ← add_nsmul,
    ← add_nsmul]
  norm_num
  exact not_fifteen_nsmul_torsion

/-- `X` does not have order `2`; `(2 : ℕ) • (6P) = (12 : ℕ) • P`. -/
theorem not_two_nsmul_x_torsion : (2 : ℕ) • x ≠ 0 := by
  rw [← six_p_eq_x, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul, ← add_nsmul,
    ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_twelve_nsmul_torsion

/-- `Y` does not have order `2`; `(2 : ℕ) • (7P) = (14 : ℕ) • P`. -/
theorem not_two_nsmul_y_torsion : (2 : ℕ) • y ≠ 0 := by
  rw [← seven_p_eq_y, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul,
    ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_fourteen_nsmul_torsion

/-- `Z` does not have order `2`; `(2 : ℕ) • (8P) = (16 : ℕ) • P`. -/
theorem not_two_nsmul_z_torsion : (2 : ℕ) • z ≠ 0 := by
  rw [← eight_p_eq_z, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, ← add_nsmul,
    ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_sixteen_nsmul_torsion

/-- `A` does not have order `2`; `(2 : ℕ) • (9P) = (18 : ℕ) • P`. -/
theorem not_two_nsmul_a_torsion : (2 : ℕ) • a ≠ 0 := by
  rw [← nine_p_eq_a, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add, nsmul_add,
    ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul, ← add_nsmul]
  norm_num
  exact not_eighteen_nsmul_torsion

/-! ## The points are pairwise distinct

A point of the curve is determined by its coordinates, so each pairwise
inequality is a rational computation.  Every listed point is `Point.some`, and
coordinate injectivity (`Point.some.injEq`) reduces each pairwise inequality to
a rational comparison, which `norm_num` decides with a kernel-checked proof
term:

- the only pairs among the twelve whose `x`-coordinates coincide are `(P, R)`
  at `x = 0`, `(Q, U)` at `x = 1`, and `(S, T)` at `x = -1`, which differ in
  `y`; these three are recorded explicitly below;
- the remaining pairs are decided wholesale by `norm_num`.

Each point is also distinct from the identity (the `*_ne_zero` theorems above),
so the identity together with the twelve points gives *thirteen* distinct
elements of the group.  Including the six negative multiples `-4P, ..., -9P`,
the full symmetric family `{0, ±P, ..., ±9P}` gives *nineteen* distinct
elements.
-/

/-- A point is determined by its coordinates. -/
theorem some_ne_of_x_ne {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    Point.some x₁ y₁ h₁ ≠ Point.some x₂ y₂ h₂ := by
  intro heq
  rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
  exact hx heq.1

/-- A point is determined by its coordinates. -/
theorem some_ne_of_y_ne {x₁ x₂ y₁ y₂ : ℚ}
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ y₂) :
    Point.some x₁ y₁ h₁ ≠ Point.some x₂ y₂ h₂ := by
  intro heq
  rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
  exact hy heq.2

/-- The points `P` and `R` (same `x`-coordinate) are distinct. -/
theorem p_ne_r : p ≠ r := by
  unfold p r
  exact some_ne_of_y_ne (by norm_num : (0 : ℚ) ≠ -1)

/-- The points `Q` and `U` (same `x`-coordinate) are distinct. -/
theorem q_ne_u : q ≠ u := by
  unfold q u
  exact some_ne_of_y_ne (by norm_num : (0 : ℚ) ≠ -1)

/-- The points `S` and `T` (same `x`-coordinate) are distinct. -/
theorem s_ne_t : s ≠ t := by
  unfold s t
  exact some_ne_of_y_ne (by norm_num : (0 : ℚ) ≠ -1)

/-- The points `T` and `V` have different `x`-coordinates, hence differ. -/
theorem t_ne_v : t ≠ v := by
  unfold t v
  exact some_ne_of_x_ne (by norm_num : (-1 : ℚ) ≠ 2)

/-- The twelve rational points are pairwise distinct (kernel-checked by
`norm_num`). -/
theorem points_nodup_nonzero :
    List.Nodup [p, q, r, s, t, u, v, w, x, y, z, a] := by
  norm_num [p, q, r, s, t, u, v, w, x, y, z, a,
    WeierstrassCurve.Affine.Point.some.injEq]

/-- The twelve rational points have cardinality twelve; together with the
identity (distinct from each of them by the `*_ne_zero` theorems above) they
form thirteen distinct elements of the group. -/
theorem points_distinct_card :
    (([p, q, r, s, t, u, v, w, x, y, z, a].toFinset) : Finset W.Point).card = 12 := by
  rw [List.toFinset_card_of_nodup points_nodup_nonzero]
  simp

/-- The twelve rational points together with the negative multiples `-4P` to
`-9P` are pairwise distinct (kernel-checked by `norm_num`). -/
theorem symmetric_nodup_nonzero :
    List.Nodup [m9, m8, m7, m6, m5, m4, s, u, r, p, q, t, v, w, x, y, z, a] := by
  norm_num [p, q, r, s, t, u, v, w, x, y, z, a, m4, m5, m6, m7, m8, m9,
    WeierstrassCurve.Affine.Point.some.injEq]

/-- The full symmetric family `{0, ±P, ..., ±9P}` has nineteen distinct
elements. -/
theorem symmetric_family_card :
    ((([(0 : W.Point), m9, m8, m7, m6, m5, m4, s, u, r, p, q, t, v, w, x, y, z, a]
      : List W.Point).toFinset) : Finset W.Point).card = 19 := by
  rw [List.toFinset_card_of_nodup]
  · simp
  · rw [List.nodup_cons]
    constructor
    · simp [p, q, r, s, t, u, v, w, x, y, z, a, m4, m5, m6, m7, m8, m9]
    · norm_num [p, q, r, s, t, u, v, w, x, y, z, a, m4, m5, m6, m7, m8, m9,
        WeierstrassCurve.Affine.Point.some.injEq]

/-! ## The extended distinctness certificate

The nine further multiples `10P, ..., 18P` are pairwise distinct (kernel-checked
by `norm_num`) and are all distinct from the identity by the `*_ne_zero`
theorems, so `{0, 10P, ..., 18P}` is a set of ten distinct group elements.  The
multiples of `P` therefore keep producing new points through `18P`, and `P` is
not torsion of any order `2 ≤ n ≤ 18` (see `not_*_nsmul_torsion`).
-/

/-- The nine further multiples `10P` through `18P` are pairwise distinct
(kernel-checked by `norm_num`). -/
theorem extended_nodup_nonzero :
    List.Nodup [j, i, h, g, f, e, d, c, b] := by
  norm_num [b, c, d, e, f, g, h, i, j,
    WeierstrassCurve.Affine.Point.some.injEq]

/-- `{0, 10P, ..., 18P}` has ten distinct elements. -/
theorem extended_family_card :
    ((([(0 : W.Point), j, i, h, g, f, e, d, c, b]
      : List W.Point).toFinset) : Finset W.Point).card = 10 := by
  rw [List.toFinset_card_of_nodup]
  · simp
  · rw [List.nodup_cons]
    constructor
    · simp [b, c, d, e, f, g, h, i, j]
    · norm_num [b, c, d, e, f, g, h, i, j,
        WeierstrassCurve.Affine.Point.some.injEq]

/-! ## No torsion through order `27` and the twenty-eight-family distinctness

The order certificates `not_*_nsmul_torsion` for `2 ≤ n ≤ 27` are gathered into
a single quantified statement.  Its payoff is multiplicative: making the
assertion that a multiple is the identity at order `n` amounts to a *linear*
constraint `(n : ℕ) • P = 0`, so distinct positive multiples `mP` and `nP`
are certified unequal by looking at the difference `|m - n|` (`≤ 27`); and a
positive multiple `mP` (`1 ≤ m ≤ 18`) is certified different from a negative
multiple `-kP` (`1 ≤ k ≤ 9`) by the sum `m + k` (`≤ 27`).  Together with the
`*_ne_zero` theorems (each listed point is distinct from the identity) and the
earlier `List.Nodup` certificates for the negative multiples, this proves the
*twenty-eight* elements `0`, `±P, ..., ±9P` and `10P, ..., 18P` are pairwise
distinct; the point named `P` is therefore not torsion of any order
`2 ≤ n ≤ 27`.
-/

/-- `P` has no torsion of any order `2 ≤ k ≤ 27`: every multiple `(k : ℕ) • P`
with `2 ≤ k ≤ 27` is distinct from the identity. -/
theorem not_nsmul_p_torsion_le_27 (k : ℕ) (hk2 : 2 ≤ k) (hk27 : k ≤ 27) :
    (k : ℕ) • p ≠ 0 := by
  interval_cases k
  all_goals
    first
    | exact not_two_nsmul_torsion
    | exact not_three_nsmul_torsion
    | exact not_four_nsmul_torsion
    | exact not_five_nsmul_torsion
    | exact not_six_nsmul_torsion
    | exact not_seven_nsmul_torsion
    | exact not_eight_nsmul_torsion
    | exact not_nine_nsmul_torsion
    | exact not_ten_nsmul_torsion
    | exact not_eleven_nsmul_torsion
    | exact not_twelve_nsmul_torsion
    | exact not_thirteen_nsmul_torsion
    | exact not_fourteen_nsmul_torsion
    | exact not_fifteen_nsmul_torsion
    | exact not_sixteen_nsmul_torsion
    | exact not_seventeen_nsmul_torsion
    | exact not_eighteen_nsmul_torsion
    | exact not_nineteen_nsmul_torsion
    | exact not_twenty_nsmul_torsion
    | exact not_twenty_one_nsmul_torsion
    | exact not_twenty_two_nsmul_torsion
    | exact not_twenty_three_nsmul_torsion
    | exact not_twenty_four_nsmul_torsion
    | exact not_twenty_five_nsmul_torsion
    | exact not_twenty_six_nsmul_torsion
    | exact not_twenty_seven_nsmul_torsion

/-- Multiplication by `P` is injective on the positive multiples up to `27P`:
if `mP = nP` with `1 ≤ m ≤ n ≤ 27`, then `m = n`; equivalently the multiples
`P, 2P, ..., 27P` are pairwise distinct. -/
theorem nsmul_p_injective_le_27 (m n : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (hn27 : n ≤ 27)
    (heq : m • p = n • p) : m = n := by
  by_cases hmnN : m = n
  · exact hmnN
  · exfalso
    have hd : 1 ≤ n - m := by omega
    have hd27 : n - m ≤ 27 := by omega
    have hzero : (n - m) • p = 0 := by
      have hrewrite : (n - m) • p + m • p = n • p := by
        rw [← add_nsmul]
        congr 1
        omega
      have h : (n - m) • p + m • p = (0 : W.Point) + m • p := by
        rw [hrewrite, heq, zero_add]
      exact add_right_cancel h
    by_cases h1 : n - m = 1
    · have hp : p = 0 := by
        simpa [h1] using hzero
      exact (p_ne_zero hp)
    · have hd2 : 2 ≤ n - m := by omega
      exact not_nsmul_p_torsion_le_27 (n - m) hd2 hd27 hzero

/-- A positive multiple `mP` (`1 ≤ m ≤ 18`) is never a negative multiple `-kP`
(`1 ≤ k ≤ 9`): such an equality would give `(m + k) • P = 0` with
`2 ≤ m + k ≤ 27`, contradicting the no-torsion certificates. -/
theorem nsmul_p_ne_zsmul_neg (m k : ℕ) (hm1 : 1 ≤ m) (hm18 : m ≤ 18) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    m • p ≠ (-(k : ℤ)) • p := by
  intro heq
  have hsum : 2 ≤ m + k := by omega
  have hsum27 : m + k ≤ 27 := by omega
  have hz : (m + k : ℕ) • p = 0 := by
    calc
      (m + k : ℕ) • p = m • p + k • p := by rw [add_nsmul]
      _ = (-(k : ℤ)) • p + (k : ℤ) • p := by rw [heq, ← natCast_zsmul]
      _ = ((-(k : ℤ) + (k : ℤ)) : ℤ) • p := by rw [← add_zsmul]
      _ = 0 := by simp
  exact not_nsmul_p_torsion_le_27 (m + k) hsum hsum27 hz

end UniversalSingularity.BSD37a1