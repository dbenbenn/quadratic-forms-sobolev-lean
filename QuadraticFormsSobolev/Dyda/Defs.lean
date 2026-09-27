import Mathlib

/-!
# Dyda's inequality (13) for the unit ball: definitions

B. Dyda, *On comparability of integral forms*, J. Math. Anal. Appl. 318 (2006) 564–577.
The proof of (13) for the unit ball `D = B(0,1)` of `ℝ^d` follows Dyda's Step 1 (the chain
`A_k = α_k x + (1 − α_k) y` and the change of variables (10)) with his family of norms replaced by
the convexity of the ball, and replaces his Step 2 (Lipschitz boxes) and case (c) by a chaining
through the pulled-in midpoint `G = (1 − s)(x + y)/2`.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- `δ_x`: the distance from `x` to the complement of the unit ball. -/
noncomputable def dist₁ (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  infDist x (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ

/-- The integrand of (13) with `p = 2`: `(u(x) − u(y))² / |x − y|^{d+α}`. -/
noncomputable def U (d : ℕ) (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α))

/-- The points `y` of the ball that `x` "sees" at relative distance `M`:
`y ≠ x` and `|y − x| < M δ_x`. -/
def far (M : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ y ≠ x ∧ ‖y - x‖ < M * dist₁ x}

/-- Dyda's chain coefficients `α_k = (q^k − q^N)/(1 − q^N)` (Step 1, with `q = 1 − η̃`). -/
noncomputable def coef (q : ℝ) (N k : ℕ) : ℝ := (q ^ k - q ^ N) / (1 - q ^ N)

/-- Dyda's chain points `A_k = α_k x + (1 − α_k) y`. -/
noncomputable def chainPt (q : ℝ) (N k : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  coef q N k • x + (1 - coef q N k) • y

/-- The `N`-th chain set of `x` (Dyda's `E^N`, with a tip `x + (1 − q^N)⁻¹ (y − x)` in the
closed ball in place of his norm family). -/
def chainSet (q M : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ y ≠ x ∧
    ‖y - x‖ < (1 - q ^ N) * (M * dist₁ x) ∧
    x + (1 - q ^ N)⁻¹ • (y - x) ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1}

lemma chainG_exists_unit (hd : 1 ≤ d) : ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), by simp⟩

/-- On the closed unit ball, `δ_x = 1 − ‖x‖`. -/
lemma dist₁_eq {x : EuclideanSpace ℝ (Fin d)} (hd : 1 ≤ d) (hx : ‖x‖ ≤ 1) :
    dist₁ x = 1 - ‖x‖ := by
  -- a point `z` of the unit sphere with `‖z - x‖ = 1 - ‖x‖`
  have hz : ∃ z : EuclideanSpace ℝ (Fin d), ‖z‖ = 1 ∧ ‖x - z‖ = 1 - ‖x‖ := by
    by_cases h0 : x = 0
    · obtain ⟨u, hu⟩ := chainG_exists_unit hd
      exact ⟨u, hu, by simp [h0, hu]⟩
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      · have : x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x := by rw [sub_smul, one_smul]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos]
        · field_simp; ring
        · rw [sub_nonpos]; exact one_le_inv_iff₀.mpr ⟨hpos, hx⟩
  obtain ⟨z, hz1, hzx⟩ := hz
  have hzmem : z ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ := by simp [hz1]
  apply le_antisymm
  · calc dist₁ x ≤ dist x z := infDist_le_dist_of_mem hzmem
      _ = 1 - ‖x‖ := by rw [dist_eq_norm, hzx]
  · refine (le_infDist ⟨z, hzmem⟩).mpr fun w hw => ?_
    simp only [Set.mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hw
    rw [dist_comm, dist_eq_norm]
    have := norm_sub_norm_le w x
    linarith

/-- `δ` is concave on the closed unit ball. -/
lemma dist₁_combo_ge (hd : 1 ≤ d) {a b : EuclideanSpace ℝ (Fin d)} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * dist₁ a + (1 - t) * dist₁ b ≤ dist₁ (t • a + (1 - t) • b) := by
  have hc : ‖t • a + (1 - t) • b‖ ≤ t * ‖a‖ + (1 - t) * ‖b‖ := by
    calc ‖t • a + (1 - t) • b‖ ≤ ‖t • a‖ + ‖(1 - t) • b‖ := norm_add_le _ _
      _ = t * ‖a‖ + (1 - t) * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht0, Real.norm_of_nonneg (by linarith)]
  have h1 : ‖t • a + (1 - t) • b‖ ≤ 1 := by nlinarith
  rw [dist₁_eq hd ha, dist₁_eq hd hb, dist₁_eq hd h1]
  nlinarith

/-- `U` vanishes on the diagonal. -/
lemma U_self (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    U d α u x x = 0 := by
  simp [U]

/-- `U` is jointly measurable for measurable `u`. -/
lemma measurable_U (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => U d α u p.1 p.2 := by
  unfold U; fun_prop

end Dyda
