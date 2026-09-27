import QuadraticFormsSobolev.Dyda.Defs

/-! # Dyda's Step 1: the chain `A_k` (pp. 569–570)

The chain points are convex combinations of `x` and `y` whose consecutive differences shrink
geometrically. For `y` in the `N`-th chain set of `x`, every consecutive pair is regional, and
Dyda's Lemma 3 (here with `p = 2`: Cauchy–Schwarz against the weights `β^k`) bounds `U(x,y)`
by a weighted sum over the chain. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

lemma coef_zero {q : ℝ} {N : ℕ} (hq : q ^ N ≠ 1) : coef q N 0 = 1 := by
  rw [coef, pow_zero]; exact div_self (sub_ne_zero.mpr (Ne.symm hq))

lemma coef_self (q : ℝ) (N : ℕ) : coef q N N = 0 := by
  simp [coef]

lemma coef_sub {q : ℝ} (N k : ℕ) : coef q N k - coef q N (k + 1) = q ^ k * (1 - q) / (1 - q ^ N) := by
  rw [coef, coef, ← sub_div]; congr 1; ring

/-- **Dyda's chain condition, for the ball** (p. 570: `|A_{k−1} − A_k| < η δ_{A_{k−1}}`). -/
theorem chainPt_mem (hd : 1 ≤ d) {η M : ℝ} (hη : 0 < η) (hη1 : η < 1) (hM : 1 ≤ M) {N : ℕ}
    (hN : 1 ≤ N) {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hy : y ∈ chainSet (1 - η / M) M N x) {k : ℕ} (hk : k < N) :
    chainPt (1 - η / M) N k x y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      chainPt (1 - η / M) N (k + 1) x y ∈
        ball (chainPt (1 - η / M) N k x y) (η * dist₁ (chainPt (1 - η / M) N k x y)) := by
  set q := 1 - η / M with hq_def
  have hM0 : 0 < M := by linarith
  have hηM : η / M < 1 := (div_lt_one hM0).mpr (by linarith)
  have hq0 : 0 < q := by rw [hq_def]; linarith
  have hq1 : q < 1 := by rw [hq_def]; linarith [div_pos hη hM0]
  have hqM : (1 - q) * M = η := by rw [hq_def]; field_simp; ring
  have hqN : q ^ N < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hD : 0 < 1 - q ^ N := by linarith
  have hqk0 : 0 < q ^ k := pow_pos hq0 k
  have hqk1 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
  obtain ⟨-, -, hyx, hT⟩ := hy
  set T := x + (1 - q ^ N)⁻¹ • (y - x) with hT_def
  have hxn : ‖x‖ < 1 := by simpa using hx
  have hTn : ‖T‖ ≤ 1 := by simpa using hT
  -- `A_k = q^k x + (1 - q^k) T`
  have hA : chainPt q N k x y = q ^ k • x + (1 - q ^ k) • T := by
    have hc : 1 - coef q N k = (1 - q ^ k) * (1 - q ^ N)⁻¹ := by
      rw [coef]; field_simp; ring
    have e1 : chainPt q N k x y = x + (1 - coef q N k) • (y - x) := by
      rw [chainPt]; module
    rw [e1, hc, hT_def]; module
  have hAn : ‖chainPt q N k x y‖ < 1 := by
    rw [hA]
    calc ‖q ^ k • x + (1 - q ^ k) • T‖ ≤ ‖q ^ k • x‖ + ‖(1 - q ^ k) • T‖ := norm_add_le _ _
      _ = q ^ k * ‖x‖ + (1 - q ^ k) * ‖T‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hqk0.le,
          Real.norm_of_nonneg (by linarith)]
      _ < 1 := by nlinarith
  refine ⟨by simpa using hAn, ?_⟩
  have hδA : q ^ k * dist₁ x ≤ dist₁ (chainPt q N k x y) := by
    have h := dist₁_combo_ge hd hxn.le hTn hqk0.le hqk1
    have hT0 : 0 ≤ dist₁ T := Metric.infDist_nonneg
    rw [hA]; nlinarith
  have hdiff : chainPt q N (k + 1) x y - chainPt q N k x y
      = (coef q N k - coef q N (k + 1)) • (y - x) := by
    simp only [chainPt]; module
  rw [mem_ball, dist_eq_norm, hdiff, coef_sub, norm_smul, Real.norm_of_nonneg
    (div_nonneg (mul_nonneg hqk0.le (by linarith)) hD.le)]
  have hpos : 0 < q ^ k * (1 - q) / (1 - q ^ N) := div_pos (mul_pos hqk0 (by linarith)) hD
  calc q ^ k * (1 - q) / (1 - q ^ N) * ‖y - x‖
      < q ^ k * (1 - q) / (1 - q ^ N) * ((1 - q ^ N) * (M * dist₁ x)) :=
        mul_lt_mul_of_pos_left hyx hpos
    _ = η * (q ^ k * dist₁ x) := by
        rw [← hqM]; field_simp
    _ ≤ η * dist₁ (chainPt q N k x y) := mul_le_mul_of_nonneg_left hδA hη.le

end Dyda
