import QuadraticFormsSobolev.Dyda.Chain

/-! # Dyda's (9) with `p = 2`: Lemma 3 along the chain -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

lemma chainS_sub (q : ℝ) (N k : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    chainPt q N k x y - chainPt q N (k + 1) x y = (coef q N k - coef q N (k + 1)) • (x - y) := by
  simp only [chainPt, sub_smul, smul_sub]
  abel

lemma chainS_geom {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    ∑ k ∈ Finset.range N, (β⁻¹) ^ (k + 1) ≤ β / (β - 1) := by
  have h0 : 0 ≤ β⁻¹ := by positivity
  have h1 : β⁻¹ < 1 := inv_lt_one_of_one_lt₀ hβ
  calc ∑ k ∈ Finset.range N, (β⁻¹) ^ (k + 1) ≤ ∑ k ∈ Finset.range N, (β⁻¹) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact pow_le_pow_of_le_one h0 h1.le (Nat.le_succ k)
    _ = ∑ k ∈ Finset.Ico 0 N, (β⁻¹) ^ k := by rw [Finset.range_eq_Ico]
    _ ≤ (β⁻¹) ^ 0 / (1 - β⁻¹) := geom_sum_Ico_le_of_lt_one h0 h1
    _ = β / (β - 1) := by
        have : β - 1 ≠ 0 := by linarith
        field_simp

lemma chainS_cs {β : ℝ} (hβ : 1 < β) (N : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, a k) ^ 2 ≤
      β / (β - 1) * ∑ k ∈ Finset.range N, β ^ (k + 1) * a k ^ 2 := by
  have hβ0 : 0 < β := by linarith
  have hg : ∀ i ∈ Finset.range N, 0 < (β⁻¹) ^ (i + 1) := fun i _ => by positivity
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.range N) a hg
  have hS : 0 ≤ ∑ k ∈ Finset.range N, (β⁻¹) ^ (k + 1) :=
    Finset.sum_nonneg fun i hi => (hg i hi).le
  have hT : 0 ≤ ∑ k ∈ Finset.range N, β ^ (k + 1) * a k ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have heq : ∑ i ∈ Finset.range N, a i ^ 2 / (β⁻¹) ^ (i + 1) =
      ∑ k ∈ Finset.range N, β ^ (k + 1) * a k ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inv_pow, div_inv_eq_mul, mul_comm]
  rw [heq] at h
  rcases hS.lt_or_eq with hS' | hS'
  · rw [div_le_iff₀ hS'] at h
    calc _ ≤ (∑ k ∈ Finset.range N, β ^ (k + 1) * a k ^ 2) *
          ∑ k ∈ Finset.range N, (β⁻¹) ^ (k + 1) := h
      _ ≤ (∑ k ∈ Finset.range N, β ^ (k + 1) * a k ^ 2) * (β / (β - 1)) :=
          mul_le_mul_of_nonneg_left (chainS_geom hβ N) hT
      _ = _ := mul_comm _ _
  · -- empty-weight case: N = 0
    have hN : N = 0 := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact h
      · exfalso
        have := Finset.sum_pos hg (Finset.nonempty_range_iff.mpr h.ne')
        linarith
    subst hN; simp

/-- **Dyda's (9)**, `p = 2`: `U(x,y)` is bounded by a weighted sum of `U` over the chain. -/
theorem U_le_chain_sum {α q β : ℝ} (hα : 0 < α) (hq0 : 0 < q) (hq1 : q < 1) (hβ : 1 < β)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) {N : ℕ} (hN : 1 ≤ N) {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : x ≠ y) :
    U d α u x y ≤ ENNReal.ofReal (β / (β - 1)) * ∑ k ∈ Finset.range N,
      ENNReal.ofReal (β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α)) *
        U d α u (chainPt q N k x y) (chainPt q N (k + 1) x y) := by
  set e : ℝ := (d : ℝ) + α with he_def
  have he : 0 < e := by positivity
  have hβ0 : 0 < β := by linarith
  have hqN : q ^ N < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hDpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hDe : 0 < ‖x - y‖ ^ e := Real.rpow_pos_of_pos hDpos e
  set a : ℕ → ℝ := fun k => u (chainPt q N k x y) - u (chainPt q N (k + 1) x y) with ha
  have hΔ : ∀ k, 0 < coef q N k - coef q N (k + 1) := fun k => by
    rw [coef_sub]
    have : 0 < 1 - q ^ N := by linarith
    have : 0 < 1 - q := by linarith
    positivity
  -- telescoping
  have hA0 : chainPt q N 0 x y = x := by
    simp [chainPt, coef_zero hqN.ne]
  have hAN : chainPt q N N x y = y := by
    simp [chainPt, coef_self]
  have htel : u x - u y = ∑ k ∈ Finset.range N, a k := by
    rw [ha, Finset.sum_range_sub' (fun k => u (chainPt q N k x y)) N, hA0, hAN]
  -- rewrite each summand
  have hterm : ∀ k ∈ Finset.range N,
      ENNReal.ofReal (β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ e) *
        U d α u (chainPt q N k x y) (chainPt q N (k + 1) x y) =
      ENNReal.ofReal (β ^ (k + 1) * a k ^ 2 / ‖x - y‖ ^ e) := by
    intro k _
    have hΔk := hΔ k
    have hΔe : 0 < (coef q N k - coef q N (k + 1)) ^ e := Real.rpow_pos_of_pos hΔk e
    rw [U, ← ENNReal.ofReal_mul (by positivity), chainS_sub, norm_smul,
      Real.norm_of_nonneg hΔk.le, Real.mul_rpow hΔk.le hDpos.le]
    congr 1
    simp only [ha]
    field_simp
    rw [← he_def]
    ring
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => by positivity), ← ENNReal.ofReal_mul (by
        have : 0 < β - 1 := by linarith
        positivity), U]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.sum_div, ← mul_div_assoc, htel]
  exact div_le_div_of_nonneg_right (chainS_cs hβ N a) hDe.le

end Dyda
