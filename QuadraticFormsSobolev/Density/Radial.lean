import QuadraticFormsSobolev.Density.Basic

/-! # `∫ min(1, |h|²) |h|^{−d−α} dh < ∞` for `0 < α < 2`

Near the origin the integrand is `|h|^{2−d−α}`, integrable because `α < 2`; at infinity it is
`|h|^{−d−α}`, integrable because `α > 0`. The reduction to one variable is Mathlib's
`integrable_fun_norm_addHaar`. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace QFS

variable {d : ℕ}

theorem integrable_minKernel (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Integrable (fun h : EuclideanSpace ℝ (Fin d) => min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  set F : ℝ → ℝ := fun r => min 1 (r ^ 2) * r ^ (-(d : ℝ) - α) with hF
  show Integrable (fun h : EuclideanSpace ℝ (Fin d) => F ‖h‖)
  rw [integrable_fun_norm_addHaar volume (f := F), finrank_euclideanSpace_fin]
  have hdn : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [Nat.cast_sub hd]; ring
  have hpow : ∀ y : ℝ, 0 < y → y ^ (d - 1) = y ^ ((d : ℝ) - 1) := by
    intro y hy; rw [← hdn, Real.rpow_natCast]
  have h1 : IntegrableOn (fun y : ℝ => y ^ (d - 1) • F y) (Ioc 0 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (1 - α)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine hi.congr_fun (fun y hy => ?_) measurableSet_Ioc
    have hy0 : 0 < y := hy.1
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by nlinarith [hy.2])
    simp only [hF, smul_eq_mul, hmin, hpow y hy0]
    rw [← Real.rpow_two, ← Real.rpow_add hy0, ← Real.rpow_add hy0]
    congr 1; ring
  have h2 : IntegrableOn (fun y : ℝ => y ^ (d - 1) • F y) (Ioi 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (-1 - α)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_iff one_pos).mpr (by linarith)
    refine hi.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy1 : 1 < y := hy
    have hy0 : 0 < y := by linarith
    have hmin : min 1 (y ^ 2) = 1 := min_eq_left (by nlinarith)
    simp only [hF, smul_eq_mul, hmin, hpow y hy0, one_mul]
    rw [← Real.rpow_add hy0]
    congr 1; ring
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

theorem lintegral_minKernel_lt_top (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∫⁻ h : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)) < ⊤ :=
  (integrable_minKernel hd hα0 hα2).lintegral_lt_top

end QFS
