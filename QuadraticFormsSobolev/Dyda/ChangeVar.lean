import QuadraticFormsSobolev.Dyda.Defs

/-! # The two linear changes of variables

Dyda's (10): `(x, y) ↦ (a x + (1 − a) y, b x + (1 − b) y)` has Jacobian `|a − b|^d`; and the
pulled-in midpoint `(x, y) ↦ (c(x + y), x)` has Jacobian `|c|^d`. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

lemma cv_lintegral_smul {c : ℝ} (hc : c ≠ 0) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x, g (c • x) = ENNReal.ofReal (|c|⁻¹ ^ d) * ∫⁻ x, g x := by
  let e : EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.smulOfNeZero c hc).toMeasurableEquiv
  have h1 : ∫⁻ x', g (c • x') = ∫⁻ x, g x ∂(Measure.map e volume) :=
    (lintegral_map_equiv g e).symm
  have h2 : Measure.map e volume = ENNReal.ofReal (|(c ^ d)⁻¹|) • volume := by
    have := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin d))) hc
    rw [finrank_euclideanSpace_fin] at this
    exact this
  rw [h1, h2, lintegral_smul_measure, smul_eq_mul, abs_inv, abs_pow, inv_pow]

lemma cv_lintegral_affine (x₀ : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : c ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x, g (x₀ + c • x) = ENNReal.ofReal (|c|⁻¹ ^ d) * ∫⁻ x, g x := by
  rw [← lintegral_add_left_eq_self g x₀]
  exact cv_lintegral_smul hc (fun x => g (x₀ + x))

/-- Dyda's change of variables (10). -/
theorem lintegral_lintegral_pair {a b : ℝ} (hb : b ≠ 1) (hab : a ≠ b)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    ∫⁻ x, ∫⁻ y, g (a • x + (1 - a) • y) (b • x + (1 - b) • y)
      = ENNReal.ofReal (|a - b|⁻¹ ^ d) * ∫⁻ x, ∫⁻ y, g x y := by
  have hb' : (1 - b : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hab' : (a - b : ℝ) ≠ 0 := sub_ne_zero.mpr hab
  set p : ℝ := (a - b) / (1 - b) with hp
  set q : ℝ := (1 - a) / (1 - b) with hq
  have hp0 : p ≠ 0 := div_ne_zero hab' hb'
  have key : ∀ x y : EuclideanSpace ℝ (Fin d),
      a • x + (1 - a) • y = p • x + q • (b • x + (1 - b) • y) := by
    intro x y
    rw [smul_add, smul_smul, smul_smul, add_left_comm, ← add_assoc, ← add_smul]
    congr 2
    · rw [hp, hq]; field_simp; ring
    · rw [hq]; field_simp
  have hK : ENNReal.ofReal (|1 - b|⁻¹ ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK2 : ENNReal.ofReal (|p|⁻¹ ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm : Measurable (Function.uncurry fun x w : EuclideanSpace ℝ (Fin d) =>
      g (p • x + q • w) w) := by
    have : Measurable fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        (p • z.1 + q • z.2, z.2) := by fun_prop
    exact hg.comp this
  calc ∫⁻ x, ∫⁻ y, g (a • x + (1 - a) • y) (b • x + (1 - b) • y)
      = ∫⁻ x, ENNReal.ofReal (|1 - b|⁻¹ ^ d) * ∫⁻ w, g (p • x + q • w) w := by
        refine lintegral_congr fun x => ?_
        simp_rw [key x]
        exact cv_lintegral_affine (b • x) hb' (fun w => g (p • x + q • w) w)
    _ = ENNReal.ofReal (|1 - b|⁻¹ ^ d) * ∫⁻ w, ∫⁻ x, g (p • x + q • w) w := by
        rw [lintegral_const_mul' _ _ hK, lintegral_lintegral_swap hm.aemeasurable]
    _ = ENNReal.ofReal (|1 - b|⁻¹ ^ d) * ∫⁻ w, ENNReal.ofReal (|p|⁻¹ ^ d) * ∫⁻ v, g v w := by
        congr 1
        refine lintegral_congr fun w => ?_
        simp_rw [add_comm (p • _) (q • w)]
        exact cv_lintegral_affine (q • w) hp0 (fun v => g v w)
    _ = ENNReal.ofReal (|a - b|⁻¹ ^ d) * ∫⁻ x, ∫⁻ y, g x y := by
        rw [lintegral_const_mul' _ _ hK2, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← mul_pow, lintegral_lintegral_swap
            (show Measurable (Function.uncurry fun w v => g v w) from
              hg.comp measurable_swap).aemeasurable]
        congr 3
        rw [hp, abs_div]
        field_simp

/-- The midpoint change of variables. -/
theorem lintegral_lintegral_mid {c : ℝ} (hc : c ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    ∫⁻ x, ∫⁻ y, g (c • (x + y)) x = ENNReal.ofReal (|c|⁻¹ ^ d) * ∫⁻ x, ∫⁻ z, g z x := by
  have hK : ENNReal.ofReal (|c|⁻¹ ^ d) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_const_mul' _ _ hK]
  refine lintegral_congr fun x => ?_
  rw [← cv_lintegral_smul hc (fun z => g z x)]
  exact lintegral_add_left_eq_self (fun y => g (c • y) x) x

end Dyda
