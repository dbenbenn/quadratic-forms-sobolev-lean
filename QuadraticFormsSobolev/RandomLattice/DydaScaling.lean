import QuadraticFormsSobolev.RandomLattice.DydaInput
import QuadraticFormsSobolev.Section1

/-!
# Dyda's inequality on every ball, from the unit ball

The substitution `x = x₀ + R x'` multiplies both sides of (13) by `R^{d-α}`, and
`dist(x₀ + R x', (B_R(x₀))ᶜ) = R dist(x', (B_1(0))ᶜ)`, so the constant for the unit ball serves
every ball. Stated with the `H^{α/2}` form of the development on the left.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace QFS

variable {d : ℕ}

lemma dydaS_lintegral_smul {R : ℝ} (hR : 0 < R) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x, g x = ENNReal.ofReal (R ^ d) * ∫⁻ x', g (R • x') := by
  have hR0 : R ≠ 0 := hR.ne'
  let e : EuclideanSpace ℝ (Fin d) ≃ᵐ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.smulOfNeZero R hR0).toMeasurableEquiv
  have h1 : ∫⁻ x', g (R • x') = ∫⁻ x, g x ∂(Measure.map e volume) :=
    (lintegral_map_equiv g e).symm
  have h2 : Measure.map e volume = ENNReal.ofReal (|(R ^ d)⁻¹|) • volume := by
    have := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin d))) hR0
    rw [finrank_euclideanSpace_fin] at this
    exact this
  rw [h1, h2, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (a := (R ^ d)⁻¹) (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

lemma dydaS_lintegral_affine (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x, g x = ENNReal.ofReal (R ^ d) * ∫⁻ x', g (x₀ + R • x') := by
  rw [← lintegral_add_left_eq_self g x₀]
  exact dydaS_lintegral_smul hR (fun x => g (x₀ + x))

lemma dydaS_measurable_affine (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    Measurable (fun x' : EuclideanSpace ℝ (Fin d) => x₀ + R • x') := by fun_prop

lemma dydaS_setLIntegral_affine (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ x in S, g x = ENNReal.ofReal (R ^ d) *
      ∫⁻ x' in (fun x' => x₀ + R • x') ⁻¹' S, g (x₀ + R • x') := by
  rw [← lintegral_indicator hS, dydaS_lintegral_affine x₀ hR,
    ← lintegral_indicator (hS.preimage (dydaS_measurable_affine x₀ R))]
  congr 1

lemma dydaS_preimage_ball (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (fun x' => x₀ + R • x') ⁻¹' ball (x₀ + R • z) (R * r) = ball z r := by
  ext x'
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  rw [show x₀ + R • x' - (x₀ + R • z) = R • (x' - z) by rw [smul_sub]; abel, norm_smul,
    Real.norm_of_nonneg hR.le]
  exact mul_lt_mul_iff_right₀ hR

lemma dydaS_compl_ball (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    (ball x₀ R)ᶜ = (x₀ + ·) '' (R • (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ) := by
  rw [← Set.image_smul, Set.image_compl_eq (f := fun x : EuclideanSpace ℝ (Fin d) => R • x)
      (Homeomorph.smulOfNeZero R hR.ne').bijective,
    Set.image_smul, smul_unitBall_of_pos hR, Set.image_add_left, Set.preimage_compl]
  congr 1
  ext y
  simp [dist_eq_norm]

lemma dydaS_infDist (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R)
    (x' : EuclideanSpace ℝ (Fin d)) :
    infDist (x₀ + R • x') (ball x₀ R)ᶜ = R * infDist x' (ball 0 1)ᶜ := by
  rw [dydaS_compl_ball x₀ hR, infDist_image (isometry_add_left x₀) , infDist_smul₀ hR.ne',
    Real.norm_of_nonneg hR.le]

lemma dydaS_integrand (f : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) (x' y' : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((f (x₀ + R • y') - f (x₀ + R • x')) ^ 2) *
        jumpKernel d α (x₀ + R • x') (x₀ + R • y') =
      ENNReal.ofReal (R ^ (-(d : ℝ) - α)) *
        ENNReal.ofReal ((f (x₀ + R • x') - f (x₀ + R • y')) ^ 2 / ‖x' - y'‖ ^ ((d : ℝ) + α)) := by
  unfold jumpKernel
  rw [show x₀ + R • x' - (x₀ + R • y') = R • (x' - y') by rw [smul_sub]; abel, norm_smul,
    Real.norm_of_nonneg hR.le, Real.mul_rpow hR.le (norm_nonneg _),
    show -(d : ℝ) - α = -((d : ℝ) + α) by ring, Real.rpow_neg (norm_nonneg (x' - y')),
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma dydaS_measurable_integrand (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) (α : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by
  unfold jumpKernel
  fun_prop

/-- **Dyda's inequality (13) on every ball**, with one constant. -/
theorem formHs_ball_le_regional (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      formHs (ball x₀ R) α f ≤ ENNReal.ofReal c *
        ∫⁻ x in ball x₀ R, ∫⁻ y in ball x (η * infDist x (ball x₀ R)ᶜ),
          ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y := by
  obtain ⟨c, hc, hdy⟩ := Dyda.lintegral_le_regional_unitBall hd hα hη hη1
  refine ⟨c, hc, fun x₀ R hR f hf => ?_⟩
  have key := hdy (fun x' => f (x₀ + R • x')) (hf.comp (dydaS_measurable_affine x₀ R))
  beta_reduce at key
  have hB : (fun x' => x₀ + R • x') ⁻¹' ball x₀ R = ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    have := dydaS_preimage_ball x₀ hR 0 1
    simpa using this
  set J := ENNReal.ofReal (R ^ d) with hJ
  set K := ENNReal.ofReal (R ^ (-(d : ℝ) - α)) with hK
  have hL : formHs (ball x₀ R) α f = J * (J * (K * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        ENNReal.ofReal ((f (x₀ + R • x) - f (x₀ + R • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    unfold formHs form
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod _ (dydaS_measurable_integrand f hf α).aemeasurable,
      dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    simp only
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ hR x' y'
  have hRt : ∫⁻ x in ball x₀ R, ∫⁻ y in ball x (η * infDist x (ball x₀ R)ᶜ),
      ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y =
      J * (J * (K * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        ∫⁻ y in ball x (η * infDist x (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ),
          ENNReal.ofReal ((f (x₀ + R • x) - f (x₀ + R • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, dydaS_infDist x₀ hR x',
      show η * (R * infDist x' (ball 0 1)ᶜ) = R * (η * infDist x' (ball 0 1)ᶜ) by ring,
      dydaS_preimage_ball x₀ hR]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ hR x' y'
  rw [hL, hRt]
  calc J * (J * (K * _)) ≤ J * (J * (K * (ENNReal.ofReal c * _))) := by gcongr
    _ = _ := by ring

end QFS
