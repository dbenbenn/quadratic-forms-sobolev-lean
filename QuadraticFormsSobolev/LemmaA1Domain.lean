import QuadraticFormsSobolev.Dyda.Domain
import QuadraticFormsSobolev.RandomLattice.GoalUniform
import QuadraticFormsSobolev.RandomLattice.Faithful

/-!
# Lemma A.1 and Theorem 1.4 on bounded Lipschitz domains

Dyda's inequality (13) on a bounded Lipschitz domain (`Dyda.lintegral_le_regional_lipschitz`),
transported to every dilate `a • Ω` with the same constant, and combined with the averaging of
`regional_le_form_of_ballComparability_open`, gives Lemma A.1 of Bux–Kassmann–Schulze in full:
the comparability on `Ω`, with a constant that is the same for every dilate of `Ω` and for every
`α ∈ [α₀, 2)`. With Theorem 1.1's ball comparability as input, it gives the domain half of
Theorem 1.4 (the comparability of seminorms and norms; the density statements are not treated).
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace QFS

variable {d : ℕ}

lemma preimage_affine_smul_set {a : ℝ} (ha : 0 < a) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (fun x' : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d)) + a • x') ⁻¹' (a • Ω) = Ω := by
  ext x'
  simp only [mem_preimage, zero_add]
  exact smul_mem_smul_set_iff₀ ha.ne' Ω x'

lemma compl_smul_set {a : ℝ} (ha : 0 < a) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (a • Ω)ᶜ = a • Ωᶜ := by
  ext w
  simp only [mem_compl_iff, mem_smul_set_iff_inv_smul_mem₀ ha.ne']

lemma infDist_affine_smul_set {a : ℝ} (ha : 0 < a) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x' : EuclideanSpace ℝ (Fin d)) :
    infDist ((0 : EuclideanSpace ℝ (Fin d)) + a • x') (a • Ω)ᶜ = a * infDist x' Ωᶜ := by
  rw [zero_add, compl_smul_set ha, infDist_smul₀ ha.ne', Real.norm_of_nonneg ha.le]

/-- **Dyda's inequality (13) on every dilate of a bounded Lipschitz domain**, in the form of the
paper's forms, with one constant for all dilates and all `α ∈ [α₀, 2)`. -/
theorem formHs_dilate_le_regional {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) {α₀ η : ℝ} (hα₀ : 0 < α₀) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 → ∀ a : ℝ, 0 < a →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      formHs (a • Ω) α f ≤ ENNReal.ofReal c *
        ∫⁻ x in a • Ω, ∫⁻ y in ball x (η * infDist x (a • Ω)ᶜ),
          ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y := by
  obtain ⟨c, hc, hdy⟩ := Dyda.lintegral_le_regional_lipschitz hΩ hα₀ hη hη1
  have hΩo : IsOpen Ω := hΩ.2.2.choose_spec.2.choose_spec.1
  refine ⟨c, hc, fun α hα₀α hα2 a ha f hf => ?_⟩
  set x₀ : EuclideanSpace ℝ (Fin d) := 0
  have key := hdy α hα₀α hα2 (fun x' => f (x₀ + a • x')) (hf.comp (dydaS_measurable_affine x₀ a))
  beta_reduce at key
  have hS : MeasurableSet (a • Ω) := (hΩo.smul₀ ha.ne').measurableSet
  have hB : (fun x' => x₀ + a • x') ⁻¹' (a • Ω) = Ω := preimage_affine_smul_set ha Ω
  set J := ENNReal.ofReal (a ^ d) with hJ
  set K := ENNReal.ofReal (a ^ (-(d : ℝ) - α)) with hK
  have hL : formHs (a • Ω) α f = J * (J * (K * ∫⁻ x in Ω, ∫⁻ y in Ω,
        ENNReal.ofReal ((f (x₀ + a • x) - f (x₀ + a • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    unfold formHs form
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod _ (dydaS_measurable_integrand f hf α).aemeasurable,
      dydaS_setLIntegral_affine x₀ ha hS, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    simp only
    rw [dydaS_setLIntegral_affine x₀ ha hS, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ ha x' y'
  have hRt : ∫⁻ x in a • Ω, ∫⁻ y in ball x (η * infDist x (a • Ω)ᶜ),
      ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y =
      J * (J * (K * ∫⁻ x in Ω, ∫⁻ y in ball x (η * infDist x Ωᶜ),
          ENNReal.ofReal ((f (x₀ + a • x) - f (x₀ + a • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    rw [dydaS_setLIntegral_affine x₀ ha hS, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    rw [dydaS_setLIntegral_affine x₀ ha measurableSet_ball, infDist_affine_smul_set ha Ω x',
      show η * (a * infDist x' Ωᶜ) = a * (η * infDist x' Ωᶜ) by ring,
      dydaS_preimage_ball x₀ ha]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ ha x' y'
  rw [hL, hRt]
  calc J * (J * (K * _)) ≤ J * (J * (K * (ENNReal.ofReal c * _))) := by gcongr; exact key
    _ = _ := by simp only [Dyda.U]; ring_nf

/-- **Lemma A.1 on bounded Lipschitz domains**, with the scaling and `α₀` clauses: one constant
`c'` serves every dilate `a • Ω` and every `α ∈ [α₀, 2)`. -/
theorem lemmaAOne_domain {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ α₀ κ : ℝ, 0 < α₀ → 1 ≤ κ →
    ∃ c' : ℝ, 0 < c' ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ (Λ : ℝ) (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
        (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      KernelBounds Γ α Λ k →
      ∀ c : ℝ, 0 < c →
      (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (ball x₀ R) α f ≤ form (ball x₀ (κ * R)) k f) →
      ∀ a : ℝ, 0 < a → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp f 2 (volume.restrict (a • Ω)) →
        ENNReal.ofReal (c' * c) * formHs (a • Ω) α f ≤ form (a • Ω) k f := by
  intro α₀ κ hα₀ hκ
  have hΩo : IsOpen Ω := hΩ.2.2.choose_spec.2.choose_spec.1
  have hη : 0 < (8 * κ)⁻¹ := by positivity
  have hη1 : (8 * κ)⁻¹ < 1 := by rw [inv_lt_one₀ (by positivity)]; linarith
  obtain ⟨cD, hcD, hdyda⟩ := formHs_dilate_le_regional hΩ hα₀ hη hη1
  have hK : 0 < cD * (24 * κ) ^ d := by positivity
  refine ⟨(cD * (24 * κ) ^ d)⁻¹, by positivity, ?_⟩
  intro α hα₀α hα2 Λ Γ k _ c hc H a ha f hf
  set B := a • Ω with hB
  have hBo : IsOpen B := hΩo.smul₀ ha.ne'
  -- a globally square-integrable measurable version of `f` on `B`
  obtain ⟨g₀, hg₀m, hfg₀⟩ : ∃ g₀ : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g₀ ∧
      f =ᵐ[volume.restrict B] g₀ :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  set g : EuclideanSpace ℝ (Fin d) → ℝ := B.indicator g₀ with hg
  have hgm : Measurable g := hg₀m.indicator hBo.measurableSet
  have hfg : f =ᵐ[volume.restrict B] g := by
    filter_upwards [hfg₀, ae_restrict_mem hBo.measurableSet] with x hx hxB
    rw [hg, Set.indicator_of_mem hxB, hx]
  have hgL2 : MemLp g 2 volume := by
    have h1 : MemLp g₀ 2 (volume.restrict B) := hf.ae_eq hfg₀
    rw [hg, memLp_indicator_iff_restrict hBo.measurableSet]
    exact h1
  obtain ⟨k', hG, hk'⟩ := exists_measurable_kernel_form_eq g k
  have hball : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      formHs (ball z r) α g ≤ ENNReal.ofReal c⁻¹ * form (ball z (κ * r)) k' g := by
    intro z r hr
    have h := H z r hr g (hgL2.restrict _)
    calc formHs (ball z r) α g
        = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * formHs (ball z r) α g) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hc.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal c⁻¹ * form (ball z (κ * r)) k' g := by rw [hk']; gcongr
  have hmain : formHs B α g ≤ ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g := by
    calc formHs B α g
        ≤ ENNReal.ofReal cD * ∫⁻ x in B, ∫⁻ y in ball x ((8 * κ)⁻¹ * infDist x Bᶜ),
            ENNReal.ofReal ((g y - g x) ^ 2) * jumpKernel d α x y :=
          hdyda α hα₀α hα2 a ha g hgm
      _ ≤ ENNReal.ofReal cD * (ENNReal.ofReal (c⁻¹ * (24 * κ) ^ d) * form B k g) := by
          gcongr
          rw [← hk' B]
          exact regional_le_form_of_ballComparability_open hκ (by positivity) hgm hG hball B hBo
      _ = ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hcD.le]
  have hconst : (cD * (24 * κ) ^ d)⁻¹ * c * (cD * (c⁻¹ * (24 * κ) ^ d)) = 1 := by
    field_simp
  calc ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) * formHs B α f
      = ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) * formHs B α g := by
        simp only [formHs]; rw [form_congr_ae _ hfg]
    _ ≤ ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) *
          (ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g) := by gcongr
    _ = form B k g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hconst, ENNReal.ofReal_one, one_mul]
    _ = form B k f := (form_congr_ae _ hfg).symm

/-- **Theorem 1.4, the domain half.** On a bounded Lipschitz domain the spaces `H_k(Ω)` and
`H^{α/2}(Ω)` coincide, and their seminorms and norms are comparable. -/
theorem theoremOneFour_domain (d : ℕ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      {g : EuclideanSpace ℝ (Fin d) → ℝ | MemLp g 2 (volume.restrict Ω) ∧ form Ω k g ≠ ⊤}
          = {g : EuclideanSpace ℝ (Fin d) → ℝ | MemLp g 2 (volume.restrict Ω) ∧
              formHs Ω α g ≠ ⊤} ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MemLp f 2 (volume.restrict Ω) →
        formHs Ω α f ≤ ENNReal.ofReal c * form Ω k f ∧
        form Ω k f ≤ ENNReal.ofReal Λ * formHs Ω α f ∧
        eLpNorm f 2 (volume.restrict Ω) ^ 2 + formHs Ω α f
          ≤ ENNReal.ofReal c * (eLpNorm f 2 (volume.restrict Ω) ^ 2 + form Ω k f) ∧
        eLpNorm f 2 (volume.restrict Ω) ^ 2 + form Ω k f
          ≤ ENNReal.ofReal Λ * (eLpNorm f 2 (volume.restrict Ω) ^ 2 + formHs Ω α f) := by
  intro ϑ Λ α hϑ hΛ hα hα2
  -- the lower inequality with some `c ≥ 1`
  have key : ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)),
      IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MemLp f 2 (volume.restrict Ω) →
        formHs Ω α f ≤ ENNReal.ofReal c * form Ω k f := by
    obtain ⟨κ, cB, hκ, hcB, hB⟩ := formHs_ball_le_form_enlargedBall d ϑ (2 * Λ) α hϑ (by linarith)
      hα hα2
    obtain ⟨c', hc', hA⟩ := lemmaAOne_domain hΩ α κ hα hκ
    refine ⟨max (c' * cB)⁻¹ 1, le_max_right _ _, fun Γ hΓ k hk f hf => ?_⟩
    obtain ⟨k₀, hk₀b, hk₀le, -⟩ := faith_lowerKernel hΓ hk
    have h := hA α le_rfl hα2 (2 * Λ) Γ k₀ hk₀b cB hcB (hB Γ hΓ k₀ hk₀b) 1 one_pos f
      (by rwa [one_smul])
    rw [one_smul] at h
    have hpos : 0 < c' * cB := by positivity
    calc formHs Ω α f
        = ENNReal.ofReal (c' * cB)⁻¹ * (ENNReal.ofReal (c' * cB) * formHs Ω α f) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hpos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (c' * cB)⁻¹ * form Ω k₀ f := by gcongr
      _ ≤ ENNReal.ofReal (max (c' * cB)⁻¹ 1) * form Ω k f := by
          gcongr
          · exact le_max_left _ _
          · exact faith_form_mono _ hk₀le f
  obtain ⟨c, hc, hkey⟩ := key
  refine ⟨c, hc, fun Γ hΓ k hk => ⟨?_, fun f hf => ⟨hkey Γ hΓ k hk f hf,
    form_le_formHs hk _ f,
    faith_add_le_mul_add hc _ (hkey Γ hΓ k hk f hf),
    faith_add_le_mul_add hΛ _ (form_le_formHs hk _ f)⟩⟩⟩
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hf, hfin⟩
    refine ⟨hf, ne_top_of_le_ne_top ?_ (hkey Γ hΓ k hk f hf)⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  · rintro ⟨hf, hfin⟩
    refine ⟨hf, ne_top_of_le_ne_top ?_ (form_le_formHs hk _ f)⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

end QFS
