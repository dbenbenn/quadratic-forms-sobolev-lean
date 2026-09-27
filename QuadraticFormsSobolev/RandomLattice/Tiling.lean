import QuadraticFormsSobolev.RandomLattice.Basic

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-! # Random lattice sampling: averaging over the shift `η` -/

/-- A distortion with columns in `B̄(0, δ)` moves `u` by at most `dδ‖u‖`. -/
lemma norm_distort_sub_le {δ : ℝ} (hδ : 0 ≤ δ) {Q : Fin d → EuclideanSpace ℝ (Fin d)}
    (hQ : Q ∈ colBox d δ) (u : EuclideanSpace ℝ (Fin d)) :
    ‖distort Q u - u‖ ≤ d * δ * ‖u‖ := by
  rw [distort_apply, add_sub_cancel_left]
  calc ‖∑ j, u j • Q j‖ ≤ ∑ j, ‖u j • Q j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, δ * ‖u‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, mul_comm]
        have h1 : ‖Q j‖ ≤ δ := by
          have := hQ j (Set.mem_univ _)
          simpa [mem_closedBall, dist_zero_right] using this
        exact mul_le_mul h1 (PiLp.norm_apply_le u j) (norm_nonneg _) hδ
    _ = d * δ * ‖u‖ := by simp [Finset.sum_const, Finset.card_univ]; ring

lemma latticePt_one_add (n w : Fin d → ℤ) :
    latticePt d 1 (n + w) = latticePt d 1 n + latticePt d 1 w := by
  ext i
  simp [latticePt]

lemma lintegral_cube_tsum {g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ η in halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)), ∑' n, g (latticePt d 1 n + η)
      = ∫⁻ u, g u := by
  rw [lintegral_tsum (f := fun n η => g (latticePt d 1 n + η))
      (fun n => (hg.comp (measurable_const_add (latticePt d 1 n))).aemeasurable),
    lintegral_eq_tsum_halfClosedCube one_pos]
  congr 1
  funext n
  rw [← lintegral_indicator (measurableSet_halfClosedCube _ _),
    ← lintegral_indicator (measurableSet_halfClosedCube _ _)]
  conv_rhs => rw [← lintegral_add_left_eq_self _ (latticePt d 1 n)]
  congr 1
  funext η
  have hmem : η ∈ halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)) ↔
      latticePt d 1 n + η ∈ halfClosedCube 1 (latticePt d 1 n) := by
    simp only [halfClosedCube, Set.mem_ofPred_eq, Set.mem_Ico, PiLp.add_apply, PiLp.zero_apply]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  by_cases h : η ∈ halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.2 h'))]

lemma norm_distort_bounds {δ : ℝ} (hδ : 0 ≤ δ) {Q : Fin d → EuclideanSpace ℝ (Fin d)}
    (hQ : Q ∈ colBox d δ) (u : EuclideanSpace ℝ (Fin d)) :
    (1 - d * δ) * ‖u‖ ≤ ‖distort Q u‖ ∧ ‖distort Q u‖ ≤ (1 + d * δ) * ‖u‖ := by
  have h := norm_distort_sub_le hδ hQ u
  have h1 := norm_sub_norm_le u (u - distort Q u)
  have h2 := norm_le_insert' (distort Q u) u
  rw [norm_sub_rev] at h1
  simp only [sub_sub_cancel] at h1
  constructor <;> nlinarith [norm_sub_rev (distort Q u) u]

lemma det_distort_ne_zero {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    {Q : Fin d → EuclideanSpace ℝ (Fin d)} (hQ : Q ∈ colBox d δ) :
    LinearMap.det (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ≠ 0 := by
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
  intro u hu
  have := (norm_distort_bounds hδ hQ u).1
  simp only [ContinuousLinearMap.coe_coe] at hu
  rw [hu, norm_zero] at this
  have : ‖u‖ ≤ 0 := by nlinarith [norm_nonneg u]
  exact norm_le_zero_iff.1 this

lemma abs_det_distort_bounds {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    {Q : Fin d → EuclideanSpace ℝ (Fin d)} (hQ : Q ∈ colBox d δ) :
    (1 - d * δ) ^ d ≤
        |LinearMap.det (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| ∧
      |LinearMap.det (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))|
        ≤ (1 + d * δ) ^ d := by
  set A := (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) with hAdef
  have hA := det_distort_ne_zero hδ hδ' hQ
  have hpos : 0 < |LinearMap.det A| := abs_pos.2 hA
  set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ∞ := measure_ball_lt_top.ne
  have hball : ∀ r : ℝ, 0 < r →
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) r) = ENNReal.ofReal (r ^ d) * V := by
    intro r hr
    rw [Measure.addHaar_ball_of_pos volume _ hr, finrank_euclideanSpace_fin]
  have hpre : ∀ r : ℝ, 0 < r → volume (A ⁻¹' ball 0 r)
      = ENNReal.ofReal ((|LinearMap.det A|)⁻¹ * r ^ d) * V := by
    intro r hr
    rw [Measure.addHaar_preimage_linearMap volume hA, hball r hr, ← mul_assoc, abs_inv,
      ENNReal.ofReal_mul (inv_nonneg.2 hpos.le)]
  have hc1 : 0 < 1 - d * δ := by linarith
  have hc2 : 0 < 1 + d * δ := by have : (0:ℝ) ≤ d * δ := by positivity
                                 linarith
  constructor
  · have hsub : A ⁻¹' ball 0 (1 - d * δ) ⊆ ball 0 1 := by
      intro u hu
      simp only [Set.mem_preimage, mem_ball, dist_zero_right] at hu ⊢
      have := (norm_distort_bounds hδ hQ u).1
      change ‖distort Q u‖ < 1 - d * δ at hu
      nlinarith
    have hle := measure_mono (μ := volume) hsub
    rw [hpre _ hc1] at hle
    have : ENNReal.ofReal ((|LinearMap.det A|)⁻¹ * (1 - d * δ) ^ d) ≤ 1 := by
      have hle' : ENNReal.ofReal ((|LinearMap.det A|)⁻¹ * (1 - d * δ) ^ d) * V ≤ 1 * V := by
        simpa using hle
      exact (ENNReal.mul_le_mul_iff_left hV0 hVt).1 hle'
    rw [ENNReal.ofReal_le_one] at this
    rw [inv_mul_le_iff₀ hpos, mul_one] at this
    exact this
  · have hsub : ball 0 1 ⊆ A ⁻¹' ball 0 (1 + d * δ) := by
      intro u hu
      simp only [Set.mem_preimage, mem_ball, dist_zero_right] at hu ⊢
      have := (norm_distort_bounds hδ hQ u).2
      change ‖distort Q u‖ < 1 + d * δ
      nlinarith
    have hle := measure_mono (μ := volume) hsub
    rw [hpre _ hc2] at hle
    have : 1 ≤ ENNReal.ofReal ((|LinearMap.det A|)⁻¹ * (1 + d * δ) ^ d) := by
      have hle' : 1 * V ≤ ENNReal.ofReal ((|LinearMap.det A|)⁻¹ * (1 + d * δ) ^ d) * V := by
        simpa using hle
      exact (ENNReal.mul_le_mul_iff_left hV0 hVt).1 hle'
    rw [ENNReal.one_le_ofReal] at this
    rw [le_inv_mul_iff₀ hpos, mul_one] at this
    exact this

lemma lintegral_comp_smul_distort {h : ℝ} {Q : Fin d → EuclideanSpace ℝ (Fin d)}
    (hdet : LinearMap.det (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))
      ≠ 0)
    {F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u, F (h • distort Q u) = ENNReal.ofReal |(LinearMap.det
      (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))))⁻¹| *
        ∫⁻ s, F s := by
  set T := h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  have hT : (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = fun u => h • distort Q u :=
    rfl
  have hTm : Measurable (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) := by
    rw [hT]; exact ((distort Q).continuous.const_smul h).measurable
  symm
  rw [← smul_eq_mul, ← lintegral_smul_measure,
    ← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, lintegral_map hF hTm, hT]

lemma lintegral_latticeSum_eq {h : ℝ} {Q : Fin d → EuclideanSpace ℝ (Fin d)}
    (hdet : LinearMap.det (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))
      ≠ 0)
    (H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ η in halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)),
        ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H (samplePt h Q η p.1, samplePt h Q η p.2)
      = ENNReal.ofReal |(LinearMap.det
      (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))))⁻¹| *
        ∑' w : Fin d → ℤ, ∫⁻ s, H (s, s + h • distort Q (latticePt d 1 w)) := by
  set G : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun w u =>
    H (h • distort Q u, h • distort Q u + h • distort Q (latticePt d 1 w)) with hGdef
  have hG : ∀ w, Measurable (G w) := by
    intro w
    have hc : Continuous fun u : EuclideanSpace ℝ (Fin d) => h • distort Q u :=
      (distort Q).continuous.const_smul h
    exact hH.comp ((hc.prodMk (hc.add continuous_const)).measurable)
  let e : (Fin d → ℤ) × (Fin d → ℤ) ≃ (Fin d → ℤ) × (Fin d → ℤ) :=
    { toFun := fun q => (q.1, q.1 + q.2)
      invFun := fun p => (p.1, p.2 - p.1)
      left_inv := fun q => by simp
      right_inv := fun p => by simp }
  have step1 : ∀ η, ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H (samplePt h Q η p.1, samplePt h Q η p.2)
      = ∑' w, ∑' n, G w (latticePt d 1 n + η) := by
    intro η
    rw [← e.tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    refine tsum_congr fun w => tsum_congr fun n => ?_
    simp only [e, Equiv.coe_fn_mk, samplePt, hGdef, latticePt_one_add, map_add, smul_add]
    congr 2
    abel
  simp_rw [step1]
  rw [lintegral_tsum (f := fun w η => ∑' n, G w (latticePt d 1 n + η))
      (fun w => (Measurable.tsum fun n =>
      (hG w).comp (measurable_const_add (latticePt d 1 n))).aemeasurable),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  rw [lintegral_cube_tsum (hG w)]
  exact lintegral_comp_smul_distort hdet (F := fun s => H (s, s + h • distort Q (latticePt d 1 w)))
    (hH.comp (measurable_id.prodMk (measurable_id.add_const _)))

lemma det_smul_distort (h : ℝ) (Q : Fin d → EuclideanSpace ℝ (Fin d)) :
    LinearMap.det (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)))
      = h ^ d * LinearMap.det (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
      := by
  rw [LinearMap.det_smul, finrank_euclideanSpace_fin]

/-- Upper half of the shift average: the lattice sum averaged over `η` is at most
`(h(1 − dδ))^{-d}` times the sum over difference vectors `w` of `∫ H(s, s + h A_Q w) ds`. -/
theorem lintegral_latticeSum_le {δ h : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    {Q : Fin d → EuclideanSpace ℝ (Fin d)} (hQ : Q ∈ colBox d δ) (hh : 0 < h)
    (H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ η in halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)),
        ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H (samplePt h Q η p.1, samplePt h Q η p.2)
      ≤ ENNReal.ofReal ((h ^ d * (1 - d * δ) ^ d)⁻¹) *
        ∑' w : Fin d → ℤ, ∫⁻ s, H (s, s + h • distort Q (latticePt d 1 w)) := by
  have hA := det_distort_ne_zero hδ hδ' hQ
  have hdet : LinearMap.det
      (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≠ 0 := by
    rw [det_smul_distort]; exact mul_ne_zero (pow_ne_zero _ hh.ne') hA
  rw [lintegral_latticeSum_eq hdet H hH]
  gcongr
  rw [det_smul_distort, abs_inv, abs_mul, abs_pow, abs_of_pos hh]
  have hc1 : 0 < 1 - d * δ := by linarith
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
    (abs_det_distort_bounds hδ hδ' hQ).1 (by positivity))

/-- Lower half of the shift average. -/
theorem le_lintegral_latticeSum {δ h : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    {Q : Fin d → EuclideanSpace ℝ (Fin d)} (hQ : Q ∈ colBox d δ) (hh : 0 < h)
    (H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hH : Measurable H) :
    ENNReal.ofReal ((h ^ d * (1 + d * δ) ^ d)⁻¹) *
        ∑' w : Fin d → ℤ, ∫⁻ s, H (s, s + h • distort Q (latticePt d 1 w))
      ≤ ∫⁻ η in halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)),
        ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H (samplePt h Q η p.1, samplePt h Q η p.2) := by
  have hA := det_distort_ne_zero hδ hδ' hQ
  have hdet : LinearMap.det
      (h • (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))) ≠ 0 := by
    rw [det_smul_distort]; exact mul_ne_zero (pow_ne_zero _ hh.ne') hA
  rw [lintegral_latticeSum_eq hdet H hH]
  gcongr
  rw [det_smul_distort, abs_inv, abs_mul, abs_pow, abs_of_pos hh]
  have hpos : 0 < |LinearMap.det
      (distort Q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))| := abs_pos.2 hA
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
    (abs_det_distort_bounds hδ hδ' hQ).2 (by positivity))

end QFS
