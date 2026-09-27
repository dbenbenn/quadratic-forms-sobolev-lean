import QuadraticFormsSobolev.RandomLattice.Tiling
import QuadraticFormsSobolev.RandomLattice.Column
import QuadraticFormsSobolev.RandomLattice.LatticeCount

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-! # Random lattice sampling: the averaged sum dominates the integral at scales above `h`

Combining the shift average (`le_lintegral_latticeSum`), the column average
(`le_lintegral_colBox`) and the lattice count (`le_tsum_count`). -/

/-- Scaling and translation: `∫_{‖y‖ ≥ C} H(s, s + h y) dy = h^{-d} ∫_{‖t − s‖ ≥ C h} H(s, t) dt`. -/
lemma avgL_scale {h : ℝ} (hh : 0 < h) (C : ℝ) (s : EuclideanSpace ℝ (Fin d))
    {H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ y in {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖}, H (s, s + h • y)
      = ENNReal.ofReal ((h ^ d)⁻¹) *
        ∫⁻ t in {t : EuclideanSpace ℝ (Fin d) | C * h ≤ ‖t - s‖}, H (s, t) := by
  set T : Set (EuclideanSpace ℝ (Fin d)) := {t | C * h ≤ ‖t - s‖} with hT
  have hTm : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_id.sub_const s).norm
  have hSm : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := T.indicator (fun t => H (s, t)) with hF
  have hFm : Measurable F :=
    (hH.comp (measurable_const.prodMk measurable_id)).indicator hTm
  have hG : Measurable fun u : EuclideanSpace ℝ (Fin d) => F (s + u) :=
    hFm.comp (measurable_const_add s)
  rw [← lintegral_indicator hSm, ← lintegral_indicator hTm]
  have h1 : ∀ y : EuclideanSpace ℝ (Fin d),
      {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖}.indicator (fun y => H (s, s + h • y)) y
        = (fun u => F (s + u)) (h • y) := by
    intro y
    have hmem : (s + h • y ∈ T) ↔ C ≤ ‖y‖ := by
      simp only [hT, Set.mem_ofPred_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hh]
      rw [mul_comm h]
      exact mul_le_mul_iff_left₀ hh
    by_cases hy : C ≤ ‖y‖
    · simp [hF, Set.indicator_of_mem (hmem.2 hy), hy]
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      simp only [hF]
      rw [Set.indicator_of_notMem (fun h' => hy (hmem.1 h'))]
  simp_rw [h1]
  rw [← lintegral_map hG (measurable_const_smul h), Measure.map_addHaar_smul volume hh.ne',
    lintegral_smul_measure, lintegral_add_left_eq_self, finrank_euclideanSpace_fin,
    abs_of_pos (by positivity : (0:ℝ) < (h ^ d)⁻¹), smul_eq_mul]

/-- Fubini for the region `‖t − s‖ ≥ R`. -/
lemma avgL_fubini (R : ℝ)
    {H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | R ≤ ‖p.2 - p.1‖}, H p
      = ∫⁻ s, ∫⁻ t in {t : EuclideanSpace ℝ (Fin d) | R ≤ ‖t - s‖}, H (s, t) := by
  have hPm : MeasurableSet
      {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | R ≤ ‖p.2 - p.1‖} :=
    measurableSet_le measurable_const (measurable_snd.sub measurable_fst).norm
  rw [← lintegral_indicator hPm, Measure.volume_eq_prod,
    lintegral_prod _ (hH.indicator hPm).aemeasurable]
  refine lintegral_congr fun s => ?_
  have hTm : MeasurableSet {t : EuclideanSpace ℝ (Fin d) | R ≤ ‖t - s‖} :=
    measurableSet_le measurable_const (measurable_id.sub_const s).norm
  rw [← lintegral_indicator hTm]
  rfl

/-- The lattice count, integrated against `g`. -/
lemma avgL_count {C k δ : ℝ}
    (hk : ∀ y : EuclideanSpace ℝ (Fin d), C ≤ ‖y‖ →
      ENNReal.ofReal k ≤ ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (δ * supNormZ w / d)).indicator (fun _ => (1 : ℝ≥0∞)) y)
    {g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g) :
    ENNReal.ofReal k * ∫⁻ y in {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖}, g y
      ≤ ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), g y := by
  have hSm : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hSm]
  have : ∀ w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), g y
      = ∫⁻ y, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (δ * supNormZ w / d)).indicator (fun _ => (1 : ℝ≥0∞)) y
          * g y := by
    intro w
    rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ closedBall (latticePt d 1 w) (δ * supNormZ w / d) <;> simp [hy]
  simp_rw [this]
  rw [← lintegral_tsum (f := fun w y => ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (δ * supNormZ w / d)).indicator (fun _ => (1 : ℝ≥0∞)) y
          * g y) fun w => ((measurable_const.mul
    (measurable_const.indicator measurableSet_closedBall)).mul hg).aemeasurable]
  refine lintegral_mono fun y => ?_
  rw [ENNReal.tsum_mul_right]
  by_cases hy : C ≤ ‖y‖
  · rw [Set.indicator_of_mem (by simpa using hy)]
    exact mul_le_mul_left (hk y hy) _
  · rw [Set.indicator_of_notMem (by simpa using hy)]
    exact zero_le

/-- The column bound, for every `w` (the `w = 0` term has weight `0`). -/
lemma avgL_col (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (w : Fin d → ℤ)
    {g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) (δ / d)) ^ (d - 1) *
        (ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), g y)
      ≤ ∫⁻ Q in colBox d δ, g (distort Q (latticePt d 1 w)) := by
  by_cases hw : w = 0
  · subst hw
    have h0 : supNormZ (0 : Fin d → ℤ) = 0 := by
      have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp [supNormZ]
    rw [h0, inv_zero, zero_pow (by omega), ENNReal.ofReal_zero, zero_mul, mul_zero]
    exact zero_le
  · rw [← mul_assoc]
    exact le_lintegral_colBox hd hδ w hw g hg

/-- Joint measurability of `(Q, s) ↦ H(s, s + h A_Q v)`. -/
lemma avgL_meas {H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hH : Measurable H) (h : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    Measurable fun p : (Fin d → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
      H (p.2, p.2 + h • distort p.1 v) := by
  have hc : Continuous fun p : (Fin d → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
      distort p.1 v := by
    simp_rw [distort_apply]
    fun_prop
  exact hH.comp ((continuous_snd.prodMk (continuous_snd.add (hc.const_smul h))).measurable)

/-- **Lower bound.** The random-lattice average of the sum of `H` over pairs of sample
points dominates `K h^{-2d} ∫∫_{‖t − s‖ ≥ C h} H`. -/
theorem le_latAvg (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ h : ℝ, 0 < h →
      ∀ H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable H →
      ENNReal.ofReal (K * h⁻¹ ^ (2 * d)) *
          ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            C * h ≤ ‖p.2 - p.1‖}, H p
        ≤ latAvg d δ h H := by
  obtain ⟨C, k, hC, hk0, hk⟩ := le_tsum_count hd hδ hδ'
  set V : ℝ≥0∞ := volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) (δ / d)) ^ (d - 1) with hVdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hV0 : V ≠ 0 := pow_ne_zero _ (measure_closedBall_pos _ _ (by positivity)).ne'
  have hVt : V ≠ ⊤ := ENNReal.pow_ne_top measure_closedBall_lt_top.ne
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  refine ⟨((1 + d * δ) ^ d)⁻¹ * V.toReal * k, C, by positivity, hC, ?_⟩
  intro h hh H hH
  set c1 : ℝ := (h ^ d * (1 + d * δ) ^ d)⁻¹ with hc1
  have hconst : ENNReal.ofReal (((1 + d * δ) ^ d)⁻¹ * V.toReal * k * h⁻¹ ^ (2 * d))
      = ENNReal.ofReal c1 * (V * (ENNReal.ofReal k * ENNReal.ofReal ((h ^ d)⁻¹))) := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hVt]
    rw [← ENNReal.ofReal_mul hk0.le, ← ENNReal.ofReal_mul hVr.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : h⁻¹ ^ (2 * d) = (h ^ d)⁻¹ * (h ^ d)⁻¹ := by
      rw [inv_pow, two_mul, pow_add, mul_inv]
    rw [hc1, this, mul_inv]
    ring
  have hg : ∀ s : EuclideanSpace ℝ (Fin d), Measurable fun y : EuclideanSpace ℝ (Fin d) => H (s, s + h • y) := fun s =>
    hH.comp (measurable_const.prodMk (measurable_const.add (measurable_id.const_smul h)))
  have hmB : ∀ B : Set (EuclideanSpace ℝ (Fin d)), Measurable fun s : EuclideanSpace ℝ (Fin d) => ∫⁻ y in B, H (s, s + h • y) := fun B =>
    Measurable.lintegral_prod_right' (ν := volume.restrict B)
      (f := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => H (p.1, p.1 + h • p.2))
      (hH.comp (measurable_fst.prodMk (measurable_fst.add (measurable_snd.const_smul h))))
  have hcolBox : MeasurableSet (colBox d δ) :=
    MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  calc ENNReal.ofReal (((1 + d * δ) ^ d)⁻¹ * V.toReal * k * h⁻¹ ^ (2 * d)) *
          ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | C * h ≤ ‖p.2 - p.1‖}, H p
        = ENNReal.ofReal c1 * ∫⁻ s, V * (ENNReal.ofReal k *
            ∫⁻ y in {y : EuclideanSpace ℝ (Fin d) | C ≤ ‖y‖}, H (s, s + h • y)) := by
          rw [hconst, avgL_fubini _ hH]
          simp_rw [avgL_scale hh C _ hH]
          rw [lintegral_const_mul' _ _ hVt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
      _ ≤ ENNReal.ofReal c1 * ∫⁻ s, V * ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
            ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), H (s, s + h • y) := by
          gcongr with s
          exact avgL_count hk (hg s)
      _ = ENNReal.ofReal c1 * ∑' w : Fin d → ℤ, ∫⁻ s, V * (ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
            ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), H (s, s + h • y)) := by
          congr 1
          rw [← lintegral_tsum (f := fun (w : Fin d → ℤ) (s : EuclideanSpace ℝ (Fin d)) =>
            V * (ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
            ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), H (s, s + h • y)))
            fun w => (measurable_const.mul (measurable_const.mul (hmB _))).aemeasurable]
          refine lintegral_congr fun s => ?_
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal c1 * ∑' w : Fin d → ℤ, ∫⁻ s, ∫⁻ Q in colBox d δ,
            H (s, s + h • distort Q (latticePt d 1 w)) := by
          gcongr with w s
          exact avgL_col hd hδ w (hg s)
      _ = ENNReal.ofReal c1 * ∑' w : Fin d → ℤ, ∫⁻ Q in colBox d δ, ∫⁻ s,
            H (s, s + h • distort Q (latticePt d 1 w)) := by
          congr 1
          refine tsum_congr fun w => ?_
          exact (lintegral_lintegral_swap (avgL_meas hH h _).aemeasurable).symm
      _ = ∫⁻ Q in colBox d δ, ENNReal.ofReal c1 * ∑' w : Fin d → ℤ, ∫⁻ s,
            H (s, s + h • distort Q (latticePt d 1 w)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum fun w =>
            (Measurable.lintegral_prod_right' (avgL_meas hH h _)).aemeasurable]
      _ ≤ latAvg d δ h H := by
          refine setLIntegral_mono' hcolBox fun Q hQ => ?_
          exact le_lintegral_latticeSum hδ.le hδ' hQ hh H hH

end QFS
