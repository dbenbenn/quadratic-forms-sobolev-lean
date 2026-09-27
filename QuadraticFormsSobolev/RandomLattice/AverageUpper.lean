import QuadraticFormsSobolev.RandomLattice.Tiling
import QuadraticFormsSobolev.RandomLattice.Column
import QuadraticFormsSobolev.RandomLattice.LatticeCount

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-! # Random lattice sampling: the averaged sum is at most the integral

Combining the shift average (`lintegral_latticeSum_le`), the column average
(`lintegral_colBox_le`) and the lattice count (`tsum_count_le`). -/

/-- Scaling and translation: `∫ F(s + h y) dy = h^{-d} ∫ F`. -/
lemma avgU_lintegral_add_smul {h : ℝ} (hh : 0 < h) (s : EuclideanSpace ℝ (Fin d))
    {F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F (s + h • y) = ENNReal.ofReal (h⁻¹ ^ d) * ∫⁻ t, F t := by
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin d) => h • y) :=
    (continuous_const_smul h).measurable
  have := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f := fun x => F (s + x)) (hF.comp (measurable_const_add s)) hm
  rw [← this, Measure.map_addHaar_smul volume hh.ne', lintegral_smul_measure,
    lintegral_add_left_eq_self (fun x => F x) s, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (by positivity), inv_pow]

/-- Summing the ball averages against the lattice count. -/
lemma avgU_tsum_ball_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    {g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g) :
    ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), g y
      ≤ ENNReal.ofReal (4 ^ d) * ∫⁻ y, g y := by
  calc ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), g y
      = ∑' w : Fin d → ℤ, ∫⁻ y, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
          (closedBall (latticePt d 1 w) (d * δ * supNormZ w)).indicator
            (fun _ => (1 : ℝ≥0∞)) y * g y := by
        refine tsum_congr fun w => ?_
        rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_const_mul' _ _
          ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ closedBall (latticePt d 1 w) (d * δ * supNormZ w)
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy]
    _ = ∫⁻ y, ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
          (closedBall (latticePt d 1 w) (d * δ * supNormZ w)).indicator
            (fun _ => (1 : ℝ≥0∞)) y * g y := by
        rw [lintegral_tsum fun w => ?_]
        exact ((measurable_const.indicator measurableSet_closedBall).const_mul _ |>.mul
          hg).aemeasurable
    _ ≤ ∫⁻ y, ENNReal.ofReal (4 ^ d) * g y := by
        refine lintegral_mono fun y => ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (tsum_count_le hd hδ hδ' y) _
    _ = ENNReal.ofReal (4 ^ d) * ∫⁻ y, g y := lintegral_const_mul _ hg

/-- **Upper bound.** The random-lattice average of the sum of `H` over pairs of sample
points is at most `K h^{-2d} ∫∫ H`, provided `H` vanishes on the diagonal. -/
theorem latAvg_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h →
      ∀ H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable H →
      (∀ s, H (s, s) = 0) →
      latAvg d δ h H ≤ ENNReal.ofReal (K * h⁻¹ ^ (2 * d)) * ∫⁻ p, H p := by
  set V := volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ) ^ (d - 1) with hV
  have hVtop : V ≠ ⊤ := ENNReal.pow_ne_top measure_closedBall_lt_top.ne
  have hc : 0 < 1 - (d : ℝ) * δ := by linarith
  refine ⟨((1 - d * δ) ^ d)⁻¹ * V.toReal * 4 ^ d, by positivity, fun h hh H hH hdiag => ?_⟩
  set c₁ := ENNReal.ofReal ((h ^ d * (1 - d * δ) ^ d)⁻¹) with hc₁
  have hFm : ∀ w : Fin d → ℤ, Measurable (fun p : (Fin d → EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => H (p.2, p.2 + h • distort p.1 (latticePt d 1 w))) := by
    intro w
    refine hH.comp (Continuous.measurable ?_)
    simp_rw [distort_apply]
    fun_prop
  have hcol : MeasurableSet (colBox d δ) :=
    MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  have hG : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      H (p.1, p.1 + h • p.2)) := hH.comp (Continuous.measurable (by fun_prop))
  have hlat0 : latticePt d 1 0 = 0 := by ext i; simp [latticePt]
  have step3 : ∀ (w : Fin d → ℤ) (s : EuclideanSpace ℝ (Fin d)),
      ∫⁻ Q in colBox d δ, H (s, s + h • distort Q (latticePt d 1 w))
        ≤ V * ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
          ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), H (s, s + h • y) := by
    intro w s
    by_cases hw : w = 0
    · subst hw
      simp [hlat0, hdiag]
    · exact lintegral_colBox_le hd hδ w hw (fun y => H (s, s + h • y))
        (hG.comp (measurable_const.prodMk measurable_id))
  have hK : ((1 - d * δ) ^ d)⁻¹ * V.toReal * 4 ^ d * h⁻¹ ^ (2 * d)
      = (h ^ d * (1 - d * δ) ^ d)⁻¹ * V.toReal * 4 ^ d * h⁻¹ ^ d := by
    rw [mul_inv, ← inv_pow, two_mul, pow_add]; ring
  have hprod : ∫⁻ p, H p = ∫⁻ s, ∫⁻ t, H (s, t) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
  calc latAvg d δ h H
      ≤ ∫⁻ Q in colBox d δ, c₁ *
          ∑' w : Fin d → ℤ, ∫⁻ s, H (s, s + h • distort Q (latticePt d 1 w)) :=
        setLIntegral_mono' hcol fun Q hQ => lintegral_latticeSum_le hδ.le hδ' hQ hh H hH
    _ = c₁ * ∑' w : Fin d → ℤ, ∫⁻ s, ∫⁻ Q in colBox d δ,
          H (s, s + h • distort Q (latticePt d 1 w)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun w => ((hFm w).lintegral_prod_right').aemeasurable]
        congr 1
        refine tsum_congr fun w => ?_
        exact lintegral_lintegral_swap (hFm w).aemeasurable
    _ ≤ c₁ * ∑' w : Fin d → ℤ, ∫⁻ s, V * ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
          ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), H (s, s + h • y) := by
        gcongr with w s
        exact step3 w s
    _ = c₁ * ∫⁻ s, V * ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
          ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), H (s, s + h • y) := by
        rw [← lintegral_tsum fun w => ((hG.lintegral_prod_right').const_mul _).aemeasurable]
        congr 1
        refine lintegral_congr fun s => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun w => mul_assoc _ _ _
    _ ≤ c₁ * ∫⁻ s, V * (ENNReal.ofReal (4 ^ d) * ∫⁻ y, H (s, s + h • y)) := by
        gcongr with s
        exact avgU_tsum_ball_le hd hδ.le hδ' (hG.comp (measurable_const.prodMk measurable_id))
    _ = c₁ * ∫⁻ s, V * (ENNReal.ofReal (4 ^ d) *
          (ENNReal.ofReal (h⁻¹ ^ d) * ∫⁻ t, H (s, t))) := by
        congr 1
        refine lintegral_congr fun s => ?_
        rw [avgU_lintegral_add_smul hh s (F := fun t => H (s, t))
          (hH.comp (measurable_const.prodMk measurable_id))]
    _ = c₁ * V * ENNReal.ofReal (4 ^ d) * ENNReal.ofReal (h⁻¹ ^ d) * ∫⁻ p, H p := by
        rw [hprod, lintegral_const_mul' _ _ hVtop, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
    _ = ENNReal.ofReal (((1 - d * δ) ^ d)⁻¹ * V.toReal * 4 ^ d * h⁻¹ ^ (2 * d)) *
          ∫⁻ p, H p := by
        rw [hK, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hVtop]

end QFS
