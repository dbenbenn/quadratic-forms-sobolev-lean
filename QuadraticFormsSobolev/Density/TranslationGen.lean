import QuadraticFormsSobolev.Density.Basic

/-! # Continuity of translation in `L²(V)`, for any finite-dimensional `V`

`Density/Translation.lean` for a general finite-dimensional real normed space with an additive Haar
measure. It is applied on `ℝ^d` and on `ℝ^d × ℝ^d` (for the difference quotient of a function on
`Ω × Ω`). -/

open MeasureTheory Metric Set Filter Topology

set_option linter.unusedSectionVars false
open scoped ENNReal

namespace QFS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
lemma lintegral_sq_add_le' {a b : V → ℝ} (ha : Measurable a) :
    ∫⁻ x, ENNReal.ofReal ((a x + b x) ^ 2) ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ + 2 * ∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ := by
  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left (by fun_prop)]
  exact lintegral_mono fun x => ofReal_sq_add_le _ _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
lemma eLpNorm_two_sq' (g : V → ℝ) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := μ) (p := 2) (by norm_num)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h
  rw [← ENNReal.rpow_natCast, Nat.cast_ofNat, h]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs]
  simp only [ENNReal.rpow_ofNat]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- A measurable `g` with `∫ g² < ∞` is in `L²`. -/
lemma memLp_two_of_lintegral_sq {g : V → ℝ} (hg : Measurable g)
    (h : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≠ ⊤) : MemLp g 2 μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have e := eLpNorm_two_sq' μ g
  rw [← e] at h
  exact lt_top_iff_ne_top.mpr fun ht => h (by rw [ht]; rfl)

theorem tendsto_translate_of_continuous' {φ : V → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    Tendsto (fun z => ∫⁻ x, ENNReal.ofReal ((φ (x - z) - φ x) ^ 2) ∂μ) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  have hφm := hc.measurable
  set K := cthickening 1 (tsupport φ) with hK
  have hKc : IsCompact K := hs.isCompact.cthickening
  set bound : V → ℝ≥0∞ := K.indicator fun _ => ENNReal.ofReal ((2 * C) ^ 2)
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 0)
    (F := fun z x => ENNReal.ofReal ((φ (x - z) - φ x) ^ 2)) (f := fun _ => 0) bound
    (Eventually.of_forall fun z => by fun_prop)
    (by
      filter_upwards [ball_mem_nhds (0 : V) one_pos] with z hz
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K
      · simp only [bound, indicator_of_mem hx]
        apply ENNReal.ofReal_le_ofReal
        have ha := hC (x - z)
        have hb := hC x
        rw [Real.norm_eq_abs] at ha hb
        obtain ⟨ha1, ha2⟩ := abs_le.mp ha
        obtain ⟨hb1, hb2⟩ := abs_le.mp hb
        nlinarith
      · simp only [bound, indicator_of_notMem hx]
        have h1 : φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (self_subset_cthickening _ h)
        have h2 : φ (x - z) = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
          refine mem_cthickening_of_dist_le x (x - z) 1 _ h ?_
          rw [dist_eq_norm, sub_sub_cancel]
          rw [mem_ball, dist_zero_right] at hz
          exact hz.le
        simp [h1, h2])
    (by
      rw [lintegral_indicator_const hKc.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKc.measure_lt_top.ne)
    (Eventually.of_forall fun x => by
      have hcont : Continuous fun z : V => ENNReal.ofReal ((φ (x - z) - φ x) ^ 2) :=
        ENNReal.continuous_ofReal.comp
          (((hc.comp (continuous_const.sub continuous_id)).sub continuous_const).pow 2)
      simpa using hcont.tendsto 0)
  simpa using h

/-- **Translation is continuous in `L²(V)`.** -/
theorem tendsto_translate' {g : V → ℝ} (hg : MemLp g 2 μ) (hgm : Measurable g) :
    Tendsto (fun z => ∫⁻ x, ENNReal.ofReal ((g (x - z) - g x) ^ 2) ∂μ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  set e := ε.toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hε.ne' htop
  have hη : ENNReal.ofReal (Real.sqrt (e / 12)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  obtain ⟨φ, hφs, hφε, hφc, -⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hη
  have hφm := hφc.measurable
  set Q : (V → ℝ) → ℝ≥0∞ := fun u => ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ with hQdef
  have hQ : Q (g - φ) ≤ ENNReal.ofReal (e / 12) := by
    show ∫⁻ x, ENNReal.ofReal ((g - φ) x ^ 2) ∂μ ≤ _
    rw [← eLpNorm_two_sq']
    calc eLpNorm (g - φ) 2 μ ^ 2 ≤ ENNReal.ofReal (Real.sqrt (e / 12)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (e / 12) := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  have hcont := ENNReal.tendsto_nhds_zero.mp (tendsto_translate_of_continuous' μ hφc hφs)
    (ENNReal.ofReal (e / 8)) (by rw [gt_iff_lt, ENNReal.ofReal_pos]; positivity)
  filter_upwards [hcont] with z hz
  set u : V → ℝ := fun x => (g - φ) (x - z)
  set w : V → ℝ := fun x => φ (x - z) - φ x
  set v : V → ℝ := φ - g
  have hu : Q u = Q (g - φ) :=
    lintegral_sub_right_eq_self (μ := μ) (fun x => ENNReal.ofReal ((g - φ) x ^ 2)) z
  have hv : Q v = Q (g - φ) := by
    simp only [hQdef, v, Pi.sub_apply]
    refine lintegral_congr fun x => ?_
    congr 1; ring
  have hum : Measurable u := (hgm.sub hφm).comp (by fun_prop)
  have hwm : Measurable w := by fun_prop
  have hsplit : ∀ x, g (x - z) - g x = u x + (w x + v x) := by
    intro x; simp only [u, w, v, Pi.sub_apply]; ring
  calc ∫⁻ x, ENNReal.ofReal ((g (x - z) - g x) ^ 2) ∂μ
      = ∫⁻ x, ENNReal.ofReal ((u x + (w x + v x)) ^ 2) ∂μ := by simp_rw [hsplit]
    _ ≤ 2 * Q u + 2 * ∫⁻ x, ENNReal.ofReal ((w x + v x) ^ 2) ∂μ :=
        lintegral_sq_add_le' μ hum
    _ ≤ 2 * Q u + 2 * (2 * Q w + 2 * Q v) := by
        gcongr; exact lintegral_sq_add_le' μ hwm
    _ ≤ 2 * ENNReal.ofReal (e / 12) + 2 * (2 * ENNReal.ofReal (e / 8) +
          2 * ENNReal.ofReal (e / 12)) := by
        rw [hu, hv]; gcongr
    _ = 6 * ENNReal.ofReal (e / 12) + 4 * ENNReal.ofReal (e / 8) := by ring
    _ = ENNReal.ofReal (6 * (e / 12)) + ENNReal.ofReal (4 * (e / 8)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ = ε := ENNReal.ofReal_toReal htop

end QFS
