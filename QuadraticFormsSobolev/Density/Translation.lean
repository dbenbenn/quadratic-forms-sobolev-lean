import QuadraticFormsSobolev.Density.Basic

/-! # Continuity of translation in `L²(ℝ^d)`

`∫ (g(x − z) − g(x))² dx → 0` as `z → 0`, for every `g ∈ L²`: first for continuous compactly
supported `g`, by dominated convergence, then in general by approximation. -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace QFS

variable {d : ℕ}

theorem tendsto_sqInt_translate_of_continuous {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous φ) (hs : HasCompactSupport φ) :
    Tendsto (fun z => sqInt (fun x => φ (x - z) - φ x)) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  have hφm := hc.measurable
  set K := cthickening 1 (tsupport φ) with hK
  have hKc : IsCompact K := hs.isCompact.cthickening
  set bound : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := K.indicator fun _ => ENNReal.ofReal ((2 * C) ^ 2)
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 0)
    (F := fun z x => ENNReal.ofReal ((φ (x - z) - φ x) ^ 2)) (f := fun _ => 0) bound
    (Eventually.of_forall fun z => by fun_prop)
    (by
      filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) one_pos] with z hz
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
      have hcont : Continuous fun z : EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal ((φ (x - z) - φ x) ^ 2) :=
        ENNReal.continuous_ofReal.comp
          (((hc.comp (continuous_const.sub continuous_id)).sub continuous_const).pow 2)
      simpa using hcont.tendsto 0)
  simpa [sqInt] using h

/-- **Translation is continuous in `L²`.** -/
theorem tendsto_sqInt_translate {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : MemLp g 2 volume)
    (hgm : Measurable g) :
    Tendsto (fun z => sqInt (fun x => g (x - z) - g x)) (𝓝 0) (𝓝 0) := by
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
  have hQ : sqInt (g - φ) ≤ ENNReal.ofReal (e / 12) := by
    rw [← eLpNorm_two_sq]
    calc eLpNorm (g - φ) 2 volume ^ 2 ≤ ENNReal.ofReal (Real.sqrt (e / 12)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (e / 12) := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  have hcont := ENNReal.tendsto_nhds_zero.mp (tendsto_sqInt_translate_of_continuous hφc hφs)
    (ENNReal.ofReal (e / 8)) (by rw [gt_iff_lt, ENNReal.ofReal_pos]; positivity)
  filter_upwards [hcont] with z hz
  set u : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (g - φ) (x - z)
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun x => φ (x - z) - φ x
  set v : EuclideanSpace ℝ (Fin d) → ℝ := φ - g
  have hsplit : (fun x => g (x - z) - g x) = u + (w + v) := by
    funext x; simp only [u, w, v, Pi.add_apply, Pi.sub_apply]; ring
  have hu : sqInt u = sqInt (g - φ) := sqInt_comp_sub (g - φ) z
  have hv : sqInt v = sqInt (g - φ) := by
    rw [show v = -(g - φ) by simp [v]]; exact sqInt_neg _
  have hum : Measurable u := (hgm.sub hφm).comp (by fun_prop)
  have hwm : Measurable w := by fun_prop
  calc sqInt (fun x => g (x - z) - g x) = sqInt (u + (w + v)) := by rw [hsplit]
    _ ≤ 2 * sqInt u + 2 * sqInt (w + v) := sqInt_add_le hum
    _ ≤ 2 * sqInt u + 2 * (2 * sqInt w + 2 * sqInt v) := by gcongr; exact sqInt_add_le hwm
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
