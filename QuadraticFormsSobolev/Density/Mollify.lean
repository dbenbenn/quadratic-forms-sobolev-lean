import QuadraticFormsSobolev.Density.Translation

/-! # Mollification converges in `H^{α/2}(ℝ^d)`

With `ρ_n` a normed smooth bump supported in `B(0, 1/(n+1))` and `m_n = ρ_n ⋆ g`:
* `‖m_n − g‖²_{L²} ≤ ∫ ρ_n(t) ‖g(· − t) − g‖²_{L²} dt` (Jensen), which tends to `0` by the
  continuity of translation;
* `D_h(m_n) ≤ D_h(g)` for every `h` (Jensen again), so `D_h(m_n − g) ≤ 4 D_h(g)`, and the seminorm
  of `m_n − g` tends to `0` by dominated convergence in `h`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Convolution

namespace QFS

variable {d : ℕ}

/-- The bump of outer radius `1/(n+1)`. -/
noncomputable def molliBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity, by
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]; linarith⟩

/-- The mollifier `ρ_n`. -/
noncomputable def molli (n : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (molliBump (d := d) n).normed volume

/-- `m_n = ρ_n ⋆ g`. -/
noncomputable def mollify (n : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  molli n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

lemma molli_nonneg (n : ℕ) (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ molli n z :=
  ContDiffBump.nonneg_normed _ _

lemma integral_molli (n : ℕ) : ∫ z, molli (d := d) n z = 1 :=
  ContDiffBump.integral_normed _

lemma integrable_molli (n : ℕ) : Integrable (molli (d := d) n) :=
  ContDiffBump.integrable_normed _

lemma continuous_molli (n : ℕ) : Continuous (molli (d := d) n) :=
  ContDiffBump.continuous_normed _

lemma hasCompactSupport_molli (n : ℕ) : HasCompactSupport (molli (d := d) n) :=
  ContDiffBump.hasCompactSupport_normed _

lemma molli_eq_zero {n : ℕ} {z : EuclideanSpace ℝ (Fin d)} (hz : z ∉ ball 0 (1 / (n + 1))) :
    molli n z = 0 := by
  have : z ∉ Function.support (molli (d := d) n) := by
    rw [molli, ContDiffBump.support_normed_eq]; exact hz
  simpa using this

lemma lintegral_molli (n : ℕ) : ∫⁻ z, ENNReal.ofReal (molli (d := d) n z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_molli n)
    (Eventually.of_forall (molli_nonneg n)), integral_molli, ENNReal.ofReal_one]

lemma mollify_apply (n : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    mollify n g x = ∫ t, molli n t * g (x - t) := by
  simp [mollify, convolution_lsmul]

lemma integrable_molli_mul {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : LocallyIntegrable g)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable fun t => molli n t * g (x - t) := by
  have := (hasCompactSupport_molli (d := d) n).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (continuous_molli n) hg x
  simpa [ConvolutionExistsAt] using this

lemma contDiff_mollify {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : LocallyIntegrable g) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify n g) :=
  (hasCompactSupport_molli n).contDiff_convolution_left (n := ⊤) _
    (ContDiffBump.contDiff_normed _) hg

lemma hasCompactSupport_mollify {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : HasCompactSupport g)
    (n : ℕ) : HasCompactSupport (mollify n g) :=
  (hasCompactSupport_molli n).convolution _ hg

/-- The difference of `ρ ⋆ g` at two points, as one integral against `ρ`. -/
lemma mollify_sub_apply {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : LocallyIntegrable g) (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    mollify n g x - mollify n g y = ∫ t, molli n t * (g (x - t) - g (y - t)) := by
  rw [mollify_apply, mollify_apply, ← integral_sub (integrable_molli_mul hg n x)
    (integrable_molli_mul hg n y)]
  simp_rw [mul_sub]

/-- **Jensen along the mollifier**, for a measurable `F` with `ρ F` integrable. -/
lemma sq_mollify_le {n : ℕ} {v : EuclideanSpace ℝ (Fin d) → ℝ} (hvm : Measurable v)
    (hv : Integrable fun t => molli n t * v t) :
    ENNReal.ofReal ((∫ t, molli n t * v t) ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) * ENNReal.ofReal (v t ^ 2) :=
  ofReal_sq_integral_le (molli_nonneg n) (integrable_molli n) (integral_molli n) hv
    hvm.aestronglyMeasurable

/-- **M1**: `‖ρ ⋆ g − g‖² ≤ ∫ ρ(t) ‖g(· − t) − g‖² dt`. -/
lemma sqInt_mollify_sub_le {g : EuclideanSpace ℝ (Fin d) → ℝ} (hgm : Measurable g)
    (hg : LocallyIntegrable g) (n : ℕ) :
    sqInt (mollify n g - g) ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) * sqInt (fun x => g (x - t) - g x) := by
  have hpt : ∀ x, ENNReal.ofReal ((mollify n g x - g x) ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x - t) - g x) ^ 2) := by
    intro x
    have he : mollify n g x - g x = ∫ t, molli n t * (g (x - t) - g x) := by
      rw [mollify_apply, show (fun t => molli n t * (g (x - t) - g x)) =
          fun t => molli n t * g (x - t) - molli n t * g x by funext t; ring,
        integral_sub (integrable_molli_mul hg n x) ((integrable_molli n).mul_const _),
        integral_mul_const, integral_molli, one_mul]
    rw [he]
    refine sq_mollify_le (by fun_prop) ?_
    rw [show (fun t => molli n t * (g (x - t) - g x)) =
        fun t => molli n t * g (x - t) - molli n t * g x by funext t; ring]
    exact (integrable_molli_mul hg n x).sub ((integrable_molli n).mul_const _)
  have hρm : Measurable (molli (d := d) n) := (continuous_molli n).measurable
  have hm : Measurable (Function.uncurry fun x t : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x - t) - g x) ^ 2)) := by
    unfold Function.uncurry; fun_prop
  calc sqInt (mollify n g - g) = ∫⁻ x, ENNReal.ofReal ((mollify n g x - g x) ^ 2) := rfl
    _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x - t) - g x) ^ 2) :=
        lintegral_mono hpt
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x - t) - g x) ^ 2) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = _ := lintegral_congr fun t => lintegral_const_mul _ (by fun_prop)

/-- **M2**: `D_h(ρ ⋆ g) ≤ D_h(g)`. -/
lemma diffInt_mollify_le {g : EuclideanSpace ℝ (Fin d) → ℝ} (hgm : Measurable g)
    (hg : LocallyIntegrable g) (n : ℕ) (h : EuclideanSpace ℝ (Fin d)) :
    diffInt (mollify n g) h ≤ diffInt g h := by
  have hpt : ∀ x, ENNReal.ofReal ((mollify n g (x + h) - mollify n g x) ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x + h - t) - g (x - t)) ^ 2) := by
    intro x
    rw [mollify_sub_apply hg]
    refine sq_mollify_le (by fun_prop) ?_
    rw [show (fun t => molli n t * (g (x + h - t) - g (x - t))) =
        fun t => molli n t * g (x + h - t) - molli n t * g (x - t) by funext t; ring]
    exact (integrable_molli_mul hg n _).sub (integrable_molli_mul hg n x)
  have hρm : Measurable (molli (d := d) n) := (continuous_molli n).measurable
  have hm : Measurable (Function.uncurry fun x t : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (molli n t) * ENNReal.ofReal ((g (x + h - t) - g (x - t)) ^ 2)) := by
    unfold Function.uncurry; fun_prop
  have hshift : ∀ t, ∫⁻ x, ENNReal.ofReal ((g (x + h - t) - g (x - t)) ^ 2) = diffInt g h := by
    intro t
    rw [diffInt, ← lintegral_sub_right_eq_self
      (fun y => ENNReal.ofReal ((g (y + h) - g y) ^ 2)) t]
    refine lintegral_congr fun x => ?_
    simp only [sub_add_eq_add_sub]
  calc diffInt (mollify n g) h
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((g (x + h - t) - g (x - t)) ^ 2) := lintegral_mono hpt
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((g (x + h - t) - g (x - t)) ^ 2) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal (molli n t) * diffInt g h := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul _ (by fun_prop), hshift]
    _ = diffInt g h := by
        rw [lintegral_mul_const _ (by fun_prop), lintegral_molli, one_mul]

/-- **Mollification converges in `L²`.** -/
theorem tendsto_sqInt_mollify_sub {g : EuclideanSpace ℝ (Fin d) → ℝ} (hgm : Measurable g)
    (hg : MemLp g 2 volume) :
    Tendsto (fun n => sqInt (mollify n g - g)) atTop (𝓝 0) := by
  have hloc := hg.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (ENNReal.tendsto_nhds_zero.mp (tendsto_sqInt_translate hg hgm) ε hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  refine ⟨N, fun n hn => (sqInt_mollify_sub_le hgm hloc n).trans ?_⟩
  calc ∫⁻ t, ENNReal.ofReal (molli n t) * sqInt (fun x => g (x - t) - g x)
      ≤ ∫⁻ t, ENNReal.ofReal (molli n t) * ε := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / (n + 1))
        · gcongr
          refine hball ?_
          rw [mem_ball] at ht
          have : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
            gcongr
          linarith
        · rw [molli_eq_zero ht]; simp
    _ = ε := by
        rw [lintegral_mul_const _ (continuous_molli n).measurable.ennreal_ofReal, lintegral_molli,
          one_mul]

/-- **Mollification converges in `H^{α/2}(ℝ^d)`.** -/
theorem tendsto_formHs_mollify_sub {g : EuclideanSpace ℝ (Fin d) → ℝ} (hgm : Measurable g)
    (hg : MemLp g 2 volume) {α : ℝ} (hS : formHs univ α g ≠ ⊤) :
    Tendsto (fun n => formHs univ α (mollify n g - g)) atTop (𝓝 0) := by
  have hloc := hg.locallyIntegrable (by norm_num)
  have hmm : ∀ n, Measurable (mollify n g) := fun n => (contDiff_mollify hloc n).continuous.measurable
  simp_rw [formHs_univ_eq ((hmm _).sub hgm)]
  have hlim := tendsto_sqInt_mollify_sub hgm hg
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n h => wK d α h * diffInt (mollify n g - g) h) (f := fun _ => 0)
    (fun h => wK d α h * (4 * diffInt g h))
    (fun n => (measurable_wK d α).mul (measurable_diffInt ((hmm n).sub hgm)))
    (fun n => Eventually.of_forall fun h => by
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      calc diffInt (mollify n g - g) h ≤ 2 * diffInt (mollify n g) h + 2 * diffInt g h :=
            diffInt_sub_le (hmm n) h
        _ ≤ 2 * diffInt g h + 2 * diffInt g h := by gcongr; exact diffInt_mollify_le hgm hloc n h
        _ = 4 * diffInt g h := by ring)
    (by
      rw [show (fun h => wK d α h * (4 * diffInt g h)) = fun h => 4 * (wK d α h * diffInt g h) by
          funext h; ring,
        lintegral_const_mul' _ _ (by norm_num),
        ← formHs_univ_eq hgm]
      exact ENNReal.mul_ne_top (by norm_num) hS)
    (Eventually.of_forall fun h => by
      have h4 : Tendsto (fun n => 4 * sqInt (mollify n g - g)) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hlim (Or.inr (by norm_num))
      have hD : Tendsto (fun n => diffInt (mollify n g - g) h) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun _ => zero_le)
          (fun n => diffInt_le_sqInt ((hmm n).sub hgm) h)
      have := ENNReal.Tendsto.const_mul hD (Or.inr (show wK d α h ≠ ⊤ from ENNReal.ofReal_ne_top))
      simpa only [mul_zero] using this)
  simpa using h

end QFS
