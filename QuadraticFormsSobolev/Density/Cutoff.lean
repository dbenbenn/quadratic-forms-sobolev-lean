import QuadraticFormsSobolev.Density.Radial

/-! # Cutting off converges in `H^{α/2}(ℝ^d)`

With `χ` a smooth bump equal to `1` on `B(0, 1)` and `χ_n(x) = χ(x/(n+1))`, the tails
`(1 − χ_n) f` tend to `0` in `L²` and in the seminorm. For the seminorm,
`(ψf)(y) − (ψf)(x) = ψ(y)(f(y) − f(x)) + f(x)(ψ(y) − ψ(x))`: the first part tends to `0` by
dominated convergence, and the second is at most `‖f‖²_{L²} ∫ min(1, |h|²/(n+1)²·L²)|h|^{−d−α} dh`,
which tends to `0` because `∫ min(1, |h|²)|h|^{−d−α} dh < ∞`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- The smooth bump `χ`: `1` on `B(0, 1)`, supported in `B(0, 2)`. -/
noncomputable def cutBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_n(x) = χ(x/(n+1))`. -/
noncomputable def cutFun (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  cutBump (((n : ℝ) + 1)⁻¹ • x)

/-- The tail `(1 − χ_n) f`. -/
noncomputable def tail (n : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (1 - cutFun n x) * f x

lemma cutFun_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ cutFun n x :=
  ContDiffBump.nonneg _

lemma cutFun_le_one (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : cutFun n x ≤ 1 :=
  ContDiffBump.le_one _

lemma cutFun_eq_one {n : ℕ} {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ ≤ n + 1) :
    cutFun n x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
  show ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity)]; linarith

lemma contDiff_cutFun (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutFun (d := d) n) :=
  (ContDiffBump.contDiff _).comp (contDiff_const_smul _)

lemma hasCompactSupport_cutFun (n : ℕ) : HasCompactSupport (cutFun (d := d) n) :=
  (ContDiffBump.hasCompactSupport _).comp_smul (by positivity)

lemma measurable_cutFun (n : ℕ) : Measurable (cutFun (d := d) n) :=
  (contDiff_cutFun n).continuous.measurable

/-- `χ` is Lipschitz; `χ_n` then has constant `L/(n+1)`. -/
lemma exists_cutFun_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (n : ℕ) (x y : EuclideanSpace ℝ (Fin d)),
      |cutFun n x - cutFun n y| ≤ L / (n + 1) * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := (ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (ContDiffBump.hasCompactSupport (cutBump (d := d)))
    (ContDiffBump.contDiff (n := 1) (cutBump (d := d))) one_ne_zero)
  refine ⟨C, C.2, fun n x y => ?_⟩
  have h := hC.dist_le_mul (((n : ℝ) + 1)⁻¹ • x) (((n : ℝ) + 1)⁻¹ • y)
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at h
  unfold cutFun
  calc |cutBump (((n : ℝ) + 1)⁻¹ • x) - cutBump (((n : ℝ) + 1)⁻¹ • y)|
      ≤ C * (((n : ℝ) + 1)⁻¹ * ‖x - y‖) := h
    _ = C / (n + 1) * ‖x - y‖ := by ring

lemma formHs_univ_eq_prod (g : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) :
    formHs univ α g = ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * jumpKernel d α p.1 p.2 := by
  unfold formHs form
  rw [univ_prod_univ, Measure.restrict_univ]

lemma sqInt_lt_top {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : MemLp g 2 volume) : sqInt g < ⊤ := by
  rw [← eLpNorm_two_sq]
  exact ENNReal.pow_lt_top hg.eLpNorm_lt_top

/-- **The tails tend to `0` in `L²`.** -/
theorem tendsto_sqInt_tail {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) : Tendsto (fun n => sqInt (tail n f)) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n x => ENNReal.ofReal (tail n f x ^ 2)) (f := fun _ => 0)
    (fun x => ENNReal.ofReal (f x ^ 2))
    (fun n => by unfold tail; have := measurable_cutFun (d := d) n; fun_prop)
    (fun n => Eventually.of_forall fun x => by
      apply ENNReal.ofReal_le_ofReal
      have h0 := cutFun_nonneg n x
      have h1 := cutFun_le_one n x
      simp only [tail, mul_pow]
      have : (1 - cutFun n x) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (f x)])
    (sqInt_lt_top hf).ne
    (Eventually.of_forall fun x => by
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖x‖⌉₊) fun n hn => ?_
      have : ‖x‖ ≤ n + 1 := by
        have := Nat.le_ceil ‖x‖
        have : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [tail, cutFun_eq_one this])
  simpa [sqInt] using h

/-- The first part of the tail seminorm. -/
noncomputable def tailA (n : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2

/-- The kernel mass of the cutoff's oscillation. -/
noncomputable def tailJ (d : ℕ) (L : ℝ) (n : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2)) * wK d α h

lemma tail_oscillation_le {L : ℝ} (hL : ∀ (n : ℕ) (x y : EuclideanSpace ℝ (Fin d)),
      |cutFun n x - cutFun n y| ≤ L / (n + 1) * ‖x - y‖) (n : ℕ) (x h : EuclideanSpace ℝ (Fin d)) :
    (cutFun n x - cutFun n (x + h)) ^ 2 ≤ min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2) := by
  have hl := hL n x (x + h)
  rw [sub_add_cancel_left, norm_neg] at hl
  have h0 := cutFun_nonneg n x
  have h1 := cutFun_le_one n x
  have h2 := cutFun_nonneg n (x + h)
  have h3 := cutFun_le_one n (x + h)
  refine le_min (by nlinarith) ?_
  rw [← mul_pow]
  exact sq_le_sq' (abs_le.mp hl).1 (abs_le.mp hl).2

lemma formHs_tail_le {L : ℝ} (hL : ∀ (n : ℕ) (x y : EuclideanSpace ℝ (Fin d)),
      |cutFun n x - cutFun n y| ≤ L / (n + 1) * ‖x - y‖)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfm : Measurable f) (α : ℝ) (n : ℕ) :
    formHs univ α (tail n f) ≤ 2 * tailA n f α + 2 * (sqInt f * tailJ d L n α) := by
  have hχ : Measurable (cutFun (d := d) n) := measurable_cutFun n
  have hjk := measurable_jumpKernel d α
  have hAm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
    (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2)).mul hjk
  have hBm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (f p.1 ^ 2 * (cutFun n p.1 - cutFun n p.2) ^ 2) * jumpKernel d α p.1 p.2 :=
    (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (f p.1 ^ 2 * (cutFun n p.1 - cutFun n p.2) ^ 2)).mul hjk
  have hpt : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((tail n f p.2 - tail n f p.1) ^ 2) * jumpKernel d α p.1 p.2 ≤
        2 * (ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2) *
          jumpKernel d α p.1 p.2) +
        2 * (ENNReal.ofReal (f p.1 ^ 2 * (cutFun n p.1 - cutFun n p.2) ^ 2) *
          jumpKernel d α p.1 p.2) := by
    intro p
    have e : tail n f p.2 - tail n f p.1 =
        (1 - cutFun n p.2) * (f p.2 - f p.1) + f p.1 * (cutFun n p.1 - cutFun n p.2) := by
      simp only [tail]; ring
    rw [e, ← mul_assoc, ← mul_assoc, ← add_mul]
    gcongr
    have := ofReal_sq_add_le ((1 - cutFun n p.2) * (f p.2 - f p.1))
      (f p.1 * (cutFun n p.1 - cutFun n p.2))
    simpa only [mul_pow] using this
  have hB : ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (f p.1 ^ 2 * (cutFun n p.1 - cutFun n p.2) ^ 2) * jumpKernel d α p.1 p.2
        ≤ sqInt f * tailJ d L n α := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hBm.aemeasurable]
    have hin : ∀ x : EuclideanSpace ℝ (Fin d), ∫⁻ y, ENNReal.ofReal (f x ^ 2 * (cutFun n x - cutFun n y) ^ 2) *
        jumpKernel d α x y ≤ ENNReal.ofReal (f x ^ 2) * tailJ d L n α := by
      intro x
      rw [tailJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left_eq_self _ x]
      refine lintegral_mono fun h => ?_
      simp only [jumpKernel, wK, sub_add_cancel_left, norm_neg]
      rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
      gcongr
      exact tail_oscillation_le hL n x h
    calc ∫⁻ x : EuclideanSpace ℝ (Fin d), ∫⁻ y : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (f x ^ 2 * (cutFun n x - cutFun n y) ^ 2) *
          jumpKernel d α x y
        ≤ ∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (f x ^ 2) * tailJ d L n α := lintegral_mono hin
      _ = sqInt f * tailJ d L n α := lintegral_mul_const _ (by fun_prop)
  rw [formHs_univ_eq_prod]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left (hAm.const_mul _), lintegral_const_mul _ hAm, lintegral_const_mul _ hBm]
  gcongr
  exact le_rfl

lemma tendsto_tailA {α : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfm : Measurable f)
    (hS : formHs univ α f ≠ ⊤) : Tendsto (fun n => tailA n f α) atTop (𝓝 0) := by
  have hjk := measurable_jumpKernel d α
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2)
    (f := fun _ => 0)
    (fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2)
    (fun n => by
      have := measurable_cutFun (d := d) n
      exact (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((1 - cutFun n p.2) ^ 2 * (f p.2 - f p.1) ^ 2)).mul hjk)
    (fun n => Eventually.of_forall fun p => by
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      have h0 := cutFun_nonneg n p.2
      have h1 := cutFun_le_one n p.2
      have : (1 - cutFun n p.2) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (f p.2 - f p.1)])
    (by rw [← formHs_univ_eq_prod]; exact hS)
    (Eventually.of_forall fun p => by
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖p.2‖⌉₊) fun n hn => ?_
      have : ‖p.2‖ ≤ n + 1 := by
        have := Nat.le_ceil ‖p.2‖
        have : (⌈‖p.2‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp [cutFun_eq_one this])
  simpa [tailA] using h

lemma tendsto_tailJ (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {L : ℝ} (hL0 : 0 ≤ L) :
    Tendsto (fun n => tailJ d L n α) atTop (𝓝 0) := by
  have hfin := lintegral_minKernel_lt_top hd hα0 hα2
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n (h : EuclideanSpace ℝ (Fin d)) => ENNReal.ofReal (min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2)) * wK d α h)
    (f := fun _ => 0)
    (fun h => ENNReal.ofReal (1 + L ^ 2) *
      ENNReal.ofReal (min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)))
    (fun n => by have := measurable_wK d α; fun_prop)
    (fun n => Eventually.of_forall fun h => by
      simp only [wK]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hw : 0 ≤ ‖h‖ ^ (-(d : ℝ) - α) := by positivity
      have hc : (L / (n + 1)) ^ 2 ≤ L ^ 2 := by
        gcongr
        exact div_le_self hL0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      have hmin : min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2) ≤ (1 + L ^ 2) * min 1 (‖h‖ ^ 2) := by
        rcases le_total 1 (‖h‖ ^ 2) with h1 | h1
        · rw [min_eq_left h1]; nlinarith [min_le_left 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2)]
        · rw [min_eq_right h1]
          have := min_le_right 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2)
          nlinarith [sq_nonneg ‖h‖]
      calc min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)
          ≤ (1 + L ^ 2) * min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α) := by gcongr
        _ = _ := by ring)
    (by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    (Eventually.of_forall fun h => by
      have hc : Tendsto (fun n : ℕ => min 1 ((L / (n + 1)) ^ 2 * ‖h‖ ^ 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => L / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
            tendsto_natCast_atTop_atTop)
        have h2 := ((h1.pow 2).mul_const (‖h‖ ^ 2))
        simp only [zero_pow two_ne_zero, zero_mul] at h2
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).min h2
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hc)
        (Or.inr (show wK d α h ≠ ⊤ from ENNReal.ofReal_ne_top))
      simpa using this)
  simpa [tailJ] using h

/-- **The tails tend to `0` in the seminorm.** -/
theorem tendsto_formHs_tail (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (hS : formHs univ α f ≠ ⊤) : Tendsto (fun n => formHs univ α (tail n f)) atTop (𝓝 0) := by
  obtain ⟨L, hL0, hL⟩ := exists_cutFun_lipschitz (d := d)
  have hlim : Tendsto (fun n => 2 * tailA n f α + 2 * (sqInt f * tailJ d L n α)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (tendsto_tailA hfm hS)
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have h2 := ENNReal.Tendsto.const_mul (tendsto_tailJ hd hα0 hα2 hL0) (Or.inr (sqInt_lt_top hf).ne)
    have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using h1.add h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    (formHs_tail_le hL hfm α)

end QFS
