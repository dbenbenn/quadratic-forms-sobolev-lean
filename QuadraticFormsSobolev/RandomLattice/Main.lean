import QuadraticFormsSobolev.RandomLattice.Pointwise
import QuadraticFormsSobolev.RandomLattice.AverageUpper
import QuadraticFormsSobolev.RandomLattice.AverageLower
import QuadraticFormsSobolev.Section3Kernel
import QuadraticFormsSobolev.LebesgueDiff
import QuadraticFormsSobolev.Section1
import QuadraticFormsSobolev.Rescaling

/-!
# Random lattice sampling: the continuous comparability in every dimension

New mathematics, not in Bux–Kassmann–Schulze. It removes the a priori hypothesis of §3.2
(`f ∈ H^{α/2}` of the larger ball, which the paper's dominated-convergence step needs) in every
dimension. Instead of averaging `f` over tiles, `f` is sampled at the points of a random affine
lattice `h A_Q (ℤ^d + η)`. Sampling keeps every difference `f(s) − f(t)`, so Theorem 1.3 applies
to each lattice (`latticeSum_le`). Averaging over `η` and `Q` recovers the two continuous forms
up to constants (`le_latAvg`, `latAvg_le`), and letting `h → 0` gives the comparability.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- **The continuous comparability on `ℝ^d`, in every dimension.** For a `ϑ`-bounded
configuration and a kernel with the bounds (2), `|f|²_{H^{α/2}(ℝ^d)} ≤ C |f|²_{H_k(ℝ^d)}` with
`C` depending only on `d, ϑ, Λ, α`. No measurability of `Γ` and no finiteness of either side is
assumed. The proof samples `f` on random lattices and applies Theorem 1.3 to each. -/
theorem formHs_univ_le_form_univ_randomLattice (hd : 1 ≤ d) {ϑ Λ α : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexLowerBound Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
      formHs Set.univ α f ≤ ENNReal.ofReal C * form Set.univ k f := by
  have hsin : 0 < Real.sin (ϑ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos hϑ) (by linarith [Real.pi_pos])
  set ε : ℝ := min (1 / 2) (Real.sin (ϑ / 2) / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (half_pos hsin)
  have hε2 : ε ≤ 1 / 2 := min_le_left _ _
  have hεs : ε < Real.sin (ϑ / 2) := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hsin)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set δ : ℝ := ε / d with hδdef
  have hδ : 0 < δ := div_pos hε0 hdpos
  have hdδ : (d : ℝ) * δ = ε := by rw [hδdef]; field_simp
  have hδ' : (d : ℝ) * δ ≤ 1 / 2 := by rw [hdδ]; exact hε2
  obtain ⟨c, hc, hlat⟩ := latticeSum_le (d := d) hϑ hΛ hα
  obtain ⟨KU, hKU, hup⟩ := latAvg_le hd hδ hδ'
  obtain ⟨KL, C₀, hKL, hC₀, hlow⟩ := le_latAvg hd hδ hδ'
  refine ⟨c * KU / KL, by positivity, ?_⟩
  intro Γ hΓ k hk f hf hG
  set F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 with hFdef
  set G : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 with hGdef
  have hFm : Measurable F :=
    ((((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal).mul
      (measurable_jumpKernel d α)
  have hG0 : ∀ s, G (s, s) = 0 := fun s => by simp [hGdef]
  -- one lattice at a time, then averaged
  have havg : ∀ h : ℝ, 0 < h → latAvg d δ h F ≤ ENNReal.ofReal c * latAvg d δ h G := by
    intro h hh
    unfold latAvg
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (MeasurableSet.univ_pi (fun _ => measurableSet_closedBall))
      (fun Q hQ => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun η => ?_)
    have hA : ∀ u, ‖distort Q u - u‖ ≤ ε * ‖u‖ := fun u => by
      have := norm_distort_sub_le hδ.le hQ u; rwa [hdδ] at this
    exact hlat ε hε0.le hε2 hεs Γ hΓ k hk f h hh (distort Q) hA η
  -- the inequality at scale `h`, with the powers of `h` cancelled
  have hscale : ∀ h : ℝ, 0 < h →
      ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | C₀ * h ≤ ‖p.2 - p.1‖},
        F p ≤ ENNReal.ofReal (c * KU / KL) * ∫⁻ p, G p := by
    intro h hh
    have hx : 0 < h⁻¹ ^ (2 * d) := by positivity
    have h1 := (hlow h hh F hFm).trans ((havg h hh).trans
      (mul_le_mul' le_rfl (hup h hh G hG hG0)))
    have hne0 : ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [← ENNReal.mul_le_mul_iff_right hne0 ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) * ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) | C₀ * h ≤ ‖p.2 - p.1‖}, F p
        ≤ ENNReal.ofReal c * (ENNReal.ofReal (KU * h⁻¹ ^ (2 * d)) * ∫⁻ p, G p) := h1
      _ = ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) * (ENNReal.ofReal (c * KU / KL) * ∫⁻ p, G p) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
  -- let `h → 0`
  set S : ℕ → Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    fun n => {p | C₀ * (1 / ((n : ℝ) + 1)) ≤ ‖p.2 - p.1‖} with hSdef
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const (measurable_snd.sub measurable_fst).norm
  have hSmono : Monotone (fun n => (S n).indicator F) := by
    intro n m hnm
    refine Set.indicator_le_indicator_of_subset (fun p hp => ?_) (fun _ => bot_le)
    simp only [hSdef, Set.mem_ofPred_eq] at hp ⊢
    refine le_trans ?_ hp
    gcongr
  have hpt : ∀ p, F p ≤ ⨆ n, (S n).indicator F p := by
    intro p
    by_cases hp : p.2 = p.1
    · simp [hFdef, hp]
    · have hpos : 0 < ‖p.2 - p.1‖ := norm_sub_pos_iff.mpr hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hpos hC₀)
      refine le_iSup_of_le n (le_of_eq ?_)
      rw [Set.indicator_of_mem]
      simp only [hSdef, Set.mem_ofPred_eq]
      rw [lt_div_iff₀ hC₀] at hn
      linarith
  calc formHs Set.univ α f = ∫⁻ p, F p := by
        simp [formHs, form, hFdef, Measure.restrict_univ]
    _ ≤ ∫⁻ p, ⨆ n, (S n).indicator F p := lintegral_mono hpt
    _ = ⨆ n, ∫⁻ p, (S n).indicator F p :=
        lintegral_iSup (fun n => hFm.indicator (hSm n)) hSmono
    _ ≤ ENNReal.ofReal (c * KU / KL) * ∫⁻ p, G p := by
        refine iSup_le (fun n => ?_)
        rw [lintegral_indicator (hSm n)]
        exact hscale _ (by positivity)
    _ = ENNReal.ofReal (c * KU / KL) * form Set.univ k f := by
        simp [form, hGdef, Measure.restrict_univ]

end QFS
