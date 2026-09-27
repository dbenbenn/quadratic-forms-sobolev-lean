import QuadraticFormsSobolev.RandomLattice.Ball
import QuadraticFormsSobolev.RandomLattice.TheoremOneThreeUniform

/-! # The enlarged-ball comparability with constants uniform in `α ∈ (0, 2)`

As `formHs_ball_le_form_ball_randomLattice`, with `κ, C` chosen before `α`: apply
`theoremOneThree_uniform` with the kernel constant `Λ 2^{d+2} ≥ Λ 2^{d+α}`. -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- `DiscreteKernelBounds` is monotone in the constant. -/
lemma bu_mono {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ₁ Λ₂ R₀ : ℝ}
    {L : Set (EuclideanSpace ℝ (Fin d))}
    {ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (h : DiscreteKernelBounds Γ α Λ₁ R₀ L ω) (hle : Λ₁ ≤ Λ₂) :
    DiscreteKernelBounds Γ α Λ₂ R₀ L ω where
  one_le := h.one_le.trans hle
  symm := h.symm
  lower := fun x hx y hy hxy => le_trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [h.one_le]) hle)) le_rfl)
      (h.lower x hx y hy hxy)
  upper := fun x hx y hy hxy => (h.upper x hx y hy hxy).trans (by gcongr)

/-- `latticeSum_ball_le` with `κ, c` chosen before `α ∈ (0, 2)`. -/
theorem bu_latticeSum_ball_le {ϑ Λ : ℝ} (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 ≤ c ∧ ∀ α : ℝ, 0 < α → α < 2 →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 → ε < Real.sin (ϑ / 2) →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ), 0 < h →
      ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ u, ‖A u - u‖ ≤ ε * ‖u‖) → ∀ η x₀ : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∑' p : (Fin d → ℤ) × (Fin d → ℤ), (ball x₀ R ×ˢ ball x₀ R).indicator
          (fun q => ENNReal.ofReal ((f q.2 - f q.1) ^ 2) * jumpKernel d α q.1 q.2)
          (latMap h A η (latticePt d 1 p.1), latMap h A η (latticePt d 1 p.2))
        ≤ ENNReal.ofReal c * ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
          (ball x₀ (3 * κ * R) ×ˢ ball x₀ (3 * κ * R)).indicator
          (fun q => ENNReal.ofReal ((f q.2 - f q.1) ^ 2) * k q.1 q.2)
          (latMap h A η (latticePt d 1 p.1), latMap h A η (latticePt d 1 p.2)) := by
  classical
  have hΛ' : 1 ≤ Λ * 2 ^ ((d : ℝ) + 2) := by
    nlinarith [Real.one_le_rpow (one_le_two : (1:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (d : ℝ) + 2)]
  obtain ⟨κ, c, hκ, hc, H13⟩ := theoremOneThree_uniform d (ϑ / 2) (Λ * 2 ^ ((d : ℝ) + 2)) (1 / 2)
    (half_pos hϑ) hΛ' (by norm_num)
  refine ⟨κ, c * 2 ^ ((d : ℝ) + 2), hκ, by positivity, ?_⟩
  intro α hα0 hα2 ε hε hε2 hεs Γ hΓ k hk f h hh A hA η x₀ R hR
  have hα : 0 ≤ α := hα0.le
  set s : ℝ := (d : ℝ) + α with hs
  have hs0 : 0 ≤ s := by positivity
  have hs2 : (2 : ℝ) ^ s ≤ 2 ^ ((d : ℝ) + 2) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [hs]; linarith)
  set T := latMap h A η with hT
  set L : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := latticePt d 1 with hL
  set f' : EuclideanSpace ℝ (Fin d) → ℝ := fun x => f (T x) with hf'
  set ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal (h ^ s) * k (T x) (T y) with hω
  have hωb : DiscreteKernelBounds (halfConfig Γ T) α (Λ * 2 ^ ((d : ℝ) + 2)) (1 / 2)
      (lattice d) ω :=
    bu_mono (discreteKernelBounds_pullback hΓ hα hε hε2 hεs hk hh A hA η)
      (mul_le_mul_of_nonneg_left hs2 (by linarith))
  set B := ball x₀ R with hB
  set B' := ball x₀ (3 * κ * R) with hB'
  -- the centre of the discrete ball
  obtain ⟨v, hv⟩ := surjective_of_near (by linarith) A hA (h⁻¹ • x₀)
  set cc : EuclideanSpace ℝ (Fin d) := v - η with hcc
  have hTcc : T cc = x₀ := by
    simp only [hT, latMap, hcc, sub_add_cancel, hv, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  have h1ε : 0 < 1 - ε := by linarith
  have hnorm : ∀ x, ‖T x - x₀‖ = h * ‖A (x - cc)‖ := by
    intro x
    rw [← hTcc, hT, latMap_sub, norm_smul, Real.norm_of_nonneg hh.le]
  set r : ℝ := R / (h * (1 - ε)) with hr
  have hrpos : 0 < r := by positivity
  have hpre : ∀ x, T x ∈ B → x ∈ ball cc r := by
    intro x hx
    rw [hB, mem_ball, dist_eq_norm, hnorm] at hx
    rw [mem_ball, dist_eq_norm, hr, lt_div_iff₀ (by positivity)]
    have := (norm_near_bounds A hA (x - cc)).1
    nlinarith
  have himg : ∀ x, x ∈ ball cc (κ * r) → T x ∈ B' := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [hB', mem_ball, dist_eq_norm, hnorm]
    have hup := (norm_near_bounds A hA (x - cc)).2
    have hκr : κ * r * (h * (1 - ε)) = κ * R := by
      rw [hr]; field_simp
    have h3 : (1 + ε) ≤ 3 * (1 - ε) := by linarith
    have hxc : ‖x - cc‖ * (h * (1 - ε)) < κ * R := by
      rw [← hκr]; exact mul_lt_mul_of_pos_right hx (by positivity)
    calc h * ‖A (x - cc)‖ ≤ h * ((1 + ε) * ‖x - cc‖) := mul_le_mul_of_nonneg_left hup hh.le
      _ ≤ h * (3 * (1 - ε) * ‖x - cc‖) := by gcongr
      _ = 3 * (‖x - cc‖ * (h * (1 - ε))) := by ring
      _ < 3 * (κ * R) := by linarith
      _ = 3 * κ * R := by ring
  set Gs := ∑' p : (Fin d → ℤ) × (Fin d → ℤ), (B' ×ˢ B').indicator
      (fun q => ENNReal.ofReal ((f q.2 - f q.1) ^ 2) * k q.1 q.2) (T (L p.1), T (L p.2)) with hGs
  have hball : discreteForm (ball cc r) (1 / 2) (jumpKernel d α) f'
      ≤ ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs) := by
    calc discreteForm (ball cc r) (1 / 2) (jumpKernel d α) f'
        ≤ ENNReal.ofReal c * discreteForm (ball cc (κ * r)) (1 / 2) ω f' :=
          H13 α hα0 hα2 (halfConfig Γ T) (isBounded_halfConfig hΓ T) ω hωb cc r f' hrpos
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs) := by
          gcongr
          rw [discreteForm_eq_restrict]
          refine (discreteForm_le_tsum _ _ _ _).trans ?_
          rw [hGs, ← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum (fun p => ?_)
          by_cases hm : L p.1 ∈ ball cc (κ * r) ∧ L p.2 ∈ ball cc (κ * r)
          · have hmem : (T (L p.1), T (L p.2)) ∈ B' ×ˢ B' := ⟨himg _ hm.1, himg _ hm.2⟩
            rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hm.1, Set.indicator_of_mem hm.2]
            simp only [hf', hω]
            rw [show (f (T (L p.1)) - f (T (L p.2))) ^ 2 = (f (T (L p.2)) - f (T (L p.1))) ^ 2
              by ring]
            apply le_of_eq; ring
          · have hz : (ball cc (κ * r)).indicator (fun _ => (1 : ℝ≥0∞)) (L p.1) *
                (ball cc (κ * r)).indicator (fun _ => (1 : ℝ≥0∞)) (L p.2) = 0 := by
              rcases not_and_or.mp hm with h1 | h1
              · rw [Set.indicator_of_notMem h1, zero_mul]
              · rw [Set.indicator_of_notMem h1, mul_zero]
            rw [hz, zero_mul, mul_zero]; exact bot_le
  refine tsum_le_of_sum_le' (by positivity) (fun t => ?_)
  set t' := t.filter (fun p => p.1 ≠ p.2 ∧ T (L p.1) ∈ B ∧ T (L p.2) ∈ B) with ht'
  have hzero : ∀ p ∈ t, p ∉ t' → (B ×ˢ B).indicator
      (fun q => ENNReal.ofReal ((f q.2 - f q.1) ^ 2) * jumpKernel d α q.1 q.2)
      (T (L p.1), T (L p.2)) = 0 := by
    intro p hp hnot
    rw [ht', Finset.mem_filter, not_and] at hnot
    have hn := hnot hp
    by_cases hin : (T (L p.1), T (L p.2)) ∈ B ×ˢ B
    · rw [Set.indicator_of_mem hin]
      have heq : p.1 = p.2 := by
        by_contra hne; exact hn ⟨hne, hin.1, hin.2⟩
      rw [heq, sub_self]; simp
    · exact Set.indicator_of_notMem hin _
  rw [← Finset.sum_subset (Finset.filter_subset _ t) hzero]
  have hpow : ENNReal.ofReal ((2 / h) ^ s) * (ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs))
      = ENNReal.ofReal (c * 2 ^ s) * Gs := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow two_pos.le hh.le]
    field_simp
  calc ∑ p ∈ t', (B ×ˢ B).indicator
        (fun q => ENNReal.ofReal ((f q.2 - f q.1) ^ 2) * jumpKernel d α q.1 q.2)
        (T (L p.1), T (L p.2))
      ≤ ∑ p ∈ t', ENNReal.ofReal ((2 / h) ^ s) *
          (ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (L p.1) (L p.2)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [ht', Finset.mem_filter] at hp
        obtain ⟨-, hne, hb1, hb2⟩ := hp
        rw [Set.indicator_of_mem (show (T (L p.1), T (L p.2)) ∈ B ×ˢ B from ⟨hb1, hb2⟩)]
        have hne' : L p.1 ≠ L p.2 := fun he => hne (latticePt_injective one_ne_zero he)
        rw [show (f (T (L p.2)) - f (T (L p.1))) ^ 2 = (f' (L p.1) - f' (L p.2)) ^ 2 by
          simp only [hf']; ring]
        calc ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (T (L p.1)) (T (L p.2))
            ≤ ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) *
                (ENNReal.ofReal ((2 / h) ^ s) * jumpKernel d α (L p.1) (L p.2)) := by
              gcongr; exact jumpKernel_latMap_le hα hε2 hh A hA η hne'
          _ = _ := by ring
    _ = ENNReal.ofReal ((2 / h) ^ s) * ∑ p ∈ t',
          ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (L p.1) (L p.2) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((2 / h) ^ s) * discreteForm (ball cc r) (1 / 2) (jumpKernel d α) f' := by
        gcongr
        refine sum_le_discreteForm_ball t' cc (fun p hp => ?_) (fun p hp => ?_) _ f'
        · exact (Finset.mem_filter.mp hp).2.1
        · obtain ⟨-, -, hb1, hb2⟩ := Finset.mem_filter.mp hp
          exact ⟨hpre _ hb1, hpre _ hb2⟩
    _ ≤ ENNReal.ofReal ((2 / h) ^ s) * (ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs)) := by
        gcongr
    _ = ENNReal.ofReal (c * 2 ^ s) * Gs := hpow
    _ ≤ ENNReal.ofReal (c * 2 ^ ((d : ℝ) + 2)) * Gs := by
        gcongr

theorem formHs_ball_le_form_ball_uniform (hd : 1 ≤ d) {ϑ Λ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) :
    ∃ κ C : ℝ, 1 ≤ κ ∧ 0 ≤ C ∧ ∀ α : ℝ, 0 < α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      formHs (ball x₀ R) α f ≤ ENNReal.ofReal C * form (ball x₀ (κ * R)) k f := by
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
  obtain ⟨κ, c, hκ, hc, hlat⟩ := bu_latticeSum_ball_le (d := d) hϑ hΛ
  obtain ⟨K, hK, havg⟩ := lintegral_le_of_latticeSum_le hd hδ hδ'
  refine ⟨3 * κ, c * K, by linarith, by positivity, ?_⟩
  intro α hα0 hα2 Γ hΓ k hk f hf hG x₀ R hR
  set F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 with hFdef
  set G : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 with hGdef
  have hFm : Measurable F :=
    ((((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal).mul
      (measurable_jumpKernel d α)
  set B := ball x₀ R with hB
  set B' := ball x₀ (3 * κ * R) with hB'
  have hBm : MeasurableSet (B ×ˢ B) := measurableSet_ball.prod measurableSet_ball
  have hB'm : MeasurableSet (B' ×ˢ B') := measurableSet_ball.prod measurableSet_ball
  have hdiag : ∀ (S : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
      (H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      (∀ s, H (s, s) = 0) → ∀ s, S.indicator H (s, s) = 0 := by
    intro S H hH s
    by_cases hs : (s, s) ∈ S
    · rw [Set.indicator_of_mem hs, hH]
    · exact Set.indicator_of_notMem hs _
  have key := havg c hc ((B ×ˢ B).indicator F) ((B' ×ˢ B').indicator G) (hFm.indicator hBm)
    (hG.indicator hB'm) (hdiag _ F (fun s => by simp [hFdef]))
    (hdiag _ G (fun s => by simp [hGdef])) (fun h hh Q hQ η => by
      have hA : ∀ u, ‖distort Q u - u‖ ≤ ε * ‖u‖ := fun u => by
        have := norm_distort_sub_le hδ.le hQ u; rwa [hdδ] at this
      exact hlat α hα0 hα2 ε hε0.le hε2 hεs Γ hΓ k hk f h hh (distort Q) hA η x₀ R hR)
  rw [lintegral_indicator hBm, lintegral_indicator hB'm] at key
  calc formHs (ball x₀ R) α f = ∫⁻ p in B ×ˢ B, F p := rfl
    _ ≤ ENNReal.ofReal (c * K) * ∫⁻ p in B' ×ˢ B', G p := key
    _ = ENNReal.ofReal (c * K) * form (ball x₀ (3 * κ * R)) k f := rfl

end QFS
