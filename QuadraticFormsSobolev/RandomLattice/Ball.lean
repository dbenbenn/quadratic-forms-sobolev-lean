import QuadraticFormsSobolev.RandomLattice.Main

/-!
# Random lattice sampling on balls: Lemma 3.7's enlarged-ball form in every dimension

The same argument as `Main.lean`, localised: sampling `f` on a random lattice and applying
Theorem 1.3 on the discrete ball about the preimage of the centre gives

  `|f|²_{H^{α/2}(B_R(x₀))} ≤ C |f|²_{H_k(B_{κR}(x₀))}`

with `κ, C` depending only on `d, ϑ, Λ, α`, for every measurable `f`, every `α ≥ 0` and every
`d ≥ 1`. This is the input `formHs_le_form_of_ballComparability` (Lemma A.1 for a ball) consumes,
without §3.2's a priori hypothesis, without condition (M) and without `d ≥ 2` or `α < 2`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- **Averaging, abstractly.** If on every lattice the sampled sum of `H₁` is at most `c` times
that of `H₂`, then `∫∫ H₁ ≤ C ∫∫ H₂` with `C` depending only on `c`, `d` and `δ`. -/
theorem lintegral_le_of_latticeSum_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : (d : ℝ) * δ ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ H₁ H₂ : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable H₁ → Measurable H₂ → (∀ s, H₁ (s, s) = 0) → (∀ s, H₂ (s, s) = 0) →
      (∀ h : ℝ, 0 < h → ∀ Q ∈ colBox d δ, ∀ η : EuclideanSpace ℝ (Fin d),
        ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H₁ (samplePt h Q η p.1, samplePt h Q η p.2)
          ≤ ENNReal.ofReal c *
            ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H₂ (samplePt h Q η p.1, samplePt h Q η p.2)) →
      ∫⁻ p, H₁ p ≤ ENNReal.ofReal (c * K) * ∫⁻ p, H₂ p := by
  obtain ⟨KU, hKU, hup⟩ := latAvg_le hd hδ hδ'
  obtain ⟨KL, C₀, hKL, hC₀, hlow⟩ := le_latAvg hd hδ hδ'
  refine ⟨KU / KL, by positivity, ?_⟩
  intro c hc H₁ H₂ hH₁ hH₂ h₁0 h₂0 hlat
  have havg : ∀ h : ℝ, 0 < h → latAvg d δ h H₁ ≤ ENNReal.ofReal c * latAvg d δ h H₂ := by
    intro h hh
    unfold latAvg
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (MeasurableSet.univ_pi (fun _ => measurableSet_closedBall))
      (fun Q hQ => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono (fun η => hlat h hh Q hQ η)
  have hscale : ∀ h : ℝ, 0 < h →
      ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) | C₀ * h ≤ ‖p.2 - p.1‖},
        H₁ p ≤ ENNReal.ofReal (c * (KU / KL)) * ∫⁻ p, H₂ p := by
    intro h hh
    have h1 := (hlow h hh H₁ hH₁).trans ((havg h hh).trans
      (mul_le_mul' le_rfl (hup h hh H₂ hH₂ h₂0)))
    have hne0 : ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [← ENNReal.mul_le_mul_iff_right hne0 ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) * ∫⁻ p in {p : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) | C₀ * h ≤ ‖p.2 - p.1‖}, H₁ p
        ≤ ENNReal.ofReal c * (ENNReal.ofReal (KU * h⁻¹ ^ (2 * d)) * ∫⁻ p, H₂ p) := h1
      _ = ENNReal.ofReal (KL * h⁻¹ ^ (2 * d)) *
            (ENNReal.ofReal (c * (KU / KL)) * ∫⁻ p, H₂ p) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
  set S : ℕ → Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    fun n => {p | C₀ * (1 / ((n : ℝ) + 1)) ≤ ‖p.2 - p.1‖} with hSdef
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const (measurable_snd.sub measurable_fst).norm
  have hSmono : Monotone (fun n => (S n).indicator H₁) := by
    intro n m hnm
    refine Set.indicator_le_indicator_of_subset (fun p hp => ?_) (fun _ => bot_le)
    simp only [hSdef, Set.mem_ofPred_eq] at hp ⊢
    refine le_trans ?_ hp
    gcongr
  have hpt : ∀ p, H₁ p ≤ ⨆ n, (S n).indicator H₁ p := by
    intro p
    by_cases hp : p.2 = p.1
    · have : p = (p.1, p.1) := Prod.ext rfl hp
      rw [this, h₁0]; exact bot_le
    · have hpos : 0 < ‖p.2 - p.1‖ := norm_sub_pos_iff.mpr hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hpos hC₀)
      refine le_iSup_of_le n (le_of_eq ?_)
      rw [Set.indicator_of_mem]
      simp only [hSdef, Set.mem_ofPred_eq]
      rw [lt_div_iff₀ hC₀] at hn
      linarith
  calc ∫⁻ p, H₁ p ≤ ∫⁻ p, ⨆ n, (S n).indicator H₁ p := lintegral_mono hpt
    _ = ⨆ n, ∫⁻ p, (S n).indicator H₁ p :=
        lintegral_iSup (fun n => hH₁.indicator (hSm n)) hSmono
    _ ≤ ENNReal.ofReal (c * (KU / KL)) * ∫⁻ p, H₂ p := by
        refine iSup_le (fun n => ?_)
        rw [lintegral_indicator (hSm n)]
        exact hscale _ (by positivity)

/-- A map within `ε < 1` of the identity is surjective. -/
lemma surjective_of_near {ε : ℝ} (hε : ε < 1)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : ∀ u, ‖A u - u‖ ≤ ε * ‖u‖) : Function.Surjective A := by
  have hinj : Function.Injective (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    intro u v huv
    have huv' : A u = A v := huv
    have h1 := (norm_near_bounds A hA (u - v)).1
    rw [map_sub, huv', sub_self, norm_zero] at h1
    have h2 : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have := LinearMap.injective_iff_surjective.mp hinj
  exact this

/-- A discrete form reads its kernel only on `S × S`. -/
lemma discreteForm_eq_restrict (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteForm S R₀ ω f = discreteForm S R₀ (fun x y =>
      S.indicator (fun _ => (1 : ℝ≥0∞)) x * S.indicator (fun _ => (1 : ℝ≥0∞)) y * ω x y) f := by
  unfold discreteForm
  refine tsum_congr (fun p => ?_)
  dsimp only
  rw [Set.indicator_of_mem p.2.1.1, Set.indicator_of_mem p.2.2.1.1, one_mul, one_mul]

/-- A finite sum over pairs of distinct integer vectors whose lattice points lie in a ball is
bounded by the discrete form of that ball. -/
lemma sum_le_discreteForm_ball (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hne : ∀ p ∈ s, p.1 ≠ p.2)
    (hR : ∀ p ∈ s, latticePt d 1 p.1 ∈ ball x₀ R ∧ latticePt d 1 p.2 ∈ ball x₀ R)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∑ p ∈ s, ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
          ω (latticePt d 1 p.1) (latticePt d 1 p.2)
      ≤ discreteForm (ball x₀ R) (1 / 2) ω f := by
  classical
  set X := {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ ball x₀ R ∩ lattice d ∧ p.2 ∈ ball x₀ R ∩ lattice d ∧ 1 / 2 < ‖p.1 - p.2‖}
  have hmem : ∀ p ∈ s, (latticePt d 1 p.1, latticePt d 1 p.2) ∈ {q :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      q.1 ∈ ball x₀ R ∩ lattice d ∧ q.2 ∈ ball x₀ R ∩ lattice d ∧ 1 / 2 < ‖q.1 - q.2‖} := by
    intro p hp
    obtain ⟨h1, h2⟩ := hR p hp
    refine ⟨⟨h1, latticePt_mem_scaledLattice 1 p.1⟩, ⟨h2, latticePt_mem_scaledLattice 1 p.2⟩, ?_⟩
    have := one_le_norm_latticePt_sub (hne p hp)
    show (1 : ℝ) / 2 < ‖latticePt d 1 p.1 - latticePt d 1 p.2‖
    linarith
  let ι : s → X := fun p => ⟨(latticePt d 1 p.1.1, latticePt d 1 p.1.2), hmem p.1 p.2⟩
  have hinj : Function.Injective ι := by
    intro p q hpq
    have := congrArg Subtype.val hpq
    simp only [ι, Prod.mk.injEq] at this
    apply Subtype.ext
    exact Prod.ext (latticePt_injective one_ne_zero this.1)
      (latticePt_injective one_ne_zero this.2)
  set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal ((f x.1.1 - f x.1.2) ^ 2) * ω x.1.1 x.1.2
  calc ∑ p ∈ s, ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
          ω (latticePt d 1 p.1) (latticePt d 1 p.2)
      = ∑' p : s, g (ι p) := by
        rw [Finset.tsum_subtype s (fun p => ENNReal.ofReal ((f (latticePt d 1 p.1) -
          f (latticePt d 1 p.2)) ^ 2) * ω (latticePt d 1 p.1) (latticePt d 1 p.2))]
    _ ≤ ∑' x : X, g x := ENNReal.tsum_comp_le_tsum_of_injective hinj g
    _ = discreteForm (ball x₀ R) (1 / 2) ω f := rfl

/-- **The inequality for one lattice, on balls.** Sampled on the lattice `T n = h A (n + η)`,
the `H^{α/2}` integrand over pairs in `B_R(x₀)` is at most `c` times the `H_k` integrand over
pairs in `B_{3κR}(x₀)`, with `κ, c` depending only on `d, ϑ, Λ, α`. -/
theorem latticeSum_ball_le {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 ≤ α) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 ≤ c ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 → ε < Real.sin (ϑ / 2) →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexLowerBound Γ ϑ →
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
  set s : ℝ := (d : ℝ) + α with hs
  have hs0 : 0 ≤ s := by positivity
  have hΛ' : 1 ≤ Λ * 2 ^ s := by nlinarith [Real.one_le_rpow (one_le_two : (1:ℝ) ≤ 2) hs0]
  obtain ⟨κ, c, hκ, hc, H13⟩ := theoremOneThree_of_nonneg (d := d) (ϑ / 2) (Λ * 2 ^ s) α (1 / 2)
    (half_pos hϑ) hΛ' hα (by norm_num)
  refine ⟨κ, c * 2 ^ s, hκ, by positivity, ?_⟩
  intro ε hε hε2 hεs Γ hΓ k hk f h hh A hA η x₀ R hR
  set T := latMap h A η with hT
  set L : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := latticePt d 1 with hL
  set f' : EuclideanSpace ℝ (Fin d) → ℝ := fun x => f (T x) with hf'
  set ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal (h ^ s) * k (T x) (T y) with hω
  have hωb : DiscreteKernelBounds (halfConfig Γ T) α (Λ * 2 ^ s) (1 / 2) (lattice d) ω :=
    discreteKernelBounds_pullback hΓ hα hε hε2 hεs hk hh A hA η
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
          H13 (halfConfig Γ T) (apexLowerBound_halfConfig hΓ T) ω hωb cc r f' hrpos
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

/-- **Lemma 3.7's enlarged-ball form, in every dimension.** There are `κ ≥ 1` and `C ≥ 0`,
depending only on `d, ϑ, Λ, α`, with `|f|²_{H^{α/2}(B_R(x₀))} ≤ C |f|²_{H_k(B_{κR}(x₀))}` for every
`ϑ`-bounded configuration, every kernel with the bounds (2), every measurable `f` whose `H_k`
integrand is measurable, and every ball. No condition (M), no finiteness assumption, any
`α ≥ 0`. -/
theorem formHs_ball_le_form_ball_randomLattice (hd : 1 ≤ d) {ϑ Λ α : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) (hα : 0 ≤ α) :
    ∃ κ C : ℝ, 1 ≤ κ ∧ 0 ≤ C ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexLowerBound Γ ϑ →
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
  obtain ⟨κ, c, hκ, hc, hlat⟩ := latticeSum_ball_le (d := d) hϑ hΛ hα
  obtain ⟨K, hK, havg⟩ := lintegral_le_of_latticeSum_le hd hδ hδ'
  refine ⟨3 * κ, c * K, by linarith, by positivity, ?_⟩
  intro Γ hΓ k hk f hf hG x₀ R hR
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
      exact hlat ε hε0.le hε2 hεs Γ hΓ k hk f h hh (distort Q) hA η x₀ R hR)
  rw [lintegral_indicator hBm, lintegral_indicator hB'm] at key
  calc formHs (ball x₀ R) α f = ∫⁻ p in B ×ˢ B, F p := rfl
    _ ≤ ENNReal.ofReal (c * K) * ∫⁻ p in B' ×ˢ B', G p := key
    _ = ENNReal.ofReal (c * K) * form (ball x₀ (3 * κ * R)) k f := rfl

end QFS
