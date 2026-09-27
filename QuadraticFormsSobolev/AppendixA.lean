import QuadraticFormsSobolev.Section3Kernel
import QuadraticFormsSobolev.LebesgueDiff
import QuadraticFormsSobolev.Section1
import QuadraticFormsSobolev.Rescaling

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace QFS

variable {d : ℕ}

/-! ## The finite-overlap step of Lemma A.1

Lemma A.1's proof runs the chain (18). Its first inequality is the only step
carried out in the paper rather than quoted: if the enlarged Whitney balls `B*`
lie in `Ω` and no point lies in more than `M` of them, the sum of the forms over
the `B*` is controlled by the form over `Ω`. -/

/-- **Finite overlap.** If each `S i` lies in `Ω` and no point of `ℝ^d` lies in
more than `M` of the `S i`, then `∑ᵢ ∫_{Sᵢ×Sᵢ} F ≤ M ∫_{Ω×Ω} F`.

The paper's display (18) uses the factor `M²`; `M` already suffices, since a
pair `(x,y)` lies in `Sᵢ × Sᵢ` only for those `i` with `x ∈ Sᵢ`, of which there
are at most `M`. -/
theorem tsum_setLIntegral_le_of_overlap {ι : Type} [Countable ι]
    {S : ι → Set (EuclideanSpace ℝ (Fin d))} {Ω : Set (EuclideanSpace ℝ (Fin d))} {M : ℕ}
    (hSm : ∀ i, MeasurableSet (S i)) (hΩ : MeasurableSet Ω) (hsub : ∀ i, S i ⊆ Ω)
    (hM : ∀ x, {i | x ∈ S i}.encard ≤ (M : ℕ∞))
    {F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hF : Measurable F) :
    ∑' i, ∫⁻ p in S i ×ˢ S i, F p ≤ (M : ℝ≥0∞) * ∫⁻ p in Ω ×ˢ Ω, F p := by
  have hprodm : ∀ i, MeasurableSet (S i ×ˢ S i) := fun i => (hSm i).prod (hSm i)
  -- rewrite each set integral as an integral of an indicator, and exchange
  have hswap : ∑' i, ∫⁻ p in S i ×ˢ S i, F p
      = ∫⁻ p, ∑' i, (S i ×ˢ S i).indicator F p := by
    rw [lintegral_tsum (fun i => ((hF.indicator (hprodm i)).aemeasurable))]
    exact tsum_congr fun i => (lintegral_indicator (hprodm i) _).symm
  -- the pointwise bound
  have hpt : ∀ p, ∑' i, (S i ×ˢ S i).indicator F p ≤ (M : ℝ≥0∞) * (Ω ×ˢ Ω).indicator F p := by
    intro p
    set T : Set ι := {i | p ∈ S i ×ˢ S i} with hT
    have hTsub : T ⊆ {i | p.1 ∈ S i} := fun i hi => hi.1
    have hTcard : T.encard ≤ (M : ℕ∞) := le_trans (Set.encard_mono hTsub) (hM p.1)
    have hsupp : Function.support (fun i => (S i ×ˢ S i).indicator F p) ⊆ T := by
      intro i hi
      by_contra hiT
      have hp : p ∉ S i ×ˢ S i := hiT
      exact hi (Set.indicator_of_notMem hp F)
    have hval : ∀ i : T, (S i.1 ×ˢ S i.1).indicator F p = F p := by
      rintro ⟨i, hi⟩
      have hp : p ∈ S i ×ˢ S i := hi
      exact Set.indicator_of_mem hp F
    have hsum : ∑' i, (S i ×ˢ S i).indicator F p = (T.encard : ℝ≥0∞) * F p := by
      rw [← tsum_subtype_eq_of_support_subset hsupp, tsum_congr hval,
        ENNReal.tsum_set_const]
    rcases Set.eq_empty_or_nonempty T with hTe | ⟨i₀, hi₀⟩
    · simp [hsum, hTe]
    · have hpΩ : p ∈ Ω ×ˢ Ω := ⟨hsub i₀ hi₀.1, hsub i₀ hi₀.2⟩
      rw [hsum, Set.indicator_of_mem hpΩ F]
      exact mul_le_mul' (by exact_mod_cast hTcard) le_rfl
  calc ∑' i, ∫⁻ p in S i ×ˢ S i, F p
      = ∫⁻ p, ∑' i, (S i ×ˢ S i).indicator F p := hswap
    _ ≤ ∫⁻ p, (M : ℝ≥0∞) * (Ω ×ˢ Ω).indicator F p := lintegral_mono hpt
    _ = (M : ℝ≥0∞) * ∫⁻ p in Ω ×ˢ Ω, F p := by
        rw [lintegral_const_mul _ (hF.indicator (hΩ.prod hΩ)), lintegral_indicator (hΩ.prod hΩ)]

/-- **The chain (18) of Lemma A.1**, the one part of that lemma the paper
carries out rather than quotes.

The two quoted inputs appear as hypotheses: `hsub` and `hM` are properties (ii)
and (iii) of the Whitney family, and `hdyda` is inequality (13) of [Dyda06].
`hball` is the comparability on balls that Lemma A.1 assumes. The conclusion is
the comparability on `Ω`, with the constant `c·c'/M` that (18) produces. -/
theorem lemma_ball_to_domain {ι : Type} [Countable ι]
    {S S' : ι → Set (EuclideanSpace ℝ (Fin d))} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {M : ℕ} {α c c' : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hS'm : ∀ i, MeasurableSet (S' i)) (hΩ : MeasurableSet Ω)
    (hsub : ∀ i, S' i ⊆ Ω)
    (hM : ∀ x, {i | x ∈ S' i}.encard ≤ (M : ℕ∞))
    (hF : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (hball : ∀ i, ENNReal.ofReal c * formHs (S i) α f ≤ form (S' i) k f)
    (hdyda : ENNReal.ofReal c' * formHs Ω α f ≤ ∑' i, formHs (S i) α f) :
    ENNReal.ofReal c * (ENNReal.ofReal c' * formHs Ω α f) ≤ (M : ℝ≥0∞) * form Ω k f := by
  calc ENNReal.ofReal c * (ENNReal.ofReal c' * formHs Ω α f)
      ≤ ENNReal.ofReal c * ∑' i, formHs (S i) α f := mul_le_mul' le_rfl hdyda
    _ = ∑' i, ENNReal.ofReal c * formHs (S i) α f := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i, form (S' i) k f := ENNReal.tsum_le_tsum hball
    _ ≤ (M : ℝ≥0∞) * form Ω k f :=
        tsum_setLIntegral_le_of_overlap hS'm hΩ hsub hM hF

/-! ## Lemma A.1 given the quoted input

Section 3.2 ends by applying Lemma A.1 with `Ω = B` a ball, turning the enlarged-ball comparability
`|f|_{H^{α/2}(B)} ≲ |f|_{H_k(B*)}` into the same-ball one. Here that step is proved for a ball and
for a domain, with the Whitney family and Dyda's inequality (13) as hypotheses, as the paper quotes
them. For balls, `lemma_A_1` in `Paper.lean` needs neither. -/

/-- The input Lemma A.1 quotes, specialised to `Ω` a ball: a countable Whitney
family whose `κ`-enlargements lie inside the ball and overlap at most
`overlapBound` times, together with the constant of Dyda's inequality (13). The
paper proves none of this — the family is produced by "the Whitney decomposition
technique" and the inequality is quoted from [Dyda06] — so it is carried as data
rather than derived. -/
structure WhitneyBallData (d : ℕ) (α κ : ℝ) where
  /-- The index set of the family; a Whitney family is countable. -/
  idx : Type
  /-- Countability of the index set. -/
  countable : Countable idx
  /-- The bound `M` of the finite-overlap property (iii). -/
  overlapBound : ℕ
  /-- A nonempty family overlaps at least once. -/
  overlapBound_pos : 0 < overlapBound
  /-- The constant of Dyda's inequality (13). -/
  dydaConst : ℝ
  /-- Dyda's constant is positive. -/
  dydaConst_pos : 0 < dydaConst
  /-- The centres of the Whitney balls for the ball `B_R(x₀)`. -/
  ctr : EuclideanSpace ℝ (Fin d) → ℝ → idx → EuclideanSpace ℝ (Fin d)
  /-- The radii of the Whitney balls for the ball `B_R(x₀)`. -/
  rad : EuclideanSpace ℝ (Fin d) → ℝ → idx → ℝ
  /-- Property (ii): the enlarged balls stay inside `Ω`. -/
  enlarged_subset : ∀ x₀ R, 0 < R → ∀ i,
    ball (ctr x₀ R i) (κ * rad x₀ R i) ⊆ ball x₀ R
  /-- Property (iii): the enlarged balls overlap at most `overlapBound` times. -/
  overlap : ∀ x₀ R, 0 < R → ∀ y,
    {i | y ∈ ball (ctr x₀ R i) (κ * rad x₀ R i)}.encard ≤ (overlapBound : ℕ∞)
  /-- Inequality (13) of [Dyda06], as used in the last step of (18). -/
  dyda : ∀ x₀ R, 0 < R → ∀ f, ENNReal.ofReal dydaConst * formHs (ball x₀ R) α f
    ≤ ∑' i, formHs (ball (ctr x₀ R i) (rad x₀ R i)) α f

/-- **The chain (18) for a single ball**, taking the enlarged-ball
comparability as an input for one fixed kernel and one fixed function.

This is the content of the passage from `B*` to `B`.

The measurability hypothesis on the integrand is where the paper's assumption
that `k` be measurable — which `QFS.KernelBounds` drops, see Deviation 20 — is
actually needed: without it the family of integrals over the Whitney balls
cannot be summed. -/
theorem formHs_le_form_of_ballComparability {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    (W : WhitneyBallData d α κ)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0 < R)
    (hf : MemLp f 2 (volume.restrict (ball x₀ R)))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
      ≤ form (ball x₀ R) k f := by
  have hcount := W.countable
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  have hM0 : W.overlapBound ≠ 0 := by have := W.overlapBound_pos; omega
  have hMne : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ 0 := by simpa using hM0
  have hMtop : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  -- the enlarged-ball comparability, renormalised so the constant sits on the left
  have hball : ∀ i, ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr x₀ R i) (W.rad x₀ R i)) α f
      ≤ form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f := by
    intro i
    by_cases hri : 0 < W.rad x₀ R i
    · have h2 := H (W.ctr x₀ R i) (W.rad x₀ R i) hri
        (hf.mono_measure (Measure.restrict_mono (W.enlarged_subset x₀ R hR i) le_rfl))
      calc ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr x₀ R i) (W.rad x₀ R i)) α f
          ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ *
              form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f) := mul_le_mul' le_rfl h2
        _ = form (ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) k f := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
              inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
    · have hempty : ball (W.ctr x₀ R i) (W.rad x₀ R i) = ∅ :=
        ball_eq_empty.mpr (not_lt.mp hri)
      simp [formHs, form, hempty]
  -- the chain (18)
  have hchain := lemma_ball_to_domain (S := fun i => ball (W.ctr x₀ R i) (W.rad x₀ R i))
    (S' := fun i => ball (W.ctr x₀ R i) (κ * W.rad x₀ R i)) (Ω := ball x₀ R)
    (M := W.overlapBound) (α := α) (c := c₀⁻¹) (c' := W.dydaConst) (k := k) (f := f)
    (fun i => measurableSet_ball) measurableSet_ball
    (W.enlarged_subset x₀ R hR) (W.overlap x₀ R hR) hFmeas hball (W.dyda x₀ R hR f)
  -- divide by the overlap bound
  have hdiv := mul_le_mul' (le_refl (((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹)) hchain
  have hRHS : ((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹ *
      (((W.overlapBound : ℕ) : ℝ≥0∞) * form (ball x₀ R) k f) = form (ball x₀ R) k f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hMne hMtop, one_mul]
  rw [hRHS] at hdiv
  refine le_trans (le_of_eq ?_) hdiv
  rw [ENNReal.ofReal_div_of_pos hMR, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  ring

/-! ## Lemma A.1 for a domain

`lemma_ball_to_domain` is the chain (18) for an arbitrary `Ω`; combining it
with the comparability on balls gives the comparability on `Ω`, which is what
Theorem 1.4 uses for a bounded Lipschitz domain. The Whitney family and Dyda's
inequality are hypotheses, exactly as in the paper. -/

/-- The Whitney family of a domain, and Dyda's inequality for it: the input
Lemma A.1 quotes rather than proves, for a general `Ω` rather than for a ball.
Compare `QFS.WhitneyBallData`. -/
structure WhitneyDomainData (d : ℕ) (α κ : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  /-- The index set of the family. -/
  idx : Type
  /-- The family is countable. -/
  countable : Countable idx
  /-- The overlap bound `M` of property (iii). -/
  overlapBound : ℕ
  /-- The overlap bound is positive. -/
  overlapBound_pos : 0 < overlapBound
  /-- The constant of Dyda's inequality (13). -/
  dydaConst : ℝ
  /-- Dyda's constant is positive. -/
  dydaConst_pos : 0 < dydaConst
  /-- The centres of the Whitney balls. -/
  ctr : idx → EuclideanSpace ℝ (Fin d)
  /-- The radii of the Whitney balls. -/
  rad : idx → ℝ
  /-- Property (ii): the enlarged balls stay inside `Ω`. -/
  enlarged_subset : ∀ i, ball (ctr i) (κ * rad i) ⊆ Ω
  /-- Property (iii): the enlarged balls overlap at most `overlapBound` times. -/
  overlap : ∀ y, {i | y ∈ ball (ctr i) (κ * rad i)}.encard ≤ (overlapBound : ℕ∞)
  /-- Inequality (13) of [Dyda06]. -/
  dyda : ∀ f, ENNReal.ofReal dydaConst * formHs Ω α f
    ≤ ∑' i, formHs (ball (ctr i) (rad i)) α f

/-- **Lemma A.1 for a domain**: the enlarged-ball comparability, a Whitney
family for `Ω` and Dyda's inequality give the comparability on `Ω`. -/
theorem formHs_le_form_domain {Ω : Set (EuclideanSpace ℝ (Fin d))} {α κ c₀ : ℝ}
    (hc₀ : 1 ≤ c₀) (hΩ : MeasurableSet Ω) (W : WhitneyDomainData d α κ Ω)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
      ≤ form Ω k f := by
  have hcount := W.countable
  have hc₀pos : (0 : ℝ) < c₀ := lt_of_lt_of_le zero_lt_one hc₀
  have hMR : (0 : ℝ) < (W.overlapBound : ℝ) := by exact_mod_cast W.overlapBound_pos
  have hMne : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : W.overlapBound ≠ 0 := by have := W.overlapBound_pos; omega
    simpa using this
  have hMtop : ((W.overlapBound : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hball : ∀ i, ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr i) (W.rad i)) α f
      ≤ form (ball (W.ctr i) (κ * W.rad i)) k f := by
    intro i
    by_cases hri : 0 < W.rad i
    · have h2 := H (W.ctr i) (W.rad i) hri
        (hf.mono_measure (Measure.restrict_mono (W.enlarged_subset i) le_rfl))
      calc ENNReal.ofReal c₀⁻¹ * formHs (ball (W.ctr i) (W.rad i)) α f
          ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal c₀ *
              form (ball (W.ctr i) (κ * W.rad i)) k f) := mul_le_mul' le_rfl h2
        _ = form (ball (W.ctr i) (κ * W.rad i)) k f := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
              inv_mul_cancel₀ (ne_of_gt hc₀pos), ENNReal.ofReal_one, one_mul]
    · have hempty : ball (W.ctr i) (W.rad i) = ∅ := ball_eq_empty.mpr (not_lt.mp hri)
      simp [formHs, form, hempty]
  have hchain := lemma_ball_to_domain (S := fun i => ball (W.ctr i) (W.rad i))
    (S' := fun i => ball (W.ctr i) (κ * W.rad i)) (Ω := Ω) (M := W.overlapBound) (α := α)
    (c := c₀⁻¹) (c' := W.dydaConst) (k := k) (f := f)
    (fun i => measurableSet_ball) hΩ W.enlarged_subset W.overlap hFmeas hball (W.dyda f)
  have hdiv := mul_le_mul' (le_refl (((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹)) hchain
  have hRHS : ((W.overlapBound : ℕ) : ℝ≥0∞)⁻¹ *
      (((W.overlapBound : ℕ) : ℝ≥0∞) * form Ω k f) = form Ω k f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hMne hMtop, one_mul]
  rw [hRHS] at hdiv
  refine le_trans (le_of_eq ?_) hdiv
  rw [ENNReal.ofReal_div_of_pos hMR, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc₀pos)),
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  ring

/-! ## The constant depends on the domain only up to scaling -/

private lemma haar_prod :
    (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))).IsAddHaarMeasure := by
  rw [show (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
        = (volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume from rfl]
  infer_instance

private lemma map_vol {a : ℝ} (ha : 0 < a) :
    Measure.map (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) volume
      = ENNReal.ofReal ((a ^ (2*d))⁻¹) • volume := by
  haveI := haar_prod (d := d)
  rw [Measure.map_addHaar_smul volume ha.ne']
  congr 2
  · rw [abs_of_nonneg (by positivity)]
    congr 2
    simp [Module.finrank_prod, two_mul]

/-- the image of a product under the diagonal scaling -/
private lemma prod_image_smul (a : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    ((a • ·) '' Ω) ×ˢ ((a • ·) '' Ω)
      = (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' (Ω ×ˢ Ω) := by
  rw [Set.prod_image_image_eq]
  rfl

noncomputable def smulEquivProd {a : ℝ} (ha : a ≠ 0) :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ≃ᵐ
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  (Homeomorph.smulOfNeZero a ha).toMeasurableEquiv

@[simp] lemma smulEquivProd_apply {a : ℝ} (ha : a ≠ 0) (p) :
    smulEquivProd (d := d) ha p = a • p := rfl

lemma setLIntegral_image_smul {a : ℝ} (ha : 0 < a)
    (A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ p in (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' A, F p
      = ENNReal.ofReal (a ^ (2*d)) * ∫⁻ q in A, F (a • q) := by
  set e := smulEquivProd (d := d) ha.ne' with he
  have hmap : Measure.map (⇑e) volume = ENNReal.ofReal ((a ^ (2*d))⁻¹) • volume := map_vol ha
  have hpow : (0:ℝ) < a ^ (2*d) := by positivity
  have hcancel : ENNReal.ofReal (a ^ (2*d)) * ENNReal.ofReal ((a ^ (2*d))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hpow.le, mul_inv_cancel₀ hpow.ne', ENNReal.ofReal_one]
  have himg : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => a • p) '' A
      = ⇑e '' A := rfl
  have hres : volume.restrict (⇑e '' A)
      = ENNReal.ofReal (a ^ (2*d)) • Measure.map (⇑e) (volume.restrict A) := by
    refine Measure.ext fun s hs => ?_
    have h1 : (volume.restrict (⇑e '' A)) s = volume (s ∩ ⇑e '' A) :=
      Measure.restrict_apply hs
    have h2 : (Measure.map (⇑e) (volume.restrict A)) s = volume (⇑e ⁻¹' s ∩ A) := by
      rw [MeasurableEquiv.map_apply, Measure.restrict_apply (e.measurable hs)]
    have h3 : volume (⇑e ⁻¹' s ∩ A) = ENNReal.ofReal ((a ^ (2*d))⁻¹) * volume (s ∩ ⇑e '' A) := by
      have := congrArg (fun μ : Measure _ => μ (s ∩ ⇑e '' A)) hmap
      simp only [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul] at this
      rw [← this]
      congr 1
      rw [Set.preimage_inter, e.preimage_image]
    rw [Measure.smul_apply, smul_eq_mul, h1, h2, h3, ← mul_assoc, hcancel, one_mul]
  rw [himg]
  show ∫⁻ p, F p ∂(volume.restrict (⇑e '' A)) = _
  rw [hres, lintegral_smul_measure, lintegral_map_equiv]
  rfl

/-- **The Gagliardo seminorm scales.** Dilating the domain by `a > 0` multiplies
`|·|²_{H^{α/2}}` by `a^{d-α}`, once the function is precomposed with the dilation. -/
theorem formHs_smul {a : ℝ} (ha : 0 < a) (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    formHs ((a • ·) '' Ω) α f
      = ENNReal.ofReal (a ^ ((d : ℝ) - α)) * formHs Ω α (fun x => f (a • x)) := by
  have hjk : ∀ q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f (a • q).2 - f (a • q).1) ^ 2) * jumpKernel d α (a • q).1 (a • q).2
        = ENNReal.ofReal (a ^ (-(d:ℝ) - α)) *
          (ENNReal.ofReal ((f (a • q.2) - f (a • q.1)) ^ 2) * jumpKernel d α q.1 q.2) := by
    intro q
    show ENNReal.ofReal ((f (a • q.2) - f (a • q.1)) ^ 2)
        * jumpKernel d α (a • q.1) (a • q.2) = _
    rw [jumpKernel_smul ha]; ring
  simp only [formHs, form]
  rw [prod_image_smul, setLIntegral_image_smul ha]
  simp only [hjk]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← Real.rpow_natCast a (2*d), ← Real.rpow_add ha]
  congr 1
  push_cast; ring

lemma image_smul_ball {a : ℝ} (ha : 0 < a) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (a • ·) '' (ball x r) = ball (a • x) (a * r) := by
  rw [Set.image_smul, _root_.smul_ball ha.ne' x r, Real.norm_eq_abs, abs_of_pos ha]

/-- **Lemma A.1's constant depends on the domain only up to scaling.** A Whitney family
for `Ω` transports along the dilation `x ↦ a • x` to one for `a • Ω`, with the *same*
overlap bound and the *same* Dyda constant — hence the same constant in Lemma A.1. -/
noncomputable def WhitneyDomainData.smul {α κ : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a) :
    WhitneyDomainData d α κ ((a • ·) '' Ω) where
  idx := W.idx
  countable := W.countable
  overlapBound := W.overlapBound
  overlapBound_pos := W.overlapBound_pos
  dydaConst := W.dydaConst
  dydaConst_pos := W.dydaConst_pos
  ctr i := a • W.ctr i
  rad i := a * W.rad i
  enlarged_subset i := by
    have : κ * (a * W.rad i) = a * (κ * W.rad i) := by ring
    rw [this, ← image_smul_ball ha]
    exact Set.image_mono (W.enlarged_subset i)
  overlap y := by
    have hset : {i | y ∈ ball (a • W.ctr i) (κ * (a * W.rad i))}
        = {i | a⁻¹ • y ∈ ball (W.ctr i) (κ * W.rad i)} := by
      ext i
      have h : κ * (a * W.rad i) = a * (κ * W.rad i) := by ring
      simp only [Set.mem_setOf_eq, h, ← image_smul_ball ha, Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; simpa [inv_smul_smul₀ ha.ne'] using hz
      · intro hy; exact ⟨a⁻¹ • y, hy, by rw [smul_inv_smul₀ ha.ne']⟩
    rw [hset]; exact W.overlap _
  dyda f := by
    have hballs : ∀ i, ball (a • W.ctr i) (a * W.rad i)
        = (a • ·) '' (ball (W.ctr i) (W.rad i)) := fun i => (image_smul_ball ha _ _).symm
    have hW := W.dyda (fun x => f (a • x))
    calc ENNReal.ofReal W.dydaConst * formHs ((a • ·) '' Ω) α f
        = ENNReal.ofReal (a ^ ((d:ℝ) - α)) *
            (ENNReal.ofReal W.dydaConst * formHs Ω α (fun x => f (a • x))) := by
          rw [formHs_smul ha]; ring
      _ ≤ ENNReal.ofReal (a ^ ((d:ℝ) - α)) *
            ∑' i, formHs (ball (W.ctr i) (W.rad i)) α (fun x => f (a • x)) :=
          mul_le_mul' le_rfl hW
      _ = ∑' i, formHs (ball (a • W.ctr i) (a * W.rad i)) α f := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun i => by rw [hballs i, formHs_smul ha]

/-! ## Lemma A.1 as the source states it -/

/-- **Lemma A.1** of Bux–Kassmann–Schulze, in the shape the source states it.

The lemma's conclusion is for *every bounded Lipschitz domain* `Ω`, with a constant
`c̃ = c̃(d, κ, α, Ω)` allowed to depend on `Ω`; the sentence that follows adds "In
particular, if `Ω` is a ball, the constant can be chosen independently of `Ω`". That
second clause is a genuine uniformity assertion, not a consequence of the first, so
both are recorded here as a conjunction.

`lemma_appendixA_stated` adds the lemma's third assertion — that the constant depends on the
domain only up to scaling — as a further conjunct; `lemma_appendixA_alpha_uniform` carries the
fourth.

The two halves differ exactly in where the Whitney data sits. `WhitneyDomainData` is
attached to a single `Ω`, so its overlap bound and Dyda constant may depend on it;
`WhitneyBallData` carries one overlap bound and one Dyda constant serving *every* ball
`B_R(x₀)` at once, which is the "independently of `Ω`" of the second clause.

Lipschitz regularity of `Ω` is not assumed: it enters the source only through the
Whitney decomposition, which is carried here as the hypothesis `W` rather than
constructed. Both halves are conditional on that quoted input, as the source's proof is. -/
theorem lemma_appendixA {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, MemLp f 2 (volume.restrict Ω) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
          ≤ form Ω k f)
      ∧ (∀ W : WhitneyBallData d α κ,
        ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
          ≤ form (ball x₀ R) k f) :=
  ⟨fun _Ω hΩ W hf => formHs_le_form_domain hc₀ hΩ W H hf hFmeas,
   fun W x₀ R hR hf => formHs_le_form_of_ballComparability hc₀ W H x₀ R hR hf hFmeas⟩

/-- **Lemma A.1's constant depends on the domain only up to scaling.** Under the same
hypotheses as `lemma_appendixA`, the conclusion holds on the dilate `a • Ω` with *literally
the same* constant as on `Ω` — the one built from `Ω`'s own Whitney family. This is the
source's "The constant `c̃` depends on the domain `Ω` only up to scaling".

It is a corollary of `WhitneyDomainData.smul`, which transports the family along the
dilation without changing its overlap bound or its Dyda constant. -/
theorem lemma_appendixA_scaling {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : MeasurableSet Ω)
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a)
    (hf : MemLp f 2 (volume.restrict ((a • ·) '' Ω))) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs ((a • ·) '' Ω) α f
      ≤ form ((a • ·) '' Ω) k f :=
  formHs_le_form_domain hc₀ (by rw [Set.image_smul]; exact hΩ.const_smul₀ a) (W.smul ha)
    H hf hFmeas

/-- **Lemma A.1 as the source states it, with its remark on the domain.** The conclusion
for every measurable `Ω` carrying a Whitney family, the "in particular, for a ball the
constant can be chosen independently of `Ω`" clause, and "the constant depends on the domain
`Ω` only up to scaling" — the three assertions the lemma makes for a fixed `α`.

The lemma's fourth assertion, that for `0 < α₀ ≤ α < 2` the constant depends on `α₀` but not
on `α`, is `lemma_appendixA_alpha_uniform`. It is not a conjunct here because it needs a
Whitney family for *every* `α` in the range, sharing one overlap bound and one Dyda constant;
requiring that would burden the three assertions above with a hypothesis the source does not
ask of them.

`lemma_appendixA` is the first two conjuncts alone. -/
theorem lemma_appendixA_stated {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, MemLp f 2 (volume.restrict Ω) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
          ≤ form Ω k f)
      ∧ (∀ W : WhitneyBallData d α κ,
        ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
          ≤ form (ball x₀ R) k f)
      ∧ (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, ∀ a : ℝ, 0 < a →
        MemLp f 2 (volume.restrict ((a • ·) '' Ω)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ))
            * formHs ((a • ·) '' Ω) α f
          ≤ form ((a • ·) '' Ω) k f) :=
  ⟨(lemma_appendixA hc₀ H hFmeas).1, (lemma_appendixA hc₀ H hFmeas).2,
   fun Ω hΩ W a ha hf => lemma_appendixA_scaling hc₀ H hFmeas Ω hΩ W ha hf⟩

/-- **Lemma A.1's constant depends on `α` only through a lower bound `α₀`.** If the Whitney
family can be chosen with one overlap bound `M` and one Dyda constant `γ` for every
`α ∈ [α₀, 2)` — which is a property of the quoted input, not something the development
proves — then Lemma A.1's constant is that one number for every such `α`. -/
theorem lemma_appendixA_alpha_uniform {κ c₀ α₀ γ : ℝ} {M : ℕ} (hc₀ : 1 ≤ c₀)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (W : ∀ α, α₀ ≤ α → α < 2 → WhitneyDomainData d α κ Ω)
    (hM : ∀ α h₁ h₂, (W α h₁ h₂).overlapBound = M)
    (hγ : ∀ α h₁ h₂, (W α h₁ h₂).dydaConst = γ)
    (H : ∀ α, α₀ ≤ α → α < 2 → ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∀ α, α₀ ≤ α → α < 2 →
      ENNReal.ofReal (c₀⁻¹ * γ / (M : ℝ)) * formHs Ω α f ≤ form Ω k f := by
  intro α h₁ h₂
  have := formHs_le_form_domain hc₀ hΩ (W α h₁ h₂) (H α h₁ h₂) hf hFmeas
  rwa [hM α h₁ h₂, hγ α h₁ h₂] at this

end QFS
