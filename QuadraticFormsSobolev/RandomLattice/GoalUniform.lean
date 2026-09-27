import QuadraticFormsSobolev.RandomLattice.BallUniform
import QuadraticFormsSobolev.Dyda.Uniform
import QuadraticFormsSobolev.RandomLattice.Ball
import QuadraticFormsSobolev.RandomLattice.DydaScaling
import QuadraticFormsSobolev.RandomLattice.LocalAverage

/-!
# Theorem 1.1 and Lemma A.1 (ball case) as printed, with their `α₀` clauses

The constant of Theorem 1.1 depends on `Λ`, `d` and `ϑ`, and for `α₀ ≤ α < 2` on `α₀` but not on
`α` (p. 2); Lemma A.1's constant `c̃` depends on `d`, `κ`, `α` and, for `α ∈ [α₀, 2)`, only on `α₀`
(p. 30). Both follow from the uniform enlarged-ball comparability, Dyda's inequality with a uniform
constant, and the averaging over the balls `B(z, δ_z/(2κ))`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

/-- **The kernel's form along one function is the form of a measurable kernel.** For any `g`,
Mathlib's measurable envelope `G ≤ (g(y) − g(x))² k(x, y)`, with the same lower integral over
every set, is `(g(y) − g(x))² k'(x, y)` for a kernel `k'` whose integrand is measurable. So no
measurability of `k` is needed wherever the function is fixed. -/
lemma exists_measurable_kernel_form_eq {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∃ k' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k' p.1 p.2) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin d)), form S k' g = form S k g := by
  obtain ⟨G, hGm, hGle, hGeq⟩ := exists_measurable_le_forall_setLIntegral_eq
    (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))
    (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k p.1 p.2)
  have key : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ENNReal.ofReal ((g p.2 - g p.1) ^ 2) *
      (G (p.1, p.2) / ENNReal.ofReal ((g p.2 - g p.1) ^ 2))) = G := by
    funext p
    by_cases h0 : ENNReal.ofReal ((g p.2 - g p.1) ^ 2) = 0
    · have hle := hGle p
      simp only [h0, zero_mul] at hle
      rw [h0, zero_mul]; exact (le_antisymm hle zero_le).symm
    · rw [mul_comm]; exact ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top
  refine ⟨fun x y => G (x, y) / ENNReal.ofReal ((g y - g x) ^ 2), ?_, fun S => ?_⟩
  · simp only; rw [key]; exact hGm
  · unfold form
    simp only
    rw [key]
    exact (hGeq (S ×ˢ S)).symm

theorem lemmaAOne_ball (d : ℕ) :
    ∀ α₀ κ : ℝ, 0 < α₀ → 1 ≤ κ →
    ∃ c' : ℝ, 0 < c' ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ (Λ : ℝ) (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      KernelBounds Γ α Λ k →
      ∀ c : ℝ, 0 < c →
      (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ (κ * R)) k f) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ R)) →
        ENNReal.ofReal (c' * c) * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ R) k f := by
  intro α₀ κ hα₀ hκ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, one_pos, fun α _ _ Λ Γ k _ c _ _ x₀ R _ f _ => ?_⟩
    rw [formHs_dim_zero, mul_zero]; exact bot_le
  have hη : 0 < (8 * κ)⁻¹ := by positivity
  have hη1 : (8 * κ)⁻¹ < 1 := by rw [inv_lt_one₀ (by positivity)]; linarith
  obtain ⟨cD, hcD, hdyda⟩ := formHs_ball_le_regional_uniform (d := d) hd hα₀ hη hη1
  have hK : 0 < cD * (24 * κ) ^ d := by positivity
  refine ⟨(cD * (24 * κ) ^ d)⁻¹, by positivity, ?_⟩
  intro α hα₀α hα2 Λ Γ k hk c hc H x₀ R hR f hf
  -- a globally square-integrable measurable version of `f` on the ball
  set B := ball x₀ R with hB
  obtain ⟨g₀, hg₀m, hfg₀⟩ : ∃ g₀ : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g₀ ∧
      f =ᵐ[volume.restrict B] g₀ :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  set g : EuclideanSpace ℝ (Fin d) → ℝ := B.indicator g₀ with hg
  have hgm : Measurable g := hg₀m.indicator measurableSet_ball
  have hfg : f =ᵐ[volume.restrict B] g := by
    filter_upwards [hfg₀, ae_restrict_mem measurableSet_ball] with x hx hxB
    rw [hg, Set.indicator_of_mem hxB, hx]
  have hgL2 : MeasureTheory.MemLp g 2 MeasureTheory.volume := by
    have h1 : MeasureTheory.MemLp g₀ 2 (volume.restrict B) := hf.ae_eq hfg₀
    rw [hg, MeasureTheory.memLp_indicator_iff_restrict measurableSet_ball]
    exact h1
  obtain ⟨k', hG, hk'⟩ := exists_measurable_kernel_form_eq g k
  have hball : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      formHs (ball z r) α g ≤ ENNReal.ofReal c⁻¹ * form (ball z (κ * r)) k' g := by
    intro z r hr
    have h := H z r hr g (hgL2.restrict _)
    have hc' : ENNReal.ofReal c ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hc
    calc formHs (ball z r) α g = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * formHs (ball z r) α g) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hc.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal c⁻¹ * form (ball z (κ * r)) k' g := by rw [hk']; gcongr
  have hmain : formHs B α g ≤ ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g := by
    calc formHs B α g
        ≤ ENNReal.ofReal cD * ∫⁻ x in B, ∫⁻ y in ball x ((8 * κ)⁻¹ * infDist x Bᶜ),
            ENNReal.ofReal ((g y - g x) ^ 2) * jumpKernel d α x y :=
          hdyda α hα₀α hα2 x₀ R hR g hgm
      _ ≤ ENNReal.ofReal cD * (ENNReal.ofReal (c⁻¹ * (24 * κ) ^ d) * form B k g) := by
          gcongr
          rw [← hk' B]
          exact regional_le_form_of_ballComparability hκ (by positivity) hgm hG hball x₀ R hR
      _ = ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hcD.le]
  have hconst : (cD * (24 * κ) ^ d)⁻¹ * c * (cD * (c⁻¹ * (24 * κ) ^ d)) = 1 := by
    field_simp
  calc ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) * formHs B α f
      = ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) * formHs B α g := by
        simp only [formHs]; rw [form_congr_ae _ hfg]
    _ ≤ ENNReal.ofReal ((cD * (24 * κ) ^ d)⁻¹ * c) *
          (ENNReal.ofReal (cD * (c⁻¹ * (24 * κ) ^ d)) * form B k g) := by gcongr
    _ = form B k g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hconst, ENNReal.ofReal_one, one_mul]
    _ = form B k f := (form_congr_ae _ hfg).symm

theorem theoremOneOne_uniform (d : ℕ) :
    ∀ ϑ Λ α₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α₀ →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ R)) →
        formHs (Metric.ball x₀ R) α f ≤ ENNReal.ofReal c * form (Metric.ball x₀ R) k f := by
  intro ϑ Λ α₀ hϑ hΛ hα₀
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, le_rfl, fun α _ _ Γ _ k _ x₀ R _ f _ => ?_⟩
    rw [formHs_dim_zero]; exact bot_le
  set ϑ₀ := min ϑ (Real.pi / 2) with hϑ₀
  have hϑ₀pos : 0 < ϑ₀ := lt_min hϑ (by positivity)
  -- the enlarged-ball comparability, uniform in `α`, for the kernels of `2Λ`
  obtain ⟨κ, C, hκ, hC, hball⟩ := formHs_ball_le_form_ball_uniform (d := d) hd hϑ₀pos
    (min_le_right _ _) (show 1 ≤ 2 * Λ by linarith)
  set C₁ := max C 1 with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- Lemma A.1 for balls removes the enlargement
  obtain ⟨c', hc', hA1⟩ := lemmaAOne_ball d α₀ κ hα₀ hκ
  refine ⟨max (c'⁻¹ * C₁) 1, le_max_right _ _, ?_⟩
  intro α hα₀α hα2 Γ hΓ k hk x₀ R hR f hf
  have hα : 0 < α := lt_of_lt_of_le hα₀ hα₀α
  have hΓ₀ : IsBounded Γ ϑ₀ :=
    ⟨hϑ₀pos, fun x => le_trans (min_le_left _ _) (hΓ.isBounded.2 x)⟩
  -- the measurable lower kernel
  set S : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    {p | p.2 - p.1 ∈ (Γ p.1).carrier} with hS
  have hSm : MeasurableSet S := hΓ.2
  set k₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal Λ⁻¹ * ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y)
    with hk₀
  have hind : ∀ x y, indE (coneAt Γ x) y = S.indicator (fun _ => (1 : ℝ≥0∞)) (x, y) := by
    intro x y
    by_cases h : y ∈ coneAt Γ x
    · have h' : (x, y) ∈ S := h
      simp [indE, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : (x, y) ∉ S := h
      simp [indE, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hjsymm : ∀ x y, jumpKernel d α x y = jumpKernel d α y x := by
    intro x y; simp only [jumpKernel, norm_sub_rev]
  have hk₀b : KernelBounds Γ α (2 * Λ) k₀ := by
    refine ⟨by linarith, fun x y => ?_, fun x y => ?_, fun x y _ => ?_⟩
    · simp only [hk₀, hjsymm x y, add_comm]
    · simp only [hk₀]
      gcongr
      linarith
    · simp only [hk₀]
      have hi : ∀ (T : Set (EuclideanSpace ℝ (Fin d))) z,
          indE T z ≤ 1 := fun T z => by
        unfold indE; by_cases hz : z ∈ T
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz]
      calc ENNReal.ofReal Λ⁻¹ * ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) *
            jumpKernel d α x y)
          ≤ ENNReal.ofReal Λ⁻¹ * ((1 + 1) * jumpKernel d α x y) := by
            gcongr <;> exact hi _ _
        _ = ENNReal.ofReal (2 * Λ⁻¹) * jumpKernel d α x y := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
        _ ≤ ENNReal.ofReal (2 * Λ) * jumpKernel d α x y := by
            gcongr
            have : Λ⁻¹ ≤ Λ := by
              rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
            linarith
  have hk₀le : ∀ x y, k₀ x y ≤ k x y := fun x y => hk.lower x y
  have hk₀m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      k₀ p.1 p.2 := by
    have e : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => k₀ p.1 p.2)
        = fun p => ENNReal.ofReal Λ⁻¹ * ((S.indicator (fun _ => (1 : ℝ≥0∞)) p +
          S.indicator (fun _ => (1 : ℝ≥0∞)) p.swap) * jumpKernel d α p.1 p.2) := by
      funext p; simp only [hk₀, hind]; rfl
    rw [e]
    refine measurable_const.mul ((((measurable_const.indicator hSm)).add
      ((measurable_const.indicator hSm).comp measurable_swap)).mul ?_)
    exact ((measurable_fst.sub measurable_snd).norm.pow_const _).ennreal_ofReal
  -- the enlarged-ball bound for `k₀`, for every square-integrable `f`, as Lemma A.1 needs it
  have H : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r → ∀ f' : EuclideanSpace ℝ (Fin d) → ℝ,
      MeasureTheory.MemLp f' 2 (MeasureTheory.volume.restrict (Metric.ball z (κ * r))) →
      ENNReal.ofReal C₁⁻¹ * formHs (Metric.ball z r) α f' ≤ form (Metric.ball z (κ * r)) k₀ f' := by
    intro z r hr f' hf'
    obtain ⟨g, hgm, hfg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g ∧
        f' =ᵐ[volume.restrict (ball z (κ * r))] g :=
      ⟨hf'.1.mk f', hf'.1.stronglyMeasurable_mk.measurable, hf'.1.ae_eq_mk⟩
    have hsub : ball z r ⊆ ball z (κ * r) := ball_subset_ball (by nlinarith)
    have hfg' : f' =ᵐ[volume.restrict (ball z r)] g := ae_restrict_of_ae_restrict_of_subset hsub hfg
    have hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k₀ p.1 p.2 :=
      (((hgm.comp measurable_snd).sub (hgm.comp measurable_fst)).pow_const 2).ennreal_ofReal.mul
        hk₀m
    have hb := hball α hα hα2 Γ hΓ₀ k₀ hk₀b g hgm hG z r hr
    calc ENNReal.ofReal C₁⁻¹ * formHs (Metric.ball z r) α f'
        = ENNReal.ofReal C₁⁻¹ * formHs (ball z r) α g := by
          rw [show formHs (ball z r) α f' = formHs (ball z r) α g from form_congr_ae _ hfg']
      _ ≤ ENNReal.ofReal C₁⁻¹ * (ENNReal.ofReal C₁ * form (ball z (κ * r)) k₀ g) := by
          gcongr
          exact hb.trans (by gcongr; exact le_max_left _ _)
      _ = form (ball z (κ * r)) k₀ g := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hC₁pos.ne',
            ENNReal.ofReal_one, one_mul]
      _ = form (Metric.ball z (κ * r)) k₀ f' := (form_congr_ae _ hfg).symm
  have hA := hA1 α hα₀α hα2 (2 * Λ) Γ k₀ hk₀b C₁⁻¹ (inv_pos.mpr hC₁pos) H x₀ R hR f hf
  calc formHs (ball x₀ R) α f
      = ENNReal.ofReal (c'⁻¹ * C₁) * (ENNReal.ofReal (c' * C₁⁻¹) * formHs (ball x₀ R) α f) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show c'⁻¹ * C₁ * (c' * C₁⁻¹) = 1 by field_simp, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (c'⁻¹ * C₁) * form (ball x₀ R) k₀ f := by gcongr
    _ ≤ ENNReal.ofReal (max (c'⁻¹ * C₁) 1) * form (ball x₀ R) k f := by
        gcongr
        · exact le_max_left _ _
        · exact lintegral_mono (fun p => mul_le_mul' le_rfl (hk₀le _ _))

end QFS
