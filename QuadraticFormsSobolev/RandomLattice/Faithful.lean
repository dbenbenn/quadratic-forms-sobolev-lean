import QuadraticFormsSobolev.RandomLattice.Ball
import QuadraticFormsSobolev.RandomLattice.DydaScaling
import QuadraticFormsSobolev.RandomLattice.LocalAverage

/-! # The paper's Theorem 1.4 on ℝ^d and §3.2's conclusion, stated as printed -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

/-- The measurable lower kernel `Λ⁻¹ (1_{V[x]}(y) + 1_{V[y]}(x)) |x-y|^{-d-α}` of an admissible
configuration: it satisfies the kernel bounds with constant `2Λ` and lies below every `k`
satisfying them with constant `Λ`. -/
lemma faith_lowerKernel {d : ℕ} {ϑ Λ α : ℝ} {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    (hΓ : IsAdmissible Γ ϑ) {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) :
    ∃ k₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      KernelBounds Γ α (2 * Λ) k₀ ∧ (∀ x y, k₀ x y ≤ k x y) ∧
      Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => k₀ p.1 p.2 := by
  have hΛ : 1 ≤ Λ := hk.one_le
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
  exact ⟨k₀, hk₀b, fun x y => hk.lower x y, hk₀m⟩

lemma faith_integrand_measurable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Measurable g)
    {k₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk₀m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => k₀ p.1 p.2) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * k₀ p.1 p.2 :=
  (((hg.comp measurable_snd).sub (hg.comp measurable_fst)).pow_const 2).ennreal_ofReal.mul hk₀m

lemma faith_form_mono {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    {k₀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (h : ∀ x y, k₀ x y ≤ k x y) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Ω k₀ f ≤ form Ω k f :=
  lintegral_mono (fun _ => mul_le_mul' le_rfl (h _ _))

/-- From a seminorm bound with constant `K ≥ 1` to the same bound for the squared norms: adding
the same `L²` term `e` to both sides costs nothing. -/
theorem faith_add_le_mul_add {K : ℝ} (hK : 1 ≤ K) (e : ℝ≥0∞) {s t : ℝ≥0∞}
    (h : s ≤ ENNReal.ofReal K * t) : e + s ≤ ENNReal.ofReal K * (e + t) := by
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr hK)) h

theorem theoremOneFour_univ (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 MeasureTheory.volume ∧ form Set.univ k g ≠ ⊤}
          = {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 MeasureTheory.volume ∧
              formHs Set.univ α g ≠ ⊤} ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 MeasureTheory.volume →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f ∧
        form Set.univ k f ≤ ENNReal.ofReal Λ * formHs Set.univ α f ∧
        MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + formHs Set.univ α f
          ≤ ENNReal.ofReal c * (MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + form Set.univ k f) ∧
        MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + form Set.univ k f
          ≤ ENNReal.ofReal Λ *
            (MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + formHs Set.univ α f) := by
  intro ϑ Λ α hϑ hΛ hα hα2
  -- the lower inequality with some `c ≥ 1`
  have key : ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)),
      IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 MeasureTheory.volume →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨1, le_rfl, fun Γ _ k _ f _ => ?_⟩
      rw [formHs_dim_zero]; exact bot_le
    set ϑ₀ := min ϑ (Real.pi / 2) with hϑ₀
    have hϑ₀pos : 0 < ϑ₀ := lt_min hϑ (by positivity)
    obtain ⟨C, hC, hwhole⟩ := formHs_univ_le_form_univ_randomLattice (d := d) hd hϑ₀pos
      (min_le_right _ _) (show 1 ≤ 2 * Λ by linarith) hα.le
    refine ⟨max C 1, le_max_right _ _, ?_⟩
    intro Γ hΓ k hk f hf
    have hΓ₀ : IsBounded Γ ϑ₀ :=
      ⟨hϑ₀pos, fun x => le_trans (min_le_left _ _) (hΓ.isBounded.2 x)⟩
    obtain ⟨k₀, hk₀b, hk₀le, hk₀m⟩ := faith_lowerKernel hΓ hk
    obtain ⟨g, hgm, hfg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g ∧
        f =ᵐ[volume] g :=
      ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
    have hfg' : ∀ᵐ x ∂(volume.restrict (Set.univ : Set (EuclideanSpace ℝ (Fin d)))),
        f x = g x := by rw [Measure.restrict_univ]; exact hfg
    calc formHs Set.univ α f = formHs Set.univ α g := form_congr_ae _ hfg'
      _ ≤ ENNReal.ofReal C * form Set.univ k₀ g :=
          hwhole Γ hΓ₀ k₀ hk₀b g hgm (faith_integrand_measurable hgm hk₀m)
      _ = ENNReal.ofReal C * form Set.univ k₀ f := by rw [form_congr_ae _ hfg']
      _ ≤ ENNReal.ofReal (max C 1) * form Set.univ k f := by
          gcongr
          · exact le_max_left _ _
          · exact faith_form_mono _ hk₀le f
  obtain ⟨c, hc, hkey⟩ := key
  refine ⟨c, hc, fun Γ hΓ k hk => ⟨?_, fun f hf => ⟨hkey Γ hΓ k hk f hf,
    form_le_formHs hk _ f,
    faith_add_le_mul_add hc _ (hkey Γ hΓ k hk f hf),
    faith_add_le_mul_add hΛ _ (form_le_formHs hk _ f)⟩⟩⟩
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hf, hfin⟩
    refine ⟨hf, ne_top_of_le_ne_top ?_ (hkey Γ hΓ k hk f hf)⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  · rintro ⟨hf, hfin⟩
    refine ⟨hf, ne_top_of_le_ne_top ?_ (form_le_formHs hk _ f)⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

theorem formHs_ball_le_form_enlargedBall (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 < c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ (κ * R)) k f := by
  intro ϑ Λ α hϑ hΛ hα hα2
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, 1, le_rfl, one_pos, fun Γ _ k _ x₀ R _ f _ => ?_⟩
    rw [formHs_dim_zero, mul_zero]; exact bot_le
  set ϑ₀ := min ϑ (Real.pi / 2) with hϑ₀
  have hϑ₀pos : 0 < ϑ₀ := lt_min hϑ (by positivity)
  obtain ⟨κ, C, hκ, hC, hball⟩ := formHs_ball_le_form_ball_randomLattice (d := d) hd hϑ₀pos
    (min_le_right _ _) (show 1 ≤ 2 * Λ by linarith) hα.le
  have hM : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨κ, 1 / max C 1, hκ, by positivity, ?_⟩
  intro Γ hΓ k hk x₀ R hR f hf
  have hΓ₀ : IsBounded Γ ϑ₀ :=
    ⟨hϑ₀pos, fun x => le_trans (min_le_left _ _) (hΓ.isBounded.2 x)⟩
  obtain ⟨k₀, hk₀b, hk₀le, hk₀m⟩ := faith_lowerKernel hΓ hk
  obtain ⟨g, hgm, hfg⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, Measurable g ∧
      f =ᵐ[volume.restrict (ball x₀ (κ * R))] g :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  have hsub : ball x₀ R ⊆ ball x₀ (κ * R) := ball_subset_ball (by nlinarith)
  have hfg' : f =ᵐ[volume.restrict (ball x₀ R)] g := ae_restrict_of_ae_restrict_of_subset hsub hfg
  have hmain : formHs (ball x₀ R) α f ≤ ENNReal.ofReal (max C 1) * form (ball x₀ (κ * R)) k f :=
    calc formHs (ball x₀ R) α f = formHs (ball x₀ R) α g := form_congr_ae _ hfg'
      _ ≤ ENNReal.ofReal C * form (ball x₀ (κ * R)) k₀ g :=
          hball Γ hΓ₀ k₀ hk₀b g hgm (faith_integrand_measurable hgm hk₀m) x₀ R hR
      _ = ENNReal.ofReal C * form (ball x₀ (κ * R)) k₀ f := by rw [form_congr_ae _ hfg]
      _ ≤ ENNReal.ofReal (max C 1) * form (ball x₀ (κ * R)) k f := by
          gcongr
          · exact le_max_left _ _
          · exact faith_form_mono _ hk₀le f
  calc ENNReal.ofReal (1 / max C 1) * formHs (ball x₀ R) α f
      ≤ ENNReal.ofReal (1 / max C 1) * (ENNReal.ofReal (max C 1) * form (ball x₀ (κ * R)) k f) := by
        gcongr
    _ = form (ball x₀ (κ * R)) k f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ hM.ne', ENNReal.ofReal_one, one_mul]

end QFS
