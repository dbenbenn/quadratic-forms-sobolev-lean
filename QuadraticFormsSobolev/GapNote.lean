/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadraticFormsSobolev.RandomLattice.Ball
import QuadraticFormsSobolev.RandomLattice.BallUniform

/-! # The gap note's headline results, as stated there

`paper/gap-note.tex` states Theorem A and Remark 3.7 with the hypotheses of Bux, Kassmann and
Schulze: a `ϑ`-bounded configuration, a measurable kernel satisfying (2), and `α ∈ (0, 2)`. The
theorems here are exactly those statements. They are wrappers around the more general
`QFS.formHs_ball_le_form_ball_randomLattice` and `QFS.formHs_ball_le_form_ball_uniform`.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace QFS.GapNote

variable {d : ℕ}

private lemma integrand_measurable {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :=
  (ENNReal.measurable_ofReal.comp
    (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2)).mul hk

/-- **Theorem A.** -/
theorem theorem_A (hd : 1 ≤ d) {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ)
    (hα : 0 < α) (hα2 : α < 2) :
    ∃ κ C : ℝ, 1 ≤ κ ∧ 0 ≤ C ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsThetaBounded Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        Measurable (Function.uncurry k) → KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal C * form (ball x₀ (κ * R)) k f := by
  have _ := hα2
  obtain ⟨κ, C, hκ, hC, H⟩ :=
    formHs_ball_le_form_ball_randomLattice hd hϑ hϑ' hΛ hα.le
  exact ⟨κ, C, hκ, hC, fun Γ hΓ k hkm hk f hf =>
    H Γ hΓ.apexLowerBound k hk f hf (integrand_measurable hf hkm)⟩

/-- **Remark 3.7.** Theorem A with `κ` and `C` independent of `α ∈ (0, 2)`. -/
theorem remark_3_7 (hd : 1 ≤ d) {ϑ Λ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) :
    ∃ κ C : ℝ, 1 ≤ κ ∧ 0 ≤ C ∧ ∀ α : ℝ, 0 < α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsThetaBounded Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        Measurable (Function.uncurry k) → KernelBounds Γ α Λ k →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        formHs (ball x₀ R) α f ≤ ENNReal.ofReal C * form (ball x₀ (κ * R)) k f := by
  obtain ⟨κ, C, hκ, hC, H⟩ := formHs_ball_le_form_ball_uniform hd hϑ hϑ' hΛ
  exact ⟨κ, C, hκ, hC, fun α h1 h2 Γ hΓ k hkm hk f hf =>
    H α h1 h2 Γ hΓ.apexLowerBound k hk f hf (integrand_measurable hf hkm)⟩

end QFS.GapNote
