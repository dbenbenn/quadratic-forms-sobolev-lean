/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadraticFormsSobolev.RandomLattice.Ball
import QuadraticFormsSobolev.RandomLattice.BallUniform
import QuadraticFormsSobolev.ChakerSilvestre

/-! # The gap note's headline results, as stated there

`paper/gap-note.tex` states Theorem A, Remark 7 and Lemma 9 with the hypotheses of Bux, Kassmann
and Schulze: a `ϑ`-bounded configuration, a (measurable) kernel satisfying (2), and `α ∈ (0, 2)`.
The theorems here are exactly those statements. They are wrappers around the more general
`QFS.formHs_ball_le_form_ball_randomLattice`, `QFS.formHs_ball_le_form_ball_uniform` and
`QFS.chakerSilvestre_assumption`.
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

/-- **Remark 7.** Theorem A with `κ` and `C` independent of `α ∈ (0, 2)`. -/
theorem remark_7 (hd : 1 ≤ d) {ϑ Λ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2) (hΛ : 1 ≤ Λ) :
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

/-- **Lemma 9.** A kernel satisfying (2) satisfies Assumption 1.1 of Chaker and Silvestre, with
`s = α/2`, `λ = Λ⁻¹` and `μ = (sin²ϑ / 16)^d`. -/
theorem lemma_9 {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {ϑ : ℝ} (hΓ : IsThetaBounded Γ ϑ)
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (p : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball p r) :
    ENNReal.ofReal ((Real.sin ϑ ^ 2 / 16) ^ d) * volume (ball p r)
      ≤ volume {z ∈ ball p r | ENNReal.ofReal (Λ⁻¹ * ‖x - z‖ ^ (-(d : ℝ) - α)) ≤ k x z} :=
  chakerSilvestre_assumption hΓ.apexLowerBound
    ((hΓ.apexLowerBound.2 x).trans (Γ x).apex_le) hk p hr hx

end QFS.GapNote
