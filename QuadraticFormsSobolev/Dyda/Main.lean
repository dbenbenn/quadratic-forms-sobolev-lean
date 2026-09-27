import QuadraticFormsSobolev.Dyda.Step1
import QuadraticFormsSobolev.Dyda.Step2

/-!
# Dyda's inequality (13) for the unit ball, `p = 2`

B. Dyda, *On comparability of integral forms*, J. Math. Anal. Appl. 318 (2006) 564–577,
inequality (13) in the proof of Theorem 1 (p. 572). Step 2 (`Step2.lean`) bounds all pairs of the
ball by the pairs `(x, y)` with `|y − x| < 5 δ_x`; Dyda's Step 1 (`Step1.lean`) bounds those by the
regional pairs `|y − x| < η δ_x`.
-/

open MeasureTheory Metric

/-- **Dyda (2006), inequality (13), for the unit ball and `p = 2`.** -/
theorem Dyda.lintegral_le_regional_unitBall {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α))
        ≤ ENNReal.ofReal c * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in ball x (η * infDist x (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ),
            ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)) := by
  obtain ⟨C₂, hC₂, h₂⟩ := Dyda.step2 (d := d) hd hα
  obtain ⟨C₁, hC₁, h₁⟩ := Dyda.step1 (d := d) hd hα hη hη1 (by norm_num : (1 : ℝ) ≤ 5)
  refine ⟨C₂ * C₁ + 1, by positivity, fun u hu => ?_⟩
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        Dyda.U d α u x y
      ≤ ENNReal.ofReal C₂ * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in Dyda.far 5 x, Dyda.U d α u x y := h₂ u hu
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in ball x (η * Dyda.dist₁ x), Dyda.U d α u x y) := by gcongr; exact h₁ u hu
    _ ≤ ENNReal.ofReal (C₂ * C₁ + 1) * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in ball x (η * Dyda.dist₁ x), Dyda.U d α u x y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC₂]
        gcongr; linarith
