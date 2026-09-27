import QuadraticFormsSobolev.LebesgueDiff
import QuadraticFormsSobolev.Section1

/-!
# Random lattice sampling: definitions

New mathematics, not in Bux–Kassmann–Schulze. The continuous comparability is derived from the
discrete Theorem 1.3 by sampling `f` at the points of a random affine lattice
`h · A_Q (ℤ^d + η)`, where `A_Q u = u + ∑ⱼ uⱼ Qⱼ` is a small random distortion of the identity,
and averaging over `η ∈ [-1/2, 1/2)^d` and over the columns `Qⱼ ∈ B̄(0, δ)`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- The distortion `A_Q u = u + ∑ⱼ uⱼ Qⱼ` with columns `Qⱼ`. -/
noncomputable def distort (Q : Fin d → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ _ + ∑ j, (EuclideanSpace.proj j).smulRight (Q j)

lemma distort_apply (Q : Fin d → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) :
    distort Q u = u + ∑ j, u j • Q j := by
  simp [distort]

/-- The sample point `h · A_Q (n + η)`. -/
noncomputable def samplePt (h : ℝ) (Q : Fin d → EuclideanSpace ℝ (Fin d))
    (η : EuclideanSpace ℝ (Fin d)) (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  h • distort Q (latticePt d 1 n + η)

/-- The admissible distortions: every column in `B̄(0, δ)`. -/
def colBox (d : ℕ) (δ : ℝ) : Set (Fin d → EuclideanSpace ℝ (Fin d)) :=
  Set.pi Set.univ (fun _ => closedBall 0 δ)

/-- The sup norm of an integer vector, as a real number. -/
noncomputable def supNormZ (w : Fin d → ℤ) : ℝ := ⨆ i, |(w i : ℝ)|

lemma abs_le_supNormZ (w : Fin d → ℤ) (i : Fin d) : |(w i : ℝ)| ≤ supNormZ w :=
  le_ciSup (f := fun i => |(w i : ℝ)|) (Set.finite_range _).bddAbove i

/-- The average of the lattice sum of `H` over the random lattice at scale `h`
(unnormalised). -/
noncomputable def latAvg (d : ℕ) (δ h : ℝ)
    (H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ Q in colBox d δ, ∫⁻ η in halfClosedCube 1 (0 : EuclideanSpace ℝ (Fin d)),
    ∑' p : (Fin d → ℤ) × (Fin d → ℤ), H (samplePt h Q η p.1, samplePt h Q η p.2)

end QFS
