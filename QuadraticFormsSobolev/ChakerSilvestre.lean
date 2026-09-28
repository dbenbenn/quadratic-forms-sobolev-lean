/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadraticFormsSobolev.ConeGap
import QuadraticFormsSobolev.Section1

/-! # Condition (2) implies Assumption 1.1 of Chaker and Silvestre

Chaker and Silvestre (Calc. Var. PDE 59 (2020), arXiv:1904.13014, Assumption 1.1) ask for
`μ ∈ (0, 1)` and `λ > 0` such that for every ball `B` and every `x ∈ B`,
`|{z ∈ B : K(x, z) ≥ λ|x − z|^{−d−2s}}| ≥ μ|B|`. A kernel satisfying the lower bound of (2) for a
configuration whose apex angles are at least `ϑ` does so, with `s = α/2`, `λ = Λ⁻¹` and
`μ = (sin²ϑ / 16)^d`.

The ball: flip the axis `v` of `Γ(x)` so that `⟪v, p − x⟫ ≥ 0`, where `p` is the centre of `B`. Put
`s = sin ϑ` and `q = x + (rs/4) v + (s²/8)(p − x)`. The ball of radius `rs²/16` about `q` lies in `B`
and in the cone `x + Ṽ(v, ϑ)`.
-/

open MeasureTheory Metric Real
open scoped ENNReal RealInnerProductSpace

namespace QFS

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The small ball lies in the big ball and in the translated cone. -/
theorem ball_subset_ball_inter_cone {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {x p : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ ball p r)
    (hvp : 0 ≤ ⟪v, p - x⟫) :
    ball (x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x)) (r * sin ϑ ^ 2 / 16)
      ⊆ ball p r ∩ {z | z - x ∈ cone v ϑ} := by
  have hs0 : 0 < sin ϑ := sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  have hs1 : sin ϑ ≤ 1 := sin_le_one ϑ
  have hun : ‖p - x‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hx
  intro z hz
  rw [mem_ball] at hz
  refine ⟨?_, ?_⟩
  · have hqp : x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - p
        = (r * sin ϑ / 4) • v - (1 - sin ϑ ^ 2 / 8) • (p - x) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    have hε1 : 0 ≤ 1 - sin ϑ ^ 2 / 8 := by nlinarith
    have hsq : ‖x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - p‖ ^ 2
        ≤ (r - r * sin ϑ ^ 2 / 16) ^ 2 := by
      rw [hqp, @norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, hv, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity), abs_of_nonneg hε1]
      have h1 : 0 ≤ 2 * (r * sin ϑ / 4 * ((1 - sin ϑ ^ 2 / 8) * ⟪v, p - x⟫)) := by positivity
      have h2 : ((1 - sin ϑ ^ 2 / 8) * ‖p - x‖) ^ 2 ≤ ((1 - sin ϑ ^ 2 / 8) * r) ^ 2 := by
        gcongr
      have hid : (r * sin ϑ / 4 * 1) ^ 2 + ((1 - sin ϑ ^ 2 / 8) * r) ^ 2
          + r ^ 2 * sin ϑ ^ 2 * (16 - 3 * sin ϑ ^ 2) / 256
          = (r - r * sin ϑ ^ 2 / 16) ^ 2 := by ring
      have hpos : 0 ≤ r ^ 2 * sin ϑ ^ 2 * (16 - 3 * sin ϑ ^ 2) / 256 := by
        have : 0 ≤ 16 - 3 * sin ϑ ^ 2 := by nlinarith
        positivity
      linarith
    have hρr : 0 ≤ r - r * sin ϑ ^ 2 / 16 := by nlinarith
    have hle : ‖x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - p‖
        ≤ r - r * sin ϑ ^ 2 / 16 := by
      nlinarith [norm_nonneg (x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - p)]
    rw [mem_ball, dist_eq_norm]
    calc ‖z - p‖ = ‖(z - (x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x)))
          + (x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - p)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < r * sin ϑ ^ 2 / 16 + (r - r * sin ϑ ^ 2 / 16) := by
        rw [← dist_eq_norm]; exact add_lt_add_of_lt_of_le hz hle
      _ = r := by ring
  · show z - x ∈ cone v ϑ
    have hqx : x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - x
        = (sin ϑ ^ 2 / 8) • (p - x) + (r * sin ϑ / 4) • v := by abel
    have hgap : r * sin ϑ ^ 2 / 16
        < coneGap v ϑ (x + (r * sin ϑ / 4) • v + (sin ϑ ^ 2 / 8) • (p - x) - x) := by
      rw [hqx, coneGap_add_smul_axis hv]
      have h0 := coneGap_sub_le hv hϑ hϑ' 0 ((sin ϑ ^ 2 / 8) • (p - x))
      rw [coneGap_zero, zero_sub, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)] at h0
      have : sin ϑ ^ 2 / 8 * ‖p - x‖ < sin ϑ ^ 2 / 8 * r :=
        mul_lt_mul_of_pos_left hun (by positivity)
      nlinarith [mul_pos hr (sq_pos_of_pos hs0)]
    refine closedBall_subset_cone hv hϑ hϑ' hgap ?_
    rw [mem_closedBall, dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact hz.le

end Geometry

end QFS

namespace QFS

variable {d : ℕ}

lemma cone_subset_of_le {v : EuclideanSpace ℝ (Fin d)} {ϑ θ : ℝ} (hϑ : 0 ≤ ϑ) (hθ : ϑ ≤ θ)
    (hθ' : θ ≤ π / 2) : cone v ϑ ⊆ cone v θ := by
  rintro h ⟨h0, hc⟩
  exact ⟨h0, lt_of_le_of_lt (cos_le_cos_of_nonneg_of_le_pi hϑ (by linarith [pi_pos]) hθ) hc⟩

lemma neg_mem_cone_neg {v h : EuclideanSpace ℝ (Fin d)} {ϑ : ℝ} (hh : h ∈ cone (-v) ϑ) :
    -h ∈ cone v ϑ := by
  obtain ⟨h0, hc⟩ := hh
  refine ⟨neg_ne_zero.mpr h0, ?_⟩
  rwa [inner_neg_right, norm_neg, ← inner_neg_left]

/-- **Condition (2) implies Assumption 1.1 of Chaker and Silvestre**, with `s = α/2`,
`λ = Λ⁻¹` and `μ = (sin²ϑ / 16)^d`. -/
theorem chakerSilvestre_assumption {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {ϑ : ℝ}
    (hΓ : ApexLowerBound Γ ϑ) (hϑ' : ϑ ≤ π / 2) {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hk : KernelBounds Γ α Λ k)
    (p : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ ball p r) :
    ENNReal.ofReal ((sin ϑ ^ 2 / 16) ^ d) * volume (ball p r)
      ≤ volume {z ∈ ball p r | ENNReal.ofReal (Λ⁻¹ * ‖x - z‖ ^ (-(d : ℝ) - α)) ≤ k x z} := by
  have hϑ := hΓ.1
  have hs0 : 0 < sin ϑ := sin_pos_of_pos_of_lt_pi hϑ (by linarith [pi_pos])
  set V := Γ x
  -- the axis, oriented towards the centre
  obtain ⟨w, hw, hwp, hwsub⟩ : ∃ w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 ∧ 0 ≤ ⟪w, p - x⟫ ∧
      cone w ϑ ⊆ V.carrier := by
    have hsub := cone_subset_of_le (v := V.axis) hϑ.le (hΓ.2 x) V.apex_le
    rcases le_total 0 ⟪V.axis, p - x⟫ with h | h
    · exact ⟨V.axis, V.norm_axis, h, fun y hy => Or.inl (hsub hy)⟩
    · refine ⟨-V.axis, by rw [norm_neg]; exact V.norm_axis, by rw [inner_neg_left]; linarith,
        fun y hy => Or.inr ?_⟩
      have hneg := neg_mem_cone_neg hy
      exact hsub (by simpa using hneg)
  set q := x + (r * sin ϑ / 4) • w + (sin ϑ ^ 2 / 8) • (p - x)
  have hsub : ball q (r * sin ϑ ^ 2 / 16)
      ⊆ {z ∈ ball p r | ENNReal.ofReal (Λ⁻¹ * ‖x - z‖ ^ (-(d : ℝ) - α)) ≤ k x z} := by
    intro z hz
    obtain ⟨hzB, hzC⟩ := ball_subset_ball_inter_cone hw hϑ hϑ' hr hx hwp hz
    refine ⟨hzB, ?_⟩
    have hmem : z ∈ coneAt Γ x := (mem_coneAt).2 (hwsub hzC)
    have hlow := hk.lower x z
    have hΛ : 0 ≤ Λ⁻¹ := inv_nonneg.mpr (by linarith [hk.one_le])
    have hind : indE (coneAt Γ x) z = 1 := by simp [indE, hmem]
    calc ENNReal.ofReal (Λ⁻¹ * ‖x - z‖ ^ (-(d : ℝ) - α))
        = ENNReal.ofReal Λ⁻¹ * (1 * jumpKernel d α x z) := by
          rw [one_mul, jumpKernel, ENNReal.ofReal_mul hΛ]
      _ ≤ ENNReal.ofReal Λ⁻¹ * ((indE (coneAt Γ x) z + indE (coneAt Γ z) x) * jumpKernel d α x z) := by
          rw [hind]; gcongr; exact le_self_add
      _ ≤ k x z := hlow
  have hρ : 0 < r * sin ϑ ^ 2 / 16 := by positivity
  calc ENNReal.ofReal ((sin ϑ ^ 2 / 16) ^ d) * volume (ball p r)
      = volume (ball q (r * sin ϑ ^ 2 / 16)) := by
        rw [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ hρ,
          finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
        congr 3; ring
    _ ≤ _ := measure_mono hsub

end QFS
