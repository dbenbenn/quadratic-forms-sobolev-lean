/-
Step 6 of the proof of Theorem 5.15: the multiplicity of edges.

An edge is used by a pair `(x, y)` only through a logarithmic scale `n`, a centre
`z` of the index lattice at that scale, and the assignment `φ_z`. Each of the
three ranges over a bounded set: the length of the edge pins the scale to within
a constant, only boundedly many centres have their ball containing the edge, and
`φ_z` has fibres of size at most `K`. Multiplying gives the bound.
-/
import QuadraticFormsSobolev.CyclicScheme

open Real Set Metric

namespace QFS

/-! ## Scale separation

The edges of the walk attached to a pair at scale `m` have length in
`[Δ^m, 2Δ^{m+1}R)` (Step 5). These windows overlap only boundedly. -/

/-- **Scale separation.** A length lies in the window of at most `C + 1`
consecutive scales, where `2^C ≥ 2ΔR`. -/
theorem scale_separation {Δ R L : ℝ} (hΔ : 2 ≤ Δ) (hR : 0 < R) {C : ℕ}
    (hC : 2 * Δ * R ≤ 2 ^ C) {m₁ m₂ : ℕ}
    (h₁ : L < 2 * Δ ^ (m₁ + 1) * R) (h₂ : Δ ^ m₂ ≤ L) : m₂ ≤ m₁ + C := by
  by_contra hcon
  rw [not_le] at hcon
  have hΔ0 : (0:ℝ) < Δ := by linarith
  have hpow : Δ ^ (m₁ + C + 1) ≤ Δ ^ m₂ :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h2C : (2:ℝ) ^ C ≤ Δ ^ C := pow_le_pow_left₀ (by norm_num) hΔ (C)
  have hpos : (0:ℝ) < Δ ^ (m₁ + 1) := by positivity
  have hexp : Δ ^ (m₁ + C + 1) = Δ ^ (m₁ + 1) * Δ ^ C := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : Δ ^ (m₁ + 1) * (2 * Δ * R) ≤ Δ ^ (m₁ + 1) * Δ ^ C :=
    mul_le_mul_of_nonneg_left (le_trans hC h2C) hpos.le
  have hA : Δ ^ (m₁ + 1) * (2 * Δ * R) ≤ L := by
    calc Δ ^ (m₁ + 1) * (2 * Δ * R) ≤ Δ ^ (m₁ + 1) * Δ ^ C := hkey
      _ = Δ ^ (m₁ + C + 1) := hexp.symm
      _ ≤ Δ ^ m₂ := hpow
      _ ≤ L := h₂
  have hB : 2 * Δ ^ (m₁ + 1) * R < Δ ^ (m₁ + 1) * (2 * Δ * R) := by
    have hd : 0 < Δ ^ (m₁ + 1) * R * (Δ - 1) := mul_pos (mul_pos hpos hR) (by linarith)
    nlinarith [hd]
  linarith

/-! ## The centre count -/

variable {d : ℕ}

/-- The centres of the index lattice whose ball of radius `sR` contains a given
point all lie in a fixed ball of the lattice. -/
theorem lattice_scaled_ball_subset {s R : ℝ} (hs : 0 < s)
    (u : EuclideanSpace ℝ (Fin d)) :
    {w : EuclideanSpace ℝ (Fin d) | w ∈ lattice d ∧ ‖s • w - u‖ < s * R}
      ⊆ ball (s⁻¹ • u) R ∩ lattice d := by
  rintro w ⟨hwlat, hw⟩
  refine ⟨?_, hwlat⟩
  rw [mem_ball, dist_eq_norm]
  have he : w - s⁻¹ • u = s⁻¹ • (s • w - u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [inv_mul_lt_iff₀ hs]
  linarith

/-- Hence there are only finitely many such centres. Step 6 needs this as well as
the count, since `Set.ncard` is `0` on infinite sets. -/
theorem lattice_scaled_ball_finite {s R : ℝ} (hs : 0 < s)
    (u : EuclideanSpace ℝ (Fin d)) :
    {w : EuclideanSpace ℝ (Fin d) | w ∈ lattice d ∧ ‖s • w - u‖ < s * R}.Finite :=
  Set.Finite.subset
    ((lattice_inter_closedBall_finite (s⁻¹ • u) R).subset
      (fun _p hp => ⟨hp.2, ball_subset_closedBall hp.1⟩))
    (lattice_scaled_ball_subset hs u)

/-- **Centre count.** At a fixed scale `s`, only `(2⌈R⌉+1)^d` centres of the index
lattice have their ball of radius `sR` containing a given point. -/
theorem ncard_lattice_scaled_ball_le {s R : ℝ} (hs : 0 < s)
    (u : EuclideanSpace ℝ (Fin d)) :
    {w : EuclideanSpace ℝ (Fin d) | w ∈ lattice d ∧ ‖s • w - u‖ < s * R}.ncard
      ≤ (2 * ⌈R⌉₊ + 1) ^ d :=
  le_trans (Set.ncard_le_ncard (lattice_scaled_ball_subset hs u)
    ((lattice_inter_closedBall_finite (s⁻¹ • u) R).subset
      (fun _p hp => ⟨hp.2, ball_subset_closedBall hp.1⟩)))
    (ncard_lattice_inter_ball_le _ R)

end QFS
