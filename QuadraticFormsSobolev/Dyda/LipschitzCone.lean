import QuadraticFormsSobolev.LipschitzDomain

/-! # Interior cones of a Lipschitz chart

Near a boundary point `z` of a Lipschitz domain with chart `(ν, φ)`, the directions
`v` with `|v|/4 + L |P v| < ⟪ν, v⟫` (`P` the projection onto `ν^⊥`) point uniformly into the domain:
from any point `T` of the closure near `z`, the ball about `T + v` of radius `|v| / (4(1 + L))`
lies in the domain. This is the geometry behind Dyda's Lipschitz boxes (Proposition 5); the
chain of `Dyda/ChainStep.lean` runs along such directions. -/

open Metric Set
open scoped RealInnerProductSpace NNReal

namespace Dyda

variable {d : ℕ}

/-- The cone of the chart direction `ν` with Lipschitz constant `L`. -/
def chartCone (ν : EuclideanSpace ℝ (Fin d)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | ‖v‖ / 4 + L * ‖(ℝ ∙ ν)ᗮ.orthogonalProjectionOnto v‖ < ⟪ν, v⟫}

lemma isOpen_chartCone (ν : EuclideanSpace ℝ (Fin d)) (L : ℝ) : IsOpen (chartCone ν L) :=
  isOpen_lt (by fun_prop) (by fun_prop)

lemma smul_mem_chartCone {ν v : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hv : v ∈ chartCone ν L)
    {s : ℝ} (hs : 0 < s) : s • v ∈ chartCone ν L := by
  simp only [chartCone, mem_ofPred_eq, map_smul, norm_smul, Real.norm_of_nonneg hs.le,
    inner_smul_right] at hv ⊢
  nlinarith

lemma ne_zero_of_mem_chartCone {ν v : EuclideanSpace ℝ (Fin d)} {L : ℝ}
    (hv : v ∈ chartCone ν L) : v ≠ 0 := by
  rintro rfl
  simp only [chartCone, mem_ofPred_eq, map_zero, norm_zero, inner_zero_right] at hv
  linarith

/-- Directions close to `ν` lie in the cone: `t ν + w` with `|w| (4L + 8) ≤ t`. -/
lemma add_mem_chartCone {ν w : EuclideanSpace ℝ (Fin d)} (hν : ‖ν‖ = 1) {L : ℝ} (hL : 0 ≤ L)
    {t : ℝ} (ht : 0 < t) (hw : ‖w‖ * (4 * L + 8) ≤ t) : t • ν + w ∈ chartCone ν L := by
  set P := (ℝ ∙ ν)ᗮ.orthogonalProjectionOnto
  have hPν : P ν = 0 := Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero ν
  have hP : ‖P (t • ν + w)‖ ≤ ‖w‖ := by
    rw [map_add, map_smul, hPν, smul_zero, zero_add]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  have hn : ‖t • ν + w‖ ≤ t + ‖w‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hν, Real.norm_of_nonneg ht.le, mul_one]
  have hi : t - ‖w‖ ≤ ⟪ν, t • ν + w⟫ := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hν]
    have := neg_abs_le ⟪ν, w⟫
    have h2 := abs_real_inner_le_norm ν w
    rw [hν, one_mul] at h2
    nlinarith
  have hLP : L * ‖P (t • ν + w)‖ ≤ L * ‖w‖ := mul_le_mul_of_nonneg_left hP hL
  show ‖t • ν + w‖ / 4 + L * ‖P (t • ν + w)‖ < ⟪ν, t • ν + w⟫
  nlinarith [norm_nonneg w]

/-- **The interior cone condition.** -/
theorem ball_subset_of_chart {Ω : Set (EuclideanSpace ℝ (Fin d))} {z ν : EuclideanSpace ℝ (Fin d)}
    {r₀ : ℝ} {L : ℝ≥0} (hν : ‖ν‖ = 1) {φ : (ℝ ∙ ν)ᗮ → ℝ} (hφ : LipschitzWith L φ)
    (hΩ : Ω ∩ ball z r₀ =
      {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < ⟪ν, x - z⟫} ∩ ball z r₀)
    {T v : EuclideanSpace ℝ (Fin d)} (hT : T ∈ closure Ω) (hTz : ‖T - z‖ < r₀ / 2)
    (hv : v ∈ chartCone ν L) (hvr : ‖v‖ < r₀ / 4) :
    ball (T + v) (‖v‖ / (4 * (1 + L))) ⊆ Ω := by
  set P := (ℝ ∙ ν)ᗮ.orthogonalProjectionOnto
  have hL : (0 : ℝ) ≤ L := L.2
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin d) => φ (P (x - z)) :=
    hφ.continuous.comp (P.continuous.comp (continuous_id.sub continuous_const))
  -- `T` is on or above the graph
  have hT' : φ (P (T - z)) ≤ ⟪ν, T - z⟫ := by
    have h1 : T ∈ closure (ball z r₀ ∩ Ω) :=
      isOpen_ball.inter_closure ⟨by rw [mem_ball, dist_eq_norm]; linarith [norm_nonneg (T - z)], hT⟩
    rw [inter_comm, hΩ] at h1
    exact closure_lt_subset_le hcont (by fun_prop) (closure_mono inter_subset_left h1)
  intro p hp
  set e := p - (T + v) with he_def
  have he : ‖e‖ < ‖v‖ / (4 * (1 + L)) := by rwa [mem_ball, dist_eq_norm] at hp
  have h4 : 0 < 4 * (1 + (L : ℝ)) := by positivity
  have he1 : (1 + L) * ‖e‖ < ‖v‖ / 4 := by
    rw [lt_div_iff₀ h4] at he; nlinarith
  have hev : ‖e‖ < r₀ / 4 := by nlinarith [norm_nonneg e]
  have hpz : p ∈ ball z r₀ := by
    rw [mem_ball, dist_eq_norm, show p - z = (T - z) + v + e by rw [he_def]; abel]
    calc ‖T - z + v + e‖ ≤ ‖T - z‖ + ‖v‖ + ‖e‖ := norm_add₃_le
      _ < r₀ := by linarith
  have hmem : p ∈ Ω ∩ ball z r₀ := by
    rw [hΩ]
    refine ⟨?_, hpz⟩
    show φ (P (p - z)) < ⟪ν, p - z⟫
    have hsplit : p - z = (T - z) + (v + e) := by rw [he_def]; abel
    -- the Lipschitz estimate
    have hlip : φ (P (p - z)) ≤ φ (P (T - z)) + L * (‖P v‖ + ‖e‖) := by
      have h := hφ.dist_le_mul (P (p - z)) (P (T - z))
      rw [Real.dist_eq, dist_eq_norm, hsplit, map_add, add_sub_cancel_left, map_add] at h
      have hPe : ‖P e‖ ≤ ‖e‖ := Submodule.norm_orthogonalProjectionOnto_apply_le _ _
      have h3 : ‖P v + P e‖ ≤ ‖P v‖ + ‖e‖ := (norm_add_le _ _).trans (by linarith)
      have h5 := mul_le_mul_of_nonneg_left h3 hL
      rw [hsplit, map_add, map_add] at *
      have h6 := le_abs_self (φ (P (T - z) + (P v + P e)) - φ (P (T - z)))
      linarith
    have hinner : ⟪ν, p - z⟫ ≥ ⟪ν, T - z⟫ + ⟪ν, v⟫ - ‖e‖ := by
      rw [hsplit, inner_add_right, inner_add_right]
      have h2 := abs_real_inner_le_norm ν e
      rw [hν, one_mul] at h2
      linarith [neg_abs_le ⟪ν, e⟫]
    have hcone : ‖v‖ / 4 + L * ‖P v‖ < ⟪ν, v⟫ := hv
    nlinarith
  exact hmem.1

/-- The distance to the complement from a ball contained in `Ω`. -/
lemma le_infDist_of_ball_subset {Ω : Set (EuclideanSpace ℝ (Fin d))} (hne : Ωᶜ.Nonempty)
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (h : ball x r ⊆ Ω) : r ≤ infDist x Ωᶜ :=
  (le_infDist hne).mpr fun w hw => not_lt.mp fun hlt =>
    hw (h (by rw [mem_ball, dist_comm]; exact hlt))

end Dyda
