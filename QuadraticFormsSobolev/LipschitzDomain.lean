import QuadraticFormsSobolev.Section1

/-!
# Bounded Lipschitz domains

Bux–Kassmann–Schulze use "bounded Lipschitz domain" (Theorem 1.4, Lemma A.1) without defining it.
The definition here is Dyda's (*On comparability of integral forms*, §3, p. 568), which is the one
Lemma A.1's quoted inequality (13) is proved for: an open set `D` is a *Lipschitz domain with
localisation radius `r₀` and Lipschitz constant `λ`* if for each `z ∈ ∂D` there are an isometry `T_z`
of `ℝ^d` and a `λ`-Lipschitz `φ_z : ℝ^{d−1} → ℝ` with
`T_z(D) ∩ B(T_z z, r₀) = {x : x_d > φ_z(x')} ∩ B(T_z z, r₀)`. Case (c) of Dyda's Theorem 1 adds that
`D` is bounded and connected.

The isometry and the split `x = (x', x_d)` are stated here without coordinates: a unit vector `ν`
plays the role of the `d`-th coordinate direction, and the hyperplane `ν^⊥` the role of `ℝ^{d−1}`,
both centred at `z`. A rotation taking `ν` to `e_d` turns one form into the other.
-/

open Real Set Metric
open scoped RealInnerProductSpace NNReal

namespace QFS

variable {d : ℕ}

/-- **A Lipschitz domain with localisation radius `r₀` and Lipschitz constant `L`** (Dyda, §3).
`Ω` is open, and near each boundary point `z` it is the part of the ball `B(z, r₀)` strictly above
the graph of an `L`-Lipschitz function `φ` on the hyperplane `ν^⊥`, in the direction of a unit
vector `ν`: `x ∈ Ω ∩ B(z, r₀)` iff `x ∈ B(z, r₀)` and `φ(P(x − z)) < ⟪ν, x − z⟫`, where `P` is the
orthogonal projection onto `ν^⊥`. -/
def IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin d))) (r₀ : ℝ) (L : ℝ≥0) : Prop :=
  IsOpen Ω ∧ ∀ z ∈ frontier Ω, ∃ ν : EuclideanSpace ℝ (Fin d), ‖ν‖ = 1 ∧
    ∃ φ : (ℝ ∙ ν)ᗮ → ℝ, LipschitzWith L φ ∧
      Ω ∩ ball z r₀ =
        {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < ⟪ν, x - z⟫} ∩ ball z r₀

/-- **A bounded Lipschitz domain**: a bounded, connected (in particular nonempty) Lipschitz domain,
with some positive localisation radius and some Lipschitz constant. This is case (c) of Dyda's
Theorem 1, and what Bux–Kassmann–Schulze's Theorem 1.4 and Lemma A.1 assume. -/
def IsBoundedLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Bornology.IsBounded Ω ∧ IsConnected Ω ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ L : ℝ≥0, IsLipschitzDomain Ω r₀ L

/-! ## Sanity check: every ball is a bounded Lipschitz domain -/

/-- On `[0, R/2]`, `s ↦ √(R² − s²)` is `1`-Lipschitz: both square roots are at least `R/2`, so the
difference of their squares, `|s₁² − s₂²| ≤ R |s₁ − s₂|`, shrinks by at least `R`. -/
lemma abs_sqrt_sub_sqrt_le {R s₁ s₂ : ℝ} (hR : 0 < R) (h₁ : 0 ≤ s₁) (h₁' : s₁ ≤ R / 2)
    (h₂ : 0 ≤ s₂) (h₂' : s₂ ≤ R / 2) :
    |Real.sqrt (R ^ 2 - s₁ ^ 2) - Real.sqrt (R ^ 2 - s₂ ^ 2)| ≤ |s₁ - s₂| := by
  set a := Real.sqrt (R ^ 2 - s₁ ^ 2)
  set b := Real.sqrt (R ^ 2 - s₂ ^ 2)
  have ha : R / 2 ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : R / 2 ≤ b := Real.le_sqrt_of_sq_le (by nlinarith)
  have ha2 : a ^ 2 = R ^ 2 - s₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb2 : b ^ 2 = R ^ 2 - s₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hab : 0 < a + b := by linarith
  -- `(a − b)(a + b) = (s₂ − s₁)(s₂ + s₁)` and `s₁ + s₂ ≤ R ≤ a + b`
  have e : (a - b) * (a + b) = -((s₁ - s₂) * (s₁ + s₂)) := by
    rw [show (a - b) * (a + b) = a ^ 2 - b ^ 2 by ring, ha2, hb2]; ring
  have key : |a - b| * (a + b) = |s₁ - s₂| * (s₁ + s₂) := by
    calc |a - b| * (a + b) = |(a - b) * (a + b)| := by rw [abs_mul, abs_of_pos hab]
      _ = |s₁ - s₂| * (s₁ + s₂) := by
        rw [e, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ s₁ + s₂)]
  by_contra hcon
  push Not at hcon
  have : |s₁ - s₂| * (s₁ + s₂) < |a - b| * (a + b) := by
    calc |s₁ - s₂| * (s₁ + s₂) ≤ |s₁ - s₂| * (a + b) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < |a - b| * (a + b) := mul_lt_mul_of_pos_right hcon hab
  linarith

/-- Near a point `z` of the sphere `‖· − x₀‖ = R`, with `ν` the inward unit normal, the ball is the
region above the graph `t > R − √(R² − |p|²)`: write `x − z = p + tν` with `p ⊥ ν`; then
`‖x − x₀‖² = |p|² + (t − R)²`. -/
lemma graph_iff {R : ℝ} (hR : 0 < R) {ν z x₀ x : EuclideanSpace ℝ (Fin d)} (hνn : ‖ν‖ = 1)
    (hx₀ : x₀ - z = R • ν) (hxz : ‖x - z‖ < R / 2) :
    ‖x - x₀‖ < R ↔
      R - Real.sqrt (R ^ 2 - (min ‖(((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) :
        EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2) < ⟪ν, x - z⟫ := by
  set w := x - z with hwdef
  have hP : (((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto w) : EuclideanSpace ℝ (Fin d))
      = w - ⟪ν, w⟫ • ν := by
    simp only [Submodule.orthogonalProjectionOnto_orthogonal]
    rw [Submodule.starProjection_unit_singleton ℝ hνn]
  rw [hP]
  set t := ⟪ν, w⟫ with htdef
  set p := w - t • ν with hpdef
  have hνν : ⟪ν, ν⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hνn]; norm_num
  have hpν : ⟪p, t • ν⟫ = 0 := by
    rw [hpdef, inner_smul_right, inner_sub_left, inner_smul_left, hνν, real_inner_comm, ← htdef]
    simp
  have hw : w = p + t • ν := by rw [hpdef]; abel
  have hsq : ‖t • ν‖ ^ 2 = t ^ 2 := by rw [norm_smul, hνn, mul_one, Real.norm_eq_abs, sq_abs]
  have hnormw : ‖w‖ ^ 2 = ‖p‖ ^ 2 + t ^ 2 := by
    rw [hw, norm_add_sq_real, hpν, hsq]; ring
  have hxx₀ : x - x₀ = p + (t - R) • ν := by
    have : x - x₀ = w - (x₀ - z) := by rw [hwdef]; abel
    rw [this, hx₀, hw, sub_smul]; abel
  have hpν' : ⟪p, (t - R) • ν⟫ = 0 := by
    rw [inner_smul_right, show ⟪p, ν⟫ = 0 by
      have := hpν; rw [inner_smul_right] at this
      rcases mul_eq_zero.mp this with h | h
      · rw [hpdef, inner_sub_left, inner_smul_left, hνν, real_inner_comm, ← htdef, h]; simp
      · exact h, mul_zero]
  have hnormx : ‖x - x₀‖ ^ 2 = ‖p‖ ^ 2 + (t - R) ^ 2 := by
    rw [hxx₀, norm_add_sq_real, hpν', norm_smul, hνn, mul_one, Real.norm_eq_abs, sq_abs]; ring
  have hw2 : ‖w‖ ^ 2 < (R / 2) ^ 2 := by
    have := norm_nonneg w; nlinarith
  have hp : ‖p‖ < R / 2 := by
    have := norm_nonneg p; nlinarith [sq_nonneg t]
  have ht : t < R / 2 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg (t - R / 2), sq_nonneg (t + R / 2)]
  rw [min_eq_left hp.le]
  have hrad : 0 ≤ R ^ 2 - ‖p‖ ^ 2 := by have := norm_nonneg p; nlinarith
  have hRt : 0 ≤ R - t := by linarith
  constructor
  · intro hx
    have h2 : ‖x - x₀‖ ^ 2 < R ^ 2 := by have := norm_nonneg (x - x₀); nlinarith
    have : R - t < Real.sqrt (R ^ 2 - ‖p‖ ^ 2) :=
      (Real.lt_sqrt hRt).mpr (by nlinarith)
    linarith
  · intro hx
    have h1 : R - t < Real.sqrt (R ^ 2 - ‖p‖ ^ 2) := by linarith
    have h2 := (Real.lt_sqrt hRt).mp h1
    have h3 : ‖x - x₀‖ ^ 2 < R ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hR.le h3


/-- **Every open ball is a bounded Lipschitz domain**, with localisation radius `R/2` and Lipschitz
constant `1`. At a boundary point `z` the direction `ν` is the inward normal, and the ball is the
region above the graph of `y ↦ R − √(R² − min(|y|, R/2)²)` over the tangent hyperplane. -/
theorem isBoundedLipschitzDomain_ball (x₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    IsBoundedLipschitzDomain (ball x₀ R) := by
  refine ⟨isBounded_ball, (convex_ball x₀ R).isConnected (nonempty_ball.2 hR),
    R / 2, by positivity, 1, isOpen_ball, ?_⟩
  intro z hz
  rw [frontier_ball x₀ hR.ne', mem_sphere, dist_eq_norm] at hz
  set ν : EuclideanSpace ℝ (Fin d) := R⁻¹ • (x₀ - z) with hν
  have hνn : ‖ν‖ = 1 := by
    rw [hν, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, norm_sub_rev, hz,
      inv_mul_cancel₀ hR.ne']
  have hx₀ : x₀ - z = R • ν := by rw [hν, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  set K := (ℝ ∙ ν)ᗮ with hK
  let φ : K → ℝ := fun y => R - Real.sqrt (R ^ 2 - (min ‖(y : EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2)
  refine ⟨ν, hνn, φ, ?_, ?_⟩
  · -- `φ` is `1`-Lipschitz
    refine LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_
    simp only [φ, NNReal.coe_one, one_mul, Real.dist_eq]
    have h1 := abs_sqrt_sub_sqrt_le hR (le_min (norm_nonneg (y₁ : EuclideanSpace ℝ (Fin d)))
      (by positivity)) (min_le_right _ _) (le_min (norm_nonneg (y₂ : EuclideanSpace ℝ (Fin d)))
      (by positivity)) (min_le_right _ _)
    have h2 : |min ‖(y₁ : EuclideanSpace ℝ (Fin d))‖ (R / 2) - min ‖(y₂ : EuclideanSpace ℝ (Fin d))‖ (R / 2)|
        ≤ dist y₁ y₂ := by
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), Subtype.dist_eq, dist_eq_norm]
      exact abs_norm_sub_norm_le _ _
    rw [show R - Real.sqrt (R ^ 2 - (min ‖(y₁ : EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2) -
        (R - Real.sqrt (R ^ 2 - (min ‖(y₂ : EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2))
        = -(Real.sqrt (R ^ 2 - (min ‖(y₁ : EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2) -
          Real.sqrt (R ^ 2 - (min ‖(y₂ : EuclideanSpace ℝ (Fin d))‖ (R / 2)) ^ 2)) by ring,
      abs_neg]
    exact h1.trans h2
  · -- the ball near `z` is the region above the graph
    ext x
    simp only [mem_inter_iff, mem_ball, Set.mem_ofPred_eq, dist_eq_norm]
    constructor
    · rintro ⟨hx, hxz⟩
      refine ⟨?_, hxz⟩
      exact (graph_iff hR hνn hx₀ hxz).mp hx
    · rintro ⟨hx, hxz⟩
      exact ⟨(graph_iff hR hνn hx₀ hxz).mpr hx, hxz⟩

end QFS
