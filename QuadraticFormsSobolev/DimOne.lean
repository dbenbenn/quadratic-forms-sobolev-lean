import QuadraticFormsSobolev.Nonvacuous

/-!
# Proposition 3.5 and Corollary 3.6 in dimension one

The proof of Proposition 3.5 goes through Lemma 3.3, which is false in dimension one. The statement
is not: on the line every double cone is `ℝ ∖ {0}`, so the lower bound in (2) holds at every pair of
distinct points, and the discretised kernel is bounded below directly, with the constant
configuration as `Γ'`.
-/

open Real Set Metric MeasureTheory ENNReal
open scoped NNReal RealInnerProductSpace

namespace QFS

/-- **On the line every double cone is `ℝ ∖ {0}`.** A nonzero `h ∈ ℝ¹` is parallel to the axis, so
`⟪v, h⟫ / ‖h‖ = ±1`, and `cos ϑ < 1` for `0 < ϑ ≤ π`. -/
lemma mem_doubleCone_dim_one {v h : EuclideanSpace ℝ (Fin 1)} (hv : ‖v‖ = 1) {ϑ : ℝ}
    (hϑ : 0 < ϑ) (hϑπ : ϑ ≤ π) (hh : h ≠ 0) : h ∈ doubleCone v ϑ := by
  have hcos : Real.cos ϑ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hϑπ hϑ
    rwa [Real.cos_zero] at this
  have hnormv : ‖v‖ = |v 0| := by rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
  have hv0 : |v 0| = 1 := by rw [← hnormv, hv]
  have hh0 : h 0 ≠ 0 := by
    intro h0; apply hh; ext i; fin_cases i; simpa using h0
  have hnorm : ‖h‖ = |h 0| := by rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]
  have hinner : ⟪v, h⟫ = v 0 * h 0 := by
    simp [PiLp.inner_apply, mul_comm]
  have hpos : 0 < |h 0| := abs_pos.mpr hh0
  -- the ratio `⟪v, h⟫ / ‖h‖` is `v 0 · sign (h 0)`, so it or its negative is `1`
  rcases le_or_gt 0 (v 0 * h 0) with hvh | hvh
  · left
    refine ⟨hh, ?_⟩
    rw [hinner, hnorm]
    have : v 0 * h 0 = |h 0| := by
      rw [← abs_of_nonneg hvh, abs_mul, hv0, one_mul]
    rw [this, div_self hpos.ne']; exact hcos
  · right
    refine ⟨neg_ne_zero.mpr hh, ?_⟩
    have hinner' : ⟪v, -h⟫ = -(v 0 * h 0) := by rw [inner_neg_right, hinner]
    rw [hinner', norm_neg, hnorm]
    have : -(v 0 * h 0) = |h 0| := by
      rw [← abs_of_neg hvh, abs_mul, hv0, one_mul]
    rw [this, div_self hpos.ne']; exact hcos

/-- **The discretised kernel in dimension one**, from below: for lattice points of `hℤ` more than
`h` apart, `k` is at least `2Λ⁻¹|s − t|^{−1−α}` on the product of their cubes, and
`|s − t| < 2|x − y|` there. The constant `2^{−3}` serves every `α ≤ 2`. -/
theorem discreteKernel_ge_dim_one {Γ : Configuration (EuclideanSpace ℝ (Fin 1))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hα : 0 < α) (hα2 : α ≤ 2) {h : ℝ} (hh : 0 < h)
    {x y : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ scaledLattice 1 h)
    (hy : y ∈ scaledLattice 1 h) (hxy : h < ‖x - y‖) :
    ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) * (2 * jumpKernel 1 α x y)
      ≤ discreteKernel 1 k h x y := by
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hxy0 : (0:ℝ) < ‖x - y‖ := lt_trans hh hxy
  have hxy' : Real.sqrt ((1:ℕ):ℝ) * h < ‖x - y‖ := by simpa using hxy
  have hexp : (-(1:ℝ) - α) ≤ 0 := by linarith
  -- the pointwise bound on the product of the cubes
  have hpt : ∀ p ∈ cube h x ×ˢ cube h y,
      ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) * (2 * jumpKernel 1 α x y) ≤ k p.1 p.2 := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    obtain ⟨hlow, hup⟩ := lemma_cubes hh hx hy hxy' hs ht
    simp only [Nat.cast_one, Real.sqrt_one, mul_one] at hlow hup
    have hst0 : (0:ℝ) < ‖s - t‖ := lt_trans (by positivity) hlow
    have hne : t - s ≠ 0 := by
      intro h0; rw [sub_eq_zero] at h0; rw [h0, sub_self, norm_zero] at hst0; exact lt_irrefl _ hst0
    have hne' : s - t ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr hne
    have hcone : ∀ u w : EuclideanSpace ℝ (Fin 1), w - u ≠ 0 → indE (coneAt Γ u) w = 1 := by
      intro u w huw
      have : w ∈ coneAt Γ u :=
        mem_doubleCone_dim_one (Γ u).norm_axis (Γ u).apex_pos
          ((Γ u).apex_le.trans (by linarith [pi_pos])) huw
      simp [indE, Set.indicator_of_mem this]
    -- `|s − t|^{−1−α} ≥ (2|x − y|)^{−1−α} ≥ 2^{−3} |x − y|^{−1−α}`
    have hkey : 2 ^ (-(3:ℝ)) * ‖x - y‖ ^ (-(1:ℝ) - α) ≤ ‖s - t‖ ^ (-(1:ℝ) - α) := by
      have h1 : (2 * ‖x - y‖) ^ (-(1:ℝ) - α) ≤ ‖s - t‖ ^ (-(1:ℝ) - α) :=
        Real.rpow_le_rpow_of_nonpos hst0 (by linarith) hexp
      have h2 : (2 * ‖x - y‖) ^ (-(1:ℝ) - α) = 2 ^ (-(1:ℝ) - α) * ‖x - y‖ ^ (-(1:ℝ) - α) :=
        Real.mul_rpow (by norm_num) hxy0.le
      have h3 : (2:ℝ) ^ (-(3:ℝ)) ≤ 2 ^ (-(1:ℝ) - α) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      calc 2 ^ (-(3:ℝ)) * ‖x - y‖ ^ (-(1:ℝ) - α)
          ≤ 2 ^ (-(1:ℝ) - α) * ‖x - y‖ ^ (-(1:ℝ) - α) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (2 * ‖x - y‖) ^ (-(1:ℝ) - α) := h2.symm
        _ ≤ ‖s - t‖ ^ (-(1:ℝ) - α) := h1
    have hlow' := hk.lower s t
    rw [hcone s t hne, hcone t s hne'] at hlow'
    refine le_trans ?_ hlow'
    have hcast : ((1:ℕ):ℝ) = 1 := by norm_num
    simp only [jumpKernel, hcast]
    rw [show (1:ℝ≥0∞) + 1 = 2 by norm_num]
    calc ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) * (2 * ENNReal.ofReal (‖x - y‖ ^ (-(1:ℝ) - α)))
        = ENNReal.ofReal Λ⁻¹ * (2 * ENNReal.ofReal (2 ^ (-(3:ℝ)) * ‖x - y‖ ^ (-(1:ℝ) - α))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ ENNReal.ofReal Λ⁻¹ * (2 * ENNReal.ofReal (‖s - t‖ ^ (-(1:ℝ) - α))) := by
          gcongr
  -- integrate
  calc ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) * (2 * jumpKernel 1 α x y)
      = ENNReal.ofReal ((h ^ (2 * 1))⁻¹) *
          ∫⁻ _ in cube h x ×ˢ cube h y, ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) *
            (2 * jumpKernel 1 α x y) := by
        rw [setLIntegral_const, volume_cube_prod hh]
        rw [show ∀ c : ℝ≥0∞, ENNReal.ofReal ((h ^ (2 * 1))⁻¹) *
            (c * (ENNReal.ofReal (h ^ 1) * ENNReal.ofReal (h ^ 1)))
          = (ENNReal.ofReal ((h ^ (2 * 1))⁻¹) *
              (ENNReal.ofReal (h ^ 1) * ENNReal.ofReal (h ^ 1))) * c from fun c => by ring,
          ofReal_inv_pow_mul hh, one_mul]
    _ ≤ discreteKernel 1 k h x y := by
        unfold discreteKernel
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        exact ae_restrict_of_forall_mem
          ((measurableSet_cube hh x).prod (measurableSet_cube hh y)) hpt

/-- There is no configuration on `ℝ⁰`: it has no unit vector to serve as an axis. -/
lemma isEmpty_configuration_zero :
    IsEmpty (Configuration (EuclideanSpace ℝ (Fin 0))) := by
  refine ⟨fun Γ => ?_⟩
  have h := (Γ 0).norm_axis
  rw [show (Γ 0).axis = 0 from Subsingleton.elim _ _, norm_zero] at h
  exact zero_ne_one h

/-- The unit vector of `ℝ¹`. -/
lemma exists_unit_dim_one : ∃ e : EuclideanSpace ℝ (Fin 1), ‖e‖ = 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- **Proposition 3.5 in dimension one.** The constant configuration serves as `Γ'`, with
`C = 2^{−3}` and `θ' = π/2`. -/
theorem prop_test_fct_dim_one {ϑ : ℝ} :
    ∃ C θ' : ℝ, 0 < C ∧ 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 1)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin 1)), IsBounded Γ' θ' ∧
        ∀ x ∈ lattice 1, ∀ y ∈ lattice 1, Real.sqrt ((1:ℕ):ℝ) < ‖x - y‖ →
          ENNReal.ofReal (C * Λ⁻¹) *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel 1 α x y)
            ≤ discreteKernel 1 k 1 x y := by
  obtain ⟨e, he⟩ := exists_unit_dim_one
  refine ⟨2 ^ (-(3:ℝ)), π / 2, by positivity, by positivity, le_rfl, ?_⟩
  intro α hα hα2 Γ _ _ Λ k hk
  refine ⟨constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩,
    isBounded_constConfig (by positivity) le_rfl he, ?_⟩
  intro x hx y hy hxy
  have hxy1 : (1:ℝ) < ‖x - y‖ := by simpa using hxy
  calc ENNReal.ofReal (2 ^ (-(3:ℝ)) * Λ⁻¹) *
        ((indE (coneAt (constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩) x) y
          + indE (coneAt (constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩) y) x)
          * jumpKernel 1 α x y)
      ≤ ENNReal.ofReal (2 ^ (-(3:ℝ)) * Λ⁻¹) * (2 * jumpKernel 1 α x y) :=
        mul_le_mul' le_rfl (mul_le_mul' (indE_add_indE_le_two _ x y) le_rfl)
    _ = ENNReal.ofReal (Λ⁻¹ * 2 ^ (-(3:ℝ))) * (2 * jumpKernel 1 α x y) := by rw [mul_comm Λ⁻¹]
    _ ≤ discreteKernel 1 k 1 x y := discreteKernel_ge_dim_one hk hα hα2 one_pos hx hy hxy1

/-- **Proposition 3.5**, in every dimension. For `d ≥ 2` this is the paper's proof
(`prop_test_fct_of_two_le`); for `d = 1`, where Lemma 3.3 fails, `prop_test_fct_dim_one`; for
`d = 0` there is no configuration. -/
theorem prop_test_fct {d : ℕ} {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ C θ' : ℝ, 0 < C ∧ 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ' θ' ∧
        ∀ x ∈ lattice d, ∀ y ∈ lattice d, Real.sqrt d < ‖x - y‖ →
          ENNReal.ofReal (C * Λ⁻¹) *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k 1 x y := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · refine ⟨1, π / 2, one_pos, by positivity, le_rfl, fun α _ _ Γ => ?_⟩
      exact (isEmpty_configuration_zero.false Γ).elim
    · exact prop_test_fct_dim_one
  · exact prop_test_fct_of_two_le hϑ hϑ' hd

/-- **Corollary 3.6 in dimension one**, both bounds. The lower one is `discreteKernel_ge_dim_one`;
the upper one holds in every dimension (`discreteKernel_le'`). -/
theorem cor_rescaled_kernel_uniform_dim_one {ϑ : ℝ} :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin 1)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin 1)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice 1 h, ∀ y ∈ scaledLattice 1 h, Real.sqrt ((1:ℕ):ℝ) * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel 1 α x y)
            ≤ discreteKernel 1 k h x y ∧
          discreteKernel 1 k h x y ≤ ENNReal.ofReal C * jumpKernel 1 α x y := by
  obtain ⟨e, he⟩ := exists_unit_dim_one
  refine ⟨π / 2, by positivity, le_rfl, fun Λ hΛ1 => ?_⟩
  have hΛ0 : (0:ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  set C₂ : ℝ := Λ⁻¹ * 2 ^ (-(3:ℝ)) with hC₂
  have hC₂0 : 0 < C₂ := by positivity
  refine ⟨max (Λ * (2 * Real.sqrt ((1:ℕ):ℝ)) ^ (((1:ℕ):ℝ) + 2)) C₂⁻¹,
    lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro α hα hα2 Γ _ _ k hk h hh
  refine ⟨constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩, fun _ => rfl,
    isBounded_constConfig (by positivity) le_rfl he, ?_⟩
  intro x hx y hy hxy
  have hxy1 : h < ‖x - y‖ := by simpa using hxy
  refine ⟨?_, ?_⟩
  · have hCle : ENNReal.ofReal (max (Λ * (2 * Real.sqrt ((1:ℕ):ℝ)) ^ (((1:ℕ):ℝ) + 2)) C₂⁻¹)⁻¹
        ≤ ENNReal.ofReal C₂ := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_le_comm₀ (by positivity) hC₂0]
      exact le_max_right _ _
    calc ENNReal.ofReal (max (Λ * (2 * Real.sqrt ((1:ℕ):ℝ)) ^ (((1:ℕ):ℝ) + 2)) C₂⁻¹)⁻¹ *
          ((indE (coneAt (constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩) x) y
            + indE (coneAt (constConfig ⟨e, he, π / 2, by positivity, le_rfl⟩) y) x)
            * jumpKernel 1 α x y)
        ≤ ENNReal.ofReal C₂ * (2 * jumpKernel 1 α x y) :=
          mul_le_mul' hCle (mul_le_mul' (indE_add_indE_le_two _ x y) le_rfl)
      _ ≤ discreteKernel 1 k h x y := discreteKernel_ge_dim_one hk hα hα2 hh hx hy hxy1
  · exact le_trans (discreteKernel_le' hk hα hα2 hh hx hy hxy)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)

/-- **Corollary 3.6**, in every dimension: `cor_rescaled_kernel_uniform_of_two_le` for `d ≥ 2`,
`cor_rescaled_kernel_uniform_dim_one` for `d = 1`, and no configuration for `d = 0`. -/
theorem cor_rescaled_kernel_uniform {d : ℕ} {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · refine ⟨π / 2, by positivity, le_rfl, fun Λ _ => ⟨1, one_pos, fun α _ _ Γ => ?_⟩⟩
      exact (isEmpty_configuration_zero.false Γ).elim
    · exact cor_rescaled_kernel_uniform_dim_one
  · exact cor_rescaled_kernel_uniform_of_two_le hϑ hϑ' hd

end QFS
