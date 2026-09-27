import QuadraticFormsSobolev.RandomLattice.Basic

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-! # Random lattice sampling: averaging over the distortion `Q`

For `w ≠ 0` pick `j` with `|w_j| = ‖w‖_∞`. With the other columns fixed,
`A_Q w = c + w_j Q_j` is an affine image of `Q_j ∈ B̄(0, δ)`, so it is uniform on
`B̄(c, δ|w_j|)` with density `(|w_j|^d vol B̄(0,δ))^{-1}`. -/

lemma lintegral_closedBall_affine {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) {a : ℝ} (ha : a ≠ 0)
    (δ : ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) δ, g (c + a • x)
      = ENNReal.ofReal (|a|⁻¹ ^ d) * ∫⁻ y in closedBall c (|a| * δ), g y := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← lintegral_indicator measurableSet_closedBall]
  set F := (closedBall c (|a| * δ)).indicator g with hF
  have hFm : Measurable F := hg.indicator measurableSet_closedBall
  have hpos : 0 < |a| := abs_pos.mpr ha
  have h1 : (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ).indicator (fun x => g (c + a • x))
      = (fun y => F (c + y)) ∘ (fun x => a • x) := by
    funext x
    simp only [Function.comp, hF, Set.indicator, mem_closedBall, dist_eq_norm, sub_zero,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_le_mul_iff_right₀ hpos]
  have h2 : ∫⁻ x, ((fun y => F (c + y)) ∘ (fun x => a • x)) x
      = ∫⁻ y, F (c + y) ∂(Measure.map (fun x : EuclideanSpace ℝ (Fin d) => a • x) volume) :=
    (lintegral_map (hFm.comp (measurable_const_add c)) (measurable_const_smul a)).symm
  rw [h1, h2, Measure.map_addHaar_smul volume ha, lintegral_smul_measure,
    lintegral_add_left_eq_self (μ := volume) F c]
  simp [abs_inv, abs_pow, inv_pow, smul_eq_mul]

lemma lintegral_colBox_split (n : ℕ) (j : Fin (n + 1)) (δ : ℝ)
    (F : (Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ Q in colBox (n + 1) δ, F Q
      = ∫⁻ R in Set.pi univ (fun _ : Fin n => closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) δ),
          ∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) δ, F (Fin.insertNth j x R) := by
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
      (closedBall 0 δ)) j).symm
  rw [colBox, volume_pi, Measure.restrict_pi_pi, volume_pi, Measure.restrict_pi_pi,
    hmp.lintegral_map_equiv F, lintegral_prod_symm]
  · rfl
  · exact (hF.comp (MeasurableEquiv.measurable _)).aemeasurable

lemma exists_supNormZ_eq_succ {n : ℕ} (w : Fin (n + 1) → ℤ) :
    ∃ j, supNormZ w = |(w j : ℝ)| := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |(w i : ℝ)|)
    Finset.univ_nonempty
  exact ⟨j, le_antisymm (ciSup_le fun i => hj i (Finset.mem_univ _)) (abs_le_supNormZ w j)⟩

lemma distort_insertNth {n : ℕ} (j : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (R : Fin n → EuclideanSpace ℝ (Fin (n + 1))) (w : Fin (n + 1) → ℤ) :
    distort (Fin.insertNth j x R) (latticePt (n + 1) 1 w)
      = (latticePt (n + 1) 1 w + ∑ k : Fin n, (w (j.succAbove k) : ℝ) • R k)
        + (w j : ℝ) • x := by
  rw [distort_apply, Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [latticePt, mul_one]
  abel

lemma norm_sum_sub_le {n : ℕ} (j : Fin (n + 1)) (R : Fin n → EuclideanSpace ℝ (Fin (n + 1)))
    (w : Fin (n + 1) → ℤ) (v : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ}
    (hR : ∀ k, ‖R k‖ ≤ r) :
    dist (v + ∑ k : Fin n, (w (j.succAbove k) : ℝ) • R k) v ≤ n * (supNormZ w * r) := by
  rw [dist_eq_norm, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hm : 0 ≤ supNormZ w := (abs_nonneg _).trans (abs_le_supNormZ w 0)
  calc ∑ k : Fin n, ‖(w (j.succAbove k) : ℝ) • R k‖ ≤ ∑ _k : Fin n, supNormZ w * r := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_le_supNormZ w _) (hR k) (norm_nonneg _) hm
    _ = n * (supNormZ w * r) := by simp

lemma measurable_distort_comp {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g)
    (u : EuclideanSpace ℝ (Fin d)) : Measurable fun Q => g (distort Q u) := by
  refine hg.comp (Continuous.measurable ?_)
  simp_rw [distort_apply]
  fun_prop

/-- Upper bound for the `Q`-average of `g(A_Q w)`. -/
theorem lintegral_colBox_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (w : Fin d → ℤ) (hw : w ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ Q in colBox d δ, g (distort Q (latticePt d 1 w))
      ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) δ) ^ (d - 1) *
        ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (d * δ * supNormZ w), g y := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨j, hj⟩ := exists_supNormZ_eq_succ w
  have hwj : (w j : ℝ) ≠ 0 := by
    intro h0
    apply hw
    funext k
    have := abs_le_supNormZ w k
    rw [hj, h0, abs_zero] at this
    exact_mod_cast abs_nonpos_iff.mp this
  rw [lintegral_colBox_split n j δ _ (measurable_distort_comp g hg _)]
  simp only [distort_insertNth, lintegral_closedBall_affine _ hwj δ g hg, ← hj]
  calc _ ≤ ∫⁻ R in Set.pi univ (fun _ : Fin n => closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) δ),
          ENNReal.ofReal ((supNormZ w)⁻¹ ^ (n + 1)) *
            ∫⁻ y in closedBall (latticePt (n + 1) 1 w) ((n + 1 : ℕ) * δ * supNormZ w), g y := by
        refine setLIntegral_mono measurable_const fun R hR => ?_
        gcongr
        apply closedBall_subset_closedBall'
        have hR' : ∀ k, ‖R k‖ ≤ δ := fun k => by
          simpa [mem_closedBall_zero_iff] using hR k (mem_univ _)
        have := norm_sum_sub_le j R w (latticePt (n + 1) 1 w) hR'
        push_cast
        nlinarith
    _ = _ := by
        rw [setLIntegral_const, volume_pi, Measure.pi_pi]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
        ring

/-- Lower bound for the `Q`-average of `g(A_Q w)`: restrict the other columns to
`B̄(0, δ/d)`. -/
theorem le_lintegral_colBox (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (w : Fin d → ℤ) (hw : w ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) (δ / d)) ^ (d - 1) *
        ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        ∫⁻ y in closedBall (latticePt d 1 w) (δ * supNormZ w / d), g y
      ≤ ∫⁻ Q in colBox d δ, g (distort Q (latticePt d 1 w)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨j, hj⟩ := exists_supNormZ_eq_succ w
  have hwj : (w j : ℝ) ≠ 0 := by
    intro h0
    apply hw
    funext k
    have := abs_le_supNormZ w k
    rw [hj, h0, abs_zero] at this
    exact_mod_cast abs_nonpos_iff.mp this
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [lintegral_colBox_split n j δ _ (measurable_distort_comp g hg _)]
  simp only [distort_insertNth, lintegral_closedBall_affine _ hwj δ g hg, ← hj]
  have hsub : Set.pi univ
      (fun _ : Fin n => closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) (δ / ((n + 1 : ℕ) : ℝ)))
      ⊆ Set.pi univ (fun _ : Fin n => closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) δ) :=
    Set.pi_mono fun _ _ => closedBall_subset_closedBall
      (div_le_self hδ.le (by exact_mod_cast Nat.succ_pos n))
  calc _ = ∫⁻ R in Set.pi univ (fun _ : Fin n =>
            closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) (δ / ((n + 1 : ℕ) : ℝ))),
          ENNReal.ofReal ((supNormZ w)⁻¹ ^ (n + 1)) *
            ∫⁻ y in closedBall (latticePt (n + 1) 1 w)
              (δ * supNormZ w / ((n + 1 : ℕ) : ℝ)), g y := by
        rw [setLIntegral_const, volume_pi, Measure.pi_pi]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
        ring
    _ ≤ _ := by
        refine setLIntegral_mono' (MeasurableSet.univ_pi fun _ => measurableSet_closedBall)
          fun R hR => ?_
        gcongr
        apply closedBall_subset_closedBall'
        have hR' : ∀ k, ‖R k‖ ≤ δ / ((n + 1 : ℕ) : ℝ) := fun k => by
          simpa [mem_closedBall_zero_iff] using hR k (mem_univ _)
        have := norm_sum_sub_le j R w (latticePt (n + 1) 1 w) hR'
        rw [dist_comm]
        have key : δ * supNormZ w / ((n + 1 : ℕ) : ℝ)
            + n * (supNormZ w * (δ / ((n + 1 : ℕ) : ℝ))) = supNormZ w * δ := by
          field_simp
          push_cast
          ring
        linarith
    _ ≤ _ := lintegral_mono_set hsub

end QFS
