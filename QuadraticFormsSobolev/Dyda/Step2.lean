import QuadraticFormsSobolev.Dyda.Shell
import QuadraticFormsSobolev.Dyda.ChangeVar

/-! # Step 2 for the ball: every pair is controlled by far pairs

Split the pairs into dyadic shells `2^k ≤ |x − y| < 2^{k+1}`, pass through the pulled-in
midpoint, change variables `(x, y) ↦ (G, x)` and `(x, y) ↦ (G, y)`, and use that each distance
`|x − G|` belongs to at most three of the ranges `[2^{k−2}, 2^{k+1})`. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

lemma st2_cont_dist₁ : Continuous (dist₁ : EuclideanSpace ℝ (Fin d) → ℝ) := by
  unfold dist₁; exact continuous_infDist_pt _

lemma st2_isOpen_far (M : ℝ) (z : EuclideanSpace ℝ (Fin d)) : IsOpen (far M z) := by
  simp only [far, Set.ofPred_and]
  exact (isOpen_ball.preimage continuous_id).inter
    ((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const))

/-- The pairs `(g, z)` with `z ∈ far 5 g` at the distance range `[2^{k−2}, 2^{k+1})`. -/
def st2_Hset (k : ℤ) : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ far 5 p.1 ∧
    (2 : ℝ) ^ (k - 2) ≤ ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ < (2 : ℝ) ^ (k + 1)}

/-- The dyadic shell of pairs of the ball. -/
def st2_Sset (k : ℤ) : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
    (2 : ℝ) ^ k ≤ ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ < (2 : ℝ) ^ (k + 1)}

/-- The far pairs. -/
def st2_Fset : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ far 5 p.1}

lemma st2_Hset_meas (k : ℤ) : MeasurableSet (st2_Hset (d := d) k) := by
  have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖p.2 - p.1‖ := by fun_prop
  have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      5 * dist₁ p.1 := continuous_const.mul (st2_cont_dist₁.comp continuous_fst)
  simp only [st2_Hset, far, Set.ofPred_and]
  refine (isOpen_ball.preimage continuous_fst).measurableSet.inter
    ((((isOpen_ball.preimage continuous_snd).inter
      ((isOpen_ne_fun continuous_snd continuous_fst).inter (isOpen_lt h1 h2))).measurableSet).inter
      ((isClosed_le continuous_const h1).measurableSet.inter
        (isOpen_lt h1 continuous_const).measurableSet))

lemma st2_Sset_meas (k : ℤ) : MeasurableSet (st2_Sset (d := d) k) := by
  have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖p.1 - p.2‖ := by fun_prop
  simp only [st2_Sset, Set.ofPred_and]
  exact (isOpen_ball.preimage continuous_fst).measurableSet.inter
    ((isOpen_ball.preimage continuous_snd).measurableSet.inter
      ((isClosed_le continuous_const h1).measurableSet.inter
        (isOpen_lt h1 continuous_const).measurableSet))

lemma st2_Fset_meas : MeasurableSet (st2_Fset (d := d)) := by
  have h1 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖p.2 - p.1‖ := by fun_prop
  have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      5 * dist₁ p.1 := continuous_const.mul (st2_cont_dist₁.comp continuous_fst)
  simp only [st2_Fset, far, Set.ofPred_and]
  exact ((isOpen_ball.preimage continuous_fst).inter
    ((isOpen_ball.preimage continuous_snd).inter
      ((isOpen_ne_fun continuous_snd continuous_fst).inter (isOpen_lt h1 h2)))).measurableSet

noncomputable def st2_H (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (k : ℤ)
    (g z : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  (st2_Hset k).indicator (fun p => U d α u p.1 p.2) (g, z)

noncomputable def st2_S (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (k : ℤ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  (st2_Sset k).indicator (fun p => U d α u p.1 p.2) (x, y)

noncomputable def st2_F (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (g z : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  st2_Fset.indicator (fun p => U d α u p.1 p.2) (g, z)

lemma st2_H_meas (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ) :
    Measurable (Function.uncurry (st2_H α u k)) :=
  (measurable_U α hu).indicator (st2_Hset_meas k)

lemma st2_H_meas_swap (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ) :
    Measurable (Function.uncurry fun x z : EuclideanSpace ℝ (Fin d) => st2_H α u k z x) := by
  have h := (st2_H_meas α hu k).comp measurable_swap
  have e : (Function.uncurry fun x z : EuclideanSpace ℝ (Fin d) => st2_H α u k z x) =
      Function.uncurry (st2_H α u k) ∘ Prod.swap := by
    funext p; rfl
  rw [e]; exact h

lemma st2_S_meas (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ) :
    Measurable (Function.uncurry (st2_S α u k)) :=
  (measurable_U α hu).indicator (st2_Sset_meas k)

lemma st2_F_meas (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable (Function.uncurry (st2_F α u)) :=
  (measurable_U α hu).indicator st2_Fset_meas

/-- Each positive distance lies in at most three ranges `[2^{k−2}, 2^{k+1})`. -/
lemma st2_count (t : ℝ) :
    ∑' k : ℤ, (if (2 : ℝ) ^ (k - 2) ≤ t ∧ t < (2 : ℝ) ^ (k + 1) then (1 : ℝ≥0∞) else 0) ≤ 3 := by
  by_cases ht : 0 < t
  · obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow ht (by norm_num : (1 : ℝ) < 2)
    rw [tsum_eq_sum (s := Finset.Icc n (n + 2))]
    · calc ∑ k ∈ Finset.Icc n (n + 2),
            (if (2 : ℝ) ^ (k - 2) ≤ t ∧ t < (2 : ℝ) ^ (k + 1) then (1 : ℝ≥0∞) else 0)
          ≤ ∑ k ∈ Finset.Icc n (n + 2), (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun k _ => by split_ifs <;> simp
        _ = 3 := by
          have e : n + 2 + 1 - n = 3 := by ring
          simp [e]
    · intro k hk
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hk
      rw [Finset.mem_Icc]
      have a : k - 2 < n + 1 := by
        rw [← zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]; linarith
      have b : n < k + 1 := by
        rw [← zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]; linarith
      omega
  · rw [ENNReal.tsum_eq_zero.2]
    · exact zero_le
    intro k
    rw [if_neg]
    rintro ⟨h1, -⟩
    have : (0 : ℝ) < 2 ^ (k - 2) := zpow_pos (by norm_num) _
    linarith

lemma st2_sumH (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (g z : EuclideanSpace ℝ (Fin d)) :
    ∑' k, st2_H α u k g z ≤ 3 * st2_F α u g z := by
  have h : ∀ k, st2_H α u k g z =
      (if (2 : ℝ) ^ (k - 2) ≤ ‖z - g‖ ∧ ‖z - g‖ < (2 : ℝ) ^ (k + 1) then (1 : ℝ≥0∞) else 0) *
        st2_F α u g z := by
    intro k
    by_cases hF : (g, z) ∈ st2_Fset
    · by_cases hc : (2 : ℝ) ^ (k - 2) ≤ ‖z - g‖ ∧ ‖z - g‖ < (2 : ℝ) ^ (k + 1)
      · rw [if_pos hc, one_mul, st2_H, st2_F, Set.indicator_of_mem, Set.indicator_of_mem hF]
        exact ⟨hF.1, hF.2, hc.1, hc.2⟩
      · rw [if_neg hc, zero_mul, st2_H, Set.indicator_of_notMem]
        rintro ⟨-, -, h1, h2⟩; exact hc ⟨h1, h2⟩
    · rw [st2_F, Set.indicator_of_notMem hF, mul_zero, st2_H, Set.indicator_of_notMem]
      rintro ⟨h1, h2, -⟩; exact hF ⟨h1, h2⟩
  simp_rw [h, ENNReal.tsum_mul_right]
  gcongr
  exact st2_count _

lemma st2_cover (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1) :
    U d α u x y ≤ ∑' k, st2_S α u k x y := by
  by_cases hxy : x = y
  · rw [hxy, U_self]; exact zero_le
  · have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow ht (by norm_num : (1 : ℝ) < 2)
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum n)
    rw [st2_S, Set.indicator_of_mem (show (x, y) ∈ st2_Sset n from ⟨hx, hy, hn1, hn2⟩)]

/-- The constant of `U_le_via`. -/
noncomputable def st2_c₁ (d : ℕ) (α : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2 * (5 / 4) ^ ((d : ℝ) + α))

/-- The bound on the Jacobian factor of the midpoint change of variables. -/
noncomputable def st2_K (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((8 / 3 : ℝ) ^ d)

lemma st2_c₁_ne_top (d : ℕ) (α : ℝ) : st2_c₁ d α ≠ ∞ := ENNReal.ofReal_ne_top

lemma st2_K_ne_top (d : ℕ) : st2_K d ≠ ∞ := ENNReal.ofReal_ne_top

lemma st2_pointwise (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (u : EuclideanSpace ℝ (Fin d) → ℝ) (k : ℤ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    st2_S α u k x y ≤ st2_c₁ d α *
      (st2_H α u k (midG k x y) x + st2_H α u k (midG k x y) y) := by
  by_cases hS : (x, y) ∈ st2_Sset k
  · have hS' := hS
    obtain ⟨hx, hy, hk1, hk2⟩ : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ (2 : ℝ) ^ k ≤ ‖x - y‖ ∧
      ‖x - y‖ < (2 : ℝ) ^ (k + 1) := hS
    obtain ⟨hG, hxG, hx1, hx2, hx3⟩ := shell_mem hd hx hy hk1 hk2
    have hk1' : (2 : ℝ) ^ k ≤ ‖y - x‖ := by rwa [norm_sub_rev]
    have hk2' : ‖y - x‖ < (2 : ℝ) ^ (k + 1) := by rwa [norm_sub_rev]
    obtain ⟨-, hyG, hy1, hy2, hy3⟩ := shell_mem hd hy hx hk1' hk2'
    rw [midG_comm k y x] at hyG hy1 hy2 hy3
    rw [norm_sub_rev y x] at hy3
    have eS : st2_S α u k x y = U d α u x y := by
      rw [st2_S, Set.indicator_of_mem hS']
    have eHx : st2_H α u k (midG k x y) x = U d α u (midG k x y) x := by
      rw [st2_H, Set.indicator_of_mem]
      exact ⟨hG, hxG, hx1, hx2⟩
    have eHy : st2_H α u k (midG k x y) y = U d α u (midG k x y) y := by
      rw [st2_H, Set.indicator_of_mem]
      exact ⟨hG, hyG, hy1, hy2⟩
    rw [eS, eHx, eHy]
    exact U_le_via hα u hxG.2.1 hyG.2.1 hx3 hy3
  · simp only [st2_S, Set.indicator_of_notMem hS]
    exact zero_le

lemma st2_c_ne (k : ℤ) : (1 - sh k) / 2 ≠ 0 := by
  have : sh k ≤ 1 / 4 := min_le_right _ _
  intro h; linarith [show 1 - sh k = 0 by linarith]

lemma st2_const (k : ℤ) :
    ENNReal.ofReal (|(1 - sh k) / 2|⁻¹ ^ d) ≤ st2_K d := by
  have hs : sh k ≤ 1 / 4 := min_le_right _ _
  have hc : (3 / 8 : ℝ) ≤ (1 - sh k) / 2 := by linarith
  have hc0 : (0 : ℝ) < (1 - sh k) / 2 := by linarith
  rw [st2_K]
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_of_pos hc0]
  calc ((1 - sh k) / 2)⁻¹ ≤ (3 / 8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hc
    _ = 8 / 3 := by norm_num

lemma st2_mid_x (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ) :
    ∫⁻ x, ∫⁻ y, st2_H α u k (midG k x y) x
      = ENNReal.ofReal (|(1 - sh k) / 2|⁻¹ ^ d) * ∫⁻ x, ∫⁻ z, st2_H α u k z x :=
  lintegral_lintegral_mid (st2_c_ne k) _ (st2_H_meas α hu k)

lemma st2_mid_y (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ) :
    ∫⁻ x, ∫⁻ y, st2_H α u k (midG k x y) y
      = ENNReal.ofReal (|(1 - sh k) / 2|⁻¹ ^ d) * ∫⁻ x, ∫⁻ z, st2_H α u k z x := by
  rw [lintegral_lintegral_swap]
  · simp_rw [midG_comm k _ _]
    exact st2_mid_x α hu k
  · have hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        (midG k p.1 p.2, p.2) := by
      unfold midG; fun_prop
    exact ((st2_H_meas α hu k).comp hG).aemeasurable

lemma st2_F_eq (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫⁻ g, ∫⁻ z, st2_F α u g z
      = ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in far 5 x, U d α u x y := by
  rw [← lintegral_indicator measurableSet_ball]
  congr 1; funext g
  by_cases hg : g ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hg, ← lintegral_indicator (st2_isOpen_far 5 g).measurableSet]
    congr 1; funext z
    by_cases hz : z ∈ far 5 g
    · rw [Set.indicator_of_mem hz, st2_F,
        Set.indicator_of_mem (show (g, z) ∈ st2_Fset from ⟨hg, hz⟩)]
    · rw [Set.indicator_of_notMem hz, st2_F, Set.indicator_of_notMem]
      rintro ⟨-, h⟩; exact hz h
  · rw [Set.indicator_of_notMem hg]
    have : ∀ z, st2_F α u g z = 0 := fun z => by
      rw [st2_F, Set.indicator_of_notMem]; rintro ⟨h, -⟩; exact hg h
    simp [this]

lemma st2_F_meas_swap (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable (Function.uncurry fun x z : EuclideanSpace ℝ (Fin d) => st2_F α u z x) := by
  have h := (st2_F_meas α hu).comp measurable_swap
  have e : (Function.uncurry fun x z : EuclideanSpace ℝ (Fin d) => st2_F α u z x) =
      Function.uncurry (st2_F α u) ∘ Prod.swap := by
    funext p; rfl
  rw [e]; exact h

lemma st2_Hmid_meas (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) (k : ℤ)
    (b : Bool) :
    Measurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin d) =>
      st2_H α u k (midG k x y) (if b then x else y)) := by
  have hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (midG k p.1 p.2, if b then p.1 else p.2) := by
    unfold midG; cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have h := (st2_H_meas α hu k).comp hG
  have e : (Function.uncurry fun x y : EuclideanSpace ℝ (Fin d) =>
      st2_H α u k (midG k x y) (if b then x else y)) =
      Function.uncurry (st2_H α u k) ∘ fun p => (midG k p.1 p.2, if b then p.1 else p.2) := by
    funext p; rfl
  rw [e]; exact h

theorem step2 (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          U d α u x y
        ≤ ENNReal.ofReal C * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
            ∫⁻ y in far 5 x, U d α u x y := by
  refine ⟨(st2_c₁ d α * 2 * st2_K d * 3).toReal, ENNReal.toReal_nonneg, fun u hu => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (st2_c₁_ne_top d α) (by simp)) (st2_K_ne_top d)) (by simp))]
  have hHm := st2_H_meas α hu
  have hSm := st2_S_meas α hu
  have hHsw := st2_H_meas_swap α hu
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          U d α u x y
      ≤ ∫⁻ x, ∫⁻ y, ∑' k, st2_S α u k x y := by
        refine (setLIntegral_mono' measurableSet_ball fun x hx => ?_).trans
          (setLIntegral_le_lintegral _ _)
        exact (setLIntegral_mono' measurableSet_ball fun y hy => st2_cover α u hx hy).trans
          (setLIntegral_le_lintegral _ _)
    _ = ∑' k, ∫⁻ x, ∫⁻ y, st2_S α u k x y := by
        rw [← lintegral_tsum fun k => ((hSm k).lintegral_prod_right).aemeasurable]
        congr 1; funext x
        exact lintegral_tsum fun k => ((hSm k).of_uncurry_left (x := x)).aemeasurable
    _ ≤ ∑' k, st2_c₁ d α * (2 * (st2_K d * ∫⁻ x, ∫⁻ z, st2_H α u k z x)) := by
        gcongr with k
        calc ∫⁻ x, ∫⁻ y, st2_S α u k x y
            ≤ ∫⁻ x, ∫⁻ y, st2_c₁ d α * (st2_H α u k (midG k x y) x + st2_H α u k (midG k x y) y) :=
              lintegral_mono fun x => lintegral_mono fun y => st2_pointwise hd hα u k x y
          _ = st2_c₁ d α * ((∫⁻ x, ∫⁻ y, st2_H α u k (midG k x y) x) +
                ∫⁻ x, ∫⁻ y, st2_H α u k (midG k x y) y) := by
              have ha := st2_Hmid_meas α hu k true
              have hb := st2_Hmid_meas α hu k false
              simp only [if_true, Bool.false_eq_true, if_false] at ha hb
              have e1 : ∀ x, ∫⁻ y, st2_c₁ d α *
                  (st2_H α u k (midG k x y) x + st2_H α u k (midG k x y) y) =
                  st2_c₁ d α *
                  ((∫⁻ y, st2_H α u k (midG k x y) x) + ∫⁻ y, st2_H α u k (midG k x y) y) := by
                intro x
                rw [lintegral_const_mul' _ _ (st2_c₁_ne_top d α),
                  lintegral_add_left (f := fun y => st2_H α u k (midG k x y) x)
                  (ha.of_uncurry_left (x := x))]
              simp_rw [e1]
              rw [lintegral_const_mul' _ _ (st2_c₁_ne_top d α),
                lintegral_add_left
                (f := fun x => ∫⁻ y, st2_H α u k (midG k x y) x) ha.lintegral_prod_right]
          _ ≤ st2_c₁ d α * (2 * (st2_K d * ∫⁻ x, ∫⁻ z, st2_H α u k z x)) := by
              rw [st2_mid_x α hu k, st2_mid_y α hu k, ← two_mul]
              gcongr _ * (_ * (?_ * _))
              exact st2_const k
    _ = st2_c₁ d α * 2 * st2_K d * ∑' k, ∫⁻ x, ∫⁻ z, st2_H α u k z x := by
        rw [← ENNReal.tsum_mul_left]; congr 1; funext k; ring
    _ = st2_c₁ d α * 2 * st2_K d * ∫⁻ x, ∫⁻ z, ∑' k, st2_H α u k z x := by
        congr 1
        rw [← lintegral_tsum fun k => (hHsw k).lintegral_prod_right.aemeasurable]
        congr 1; funext x
        rw [← lintegral_tsum (f := fun k z => st2_H α u k z x)
          fun k => ((hHm k).of_uncurry_right (y := x)).aemeasurable]
    _ ≤ st2_c₁ d α * 2 * st2_K d * ∫⁻ x, ∫⁻ z, 3 * st2_F α u z x := by
        gcongr with x z
        exact st2_sumH α u z x
    _ = st2_c₁ d α * 2 * st2_K d * 3 * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
            ∫⁻ y in far 5 x, U d α u x y := by
        simp_rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by simp)]
        rw [lintegral_lintegral_swap (st2_F_meas_swap α hu).aemeasurable, st2_F_eq]
        ring

end Dyda
