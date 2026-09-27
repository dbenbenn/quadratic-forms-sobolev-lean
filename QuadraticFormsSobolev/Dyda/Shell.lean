import QuadraticFormsSobolev.Dyda.Defs

/-! # Step 2 for the ball: the pulled-in midpoint

For `x, y` in the ball with `2^k ≤ |x − y| < 2^{k+1}`, the point `G = (1 − s)(x + y)/2`,
`s = 2^k/4`, lies at depth `> s` while `|x − G|, |y − G| < 5s`, so both `x` and `y` lie in
`far 5 G`. (This replaces Dyda's Step 2 in Lipschitz boxes, pp. 571–572.) -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- The shell scale `s_k = min(2^k/4, 1/4)`. -/
noncomputable def sh (k : ℤ) : ℝ := min ((2 : ℝ) ^ k / 4) (1 / 4)

/-- The pulled-in midpoint. -/
noncomputable def midG (k : ℤ) (x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ((1 - sh k) / 2) • (x + y)

lemma midG_comm (k : ℤ) (x y : EuclideanSpace ℝ (Fin d)) : midG k x y = midG k y x := by
  simp only [midG, add_comm]

/-- The geometry of the pulled-in midpoint. -/
theorem shell_mem (hd : 1 ≤ d) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1) (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1)
    {k : ℤ} (hk : (2 : ℝ) ^ k ≤ ‖x - y‖) (hk' : ‖x - y‖ < (2 : ℝ) ^ (k + 1)) :
    midG k x y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ x ∈ far 5 (midG k x y) ∧
      (2 : ℝ) ^ (k - 2) ≤ ‖x - midG k x y‖ ∧ ‖x - midG k x y‖ < (2 : ℝ) ^ (k + 1) ∧
      ‖x - midG k x y‖ ≤ 5 / 4 * ‖x - y‖ := by
  have hxn : ‖x‖ < 1 := by simpa using hx
  have hyn : ‖y‖ < 1 := by simpa using hy
  set t : ℝ := (2 : ℝ) ^ k with ht
  have tpos : 0 < t := zpow_pos (by norm_num) k
  have hr2 : ‖x - y‖ < 2 := by
    have := norm_sub_le x y; linarith
  have ht1 : t ≤ 1 := by
    by_contra h
    push Not at h
    have hk0 : 1 ≤ k := by
      by_contra h'
      push Not at h'
      have : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_zero] at this; linarith
    have : (2 : ℝ) ^ (1 : ℤ) ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk0
    rw [zpow_one] at this; linarith
  have hk1 : (2 : ℝ) ^ (k + 1) = 2 * t := by
    rw [zpow_add₀ (by norm_num), zpow_one, ht]; ring
  have hk2 : (2 : ℝ) ^ (k - 2) = t / 4 := by
    rw [zpow_sub₀ (by norm_num), ht]; norm_num
  have hsh : sh k = t / 4 := by
    unfold sh; rw [min_eq_left (by linarith)]
  set m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (x + y) with hm
  have hmn : ‖m‖ < 1 := by
    rw [hm, norm_smul]
    have := norm_add_le x y
    norm_num; linarith
  have hmn0 : 0 ≤ ‖m‖ := norm_nonneg _
  have hG : midG k x y = (1 - t / 4) • m := by
    rw [midG, hsh, hm, smul_smul]; congr 1; ring
  have hGn : ‖midG k x y‖ = (1 - t / 4) * ‖m‖ := by
    rw [hG, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hGlt : ‖midG k x y‖ < 1 := by rw [hGn]; nlinarith
  have hdist : dist₁ (midG k x y) = 1 - (1 - t / 4) * ‖m‖ := by
    rw [dist₁_eq hd hGlt.le, hGn]
  have hxG : x - midG k x y = (1 / 2 : ℝ) • (x - y) + (t / 4) • m := by
    rw [hG, hm, smul_add, smul_add, smul_add, smul_sub, smul_smul, smul_smul]
    module
  have hhalf : ‖(1 / 2 : ℝ) • (x - y)‖ = ‖x - y‖ / 2 := by
    rw [norm_smul]; norm_num; ring
  have hsm : ‖(t / 4) • m‖ = t / 4 * ‖m‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  have hup : ‖x - midG k x y‖ ≤ ‖x - y‖ / 2 + t / 4 * ‖m‖ := by
    rw [hxG, ← hhalf, ← hsm]; exact norm_add_le _ _
  have hlow : ‖x - y‖ / 2 - t / 4 * ‖m‖ ≤ ‖x - midG k x y‖ := by
    have := norm_sub_le (x - midG k x y) ((t / 4) • m)
    rw [hxG, add_sub_cancel_right, hhalf, hsm] at this
    rw [hxG]; linarith
  have hsm_le : t / 4 * ‖m‖ ≤ t / 4 := by nlinarith
  have hup' : ‖x - midG k x y‖ < 5 * (t / 4) := by linarith
  have hlow' : t / 4 ≤ ‖x - midG k x y‖ := by linarith
  refine ⟨by simpa using hGlt, ⟨hx, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro h
    have h0 : ‖x - midG k x y‖ = 0 := by rw [sub_eq_zero.mpr h, norm_zero]
    linarith
  · rw [hdist]; nlinarith
  · rw [hk2]; exact hlow'
  · rw [hk1]; linarith
  · linarith

/-- Comparing the kernels at comparable distances. -/
lemma shell_div_le {A a r p : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hp : 0 ≤ p) (har : a ≤ 5 / 4 * r) :
    A / r ^ p ≤ (5 / 4 : ℝ) ^ p * (A / a ^ p) := by
  have hr : 0 < r := by linarith
  have hap : 0 < a ^ p := Real.rpow_pos_of_pos ha p
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have hcp : 0 < (5 / 4 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have h1 : a ^ p ≤ (5 / 4 : ℝ) ^ p * r ^ p := by
    rw [← Real.mul_rpow (by norm_num) hr.le]
    exact Real.rpow_le_rpow ha.le har hp
  rw [div_le_iff₀ hrp]
  calc A = (5 / 4 : ℝ) ^ p * (A / a ^ p) * (a ^ p / (5 / 4 : ℝ) ^ p) := by
        field_simp
    _ ≤ (5 / 4 : ℝ) ^ p * (A / a ^ p) * r ^ p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hcp]; linarith

/-- The triangle inequality through `G`. -/
theorem U_le_via {α : ℝ} (hα : 0 < α) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    {x y G : EuclideanSpace ℝ (Fin d)} (hxG : x ≠ G) (hyG : y ≠ G)
    (hx : ‖x - G‖ ≤ 5 / 4 * ‖x - y‖) (hy : ‖y - G‖ ≤ 5 / 4 * ‖x - y‖) :
    U d α u x y ≤ ENNReal.ofReal (2 * (5 / 4) ^ ((d : ℝ) + α)) * (U d α u G x + U d α u G y) := by
  set p : ℝ := (d : ℝ) + α with hpdef
  have hp : 0 ≤ p := by positivity
  have ha : 0 < ‖G - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxG.symm)
  have hb : 0 < ‖G - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyG.symm)
  have hx' : ‖G - x‖ ≤ 5 / 4 * ‖x - y‖ := by rwa [norm_sub_rev]
  have hy' : ‖G - y‖ ≤ 5 / 4 * ‖x - y‖ := by rwa [norm_sub_rev]
  have h1 := shell_div_le (sq_nonneg (u G - u x)) ha hp hx'
  have h2 := shell_div_le (sq_nonneg (u G - u y)) hb hp hy'
  have hsq : (u x - u y) ^ 2 ≤ 2 * (u G - u x) ^ 2 + 2 * (u G - u y) ^ 2 := by
    nlinarith [sq_nonneg (u x + u y - 2 * u G)]
  have hrp : 0 ≤ ‖x - y‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
  have hmain : (u x - u y) ^ 2 / ‖x - y‖ ^ p ≤
      2 * (5 / 4 : ℝ) ^ p * ((u G - u x) ^ 2 / ‖G - x‖ ^ p + (u G - u y) ^ 2 / ‖G - y‖ ^ p) := by
    calc (u x - u y) ^ 2 / ‖x - y‖ ^ p
        ≤ (2 * (u G - u x) ^ 2 + 2 * (u G - u y) ^ 2) / ‖x - y‖ ^ p :=
          div_le_div_of_nonneg_right hsq hrp
      _ = 2 * ((u G - u x) ^ 2 / ‖x - y‖ ^ p) + 2 * ((u G - u y) ^ 2 / ‖x - y‖ ^ p) := by
          ring
      _ ≤ _ := by nlinarith
  unfold U
  rw [← hpdef, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hmain

end Dyda
