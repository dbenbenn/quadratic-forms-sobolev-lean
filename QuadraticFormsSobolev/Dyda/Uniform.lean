import QuadraticFormsSobolev.Dyda.Main
import QuadraticFormsSobolev.RandomLattice.DydaScaling

/-! # Dyda's inequality with a constant uniform in `α ∈ [α₀, 2)`

Needed for the `α₀` clauses of Theorem 1.1 and Lemma A.1: the constants of Step 1
(`β²/((β−1)(1−γ))` with `β = (1+θ)^α`, `γ = (1−θ²)^α`) and of Step 2 (`2(5/4)^{d+α}`, …) stay
bounded for `α ∈ [α₀, 2)`. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- `step1` with its constant exposed. -/
lemma dyu_step1 (hd : 1 ≤ d) {α η M : ℝ} (hα : 0 < α) (hη : 0 < η) (hη1 : η < 1) (hM : 1 ≤ M)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in far M x, U d α u x y
      ≤ ENNReal.ofReal ((1 + η / M) ^ α / ((1 + η / M) ^ α - 1) *
          ((1 + η / M) ^ α / (1 - (1 + η / M) ^ α * (1 - η / M) ^ α))) *
        ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in ball x (η * dist₁ x), U d α u x y := by
  have hM0 : 0 < M := by linarith
  have hθ0 : 0 < η / M := div_pos hη hM0
  have hθ1 : η / M < 1 := (div_lt_one hM0).mpr (by linarith)
  have hq0 : 0 < 1 - η / M := by linarith
  have hq1 : 1 - η / M < 1 := by linarith
  set β := (1 + η / M) ^ α with hβdef
  have hβ : 1 < β := Real.one_lt_rpow (by linarith) hα
  have hγ : β * (1 - η / M) ^ α < 1 := by
    rw [hβdef, ← Real.mul_rpow (by linarith) hq0.le]
    exact Real.rpow_lt_one (by nlinarith) (by nlinarith) hα
  set F : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun N x y =>
    {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ chainSet (1 - η / M) M N p.1}.indicator
          (fun p => U d α u p.1 p.2) (x, y) with hF
  have hFm : ∀ N, Measurable (Function.uncurry (F N)) := fun N =>
    (measurable_U α hu).indicator (st1_measurableSet_S _ M N)
  have hFy : ∀ N x, Measurable (F N x) := fun N x => (hFm N).of_uncurry_left
  have hFx : ∀ N, Measurable fun x => ∫⁻ y, F N x y := fun N => (hFm N).lintegral_prod_right
  have hbound : ∀ N, 1 ≤ N → ∫⁻ x, ∫⁻ y, F N x y ≤ ENNReal.ofReal
      (β / (β - 1) * (β / (1 - β * (1 - η / M) ^ α))) * ∫⁻ x, ∫⁻ y, st1_R η α u x y :=
    fun N hN => st1_chain_bound hd hα hη hη1 hM hq0 hq1 hβ hγ hu hN
  have hin : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫⁻ y in far M x, U d α u x y ≤ Filter.liminf (fun N => ∫⁻ y, F N x y) Filter.atTop := by
    intro x hx
    calc ∫⁻ y in far M x, U d α u x y
        ≤ ∫⁻ y in far M x, Filter.liminf (fun N => F N x y) Filter.atTop := by
          refine setLIntegral_mono (Measurable.liminf fun N => hFy N x) fun y hy => ?_
          refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
          filter_upwards [st1_eventually_mem hq0.le hq1 hy] with N hN
          simp only [hF]
          rw [Set.indicator_of_mem (show (x, y) ∈ {p : EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d) | p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
              p.2 ∈ chainSet (1 - η / M) M N p.1} from ⟨hx, hN⟩)]
      _ ≤ ∫⁻ y, Filter.liminf (fun N => F N x y) Filter.atTop := setLIntegral_le_lintegral _ _
      _ ≤ Filter.liminf (fun N => ∫⁻ y, F N x y) Filter.atTop := lintegral_liminf_le (hFy · x)
  rw [← st1_rhs]
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in far M x, U d α u x y
      ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          Filter.liminf (fun N => ∫⁻ y, F N x y) Filter.atTop :=
        setLIntegral_mono (Measurable.liminf hFx) hin
    _ ≤ ∫⁻ x, Filter.liminf (fun N => ∫⁻ y, F N x y) Filter.atTop := setLIntegral_le_lintegral _ _
    _ ≤ Filter.liminf (fun N => ∫⁻ x, ∫⁻ y, F N x y) Filter.atTop := lintegral_liminf_le hFx
    _ ≤ _ := Filter.liminf_le_of_frequently_le'
        ((Filter.eventually_ge_atTop 1).mono hbound).frequently

/-- The constant of `dyu_step1` is bounded uniformly for `α ∈ [α₀, 2)`. -/
lemma dyu_step1_const_le {α₀ α θ : ℝ} (hα₀ : 0 < α₀) (hα₀α : α₀ ≤ α) (hα2 : α < 2)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (1 + θ) ^ α / ((1 + θ) ^ α - 1) * ((1 + θ) ^ α / (1 - (1 + θ) ^ α * (1 - θ) ^ α))
      ≤ (1 + θ) ^ (2 : ℝ) / ((1 + θ) ^ α₀ - 1) *
          ((1 + θ) ^ (2 : ℝ) / (1 - (1 - θ ^ 2) ^ α₀)) := by
  have hb : 1 ≤ 1 + θ := by linarith
  have hβ2 : (1 + θ) ^ α ≤ (1 + θ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hα2.le
  have hβ0 : (1 + θ) ^ α₀ ≤ (1 + θ) ^ α := Real.rpow_le_rpow_of_exponent_le hb hα₀α
  have hl0 : 0 < (1 + θ) ^ α₀ - 1 := by
    have := Real.one_lt_rpow (by linarith : 1 < 1 + θ) hα₀; linarith
  have hg0 : 0 < 1 - θ ^ 2 := by nlinarith
  have hg1 : 1 - θ ^ 2 ≤ 1 := by nlinarith
  have hγ : (1 + θ) ^ α * (1 - θ) ^ α = (1 - θ ^ 2) ^ α := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]; ring_nf
  have hγle : (1 - θ ^ 2) ^ α ≤ (1 - θ ^ 2) ^ α₀ :=
    Real.rpow_le_rpow_of_exponent_ge hg0 hg1 hα₀α
  have hm0 : 0 < 1 - (1 - θ ^ 2) ^ α₀ := by
    have := Real.rpow_lt_one hg0.le (by nlinarith : 1 - θ ^ 2 < 1) hα₀; linarith
  have hβpos : 0 ≤ (1 + θ) ^ α := by positivity
  rw [hγ]
  have h1 : (1 + θ) ^ α / ((1 + θ) ^ α - 1) ≤ (1 + θ) ^ (2 : ℝ) / ((1 + θ) ^ α₀ - 1) :=
    div_le_div₀ (by positivity) hβ2 hl0 (by linarith)
  have h2 : (1 + θ) ^ α / (1 - (1 - θ ^ 2) ^ α) ≤ (1 + θ) ^ (2 : ℝ) / (1 - (1 - θ ^ 2) ^ α₀) :=
    div_le_div₀ (by positivity) hβ2 hm0 (by linarith)
  exact mul_le_mul h1 h2 (div_nonneg hβpos (by linarith)) (by positivity)

/-- `step2` with its constant exposed. -/
lemma dyu_step2 (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Measurable u) :
    ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        U d α u x y
      ≤ st2_c₁ d α * 2 * st2_K d * 3 * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in far 5 x, U d α u x y := by
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

lemma dyu_c₁_le {α : ℝ} (hα2 : α < 2) :
    st2_c₁ d α ≤ ENNReal.ofReal (2 * (5 / 4) ^ ((d : ℝ) + 2)) := by
  unfold st2_c₁
  apply ENNReal.ofReal_le_ofReal
  gcongr
  norm_num

end Dyda

/-- Dyda's inequality (13) for the unit ball, with one constant for all `α ∈ [α₀, 2)`. -/
theorem Dyda.lintegral_le_regional_unitBall_uniform {d : ℕ} (hd : 1 ≤ d) {α₀ : ℝ} (hα₀ : 0 < α₀)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α))
        ≤ ENNReal.ofReal c * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in ball x (η * infDist x (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ),
            ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)) := by
  set θ : ℝ := η / 5 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  set K₁ : ℝ := (1 + θ) ^ (2 : ℝ) / ((1 + θ) ^ α₀ - 1) *
    ((1 + θ) ^ (2 : ℝ) / (1 - (1 - θ ^ 2) ^ α₀)) with hK₁
  set E : ℝ≥0∞ := ENNReal.ofReal (2 * (5 / 4) ^ ((d : ℝ) + 2)) * 2 * Dyda.st2_K d * 3 with hE
  have hEtop : E ≠ ∞ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simp)) (Dyda.st2_K_ne_top d)) (by simp)
  have hK₁0 : 0 ≤ K₁ := by
    have h1 := Real.one_lt_rpow (by linarith : 1 < 1 + θ) hα₀
    have h2 := Real.rpow_lt_one (by nlinarith : 0 ≤ 1 - θ ^ 2) (by nlinarith : 1 - θ ^ 2 < 1) hα₀
    rw [hK₁]
    exact mul_nonneg (div_nonneg (by positivity) (by linarith))
      (div_nonneg (by positivity) (by linarith))
  refine ⟨E.toReal * K₁ + 1, add_pos_of_nonneg_of_pos (mul_nonneg ENNReal.toReal_nonneg hK₁0)
    one_pos, fun α hα₀α hα2 u hu => ?_⟩
  have hα : 0 < α := lt_of_lt_of_le hα₀ hα₀α
  calc ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        Dyda.U d α u x y
      ≤ Dyda.st2_c₁ d α * 2 * Dyda.st2_K d * 3 * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in Dyda.far 5 x, Dyda.U d α u x y := Dyda.dyu_step2 hd hα hu
    _ ≤ E * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in Dyda.far 5 x, Dyda.U d α u x y := by
        rw [hE]; gcongr; exact Dyda.dyu_c₁_le hα2
    _ ≤ E * (ENNReal.ofReal ((1 + η / 5) ^ α / ((1 + η / 5) ^ α - 1) *
          ((1 + η / 5) ^ α / (1 - (1 + η / 5) ^ α * (1 - η / 5) ^ α))) *
          ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
            ∫⁻ y in ball x (η * Dyda.dist₁ x), Dyda.U d α u x y) := by
        gcongr; exact Dyda.dyu_step1 hd hα hη hη1 (by norm_num) hu
    _ ≤ E * (ENNReal.ofReal K₁ * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
            ∫⁻ y in ball x (η * Dyda.dist₁ x), Dyda.U d α u x y) := by
        gcongr
        exact Dyda.dyu_step1_const_le hα₀ hα₀α hα2 hθ0 hθ1
    _ = ENNReal.ofReal (E.toReal * K₁) * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
            ∫⁻ y in ball x (η * Dyda.dist₁ x), Dyda.U d α u x y := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hEtop, hE]
        ring
    _ ≤ _ := by
        gcongr ?_ * _
        exact ENNReal.ofReal_le_ofReal (by linarith)

namespace QFS

variable {d : ℕ}

/-- Dyda's inequality on every ball, with one constant for all `α ∈ [α₀, 2)`. -/
theorem formHs_ball_le_regional_uniform (hd : 1 ≤ d) {α₀ : ℝ} (hα₀ : 0 < α₀) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 → ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      formHs (ball x₀ R) α f ≤ ENNReal.ofReal c *
        ∫⁻ x in ball x₀ R, ∫⁻ y in ball x (η * infDist x (ball x₀ R)ᶜ),
          ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y := by
  obtain ⟨c, hc, hdy⟩ := Dyda.lintegral_le_regional_unitBall_uniform hd hα₀ hη hη1
  refine ⟨c, hc, fun α hα₀α hα2 x₀ R hR f hf => ?_⟩
  have key := hdy α hα₀α hα2 (fun x' => f (x₀ + R • x')) (hf.comp (dydaS_measurable_affine x₀ R))
  beta_reduce at key
  have hB : (fun x' => x₀ + R • x') ⁻¹' ball x₀ R = ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    have := dydaS_preimage_ball x₀ hR 0 1
    simpa using this
  set J := ENNReal.ofReal (R ^ d) with hJ
  set K := ENNReal.ofReal (R ^ (-(d : ℝ) - α)) with hK
  have hL : formHs (ball x₀ R) α f = J * (J * (K * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        ENNReal.ofReal ((f (x₀ + R • x) - f (x₀ + R • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    unfold formHs form
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      lintegral_prod _ (dydaS_measurable_integrand f hf α).aemeasurable,
      dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    simp only
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ hR x' y'
  have hRt : ∫⁻ x in ball x₀ R, ∫⁻ y in ball x (η * infDist x (ball x₀ R)ᶜ),
      ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y =
      J * (J * (K * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        ∫⁻ y in ball x (η * infDist x (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ),
          ENNReal.ofReal ((f (x₀ + R • x) - f (x₀ + R • y)) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)))) := by
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, hB]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x'
    rw [dydaS_setLIntegral_affine x₀ hR measurableSet_ball, dydaS_infDist x₀ hR x',
      show η * (R * infDist x' (ball 0 1)ᶜ) = R * (η * infDist x' (ball 0 1)ᶜ) by ring,
      dydaS_preimage_ball x₀ hR]
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y'
    exact dydaS_integrand f α x₀ hR x' y'
  rw [hL, hRt]
  calc J * (J * (K * _)) ≤ J * (J * (K * (ENNReal.ofReal c * _))) := by gcongr
    _ = _ := by ring

end QFS
