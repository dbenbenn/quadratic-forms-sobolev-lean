import QuadraticFormsSobolev.Dyda.Defs

/-! # Averaging over a sun

Dyda's Step 2 (p. 570) compares a pair `(x, y)` with pairs `(z, x)`, `(z, y)` for `z` in a ball
`G` (his "sun") at distance comparable to `|x − y|`. Here the sun is not chosen: the average runs
over the whole set `sunSet A C x y` of admissible `z`, which is measurable, and the hypothesis is
only that this set contains *some* ball of radius `ε |x − y|`. Near pairs of `Ω` are then
controlled by the pairs in `A`, with a constant that depends on `ε`, `C` and `d` only. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- The points `z` through which the pair `(x, y)` is averaged: both `(z, x)` and `(z, y)` lie in
`A`, and `z` is at distance between `|x − y|` and `C |x − y|` from each of `x` and `y`. -/
def sunSet (A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (C : ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {z | (z, x) ∈ A ∧ (z, y) ∈ A ∧ ‖x - y‖ ≤ ‖z - x‖ ∧ ‖z - x‖ ≤ C * ‖x - y‖ ∧
    ‖x - y‖ ≤ ‖z - y‖ ∧ ‖z - y‖ ≤ C * ‖x - y‖}

/-- `(u(a) − u(z))² / |z − a|^{2d+α}`. -/
noncomputable def sunψ (α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) (a z : EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((u a - u z) ^ 2 / (‖z - a‖ ^ d * ‖z - a‖ ^ ((d : ℝ) + α)))

/-- The one-sided integrand `1[(z, x) ∈ A, |x − y| ≤ |z − x|] ψ(x, z)`. -/
noncomputable def sunF (A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x y z : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      (q.2.2, q.1) ∈ A ∧ ‖q.1 - q.2.1‖ ≤ ‖q.2.2 - q.1‖}.indicator
    (fun q => sunψ α u q.1 q.2.2) (x, y, z)

lemma sun_real {a b c r s₁ s₂ C α : ℝ} (hα : 0 < α) (hr : 0 < r)
    (h₁ : r ≤ s₁) (h₁' : s₁ ≤ C * r) (h₂ : r ≤ s₂) (h₂' : s₂ ≤ C * r) :
    (a - c) ^ 2 / r ^ ((d : ℝ) + α) ≤ 2 * C ^ d * C ^ ((d : ℝ) + α) * r ^ d *
      ((a - b) ^ 2 / (s₁ ^ d * s₁ ^ ((d : ℝ) + α)) + (c - b) ^ 2 / (s₂ ^ d * s₂ ^ ((d : ℝ) + α))) := by
  set e : ℝ := (d : ℝ) + α with he
  have he0 : 0 < e := by positivity
  have hC0 : 0 < C := by
    by_contra h; push Not at h; nlinarith
  have hkey : ∀ s, r ≤ s → s ≤ C * r → 1 / r ^ e ≤ C ^ d * C ^ e * r ^ d / (s ^ d * s ^ e) := by
    intro s hs hs'
    have hs0 : 0 < s := hr.trans_le hs
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h1 : s ^ d ≤ C ^ d * r ^ d := by rw [← mul_pow]; exact pow_le_pow_left₀ hs0.le hs' d
    have h2 : s ^ e ≤ C ^ e * r ^ e := by
      rw [← Real.mul_rpow hC0.le hr.le]; exact Real.rpow_le_rpow hs0.le hs' he0.le
    calc s ^ d * s ^ e ≤ (C ^ d * r ^ d) * (C ^ e * r ^ e) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C ^ d * C ^ e * r ^ d * r ^ e := by ring
  have k1 := hkey s₁ h₁ h₁'
  have k2 := hkey s₂ h₂ h₂'
  have hsq : (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (c - b) ^ 2 := by
    nlinarith [sq_nonneg (a - 2 * b + c)]
  calc (a - c) ^ 2 / r ^ e = (a - c) ^ 2 * (1 / r ^ e) := by ring
    _ ≤ (2 * (a - b) ^ 2 + 2 * (c - b) ^ 2) * (1 / r ^ e) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = 2 * (a - b) ^ 2 * (1 / r ^ e) + 2 * (c - b) ^ 2 * (1 / r ^ e) := by ring
    _ ≤ 2 * (a - b) ^ 2 * (C ^ d * C ^ e * r ^ d / (s₁ ^ d * s₁ ^ e)) +
          2 * (c - b) ^ 2 * (C ^ d * C ^ e * r ^ d / (s₂ ^ d * s₂ ^ e)) := by
        gcongr
    _ = _ := by ring

lemma measurable_sunψ (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => sunψ α u p.1 p.2 := by
  unfold sunψ; fun_prop

lemma measurable_sunF {A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    (hA : MeasurableSet A) (α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) => sunF A α u q.1 q.2.1 q.2.2 := by
  have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | (q.2.2, q.1) ∈ A ∧ ‖q.1 - q.2.1‖ ≤ ‖q.2.2 - q.1‖} :=
    (hA.preimage (by fun_prop)).inter (measurableSet_le
      (by fun_prop : Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d) => ‖q.1 - q.2.1‖)
      (by fun_prop : Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d) => ‖q.2.2 - q.1‖))
  exact ((measurable_sunψ α hu).comp (by fun_prop : Measurable fun q : EuclideanSpace ℝ (Fin d) ×
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (q.1, q.2.2))).indicator hS

/-- `∫_y F(x, y, z) = V · 1_A(z, x) U(z, x)`: the `y`-integral of the one-sided integrand. -/
lemma lintegral_sunF {A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (α : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x z : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ y, sunF A α u x y z = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
      A.indicator (fun p => U d α u p.1 p.2) (z, x) := by
  have hF : (fun y => sunF A α u x y z) = (closedBall x ‖z - x‖).indicator
      (fun _ => A.indicator (fun p => sunψ α u p.2 p.1) (z, x)) := by
    funext y
    by_cases h1 : (z, x) ∈ A <;> by_cases h2 : ‖x - y‖ ≤ ‖z - x‖ <;>
      simp [sunF, Set.indicator, h1, h2, mem_closedBall, dist_eq_norm, norm_sub_rev y x]
  rw [hF, lintegral_indicator_const measurableSet_closedBall,
    Measure.addHaar_closedBall _ _ (norm_nonneg _), finrank_euclideanSpace_fin]
  by_cases h1 : (z, x) ∈ A
  swap
  · simp [Set.indicator_of_notMem h1]
  rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
  by_cases hzx : z = x
  · subst hzx; simp [sunψ, U_self]
  have hs : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have key : ENNReal.ofReal (‖z - x‖ ^ d) *
      ENNReal.ofReal ((u x - u z) ^ 2 / (‖z - x‖ ^ d * ‖z - x‖ ^ ((d : ℝ) + α))) = U d α u z x := by
    rw [← ENNReal.ofReal_mul (by positivity), U]
    congr 1
    field_simp
    ring
  simp only [sunψ]
  calc _ = volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (ENNReal.ofReal (‖z - x‖ ^ d) *
      ENNReal.ofReal ((u x - u z) ^ 2 / (‖z - x‖ ^ d * ‖z - x‖ ^ ((d : ℝ) + α)))) := by ring
    _ = _ := by rw [key]

/-- **Averaging over a sun.** -/
theorem sun_bound {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A)
    {ρ ε C α : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) (hα : 0 < α) (hα2 : α ≤ 2)
    (hsun : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖x - y‖ < ρ →
      ∃ G, ball G (ε * ‖x - y‖) ⊆ sunSet A C x y)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x ρ, U d α u x y
      ≤ ENNReal.ofReal (4 * C ^ d * C ^ ((d : ℝ) + 2) / ε ^ d) *
          ∫⁻ z, ∫⁻ w, A.indicator (fun p => U d α u p.1 p.2) (z, w) := by
  set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hVdef
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set K : ℝ := 2 * C ^ d * C ^ ((d : ℝ) + α) / ε ^ d with hKdef
  set c₀ : ℝ≥0∞ := V⁻¹ * ENNReal.ofReal K with hc₀
  have hc₀t : c₀ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0) ENNReal.ofReal_ne_top
  set F := sunF A α u with hFdef
  have hFm := measurable_sunF hA α hu
  have hFz : ∀ x y, Measurable (F x y) := fun x y =>
    hFm.comp (f := fun z : EuclideanSpace ℝ (Fin d) => (x, y, z)) (by fun_prop)
  have hFyz : ∀ x, Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      F x p.1 p.2 := fun x =>
    hFm.comp (f := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => (x, p.1, p.2))
      (by fun_prop)
  have hFxy : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z, F p.1 p.2 z := by
    have : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => F q.1.1 q.1.2 q.2 :=
      hFm.comp (f := fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => (q.1.1, q.1.2, q.2)) (by fun_prop)
    exact this.lintegral_prod_right'
  have hFx : ∀ x, Measurable fun y => ∫⁻ z, F x y z := fun x =>
    hFxy.comp (f := fun y : EuclideanSpace ℝ (Fin d) => (x, y)) (by fun_prop)
  have hFxx : Measurable fun x => ∫⁻ y, ∫⁻ z, F x y z := hFxy.lintegral_prod_right'
  -- the pointwise bound
  have hpt : ∀ x ∈ Ω, ∀ y ∈ Ω ∩ ball x ρ,
      U d α u x y ≤ c₀ * ∫⁻ z, (F x y z + F y x z) := by
    rintro x hx y ⟨hy, hyx⟩
    by_cases hxy : x = y
    · subst hxy; rw [U_self]; exact zero_le
    set r := ‖x - y‖ with hr_def
    have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hrρ : r < ρ := by rw [mem_ball, dist_eq_norm, norm_sub_rev] at hyx; exact hyx
    obtain ⟨G, hG⟩ := hsun x hx y hy hxy hrρ
    have hz : ∀ z ∈ ball G (ε * r), U d α u x y ≤
        ENNReal.ofReal (2 * C ^ d * C ^ ((d : ℝ) + α) * r ^ d) * (F x y z + F y x z) := by
      intro z hzG
      obtain ⟨hA1, hA2, h1, h1', h2, h2'⟩ := hG hzG
      have m1 : (x, y, z) ∈ {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) | (q.2.2, q.1) ∈ A ∧ ‖q.1 - q.2.1‖ ≤ ‖q.2.2 - q.1‖} :=
        ⟨hA1, h1⟩
      have m2 : (y, x, z) ∈ {q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin d) | (q.2.2, q.1) ∈ A ∧ ‖q.1 - q.2.1‖ ≤ ‖q.2.2 - q.1‖} :=
        ⟨hA2, by simp only; rwa [norm_sub_rev y x]⟩
      rw [hFdef, sunF, sunF, Set.indicator_of_mem m1, Set.indicator_of_mem m2]
      simp only [U, sunψ]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (sun_real hα hr h1 h1' h2 h2')
    have hmz : Measurable fun z => F x y z + F y x z := (hFz x y).add (hFz y x)
    set a : ℝ≥0∞ := ENNReal.ofReal ((ε * r) ^ d) with ha_def
    have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hvol : volume (ball G (ε * r)) = a * V := by
      rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace_fin]
    have hsplit : ENNReal.ofReal (2 * C ^ d * C ^ ((d : ℝ) + α) * r ^ d) = ENNReal.ofReal K * a := by
      rw [← ENNReal.ofReal_mul (by positivity), hKdef, mul_pow]
      congr 1
      field_simp
    set I := ∫⁻ z, (F x y z + F y x z)
    have h1 : a * V * U d α u x y ≤ ENNReal.ofReal K * a * I := by
      calc a * V * U d α u x y = ∫⁻ _ in ball G (ε * r), U d α u x y := by
            rw [setLIntegral_const, hvol, mul_comm]
        _ ≤ ∫⁻ z in ball G (ε * r),
              ENNReal.ofReal (2 * C ^ d * C ^ ((d : ℝ) + α) * r ^ d) * (F x y z + F y x z) :=
            setLIntegral_mono' measurableSet_ball hz
        _ ≤ ∫⁻ z, ENNReal.ofReal (2 * C ^ d * C ^ ((d : ℝ) + α) * r ^ d) * (F x y z + F y x z) :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal K * a * I := by rw [lintegral_const_mul _ hmz, hsplit]
    have hav : a * V ≠ 0 := mul_ne_zero ha0 hV0
    have havt : a * V ≠ ⊤ := ENNReal.mul_ne_top hat hVt
    calc U d α u x y = (a * V)⁻¹ * (a * V * U d α u x y) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hav havt, one_mul]
      _ ≤ (a * V)⁻¹ * (ENNReal.ofReal K * a * I) := by gcongr
      _ = (a⁻¹ * a) * (V⁻¹ * ENNReal.ofReal K * I) := by
          rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]; ring
      _ = c₀ * I := by rw [ENNReal.inv_mul_cancel ha0 hat, one_mul]
  -- the one-sided triple integral
  set X := ∫⁻ x, ∫⁻ y, ∫⁻ z, F x y z with hX
  set R := ∫⁻ z, ∫⁻ w, A.indicator (fun p => U d α u p.1 p.2) (z, w)
  have hXR : X = V * R := by
    have hR : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        A.indicator (fun p => U d α u p.1 p.2) (p.2, p.1) :=
      ((measurable_U α hu).indicator hA).comp measurable_swap
    calc X = ∫⁻ x, ∫⁻ z, ∫⁻ y, F x y z :=
          lintegral_congr fun x => lintegral_lintegral_swap (hFyz x).aemeasurable
      _ = ∫⁻ x, ∫⁻ z, V * A.indicator (fun p => U d α u p.1 p.2) (z, x) :=
          lintegral_congr fun x => lintegral_congr fun z => lintegral_sunF α u x z
      _ = V * ∫⁻ x, ∫⁻ z, A.indicator (fun p => U d α u p.1 p.2) (z, x) := by
          rw [← lintegral_const_mul' _ _ hVt]
          exact lintegral_congr fun x => lintegral_const_mul' _ _ hVt
      _ = V * R := by rw [lintegral_lintegral_swap hR.aemeasurable]
  have hK : ENNReal.ofReal (2 * K) ≤ ENNReal.ofReal (4 * C ^ d * C ^ ((d : ℝ) + 2) / ε ^ d) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hKdef]
    have : C ^ ((d : ℝ) + α) ≤ C ^ ((d : ℝ) + 2) :=
      Real.rpow_le_rpow_of_exponent_le hC (by linarith)
    have hC0 : 0 ≤ C ^ d := by positivity
    calc 2 * (2 * C ^ d * C ^ ((d : ℝ) + α) / ε ^ d)
        = 4 * C ^ d * C ^ ((d : ℝ) + α) / ε ^ d := by ring
      _ ≤ 4 * C ^ d * C ^ ((d : ℝ) + 2) / ε ^ d := by gcongr
  calc ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x ρ, U d α u x y
      ≤ ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x ρ, c₀ * ∫⁻ z, (F x y z + F y x z) :=
        setLIntegral_mono' hΩ fun x hx =>
          setLIntegral_mono' (hΩ.inter measurableSet_ball) fun y hy => hpt x hx y hy
    _ ≤ ∫⁻ x, ∫⁻ y, c₀ * ∫⁻ z, (F x y z + F y x z) :=
        (setLIntegral_le_lintegral _ _).trans
          (lintegral_mono fun x => setLIntegral_le_lintegral _ _)
    _ = c₀ * (X + ∫⁻ x, ∫⁻ y, ∫⁻ z, F y x z) := by
        have e1 : ∀ x y, ∫⁻ z, (F x y z + F y x z) = (∫⁻ z, F x y z) + ∫⁻ z, F y x z :=
          fun x y => lintegral_add_left (hFz x y) _
        calc ∫⁻ x, ∫⁻ y, c₀ * ∫⁻ z, (F x y z + F y x z)
            = ∫⁻ x, c₀ * ∫⁻ y, ∫⁻ z, (F x y z + F y x z) :=
              lintegral_congr fun x => lintegral_const_mul' _ _ hc₀t
          _ = c₀ * ∫⁻ x, ∫⁻ y, ∫⁻ z, (F x y z + F y x z) := lintegral_const_mul' _ _ hc₀t
          _ = _ := by
              congr 1
              simp_rw [e1]
              rw [lintegral_congr fun x => lintegral_add_left (hFx x) _]
              exact lintegral_add_left hFxx _
    _ = c₀ * (X + X) := by
        rw [lintegral_lintegral_swap (f := fun x y => ∫⁻ z, F y x z)
          ((hFxy.comp measurable_swap).aemeasurable)]
    _ = ENNReal.ofReal (2 * K) * R := by
        rw [hXR, hc₀, ← two_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        have : V⁻¹ * ENNReal.ofReal K * (2 * (V * R)) = (V⁻¹ * V) * (2 * ENNReal.ofReal K * R) := by
          ring
        rw [this, ENNReal.inv_mul_cancel hV0 hVt, one_mul]
    _ ≤ _ := by gcongr

end Dyda
