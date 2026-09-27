import QuadraticFormsSobolev.Density.Mollify
import QuadraticFormsSobolev.Density.Cutoff
import QuadraticFormsSobolev.Density.TranslationGen

/-!
# Density on a domain: one piece

For `f` on `Ω`, let `F₀ = f·1_Ω` and `G(x, y) = 1_{Ω×Ω}(x,y)(f(y) − f(x))|x − y|^{−(d+α)/2}`, so that
`∫ G² = |f|²_{H^{α/2}(Ω)}`. Shift by `v` and mollify: `m = ρ_n ⋆ F₀(· + v)`, `u = f − m`. If `δ`
bounds the `L²` translation errors of `F₀` and of `G` for the shifts `w = v − t`, `|t| < 1/(n+1)`,
then
* `∫_U u² ≤ δ` for any `U ⊆ Ω`, and
* `∫_{U×U} (u(y) − u(x))² |x − y|^{−d−α} ≤ δ` as soon as every shift keeps `U` inside `Ω`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

set_option hygiene false in
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- `F₀ = f·1_Ω`. -/
noncomputable def F0 (Ω : Set 𝔼) (f : 𝔼 → ℝ) : 𝔼 → ℝ := Ω.indicator f

/-- `G(x, y) = 1_{Ω×Ω}(f(y) − f(x))|x − y|^{−(d+α)/2}`. -/
noncomputable def Gq (Ω : Set 𝔼) (α : ℝ) (f : 𝔼 → ℝ) : 𝔼 × 𝔼 → ℝ :=
  (Ω ×ˢ Ω).indicator fun p => (f p.2 - f p.1) * ‖p.1 - p.2‖ ^ (-((d : ℝ) + α) / 2)

/-- The error of one piece: `u = f − ρ_n ⋆ F₀(· + v)`. -/
noncomputable def pieceU (Ω : Set 𝔼) (f : 𝔼 → ℝ) (v : 𝔼) (n : ℕ) : 𝔼 → ℝ :=
  fun x => f x - mollify n (fun y => F0 Ω f (y + v)) x

lemma ofReal_sq_mul_rpow (a r α : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal ((a * r ^ (-((d : ℝ) + α) / 2)) ^ 2) =
      ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (r ^ (-(d : ℝ) - α)) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow, ← Real.rpow_natCast (r ^ _),
    ← Real.rpow_mul hr]
  congr 3; push_cast; ring

lemma measurable_F0 {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ} (hf : Measurable f) :
    Measurable (F0 Ω f) := hf.indicator hΩ

lemma measurable_Gq {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (α : ℝ) {f : 𝔼 → ℝ} (hf : Measurable f) :
    Measurable (Gq Ω α f) :=
  (by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
    (f p.2 - f p.1) * ‖p.1 - p.2‖ ^ (-((d : ℝ) + α) / 2)).indicator (hΩ.prod hΩ)

/-- `∫ G² = |f|²_{H^{α/2}(Ω)}`. -/
lemma lintegral_Gq_sq {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) (α : ℝ) (f : 𝔼 → ℝ) :
    ∫⁻ p, ENNReal.ofReal (Gq Ω α f p ^ 2) = formHs Ω α f := by
  unfold formHs form
  rw [← lintegral_indicator (hΩ.prod hΩ)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ Ω ×ˢ Ω
  · rw [Gq, indicator_of_mem hp, indicator_of_mem hp, ofReal_sq_mul_rpow _ _ _ (norm_nonneg _)]
    rfl
  · rw [Gq, indicator_of_notMem hp, indicator_of_notMem hp]; simp

lemma memLp_F0 {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) :
    MemLp (F0 Ω f) 2 volume :=
  (memLp_indicator_iff_restrict hΩ).mpr hf

lemma memLp_F0_shift {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (v : 𝔼) :
    MemLp (fun y => F0 Ω f (y + v)) 2 volume :=
  (memLp_F0 hΩ hf).comp_measurePreserving (measurePreserving_add_right volume v)

/-- **The `L²` error of a piece.** -/
lemma piece_sq_le {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.restrict Ω)) {U : Set 𝔼} (hU : MeasurableSet U) (hUΩ : U ⊆ Ω) (v : 𝔼)
    (n : ℕ) {δ : ℝ≥0∞}
    (hT1 : ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ x, ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) ≤ δ) :
    ∫⁻ x in U, ENNReal.ofReal (pieceU Ω f v n x ^ 2) ≤ δ := by
  have hF := measurable_F0 hΩ hfm
  have hloc := (memLp_F0_shift hΩ hf v).locallyIntegrable (by norm_num)
  have hρm : Measurable (molli (d := d) n) := (continuous_molli n).measurable
  have hpt : ∀ x ∈ U, ENNReal.ofReal (pieceU Ω f v n x ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) *
        ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) := by
    intro x hx
    have hfx : f x = F0 Ω f x := (indicator_of_mem (hUΩ hx) f).symm
    have e : pieceU Ω f v n x = ∫ t, molli n t * (F0 Ω f x - F0 Ω f (x - t + v)) := by
      rw [pieceU, mollify_apply, hfx,
        show (fun t => molli n t * (F0 Ω f x - F0 Ω f (x - t + v))) =
          fun t => molli n t * F0 Ω f x - molli n t * F0 Ω f (x - t + v) by funext t; ring,
        integral_sub ((integrable_molli n).mul_const _) (integrable_molli_mul hloc n x),
        integral_mul_const, integral_molli, one_mul]
    rw [e]
    have hint : Integrable fun t => molli n t * (F0 Ω f x - F0 Ω f (x - t + v)) := by
      rw [show (fun t => molli n t * (F0 Ω f x - F0 Ω f (x - t + v))) =
          fun t => molli n t * F0 Ω f x - molli n t * F0 Ω f (x - t + v) by funext t; ring]
      exact ((integrable_molli n).mul_const _).sub (integrable_molli_mul hloc n x)
    refine (sq_mollify_le (by fun_prop) hint).trans (lintegral_mono fun t => ?_)
    rw [show x - t + v = x - -(v - t) by abel, show (F0 Ω f x - F0 Ω f (x - -(v - t))) ^ 2 =
      (F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2 by ring]
  have hm : Measurable (Function.uncurry fun x t : 𝔼 =>
      ENNReal.ofReal (molli n t) * ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2)) := by
    unfold Function.uncurry; fun_prop
  calc ∫⁻ x in U, ENNReal.ofReal (pieceU Ω f v n x ^ 2)
      ≤ ∫⁻ x in U, ∫⁻ t, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) :=
        setLIntegral_mono' hU hpt
    _ ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t, ENNReal.ofReal (molli n t) *
          ∫⁻ x, ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
        exact lintegral_congr fun t => lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ t, ENNReal.ofReal (molli n t) * δ := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ ball (0 : 𝔼) (1 / (n + 1))
        · gcongr; exact hT1 t ht
        · rw [molli_eq_zero ht]; simp
    _ = δ := by rw [lintegral_mul_const _ hρm.ennreal_ofReal, lintegral_molli, one_mul]

/-- **The seminorm error of a piece, on `U × U`.** -/
lemma piece_diff_le {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.restrict Ω)) (α : ℝ) {U : Set 𝔼} (hU : MeasurableSet U) (hUΩ : U ⊆ Ω)
    (v : 𝔼) (n : ℕ) {δ : ℝ≥0∞}
    (hshift : ∀ x ∈ U, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)), x - -(v - t) ∈ Ω)
    (hT2 : ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ p, ENNReal.ofReal ((Gq Ω α f (p - -((v - t, v - t) : 𝔼 × 𝔼)) - Gq Ω α f p) ^ 2) ≤ δ) :
    ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((pieceU Ω f v n p.2 - pieceU Ω f v n p.1) ^ 2) *
      jumpKernel d α p.1 p.2 ≤ δ := by
  have hF := measurable_F0 hΩ hfm
  have hG := measurable_Gq hΩ α hfm
  have hloc := (memLp_F0_shift hΩ hf v).locallyIntegrable (by norm_num)
  have hρm : Measurable (molli (d := d) n) := (continuous_molli n).measurable
  set W : 𝔼 → 𝔼 × 𝔼 := fun t => ((v - t, v - t) : 𝔼 × 𝔼) with hW
  have hpt : ∀ p ∈ U ×ˢ U, ENNReal.ofReal ((pieceU Ω f v n p.2 - pieceU Ω f v n p.1) ^ 2) *
      jumpKernel d α p.1 p.2 ≤
      ∫⁻ t, ENNReal.ofReal (molli n t) *
        ENNReal.ofReal ((Gq Ω α f (p - -W t) - Gq Ω α f p) ^ 2) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only at hx hy ⊢
    set r := ‖x - y‖ ^ (-((d : ℝ) + α) / 2) with hr
    rw [jumpKernel, ← ofReal_sq_mul_rpow _ _ _ (norm_nonneg _)]
    -- the difference quotient as one integral against `ρ`
    have hint1 : Integrable fun t => molli n t * ((f y - f x) * r -
        (F0 Ω f (y - t + v) - F0 Ω f (x - t + v)) * r) := by
      rw [show (fun t => molli n t * ((f y - f x) * r -
          (F0 Ω f (y - t + v) - F0 Ω f (x - t + v)) * r)) =
          fun t => molli n t * ((f y - f x) * r) -
            (molli n t * F0 Ω f (y - t + v) - molli n t * F0 Ω f (x - t + v)) * r by
          funext t; ring]
      exact ((integrable_molli n).mul_const _).sub
        (((integrable_molli_mul hloc n y).sub (integrable_molli_mul hloc n x)).mul_const _)
    have e1 : (pieceU Ω f v n y - pieceU Ω f v n x) * r = ∫ t, molli n t * ((f y - f x) * r -
        (F0 Ω f (y - t + v) - F0 Ω f (x - t + v)) * r) := by
      have hm := mollify_sub_apply hloc n y x
      rw [show (fun t => molli n t * ((f y - f x) * r -
          (F0 Ω f (y - t + v) - F0 Ω f (x - t + v)) * r)) =
          fun t => molli n t * ((f y - f x) * r) -
            (molli n t * (F0 Ω f (y - t + v) - F0 Ω f (x - t + v))) * r by funext t; ring,
        integral_sub ((integrable_molli n).mul_const _) ?_, integral_mul_const, integral_molli,
        integral_mul_const, ← hm, pieceU, pieceU]
      · ring
      · refine Integrable.mul_const ?_ _
        rw [show (fun t => molli n t * (F0 Ω f (y - t + v) - F0 Ω f (x - t + v))) =
          fun t => molli n t * F0 Ω f (y - t + v) - molli n t * F0 Ω f (x - t + v) by
          funext t; ring]
        exact (integrable_molli_mul hloc n y).sub (integrable_molli_mul hloc n x)
    have e2 : (fun t => molli n t * ((f y - f x) * r -
        (F0 Ω f (y - t + v) - F0 Ω f (x - t + v)) * r)) =
        fun t => molli n t * (Gq Ω α f (x, y) - Gq Ω α f ((x, y) - -W t)) := by
      funext t
      by_cases ht : t ∈ ball (0 : 𝔼) (1 / (n + 1))
      · have hx' := hshift x hx t ht
        have hy' := hshift y hy t ht
        have hpq : ((x, y) - -W t : 𝔼 × 𝔼) = (x - -(v - t), y - -(v - t)) := rfl
        rw [hpq]
        unfold Gq
        rw [indicator_of_mem (show (x, y) ∈ Ω ×ˢ Ω from ⟨hUΩ hx, hUΩ hy⟩),
          indicator_of_mem (show (x - -(v - t), y - -(v - t)) ∈ Ω ×ˢ Ω from ⟨hx', hy'⟩)]
        simp only
        rw [show x - -(v - t) - (y - -(v - t)) = x - y by abel,
          show y - t + v = y - -(v - t) by abel, show x - t + v = x - -(v - t) by abel]
        unfold F0
        rw [indicator_of_mem hx', indicator_of_mem hy']
      · rw [molli_eq_zero ht]; simp
    rw [e1, e2]
    have hint2 : Integrable fun t => molli n t * (Gq Ω α f (x, y) - Gq Ω α f ((x, y) - -W t)) :=
      e2 ▸ hint1
    refine (sq_mollify_le (by fun_prop) hint2).trans (lintegral_mono fun t => ?_)
    rw [show (Gq Ω α f (x, y) - Gq Ω α f ((x, y) - -W t)) ^ 2 =
      (Gq Ω α f ((x, y) - -W t) - Gq Ω α f (x, y)) ^ 2 by ring]
  have hm : Measurable (Function.uncurry fun (p : 𝔼 × 𝔼) (t : 𝔼) =>
      ENNReal.ofReal (molli n t) * ENNReal.ofReal ((Gq Ω α f (p - -W t) - Gq Ω α f p) ^ 2)) := by
    unfold Function.uncurry; simp only [hW]; fun_prop
  calc ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((pieceU Ω f v n p.2 - pieceU Ω f v n p.1) ^ 2) *
        jumpKernel d α p.1 p.2
      ≤ ∫⁻ p in U ×ˢ U, ∫⁻ t, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((Gq Ω α f (p - -W t) - Gq Ω α f p) ^ 2) := setLIntegral_mono' (hU.prod hU) hpt
    _ ≤ ∫⁻ p, ∫⁻ t, ENNReal.ofReal (molli n t) *
          ENNReal.ofReal ((Gq Ω α f (p - -W t) - Gq Ω α f p) ^ 2) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t, ENNReal.ofReal (molli n t) *
          ∫⁻ p, ENNReal.ofReal ((Gq Ω α f (p - -W t) - Gq Ω α f p) ^ 2) := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
        refine lintegral_congr fun t => lintegral_const_mul _ ?_
        simp only [hW]; fun_prop
    _ ≤ ∫⁻ t, ENNReal.ofReal (molli n t) * δ := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ ball (0 : 𝔼) (1 / (n + 1))
        · gcongr; exact hT2 t ht
        · rw [molli_eq_zero ht]; simp
    _ = δ := by rw [lintegral_mul_const _ hρm.ennreal_ofReal, lintegral_molli, one_mul]

/-- `J_L = ∫ min(1, L²|h|²) |h|^{−d−α} dh`. -/
noncomputable def kerJ (d : ℕ) (α L : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (min 1 (L ^ 2 * ‖h‖ ^ 2)) * wK d α h

/-- `T_{δ₀} = ∫_{|h| ≥ δ₀} |h|^{−d−α} dh`. -/
noncomputable def kerT (d : ℕ) (α δ₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : EuclideanSpace ℝ (Fin d), {h | δ₀ ≤ ‖h‖}.indicator (wK d α) h

lemma kerJ_lt_top (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (L : ℝ) : kerJ d α L < ⊤ := by
  have hfin := lintegral_minKernel_lt_top hd hα0 hα2
  calc kerJ d α L ≤ ∫⁻ h : 𝔼, ENNReal.ofReal (1 + L ^ 2) *
        ENNReal.ofReal (min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)) := by
        refine lintegral_mono fun h => ?_
        simp only [wK]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hw : 0 ≤ ‖h‖ ^ (-(d : ℝ) - α) := by positivity
        have hmin : min 1 (L ^ 2 * ‖h‖ ^ 2) ≤ (1 + L ^ 2) * min 1 (‖h‖ ^ 2) := by
          rcases le_total 1 (‖h‖ ^ 2) with h1 | h1
          · rw [min_eq_left h1]; nlinarith [min_le_left 1 (L ^ 2 * ‖h‖ ^ 2), sq_nonneg L]
          · rw [min_eq_right h1]
            have := min_le_right 1 (L ^ 2 * ‖h‖ ^ 2)
            nlinarith [sq_nonneg ‖h‖, sq_nonneg L]
        calc min 1 (L ^ 2 * ‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)
            ≤ (1 + L ^ 2) * min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α) := by gcongr
          _ = _ := by ring
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

lemma kerT_lt_top (hd : 1 ≤ d) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    kerT d α δ₀ < ⊤ := by
  have hfin := lintegral_minKernel_lt_top hd hα0 hα2
  set c := min 1 (δ₀ ^ 2) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  calc kerT d α δ₀ ≤ ∫⁻ h : 𝔼, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)) := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ {h : 𝔼 | δ₀ ≤ ‖h‖}
        · rw [indicator_of_mem hh, wK, ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hcle : c ≤ min 1 (‖h‖ ^ 2) := by
            have : δ₀ ^ 2 ≤ ‖h‖ ^ 2 := by
              have : δ₀ ≤ ‖h‖ := hh
              nlinarith
            exact min_le_min le_rfl this
          have hw : 0 ≤ ‖h‖ ^ (-(d : ℝ) - α) := by positivity
          calc ‖h‖ ^ (-(d : ℝ) - α) = c⁻¹ * (c * ‖h‖ ^ (-(d : ℝ) - α)) := by field_simp
            _ ≤ c⁻¹ * (min 1 (‖h‖ ^ 2) * ‖h‖ ^ (-(d : ℝ) - α)) := by gcongr
        · rw [indicator_of_notMem hh]; exact zero_le
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

lemma lintegral_kerJ (α L : ℝ) (x : 𝔼) :
    ∫⁻ y, ENNReal.ofReal (min 1 (L ^ 2 * ‖x - y‖ ^ 2)) * jumpKernel d α x y = kerJ d α L := by
  rw [kerJ, ← lintegral_add_left_eq_self _ x]
  refine lintegral_congr fun h => ?_
  simp only [jumpKernel, wK, sub_add_cancel_left, norm_neg]

lemma lintegral_kerT (α δ₀ : ℝ) (x : 𝔼) :
    ∫⁻ y, {y | δ₀ ≤ ‖x - y‖}.indicator (fun y => jumpKernel d α x y) y = kerT d α δ₀ := by
  rw [kerT, ← lintegral_add_left_eq_self _ x]
  refine lintegral_congr fun h => ?_
  by_cases hh : δ₀ ≤ ‖h‖
  · rw [indicator_of_mem (show x + h ∈ {y | δ₀ ≤ ‖x - y‖} by
        simp only [mem_ofPred_eq, sub_add_cancel_left, norm_neg]; exact hh),
      indicator_of_mem (show h ∈ {h : 𝔼 | δ₀ ≤ ‖h‖} from hh)]
    simp only [jumpKernel, wK, sub_add_cancel_left, norm_neg]
  · rw [indicator_of_notMem (show x + h ∉ {y | δ₀ ≤ ‖x - y‖} by
        simp only [mem_ofPred_eq, sub_add_cancel_left, norm_neg]; exact hh),
      indicator_of_notMem (show h ∉ {h : 𝔼 | δ₀ ≤ ‖h‖} from hh)]

/-- The three dominating terms of a cut-off difference. -/
noncomputable def pieceB (U : Set 𝔼) (α L δ₀ : ℝ) (u : 𝔼 → ℝ) (p : 𝔼 × 𝔼) : ℝ≥0∞ :=
  (U ×ˢ U).indicator (fun p => 2 * (ENNReal.ofReal ((u p.2 - u p.1) ^ 2) * jumpKernel d α p.1 p.2) +
      2 * (ENNReal.ofReal (u p.1 ^ 2) *
        (ENNReal.ofReal (min 1 (L ^ 2 * ‖p.1 - p.2‖ ^ 2)) * jumpKernel d α p.1 p.2))) p +
    {p : 𝔼 × 𝔼 | p.1 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖}.indicator
      (fun p => ENNReal.ofReal (u p.1 ^ 2) * jumpKernel d α p.1 p.2) p +
    {p : 𝔼 × 𝔼 | p.2 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖}.indicator
      (fun p => ENNReal.ofReal (u p.2 ^ 2) * jumpKernel d α p.1 p.2) p

/-- **Leibniz for a cut-off difference, with the far pairs apart.** -/
lemma piece_pointwise {Ω U : Set 𝔼} {ψ : 𝔼 → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    {L : ℝ} (hL : ∀ x y, |ψ x - ψ y| ≤ L * ‖x - y‖) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsupp : ∀ x ∈ Ω, ψ x ≠ 0 → ∀ y ∈ Ω, ‖x - y‖ < δ₀ → y ∈ U) (α : ℝ) (u : 𝔼 → ℝ)
    {x y : 𝔼} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ENNReal.ofReal ((ψ y * u y - ψ x * u x) ^ 2) * jumpKernel d α x y ≤
      pieceB U α L δ₀ u (x, y) := by
  unfold pieceB
  have hk0 : ∀ x y : 𝔼, 0 ≤ jumpKernel d α x y := fun _ _ => zero_le
  by_cases hxy : x ∈ U ∧ y ∈ U
  · rw [indicator_of_mem (show (x, y) ∈ U ×ˢ U from hxy), add_assoc]
    refine le_trans ?_ le_self_add
    simp only
    have hsq : (ψ y * u y - ψ x * u x) ^ 2 ≤
        2 * (u y - u x) ^ 2 + 2 * (u x ^ 2 * min 1 (L ^ 2 * ‖x - y‖ ^ 2)) := by
      have e : ψ y * u y - ψ x * u x = ψ y * (u y - u x) + u x * (ψ y - ψ x) := by ring
      have h1 : (ψ y * (u y - u x)) ^ 2 ≤ (u y - u x) ^ 2 := by
        rw [mul_pow]
        have := hψ0 y; have := hψ1 y
        have : ψ y ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (u y - u x)]
      have h2 : (u x * (ψ y - ψ x)) ^ 2 ≤ u x ^ 2 * min 1 (L ^ 2 * ‖x - y‖ ^ 2) := by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) (sq_nonneg _)
        · have := hψ0 x; have := hψ1 x; have := hψ0 y; have := hψ1 y; nlinarith
        · have hl := hL y x
          rw [← mul_pow, norm_sub_rev]
          exact sq_le_sq' (by linarith [(abs_le.mp hl).1]) (abs_le.mp hl).2
      rw [e]
      nlinarith [sq_nonneg (ψ y * (u y - u x) - u x * (ψ y - ψ x))]
    calc ENNReal.ofReal ((ψ y * u y - ψ x * u x) ^ 2) * jumpKernel d α x y
        ≤ ENNReal.ofReal (2 * (u y - u x) ^ 2 + 2 * (u x ^ 2 * min 1 (L ^ 2 * ‖x - y‖ ^ 2))) *
            jumpKernel d α x y := by gcongr
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (sq_nonneg _)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  · have hδ0 : ‖x - x‖ < δ₀ := by simpa using hδ₀
    by_cases hψx : ψ x = 0
    · by_cases hψy : ψ y = 0
      · simp [hψx, hψy]
      · have hyU : y ∈ U := hsupp y hy hψy y hy (by simpa using hδ₀)
        have hxU : x ∉ U := fun h => hxy ⟨h, hyU⟩
        have hfar : δ₀ ≤ ‖x - y‖ := by
          by_contra h; push Not at h
          exact hxU (hsupp y hy hψy x hx (by rwa [norm_sub_rev]))
        rw [indicator_of_mem (show (x, y) ∈ {p : 𝔼 × 𝔼 | p.2 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖} from
          ⟨hyU, hfar⟩)]
        refine le_trans ?_ le_add_self
        simp only [hψx, zero_mul, sub_zero]
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [mul_pow]
        have := hψ0 y; have := hψ1 y
        have : ψ y ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (u y)]
    · have hxU : x ∈ U := hsupp x hx hψx x hx (by simpa using hδ₀)
      have hyU : y ∉ U := fun h => hxy ⟨hxU, h⟩
      have hfar : δ₀ ≤ ‖x - y‖ := by
        by_contra h; push Not at h
        exact hyU (hsupp x hx hψx y hy h)
      have hψy : ψ y = 0 := by
        by_contra h
        exact hyU (hsupp y hy h y hy (by simpa using hδ₀))
      rw [indicator_of_mem (show (x, y) ∈ {p : 𝔼 × 𝔼 | p.1 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖} from
        ⟨hxU, hfar⟩)]
      refine le_trans ?_ (le_trans le_add_self le_self_add)
      simp only [hψy, zero_mul, zero_sub, neg_sq]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      rw [mul_pow]
      have := hψ0 x; have := hψ1 x
      have : ψ x ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (u x)]

lemma setLIntegral_prod_univ {U : Set 𝔼} (F : 𝔼 × 𝔼 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in U ×ˢ univ, F p = ∫⁻ x in U, ∫⁻ y, F (x, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ hF.aemeasurable]

/-- **One piece.** For a cutoff `ψ` with values in `[0, 1]` and Lipschitz constant `L`, whose
support is `δ₀`-inside a region `U` on which the shifts stay in `Ω`, the `L²(Ω)` norm and the
`H^{α/2}(Ω)` seminorm of `ψ u` are at most `(3 + 2 J_L + 2 T_{δ₀}) δ`. -/
theorem piece_bound {Ω : Set 𝔼} (hΩ : MeasurableSet Ω) {f : 𝔼 → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.restrict Ω)) (α : ℝ) {ψ : 𝔼 → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∀ x, ψ x ≤ 1) {L : ℝ} (hL : ∀ x y, |ψ x - ψ y| ≤ L * ‖x - y‖) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {U : Set 𝔼} (hU : MeasurableSet U) (hUΩ : U ⊆ Ω)
    (hsupp : ∀ x ∈ Ω, ψ x ≠ 0 → ∀ y ∈ Ω, ‖x - y‖ < δ₀ → y ∈ U) (v : 𝔼) (n : ℕ) {δ : ℝ≥0∞}
    (hshift : ∀ x ∈ U, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)), x - -(v - t) ∈ Ω)
    (hT1 : ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ x, ENNReal.ofReal ((F0 Ω f (x - -(v - t)) - F0 Ω f x) ^ 2) ≤ δ)
    (hT2 : ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ p, ENNReal.ofReal ((Gq Ω α f (p - -((v - t, v - t) : 𝔼 × 𝔼)) - Gq Ω α f p) ^ 2) ≤ δ) :
    (∫⁻ x in Ω, ENNReal.ofReal ((ψ x * pieceU Ω f v n x) ^ 2)) +
        formHs Ω α (fun x => ψ x * pieceU Ω f v n x)
      ≤ (3 + 2 * kerJ d α L + 2 * kerT d α δ₀) * δ := by
  set u := pieceU Ω f v n with hu
  have hloc := (memLp_F0_shift hΩ hf v).locallyIntegrable (by norm_num)
  have hum : Measurable u := hfm.sub (contDiff_mollify hloc n).continuous.measurable
  have hk := measurable_jumpKernel d α
  have hA := piece_sq_le hΩ hfm hf hU hUΩ v n hT1
  have hB := piece_diff_le hΩ hfm hf α hU hUΩ v n hshift hT2
  -- `L²`
  have hL2 : ∫⁻ x in Ω, ENNReal.ofReal ((ψ x * u x) ^ 2) ≤ δ := by
    refine le_trans ?_ hA
    rw [← lintegral_indicator hΩ, ← lintegral_indicator hU]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Ω
    · by_cases hψ : ψ x = 0
      · simp [indicator_of_mem hx, hψ]
      · have hxU : x ∈ U := hsupp x hx hψ x hx (by simpa using hδ₀)
        rw [indicator_of_mem hx, indicator_of_mem hxU]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow]
        have := hψ0 x; have := hψ1 x
        have : ψ x ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (u x)]
    · rw [indicator_of_notMem hx]; exact zero_le
  -- the seminorm, dominated by `pieceB`
  have hS : formHs Ω α (fun x => ψ x * u x) ≤ ∫⁻ p, pieceB U α L δ₀ u p := by
    unfold formHs form
    exact (setLIntegral_mono' (hΩ.prod hΩ) fun p hp =>
      piece_pointwise hψ0 hψ1 hL hδ₀ hsupp α u hp.1 hp.2).trans (setLIntegral_le_lintegral _ _)
  -- the three terms
  set a : 𝔼 × 𝔼 → ℝ≥0∞ := fun p => ENNReal.ofReal ((u p.2 - u p.1) ^ 2) * jumpKernel d α p.1 p.2
  set b : 𝔼 × 𝔼 → ℝ≥0∞ := fun p => ENNReal.ofReal (u p.1 ^ 2) *
    (ENNReal.ofReal (min 1 (L ^ 2 * ‖p.1 - p.2‖ ^ 2)) * jumpKernel d α p.1 p.2)
  set c2 : 𝔼 × 𝔼 → ℝ≥0∞ := fun p => ENNReal.ofReal (u p.1 ^ 2) * jumpKernel d α p.1 p.2
  set c3 : 𝔼 × 𝔼 → ℝ≥0∞ := fun p => ENNReal.ofReal (u p.2 ^ 2) * jumpKernel d α p.1 p.2
  set S2 := {p : 𝔼 × 𝔼 | p.1 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖}
  set S3 := {p : 𝔼 × 𝔼 | p.2 ∈ U ∧ δ₀ ≤ ‖p.1 - p.2‖}
  have ha : Measurable a := (by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
    ENNReal.ofReal ((u p.2 - u p.1) ^ 2)).mul hk
  have hb : Measurable b := (by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
    ENNReal.ofReal (u p.1 ^ 2)).mul ((by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
      ENNReal.ofReal (min 1 (L ^ 2 * ‖p.1 - p.2‖ ^ 2))).mul hk)
  have hc2 : Measurable c2 := (by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
    ENNReal.ofReal (u p.1 ^ 2)).mul hk
  have hc3 : Measurable c3 := (by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
    ENNReal.ofReal (u p.2 ^ 2)).mul hk
  have hfar : MeasurableSet {p : 𝔼 × 𝔼 | δ₀ ≤ ‖p.1 - p.2‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have hS2 : MeasurableSet S2 := (measurable_fst hU).inter hfar
  have hS3 : MeasurableSet S3 := (measurable_snd hU).inter hfar
  have hUU := hU.prod hU
  have hpB : (fun p => pieceB U α L δ₀ u p) =
      fun p => (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p + S2.indicator c2 p +
        S3.indicator c3 p := rfl
  have hI : ∫⁻ p, pieceB U α L δ₀ u p =
      (2 * (∫⁻ p in U ×ˢ U, a p) + 2 * ∫⁻ p in U ×ˢ U, b p) + (∫⁻ p in S2, c2 p) +
        ∫⁻ p in S3, c3 p := by
    have hm1 : Measurable fun p => (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p := by
      exact ((ha.const_mul 2).add (hb.const_mul 2)).indicator hUU
    have hm2 : Measurable fun p => (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p +
        S2.indicator c2 p := hm1.add (hc2.indicator hS2)
    have e1 : ∫⁻ p, pieceB U α L δ₀ u p =
        (∫⁻ p, (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p) + (∫⁻ p, S2.indicator c2 p) +
          ∫⁻ p, S3.indicator c3 p := by
      rw [hpB, lintegral_add_left (f := fun p => (U ×ˢ U).indicator
        (fun p => 2 * a p + 2 * b p) p + S2.indicator c2 p) hm2,
        lintegral_add_left (f := fun p => (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p) hm1]
    have e2 : ∫⁻ p, (U ×ˢ U).indicator (fun p => 2 * a p + 2 * b p) p =
        2 * (∫⁻ p in U ×ˢ U, a p) + 2 * ∫⁻ p in U ×ˢ U, b p := by
      rw [lintegral_indicator hUU, lintegral_add_left (f := fun p => 2 * a p) (ha.const_mul 2),
        lintegral_const_mul _ ha, lintegral_const_mul _ hb]
    rw [e1, e2, lintegral_indicator hS2, lintegral_indicator hS3]
  -- the `b` term
  have hIb : ∫⁻ p in U ×ˢ U, b p ≤ δ * kerJ d α L := by
    calc ∫⁻ p in U ×ˢ U, b p ≤ ∫⁻ p in U ×ˢ univ, b p :=
          lintegral_mono_set (prod_mono le_rfl (subset_univ U))
      _ = ∫⁻ x in U, ENNReal.ofReal (u x ^ 2) * kerJ d α L := by
          rw [setLIntegral_prod_univ b hb]
          refine lintegral_congr fun x => ?_
          simp only [b]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_kerJ]
      _ = (∫⁻ x in U, ENNReal.ofReal (u x ^ 2)) * kerJ d α L :=
          lintegral_mul_const _ (by fun_prop)
      _ ≤ δ * kerJ d α L := by gcongr
  -- the far terms
  have hI2 : ∫⁻ p in S2, c2 p ≤ δ * kerT d α δ₀ := by
    rw [← lintegral_indicator hS2, Measure.volume_eq_prod,
      lintegral_prod _ (hc2.indicator hS2).aemeasurable]
    calc ∫⁻ x, ∫⁻ y, S2.indicator c2 (x, y)
        = ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (u x ^ 2) * kerT d α δ₀) x := by
          refine lintegral_congr fun x => ?_
          by_cases hx : x ∈ U
          · rw [indicator_of_mem hx, ← lintegral_kerT α δ₀ x,
              ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun y => ?_
            by_cases hy : δ₀ ≤ ‖x - y‖
            · rw [indicator_of_mem (show (x, y) ∈ S2 from ⟨hx, hy⟩),
                indicator_of_mem (show y ∈ {y | δ₀ ≤ ‖x - y‖} from hy)]
            · rw [indicator_of_notMem (show (x, y) ∉ S2 from fun h => hy h.2),
                indicator_of_notMem (show y ∉ {y | δ₀ ≤ ‖x - y‖} from hy), mul_zero]
          · rw [indicator_of_notMem hx]
            have h0 : ∀ y, S2.indicator c2 (x, y) = 0 := fun y =>
              indicator_of_notMem (show (x, y) ∉ S2 from fun h => hx h.1) _
            simp [h0]
      _ = (∫⁻ x in U, ENNReal.ofReal (u x ^ 2)) * kerT d α δ₀ := by
          rw [lintegral_indicator hU, lintegral_mul_const _ (by fun_prop)]
      _ ≤ δ * kerT d α δ₀ := by gcongr
  have hI3 : ∫⁻ p in S3, c3 p = ∫⁻ p in S2, c2 p := by
    rw [← lintegral_indicator hS3, ← lintegral_indicator hS2, Measure.volume_eq_prod,
      ← lintegral_prod_swap]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ S2
    · rw [indicator_of_mem hp, indicator_of_mem (show p.swap ∈ S3 from
        ⟨hp.1, by rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]; exact hp.2⟩)]
      simp only [c2, c3, Prod.fst_swap, Prod.snd_swap, jumpKernel, norm_sub_rev]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p.swap ∉ S3 from fun h =>
        hp ⟨h.1, by rw [norm_sub_rev]; exact h.2⟩)]
  calc (∫⁻ x in Ω, ENNReal.ofReal ((ψ x * u x) ^ 2)) + formHs Ω α (fun x => ψ x * u x)
      ≤ δ + ((2 * δ + 2 * (δ * kerJ d α L)) + δ * kerT d α δ₀ + δ * kerT d α δ₀) := by
        refine add_le_add hL2 (hS.trans ?_)
        rw [hI, hI3]
        exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB zero_le)
          (mul_le_mul_of_nonneg_left hIb zero_le)) hI2) hI2
    _ = (3 + 2 * kerJ d α L + 2 * kerT d α δ₀) * δ := by ring

end QFS
