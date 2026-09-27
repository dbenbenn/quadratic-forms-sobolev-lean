import QuadraticFormsSobolev.Section1

/-!
# Density in `H^{α/2}(ℝ^d)`: basic tools

The whole-space seminorm is an average of `L²` differences:
`|f|²_{H^{α/2}(ℝ^d)} = ∫ |h|^{−d−α} D_h(f) dh`, where `D_h(f) = ∫ (f(x + h) − f(x))² dx`.
Everything here is stated with lower Lebesgue integrals of squares, `sqInt g = ∫ g²`, which is
`‖g‖²_{L²}` (`eLpNorm_two_sq`).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace QFS

variable {d : ℕ}

/-- `∫ g²`. -/
noncomputable def sqInt (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (g x ^ 2)

/-- `D_h(g) = ∫ (g(x + h) − g(x))²`. -/
noncomputable def diffInt (g : EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((g (x + h) - g x) ^ 2)

/-- The weight `|h|^{−d−α}`. -/
noncomputable def wK (d : ℕ) (α : ℝ) (h : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖h‖ ^ (-(d : ℝ) - α))

lemma ofReal_sq_add_le (a b : ℝ) :
    ENNReal.ofReal ((a + b) ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - b)])

lemma measurable_wK (d : ℕ) (α : ℝ) : Measurable (wK d α) := by
  unfold wK; fun_prop

lemma sqInt_add_le {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a) :
    sqInt (a + b) ≤ 2 * sqInt a + 2 * sqInt b := by
  unfold sqInt
  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left (by fun_prop)]
  exact lintegral_mono fun x => ofReal_sq_add_le _ _

lemma sqInt_neg (a : EuclideanSpace ℝ (Fin d) → ℝ) : sqInt (-a) = sqInt a := by
  simp [sqInt]

lemma sqInt_sub_le {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a) :
    sqInt (a - b) ≤ 2 * sqInt a + 2 * sqInt b := by
  rw [sub_eq_add_neg, ← sqInt_neg b]
  exact sqInt_add_le ha

lemma sqInt_comp_add (g : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    sqInt (fun x => g (x + z)) = sqInt g :=
  lintegral_add_right_eq_self (fun x => ENNReal.ofReal (g x ^ 2)) z

lemma sqInt_comp_sub (g : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    sqInt (fun x => g (x - z)) = sqInt g :=
  lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (g x ^ 2)) z

lemma eLpNorm_two_sq (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    eLpNorm g 2 volume ^ 2 = sqInt g := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := volume) (p := 2) (by norm_num)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h
  rw [← ENNReal.rpow_natCast, Nat.cast_ofNat, h, sqInt]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs]
  simp only [ENNReal.rpow_ofNat]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma diffInt_le_sqInt {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Measurable g)
    (h : EuclideanSpace ℝ (Fin d)) : diffInt g h ≤ 4 * sqInt g := by
  have := sqInt_sub_le (a := fun x => g (x + h)) (b := g) (by fun_prop)
  rw [sqInt_comp_add] at this
  calc diffInt g h = sqInt ((fun x => g (x + h)) - g) := rfl
    _ ≤ 2 * sqInt g + 2 * sqInt g := this
    _ = 4 * sqInt g := by ring

lemma diffInt_sub_le {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a)
    (h : EuclideanSpace ℝ (Fin d)) :
    diffInt (a - b) h ≤ 2 * diffInt a h + 2 * diffInt b h := by
  unfold diffInt
  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_const_mul' _ _ (by norm_num),
    ← lintegral_add_left (by fun_prop)]
  refine lintegral_mono fun x => ?_
  have := ofReal_sq_add_le (a (x + h) - a x) (-(b (x + h) - b x))
  simp only [Pi.sub_apply, neg_sq] at this ⊢
  convert this using 3; ring

lemma measurable_diffInt {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Measurable g) :
    Measurable (diffInt g) := by
  have : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g (p.2 + p.1) - g p.2) ^ 2) := by fun_prop
  exact this.lintegral_prod_right'

/-- The whole-space form as an iterated integral. -/
lemma formHs_univ_eq_iter {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Measurable g) (α : ℝ) :
    formHs univ α g =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((g y - g x) ^ 2) * jumpKernel d α x y := by
  have hm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2) * jumpKernel d α p.1 p.2 :=
    (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g p.2 - g p.1) ^ 2)).mul (measurable_jumpKernel d α)
  unfold formHs form
  rw [univ_prod_univ, Measure.restrict_univ, Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]

/-- **The seminorm as an average of `L²` differences.** -/
lemma formHs_univ_eq {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Measurable g) (α : ℝ) :
    formHs univ α g = ∫⁻ h, wK d α h * diffInt g h := by
  rw [formHs_univ_eq_iter hg]
  have step : ∀ x, ∫⁻ y, ENNReal.ofReal ((g y - g x) ^ 2) * jumpKernel d α x y =
      ∫⁻ h, ENNReal.ofReal ((g (x + h) - g x) ^ 2) * wK d α h := by
    intro x
    rw [← lintegral_add_left_eq_self _ x]
    refine lintegral_congr fun h => ?_
    simp only [jumpKernel, wK, sub_add_cancel_left, norm_neg]
  simp_rw [step]
  have hm : Measurable (Function.uncurry fun x h : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g (x + h) - g x) ^ 2) * wK d α h) :=
    (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((g (p.1 + p.2) - g p.1) ^ 2)).mul ((measurable_wK d α).comp measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine lintegral_congr fun h => ?_
  rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  rfl

/-- **Jensen for a probability density**: `(∫ ρ v)² ≤ ∫ ρ v²`. -/
lemma ofReal_sq_integral_le {ρ v : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρi : Integrable ρ) (hρ1 : ∫ z, ρ z = 1) (hv : Integrable fun z => ρ z * v z)
    (hvm : AEStronglyMeasurable v) :
    ENNReal.ofReal ((∫ z, ρ z * v z) ^ 2) ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * ENNReal.ofReal (v z ^ 2) := by
  simp_rw [← ENNReal.ofReal_mul (hρ0 _)]
  by_cases hfin : ∫⁻ z, ENNReal.ofReal (ρ z * v z ^ 2) = ⊤
  · rw [hfin]; exact le_top
  have hmeas : AEStronglyMeasurable fun z => ρ z * v z ^ 2 :=
    hρi.aestronglyMeasurable.mul (hvm.pow 2)
  have hi : Integrable fun z => ρ z * v z ^ 2 := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by
      have := hρ0 z; positivity)]
    exact Ne.lt_top hfin
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => by
    have := hρ0 z; positivity)]
  apply ENNReal.ofReal_le_ofReal
  set m := ∫ z, ρ z * v z
  -- `0 ≤ ∫ ρ (v − m)² = ∫ ρ v² − m²`
  have h0 : 0 ≤ ∫ z, ρ z * (v z - m) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (hρ0 z) (sq_nonneg _)
  have hexp : (fun z => ρ z * (v z - m) ^ 2) =
      fun z => ρ z * v z ^ 2 - 2 * m * (ρ z * v z) + m ^ 2 * ρ z := by
    funext z; ring
  have e : ∫ z, (ρ z * v z ^ 2 - 2 * m * (ρ z * v z) + m ^ 2 * ρ z) =
      (∫ z, ρ z * v z ^ 2) - 2 * m * m + m ^ 2 * 1 := by
    rw [integral_add (f := fun z => ρ z * v z ^ 2 - 2 * m * (ρ z * v z))
        (g := fun z => m ^ 2 * ρ z) (hi.sub (hv.const_mul _)) (hρi.const_mul _),
      integral_sub (f := fun z => ρ z * v z ^ 2) (g := fun z => 2 * m * (ρ z * v z)) hi
        (hv.const_mul _), integral_const_mul, integral_const_mul, hρ1]
  rw [hexp, e] at h0
  nlinarith

end QFS
