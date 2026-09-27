import QuadraticFormsSobolev.Dyda.ChainSum
import QuadraticFormsSobolev.Dyda.ChangeVar

/-! # Dyda's Step 1 for an abstract family of chains

Dyda's Step 1 (pp. 569–570) in a form that needs no convexity. The chain from `x` through `y`
has points `A_k = T + q^k (x − T)` accumulating at the tip `T = x + (1 − q^N)⁻¹ (y − x)`, and
consecutive points are regional pairs as soon as the pair `(x, T)` is *admissible*: every point
`T + s (x − T)`, `0 < s ≤ 1`, lies in `Ω` at distance more than `θ s |x − T| / η` from `Ωᶜ`.
Pairs `(x, y)` whose tips are eventually admissible are then controlled by the regional pairs
`|y − x| < η δ_x`, with the constant `chainConst α θ`, which does not depend on `Ω`. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- `δ_x`: the distance from `x` to the complement of `K`. -/
noncomputable def distC (K : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  infDist x Kᶜ

/-- The tip `x + (1 − q^N)⁻¹ (y − x)` of the `N`-th chain from `x` through `y`. -/
noncomputable def tip (q : ℝ) (N : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x + (1 - q ^ N)⁻¹ • (y - x)

/-- The constant of Step 1: `β/(β − 1) · β/(1 − β(1 − θ)^α)` with `β = (1 + θ)^α`. -/
noncomputable def chainConst (α θ : ℝ) : ℝ :=
  (1 + θ) ^ α / ((1 + θ) ^ α - 1) * ((1 + θ) ^ α / (1 - (1 + θ) ^ α * (1 - θ) ^ α))

/-- The pairs whose `N`-th tip is admissible. -/
def chainStepSet (P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (q : ℝ)
    (N : ℕ) : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ≠ p.2 ∧ (p.1, tip q N p.1 p.2) ∈ P}

lemma chainPt_eq_tip {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    chainPt q N k x y = tip q N x y + q ^ k • (x - tip q N x y) := by
  have hqN : q ^ N < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hD : 1 - q ^ N ≠ 0 := by linarith
  have hc : 1 - coef q N k = (1 - q ^ k) * (1 - q ^ N)⁻¹ := by
    rw [coef]; field_simp; ring
  have e1 : chainPt q N k x y = x + (1 - coef q N k) • (y - x) := by
    rw [chainPt]; module
  rw [e1, hc, tip]; module

/-- **The chain condition.** If the tip of `(x, y)` is admissible, consecutive chain points are
regional pairs. -/
lemma chainStep_mem {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} {η θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hPΩ : ∀ p ∈ P, ∀ s : ℝ, 0 < s → s ≤ 1 →
      p.2 + s • (p.1 - p.2) ∈ Ω ∧ θ * s * ‖p.1 - p.2‖ < η * distC Ω (p.2 + s • (p.1 - p.2)))
    {N : ℕ} (hN : 1 ≤ N) {x y : EuclideanSpace ℝ (Fin d)} (hP : (x, tip (1 - θ) N x y) ∈ P)
    (k : ℕ) :
    chainPt (1 - θ) N k x y ∈ Ω ∧ chainPt (1 - θ) N (k + 1) x y ∈
      ball (chainPt (1 - θ) N k x y) (η * distC Ω (chainPt (1 - θ) N k x y)) := by
  have hq0 : 0 < 1 - θ := by linarith
  have hq1 : 1 - θ < 1 := by linarith
  have hs0 : 0 < (1 - θ) ^ k := pow_pos hq0 k
  have hs1 : (1 - θ) ^ k ≤ 1 := pow_le_one₀ hq0.le hq1.le
  obtain ⟨hmem, hlt⟩ := hPΩ _ hP _ hs0 hs1
  simp only at hmem hlt
  rw [chainPt_eq_tip hq0 hq1 hN, chainPt_eq_tip hq0 hq1 hN]
  refine ⟨hmem, ?_⟩
  set T := tip (1 - θ) N x y
  rw [mem_ball, dist_eq_norm,
    show T + (1 - θ) ^ (k + 1) • (x - T) - (T + (1 - θ) ^ k • (x - T))
      = -(θ * (1 - θ) ^ k) • (x - T) by module,
    norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
  exact hlt

lemma sc_continuous_distC (K : Set (EuclideanSpace ℝ (Fin d))) : Continuous (distC K) :=
  continuous_infDist_pt _

/-- The regional integrand `1[a ∈ K, b ∈ B(a, η δ_a)] U(a, b)`. -/
noncomputable def sc_R (K : Set (EuclideanSpace ℝ (Fin d))) (η α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a b : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 ∈ K ∧ p.2 ∈ ball p.1 (η * distC K p.1)}.indicator
    (fun p => U d α u p.1 p.2) (a, b)

lemma sc_measurable_R {K : Set (EuclideanSpace ℝ (Fin d))} (hKo : IsOpen K) (η α : ℝ)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable (Function.uncurry (sc_R K η α u)) := by
  have hδ : Measurable (distC K) := (sc_continuous_distC K).measurable
  have hS : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 ∈ K ∧ p.2 ∈ ball p.1 (η * distC K p.1)} := by
    simp only [mem_ball, Set.ofPred_and]
    exact (measurable_fst hKo.measurableSet).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  exact (measurable_U α hu).indicator hS

lemma sc_rhs {K : Set (EuclideanSpace ℝ (Fin d))} (hKo : IsOpen K) (η α : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫⁻ x, ∫⁻ y, sc_R K η α u x y = ∫⁻ x in K,
      ∫⁻ y in ball x (η * distC K x), U d α u x y := by
  rw [← lintegral_indicator hKo.measurableSet]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ ball x (η * distC K x)
    · rw [Set.indicator_of_mem hy, sc_R, Set.indicator_of_mem]
      exact ⟨hx, hy⟩
    · rw [Set.indicator_of_notMem hy, sc_R, Set.indicator_of_notMem]
      exact fun h => hy h.2
  · rw [Set.indicator_of_notMem hx]
    refine lintegral_eq_zero_iff' ?_ |>.mpr ?_
    · exact aemeasurable_const.congr (Filter.Eventually.of_forall fun y => by
        rw [sc_R, Set.indicator_of_notMem]; exact fun h => hx h.1)
    · exact Filter.Eventually.of_forall fun y => by
        rw [sc_R, Set.indicator_of_notMem]; · rfl
        exact fun h => hx h.1

lemma sc_one_sub_pow {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) :
    1 - q ≤ 1 - q ^ N := by
  have := pow_le_of_le_one hq0.le hq1.le (by omega : N ≠ 0); linarith

lemma sc_delta_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    0 < coef q N k - coef q N (k + 1) := by
  rw [coef_sub]
  have := sc_one_sub_pow hq0 hq1 hN
  apply div_pos (mul_pos (pow_pos hq0 k) (by linarith)) (by linarith)

lemma sc_coef_ne_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    coef q N (k + 1) ≠ 1 := by
  have h := sc_one_sub_pow hq0 hq1 hN
  have hk : q ^ (k + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  unfold coef
  rw [Ne, div_eq_one_iff_eq (by linarith)]
  intro h'; linarith

lemma sc_term {α q β : ℝ} (hα : 0 < α) (hq0 : 0 < q) (hq1 : q < 1) (hβ : 0 < β) {N : ℕ}
    (hN : 1 ≤ N) (k : ℕ) :
    β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α) *
        |coef q N k - coef q N (k + 1)|⁻¹ ^ d ≤ β * (β * q ^ α) ^ k := by
  have hpos := sc_delta_pos hq0 hq1 hN k
  have hle : coef q N k - coef q N (k + 1) ≤ q ^ k := by
    rw [coef_sub]
    have := sc_one_sub_pow hq0 hq1 hN
    rw [mul_div_assoc]
    have h1 : (1 - q) / (1 - q ^ N) ≤ 1 := (div_le_one (by linarith)).mpr this
    calc q ^ k * ((1 - q) / (1 - q ^ N)) ≤ q ^ k * 1 := by gcongr
      _ = q ^ k := mul_one _
  set Δ := coef q N k - coef q N (k + 1)
  rw [abs_of_pos hpos, Real.rpow_add hpos, Real.rpow_natCast]
  have hΔd : Δ ^ d * Δ⁻¹ ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow]
  calc β ^ (k + 1) * (Δ ^ d * Δ ^ α) * Δ⁻¹ ^ d = β ^ (k + 1) * Δ ^ α * (Δ ^ d * Δ⁻¹ ^ d) := by
        ring
    _ = β ^ (k + 1) * Δ ^ α := by rw [hΔd, mul_one]
    _ ≤ β ^ (k + 1) * (q ^ k) ^ α := by
        gcongr
    _ = β * (β * q ^ α) ^ k := by
        rw [← Real.rpow_natCast_mul hq0.le, mul_comm (k : ℝ), Real.rpow_mul_natCast hq0.le]
        ring

lemma sc_chain_bound {K : Set (EuclideanSpace ℝ (Fin d))} (hKo : IsOpen K)
    {P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} {α η θ β : ℝ} (hα : 0 < α)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hPΩ : ∀ p ∈ P, ∀ s : ℝ, 0 < s → s ≤ 1 →
      p.2 + s • (p.1 - p.2) ∈ K ∧ θ * s * ‖p.1 - p.2‖ < η * distC K (p.2 + s • (p.1 - p.2)))
    (hq0 : 0 < 1 - θ) (hq1 : 1 - θ < 1) (hβ : 1 < β)
    (hγ : β * (1 - θ) ^ α < 1)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ x, ∫⁻ y, (chainStepSet P (1 - θ) N).indicator (fun p => U d α u p.1 p.2) (x, y)
      ≤ ENNReal.ofReal (β / (β - 1) * (β / (1 - β * (1 - θ) ^ α))) *
          ∫⁻ x, ∫⁻ y, sc_R K η α u x y := by
  set q := 1 - θ with hq
  set S := chainStepSet P q N
  set c : ENNReal := ENNReal.ofReal (β / (β - 1))
  set e : ℕ → ENNReal := fun k =>
    ENNReal.ofReal (β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α))
  set g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ENNReal := fun k x y =>
    sc_R K η α u (chainPt q N k x y) (chainPt q N (k + 1) x y)
  have hR := sc_measurable_R hKo η α hu
  have hg : ∀ k, Measurable (Function.uncurry (g k)) := by
    intro k
    have hf : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        (chainPt q N k p.1 p.2, chainPt q N (k + 1) p.1 p.2) := by
      unfold chainPt; fun_prop
    have h := hR.comp hf
    rw [Function.uncurry_def]
    exact h
  have hgy : ∀ k x, Measurable (g k x) := fun k x => (hg k).of_uncurry_left
  have hgx : ∀ k, Measurable fun x => ∫⁻ y, g k x y := fun k => (hg k).lintegral_prod_right
  have hpt : ∀ x y, S.indicator (fun p => U d α u p.1 p.2) (x, y) ≤
      c * ∑ k ∈ Finset.range N, e k * g k x y := by
    intro x y
    by_cases h : (x, y) ∈ S
    · rw [Set.indicator_of_mem h]
      obtain ⟨hxy, hP⟩ := h
      refine (U_le_chain_sum hα hq0 hq1 hβ u hN hxy).trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      simp only [g]
      rw [sc_R, Set.indicator_of_mem]
      exact chainStep_mem hθ0 hθ1 hPΩ hN hP k
    · rw [Set.indicator_of_notMem h]; exact zero_le
  have hinner : ∀ x, ∫⁻ y, c * ∑ k ∈ Finset.range N, e k * g k x y =
      c * ∑ k ∈ Finset.range N, e k * ∫⁻ y, g k x y := by
    intro x
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => (hgy k x).const_mul _),
      lintegral_finsetSum _ fun k _ => (hgy k x).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun k _ => lintegral_const_mul _ (hgy k x)
  have houter : ∫⁻ x, c * ∑ k ∈ Finset.range N, e k * ∫⁻ y, g k x y =
      c * ∑ k ∈ Finset.range N, e k * ∫⁻ x, ∫⁻ y, g k x y := by
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => (hgx k).const_mul _),
      lintegral_finsetSum _ fun k _ => (hgx k).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun k _ => lintegral_const_mul _ (hgx k)
  set I := ∫⁻ x, ∫⁻ y, sc_R K η α u x y
  have hcv : ∀ k ∈ Finset.range N, ∫⁻ x, ∫⁻ y, g k x y =
      ENNReal.ofReal (|coef q N k - coef q N (k + 1)|⁻¹ ^ d) * I := by
    intro k _
    simp only [g, chainPt]
    exact lintegral_lintegral_pair (sc_coef_ne_one hq0 hq1 hN k)
      (sub_ne_zero.mp (sc_delta_pos hq0 hq1 hN k).ne') _ hR
  have hβ0 : 0 < β := by linarith
  have hterm_nn : ∀ k, 0 ≤ β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α) *
      |coef q N k - coef q N (k + 1)|⁻¹ ^ d := fun k =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _)
      (Real.rpow_nonneg (sc_delta_pos hq0 hq1 hN k).le _)) (by positivity)
  calc ∫⁻ x, ∫⁻ y, S.indicator (fun p => U d α u p.1 p.2) (x, y)
      ≤ ∫⁻ x, ∫⁻ y, c * ∑ k ∈ Finset.range N, e k * g k x y :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = c * ∑ k ∈ Finset.range N, e k * ∫⁻ x, ∫⁻ y, g k x y := by
        simp_rw [hinner]; exact houter
    _ = ENNReal.ofReal (β / (β - 1) * ∑ k ∈ Finset.range N,
          β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α) *
            |coef q N k - coef q N (k + 1)|⁻¹ ^ d) * I := by
        rw [Finset.sum_congr rfl fun k hk => by rw [hcv k hk], ENNReal.ofReal_mul (by
          have := hβ0; exact div_nonneg this.le (by linarith)),
          ENNReal.ofReal_sum_of_nonneg fun k _ => hterm_nn k, mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul
          (mul_nonneg (pow_nonneg hβ0.le _) (Real.rpow_nonneg (sc_delta_pos hq0 hq1 hN k).le _))]
    _ ≤ ENNReal.ofReal (β / (β - 1) * (β / (1 - β * q ^ α))) * I := by
        gcongr ENNReal.ofReal ?_ * I
        have hb : 0 ≤ β / (β - 1) := div_nonneg hβ0.le (by linarith)
        refine mul_le_mul_of_nonneg_left ?_ hb
        have hγ0 : 0 ≤ β * q ^ α := by positivity
        calc _ ≤ ∑ k ∈ Finset.range N, β * (β * q ^ α) ^ k :=
              Finset.sum_le_sum fun k _ => sc_term hα hq0 hq1 hβ0 hN k
          _ = β * ∑ k ∈ Finset.Ico 0 N, (β * q ^ α) ^ k := by
              rw [Finset.mul_sum, Finset.range_eq_Ico]
          _ ≤ β * ((β * q ^ α) ^ 0 / (1 - β * q ^ α)) := by
              gcongr; exact geom_sum_Ico_le_of_lt_one hγ0 hγ
          _ = β / (1 - β * q ^ α) := by rw [pow_zero, mul_one_div]

/-- **Dyda's Step 1, abstract form.** Pairs `(x, y)`, `x ≠ y`, whose tips are eventually
admissible are controlled by the regional pairs. -/
theorem chain_step {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hP : MeasurableSet P)
    {α η θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hPΩ : ∀ p ∈ P, ∀ s : ℝ, 0 < s → s ≤ 1 →
      p.2 + s • (p.1 - p.2) ∈ Ω ∧ θ * s * ‖p.1 - p.2‖ < η * distC Ω (p.2 + s • (p.1 - p.2)))
    {A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))}
    (hAP : ∀ p ∈ A, p.1 ≠ p.2 → ∀ᶠ N : ℕ in Filter.atTop, (p.1, tip (1 - θ) N p.1 p.2) ∈ P)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    ∫⁻ x, ∫⁻ y, A.indicator (fun p => U d α u p.1 p.2) (x, y)
      ≤ ENNReal.ofReal (chainConst α θ) *
          ∫⁻ x in Ω, ∫⁻ y in ball x (η * distC Ω x), U d α u x y := by
  have hq0 : 0 < 1 - θ := by linarith
  have hq1 : 1 - θ < 1 := by linarith
  set β := (1 + θ) ^ α with hβdef
  have hβ : 1 < β := Real.one_lt_rpow (by linarith) hα
  have hγ : β * (1 - θ) ^ α < 1 := by
    rw [hβdef, ← Real.mul_rpow (by linarith) hq0.le]
    exact Real.rpow_lt_one (by nlinarith) (by nlinarith) hα
  set F : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun N x y =>
    (chainStepSet P (1 - θ) N).indicator (fun p => U d α u p.1 p.2) (x, y) with hF
  have hS : ∀ N, MeasurableSet (chainStepSet P (1 - θ) N) := fun N =>
    (measurableSet_eq_fun measurable_fst measurable_snd).compl.inter
      (hP.preimage (by unfold tip; fun_prop))
  have hFm : ∀ N, Measurable (Function.uncurry (F N)) := fun N =>
    (measurable_U α hu).indicator (hS N)
  have hFy : ∀ N x, Measurable (F N x) := fun N x => (hFm N).of_uncurry_left
  have hFx : ∀ N, Measurable fun x => ∫⁻ y, F N x y := fun N => (hFm N).lintegral_prod_right
  have hbound : ∀ N, 1 ≤ N → ∫⁻ x, ∫⁻ y, F N x y ≤ ENNReal.ofReal (chainConst α θ) *
      ∫⁻ x, ∫⁻ y, sc_R Ω η α u x y :=
    fun N hN => sc_chain_bound hΩ hα hθ0 hθ1 hPΩ hq0 hq1 hβ hγ hu hN
  have hin : ∀ x y, A.indicator (fun p => U d α u p.1 p.2) (x, y)
      ≤ Filter.liminf (fun N => F N x y) Filter.atTop := by
    intro x y
    by_cases h : (x, y) ∈ A
    · rw [Set.indicator_of_mem h]
      by_cases hxy : x = y
      · subst hxy; rw [U_self]; exact zero_le
      refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hAP _ h hxy] with N hN
      simp only [hF]
      rw [Set.indicator_of_mem (show (x, y) ∈ chainStepSet P (1 - θ) N from ⟨hxy, hN⟩)]
    · rw [Set.indicator_of_notMem h]; exact zero_le
  rw [← sc_rhs hΩ]
  calc ∫⁻ x, ∫⁻ y, A.indicator (fun p => U d α u p.1 p.2) (x, y)
      ≤ ∫⁻ x, ∫⁻ y, Filter.liminf (fun N => F N x y) Filter.atTop :=
        lintegral_mono fun x => lintegral_mono fun y => hin x y
    _ ≤ ∫⁻ x, Filter.liminf (fun N => ∫⁻ y, F N x y) Filter.atTop :=
        lintegral_mono fun x => lintegral_liminf_le (hFy · x)
    _ ≤ Filter.liminf (fun N => ∫⁻ x, ∫⁻ y, F N x y) Filter.atTop := lintegral_liminf_le hFx
    _ ≤ _ := Filter.liminf_le_of_frequently_le'
        ((Filter.eventually_ge_atTop 1).mono hbound).frequently

end Dyda
