import QuadraticFormsSobolev.Dyda.ChainSum
import QuadraticFormsSobolev.Dyda.ChangeVar

/-! # Dyda's Step 1 for the ball: far pairs are controlled by regional pairs

Letting `N → ∞` (the chain sets increase to `far M x`), (9) and the change of variables (10) give
`∫∫_{far} U ≤ C ∫∫_{regional} U` with the geometric ratio `γ = (1 − η̃²)^α < 1` (p. 570). -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

lemma st1_continuous_dist₁ : Continuous (dist₁ (d := d)) :=
  continuous_infDist_pt _

lemma st1_measurableSet_S (q M : ℝ) (N : ℕ) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ chainSet q M N p.1} := by
  have hδ : Measurable (dist₁ (d := d)) := st1_continuous_dist₁.measurable
  simp only [chainSet, mem_ball, mem_closedBall, dist_zero_right, Set.ofPred_and]
  refine (measurableSet_lt (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
    (((measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop)))))

/-- The regional integrand `1[a ∈ B, b ∈ B(a, η δ_a)] U(a, b)`. -/
noncomputable def st1_R (η α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (a b : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ ball p.1 (η * dist₁ p.1)}.indicator
    (fun p => U d α u p.1 p.2) (a, b)

lemma st1_measurable_R (η α : ℝ) {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable (Function.uncurry (st1_R η α u)) := by
  have hδ : Measurable (dist₁ (d := d)) := st1_continuous_dist₁.measurable
  have hS : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ ball p.1 (η * dist₁ p.1)} := by
    simp only [mem_ball, dist_zero_right, Set.ofPred_and]
    exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  exact (measurable_U α hu).indicator hS

lemma st1_rhs (η α : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫⁻ x, ∫⁻ y, st1_R η α u x y = ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫⁻ y in ball x (η * dist₁ x), U d α u x y := by
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx, ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ ball x (η * dist₁ x)
    · rw [Set.indicator_of_mem hy, st1_R, Set.indicator_of_mem]
      exact ⟨hx, hy⟩
    · rw [Set.indicator_of_notMem hy, st1_R, Set.indicator_of_notMem]
      exact fun h => hy h.2
  · rw [Set.indicator_of_notMem hx]
    refine lintegral_eq_zero_iff' ?_ |>.mpr ?_
    · exact aemeasurable_const.congr (Filter.Eventually.of_forall fun y => by
        rw [st1_R, Set.indicator_of_notMem]; exact fun h => hx h.1)
    · exact Filter.Eventually.of_forall fun y => by
        rw [st1_R, Set.indicator_of_notMem]; · rfl
        exact fun h => hx h.1

lemma st1_eventually_mem {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {x y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ far M x) : ∀ᶠ N in Filter.atTop, y ∈ chainSet q M N x := by
  obtain ⟨hyb, hyx, hlt⟩ := hy
  have hpow : Filter.Tendsto (fun N : ℕ => q ^ N) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have h1 : Filter.Tendsto (fun N : ℕ => (1 - q ^ N) * (M * dist₁ x)) Filter.atTop
      (nhds (M * dist₁ x)) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hpow).mul_const (M * dist₁ x)
  have h2 : Filter.Tendsto (fun N : ℕ => x + (1 - q ^ N)⁻¹ • (y - x)) Filter.atTop (nhds y) := by
    have : Filter.Tendsto (fun N : ℕ => (1 - q ^ N)⁻¹) Filter.atTop (nhds 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hpow).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using (tendsto_const_nhds (x := x)).add (this.smul_const (y - x))
  filter_upwards [h1.eventually_const_lt hlt, h2.eventually (isOpen_ball.mem_nhds hyb)]
    with N hN1 hN2
  exact ⟨hyb, hyx, hN1, ball_subset_closedBall hN2⟩

lemma st1_one_sub_pow {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) :
    1 - q ≤ 1 - q ^ N := by
  have := pow_le_of_le_one hq0.le hq1.le (by omega : N ≠ 0); linarith

lemma st1_delta_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    0 < coef q N k - coef q N (k + 1) := by
  rw [coef_sub]
  have := st1_one_sub_pow hq0 hq1 hN
  apply div_pos (mul_pos (pow_pos hq0 k) (by linarith)) (by linarith)

lemma st1_coef_ne_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    coef q N (k + 1) ≠ 1 := by
  have h := st1_one_sub_pow hq0 hq1 hN
  have hk : q ^ (k + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  unfold coef
  rw [Ne, div_eq_one_iff_eq (by linarith)]
  intro h'; linarith

lemma st1_term {α q β : ℝ} (hα : 0 < α) (hq0 : 0 < q) (hq1 : q < 1) (hβ : 0 < β) {N : ℕ}
    (hN : 1 ≤ N) (k : ℕ) :
    β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α) *
        |coef q N k - coef q N (k + 1)|⁻¹ ^ d ≤ β * (β * q ^ α) ^ k := by
  have hpos := st1_delta_pos hq0 hq1 hN k
  have hle : coef q N k - coef q N (k + 1) ≤ q ^ k := by
    rw [coef_sub]
    have := st1_one_sub_pow hq0 hq1 hN
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

lemma st1_chain_bound (hd : 1 ≤ d) {α η M β : ℝ} (hα : 0 < α) (hη : 0 < η) (hη1 : η < 1)
    (hM : 1 ≤ M) (hq0 : 0 < 1 - η / M) (hq1 : 1 - η / M < 1) (hβ : 1 < β)
    (hγ : β * (1 - η / M) ^ α < 1)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ x, ∫⁻ y, {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ chainSet (1 - η / M) M N p.1}.indicator
          (fun p => U d α u p.1 p.2) (x, y)
      ≤ ENNReal.ofReal (β / (β - 1) * (β / (1 - β * (1 - η / M) ^ α))) *
          ∫⁻ x, ∫⁻ y, st1_R η α u x y := by
  set q := 1 - η / M with hq
  set S := {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
        p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ∧ p.2 ∈ chainSet q M N p.1}
  set c : ENNReal := ENNReal.ofReal (β / (β - 1))
  set e : ℕ → ENNReal := fun k =>
    ENNReal.ofReal (β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α))
  set g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ENNReal := fun k x y =>
    st1_R η α u (chainPt q N k x y) (chainPt q N (k + 1) x y)
  have hR := st1_measurable_R η α hu
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
      obtain ⟨hx, hy⟩ := h
      refine (U_le_chain_sum hα hq0 hq1 hβ u hN (Ne.symm hy.2.1)).trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      simp only [g]
      rw [st1_R, Set.indicator_of_mem]
      exact chainPt_mem hd hη hη1 hM hN hx hy (Finset.mem_range.mp hk)
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
  set I := ∫⁻ x, ∫⁻ y, st1_R η α u x y
  have hcv : ∀ k ∈ Finset.range N, ∫⁻ x, ∫⁻ y, g k x y =
      ENNReal.ofReal (|coef q N k - coef q N (k + 1)|⁻¹ ^ d) * I := by
    intro k _
    simp only [g, chainPt]
    exact lintegral_lintegral_pair (st1_coef_ne_one hq0 hq1 hN k)
      (sub_ne_zero.mp (st1_delta_pos hq0 hq1 hN k).ne') _ hR
  have hβ0 : 0 < β := by linarith
  have hterm_nn : ∀ k, 0 ≤ β ^ (k + 1) * (coef q N k - coef q N (k + 1)) ^ ((d : ℝ) + α) *
      |coef q N k - coef q N (k + 1)|⁻¹ ^ d := fun k =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ0.le _)
      (Real.rpow_nonneg (st1_delta_pos hq0 hq1 hN k).le _)) (by positivity)
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
          (mul_nonneg (pow_nonneg hβ0.le _) (Real.rpow_nonneg (st1_delta_pos hq0 hq1 hN k).le _))]
    _ ≤ ENNReal.ofReal (β / (β - 1) * (β / (1 - β * q ^ α))) * I := by
        gcongr ENNReal.ofReal ?_ * I
        have hb : 0 ≤ β / (β - 1) := div_nonneg hβ0.le (by linarith)
        refine mul_le_mul_of_nonneg_left ?_ hb
        have hγ0 : 0 ≤ β * q ^ α := by positivity
        calc _ ≤ ∑ k ∈ Finset.range N, β * (β * q ^ α) ^ k :=
              Finset.sum_le_sum fun k _ => st1_term hα hq0 hq1 hβ0 hN k
          _ = β * ∑ k ∈ Finset.Ico 0 N, (β * q ^ α) ^ k := by
              rw [Finset.mul_sum, Finset.range_eq_Ico]
          _ ≤ β * ((β * q ^ α) ^ 0 / (1 - β * q ^ α)) := by
              gcongr; exact geom_sum_Ico_le_of_lt_one hγ0 hγ
          _ = β / (1 - β * q ^ α) := by rw [pow_zero, mul_one_div]

theorem step1 (hd : 1 ≤ d) {α η M : ℝ} (hα : 0 < α) (hη : 0 < η) (hη1 : η < 1) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1, ∫⁻ y in far M x, U d α u x y
        ≤ ENNReal.ofReal C * ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
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
  refine ⟨β / (β - 1) * (β / (1 - β * (1 - η / M) ^ α)),
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith)),
    fun u hu => ?_⟩
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

end Dyda
