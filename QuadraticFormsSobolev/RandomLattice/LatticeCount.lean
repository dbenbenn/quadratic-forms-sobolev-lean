import QuadraticFormsSobolev.RandomLattice.Basic

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-! ## Helper lemmas -/

lemma supNormZ_nonneg (w : Fin d → ℤ) : 0 ≤ supNormZ w :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

lemma exists_supNormZ_eq (hd : 1 ≤ d) (w : Fin d → ℤ) : ∃ i, supNormZ w = |(w i : ℝ)| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => |(w i : ℝ)|)
  exact ⟨i, hi.symm⟩

lemma supNormZ_le {w : Fin d → ℤ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |(w i : ℝ)| ≤ r) :
    supNormZ w ≤ r := Real.iSup_le h hr

lemma one_le_supNormZ (hd : 1 ≤ d) {w : Fin d → ℤ} (h : supNormZ w ≠ 0) : 1 ≤ supNormZ w := by
  obtain ⟨i, hi⟩ := exists_supNormZ_eq hd w
  rw [hi] at h ⊢
  have : w i ≠ 0 := by intro h0; simp [h0] at h
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs this

lemma abs_coord_sub_le (y : EuclideanSpace ℝ (Fin d)) (w : Fin d → ℤ) (i : Fin d) :
    |y i - w i| ≤ dist y (latticePt d 1 w) := by
  have := PiLp.norm_apply_le (y - latticePt d 1 w) i
  rw [dist_eq_norm]
  simpa [latticePt, Real.norm_eq_abs] using this

lemma norm_le_of_abs_le {v : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, |v i| ≤ r) : ‖v‖ ≤ d * r := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * r ^ 2 := by simp
    _ ≤ (d * r) ^ 2 := by
        rw [mul_pow]
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · simp [h0]
        · have : (1:ℝ) ≤ d := by exact_mod_cast h0
          have hd2 : (d:ℝ) ≤ d ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg r)

lemma abs_le_supR (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |y i| ≤ ⨆ j, |y j| :=
  le_ciSup (f := fun j => |y j|) (Set.finite_range _).bddAbove i

lemma exists_supR_eq (hd : 1 ≤ d) (y : EuclideanSpace ℝ (Fin d)) : ∃ i, (⨆ j, |y j|) = |y i| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun j => |y j|)
  exact ⟨i, hi.symm⟩

lemma card_Icc_ceil_floor_le (a b : ℝ) (hab : a ≤ b) :
    (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℕ) : ℝ) ≤ b - a + 1 := by
  rw [Int.card_Icc]
  have h1 : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) = (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) := by norm_cast
  rw [h1, Int.toNat_eq_max]
  push_cast
  apply max_le
  · have := Int.floor_le b; have := Int.le_ceil a; linarith
  · linarith

lemma le_card_Icc_ceil_floor (a b : ℝ) :
    b - a - 1 ≤ (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℕ) : ℝ) := by
  rw [Int.card_Icc]
  have h1 : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) = (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) := by norm_cast
  rw [h1, Int.toNat_eq_max]
  push_cast
  refine le_trans ?_ (le_max_left _ _)
  have := Int.lt_floor_add_one b; have := Int.ceil_lt_add_one a; linarith

/-- The upper bound, uniform in `y`. -/
theorem tsum_count_le (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (d * δ * supNormZ w)).indicator (fun _ => (1 : ℝ≥0∞)) y
      ≤ ENNReal.ofReal (4 ^ d) := by
  set M : ℝ := ⨆ j, |y j| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (abs_le_supR y ⟨0, hd⟩)
  set c : ℝ := if M ≤ 3 / 2 then 1 else 3 / (2 * M) with hc
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> positivity
  set S : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => Finset.Icc ⌈y i - M⌉ ⌊y i + M⌋) with hS
  -- the pointwise analysis
  have key : ∀ w : Fin d → ℤ, y ∈ closedBall (latticePt d 1 w) (d * δ * supNormZ w) →
      supNormZ w ≠ 0 → w ∈ S ∧ (supNormZ w)⁻¹ ≤ c := by
    intro w hy hm
    set m := supNormZ w
    have hm0 : 0 ≤ m := supNormZ_nonneg w
    have hm1 : 1 ≤ m := one_le_supNormZ hd hm
    have hdist : dist y (latticePt d 1 w) ≤ m / 2 := by
      rw [mem_closedBall] at hy
      refine hy.trans ?_
      nlinarith
    have hco : ∀ i, |y i - w i| ≤ m / 2 := fun i => (abs_coord_sub_le y w i).trans hdist
    obtain ⟨i0, hi0⟩ := exists_supNormZ_eq hd w
    have hm2M : m ≤ 2 * M := by
      have h1 := hco i0
      have h2 := abs_le_supR y i0
      have h3 : |(w i0 : ℝ)| ≤ |y i0| + |y i0 - w i0| := by
        have := abs_sub_abs_le_abs_sub (w i0 : ℝ) (y i0)
        rw [abs_sub_comm] at this; linarith
      linarith
    have hM3m : M ≤ 3 * m / 2 := by
      apply Real.iSup_le _ (by positivity)
      intro i
      have h1 := hco i
      have h2 := abs_le_supNormZ w i
      have h3 : |y i| ≤ |(w i : ℝ)| + |y i - w i| := by
        have := abs_sub_abs_le_abs_sub (y i) (w i : ℝ); linarith
      linarith
    refine ⟨?_, ?_⟩
    · rw [hS, Fintype.mem_piFinset]
      intro i
      have h1 := abs_le.mp (hco i)
      rw [Finset.mem_Icc]
      constructor
      · apply Int.ceil_le.mpr; linarith
      · apply Int.le_floor.mpr; linarith
    · rw [hc]
      split_ifs with h
      · exact inv_le_one_of_one_le₀ hm1
      · rw [not_le] at h
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
  have hzero : ∀ w ∉ S, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
      (closedBall (latticePt d 1 w) (d * δ * supNormZ w)).indicator (fun _ => (1 : ℝ≥0∞)) y
        = 0 := by
    intro w hw
    by_cases hy : y ∈ closedBall (latticePt d 1 w) (d * δ * supNormZ w)
    · by_cases hm : supNormZ w = 0
      · simp [hm, zero_pow (by omega : d ≠ 0)]
      · exact absurd (key w hy hm).1 hw
    · simp [hy]
  rw [tsum_eq_sum (s := S) hzero]
  calc ∑ w ∈ S, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
      (closedBall (latticePt d 1 w) (d * δ * supNormZ w)).indicator (fun _ => (1 : ℝ≥0∞)) y
      ≤ ∑ _w ∈ S, ENNReal.ofReal (c ^ d) := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hy : y ∈ closedBall (latticePt d 1 w) (d * δ * supNormZ w)
        · by_cases hm : supNormZ w = 0
          · simp [hm, zero_pow (by omega : d ≠ 0)]
          · rw [indicator_of_mem hy, mul_one]
            exact ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (inv_nonneg.mpr (supNormZ_nonneg w)) (key w hy hm).2 d)
        · simp [hy]
    _ = ENNReal.ofReal ((S.card : ℝ) * c ^ d) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 ^ d) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hS, Fintype.card_piFinset]
        push_cast
        rw [← Fin.prod_const d c, ← Finset.prod_mul_distrib, ← Fin.prod_const d (4:ℝ)]
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        have hcard := card_Icc_ceil_floor_le (y i - M) (y i + M) (by linarith)
        rw [hc]
        split_ifs with h
        · linarith
        · rw [not_le] at h
          calc (((Finset.Icc ⌈y i - M⌉ ⌊y i + M⌋).card : ℕ) : ℝ) * (3 / (2 * M))
              ≤ (2 * M + 1) * (3 / (2 * M)) :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ ≤ 4 := by
                rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith

/-- The lower bound, for `‖y‖` large. -/
theorem le_tsum_count (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (hδ' : (d : ℝ) * δ ≤ 1 / 2) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ y : EuclideanSpace ℝ (Fin d), C ≤ ‖y‖ →
      ENNReal.ofReal k ≤ ∑' w : Fin d → ℤ, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (δ * supNormZ w / d)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hδ1 : δ ≤ 1 := by nlinarith
  refine ⟨2 * d ^ 3 / δ, (δ / (4 * d ^ 2)) ^ d, by positivity, by positivity, ?_⟩
  intro y hy
  set M : ℝ := ⨆ j, |y j| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (abs_le_supR y ⟨0, hd⟩)
  have hyM : ‖y‖ ≤ d * M := norm_le_of_abs_le hM0 (fun i => abs_le_supR y i)
  have hMbig : 2 * d ^ 2 ≤ δ * M := by
    have h1 : 2 * d ^ 3 ≤ δ * ‖y‖ := by
      rw [div_le_iff₀ hδ] at hy; linarith
    have h2 : δ * ‖y‖ ≤ δ * (d * M) := mul_le_mul_of_nonneg_left hyM hδ.le
    nlinarith
  have hMpos : 0 < M := by
    by_contra h
    have : M = 0 := le_antisymm (not_lt.mp h) hM0
    rw [this, mul_zero] at hMbig; nlinarith
  set r : ℝ := δ * M / (2 * d ^ 2) with hr
  have hr2 : 2 * d ^ 2 * r = δ * M := by rw [hr]; field_simp
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ (by positivity)]; linarith
  have hrM : r ≤ M / 2 := by
    rw [hr, div_le_iff₀ (by positivity)]
    have h1 : δ * M ≤ 1 * M := mul_le_mul_of_nonneg_right hδ1 hM0
    have h2 : (1 : ℝ) ≤ d ^ 2 := one_le_pow₀ hd1
    nlinarith
  set S : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => Finset.Icc ⌈y i - r⌉ ⌊y i + r⌋) with hS
  have key : ∀ w ∈ S, y ∈ closedBall (latticePt d 1 w) (δ * supNormZ w / d) ∧
      (2 * M)⁻¹ ≤ (supNormZ w)⁻¹ := by
    intro w hw
    rw [hS, Fintype.mem_piFinset] at hw
    have hco : ∀ i, |y i - w i| ≤ r := by
      intro i
      have h := Finset.mem_Icc.mp (hw i)
      have h1 := Int.ceil_le.mp h.1
      have h2 := Int.le_floor.mp h.2
      rw [abs_le]; constructor <;> linarith
    set m := supNormZ w
    obtain ⟨i0, hi0⟩ := exists_supR_eq hd y
    have hmlo : M - r ≤ m := by
      have h1 := hco i0
      have h2 := abs_le_supNormZ w i0
      have h3 : |y i0| ≤ |(w i0 : ℝ)| + |y i0 - w i0| := by
        have := abs_sub_abs_le_abs_sub (y i0) (w i0 : ℝ); linarith
      rw [hM] at *; linarith
    have hmhi : m ≤ M + r := by
      apply supNormZ_le (by linarith)
      intro i
      have h1 := hco i
      have h2 := abs_le_supR y i
      have h3 : |(w i : ℝ)| ≤ |y i| + |y i - w i| := by
        have := abs_sub_abs_le_abs_sub (w i : ℝ) (y i)
        rw [abs_sub_comm] at this; linarith
      linarith
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      have hn : ‖y - latticePt d 1 w‖ ≤ d * r :=
        norm_le_of_abs_le (by linarith) (fun i => by simpa [latticePt] using hco i)
      refine hn.trans ?_
      rw [le_div_iff₀ hd0]
      have : δ * (M / 2) ≤ δ * m := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      nlinarith
    · exact inv_anti₀ (by linarith) (by linarith)
  calc ENNReal.ofReal ((δ / (4 * d ^ 2)) ^ d)
      ≤ ENNReal.ofReal ((S.card : ℝ) * (2 * M)⁻¹ ^ d) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hS, Fintype.card_piFinset]
        push_cast
        have hq : δ / (4 * d ^ 2) = r * (2 * M)⁻¹ := by
          rw [hr]; field_simp; ring
        rw [hq, mul_pow, ← Fin.prod_const d r]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        have := le_card_Icc_ceil_floor (y i - r) (y i + r)
        linarith
    _ = ∑ _w ∈ S, ENNReal.ofReal ((2 * M)⁻¹ ^ d) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ w ∈ S, ENNReal.ofReal ((supNormZ w)⁻¹ ^ d) *
        (closedBall (latticePt d 1 w) (δ * supNormZ w / d)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [indicator_of_mem (key w hw).1, mul_one]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (key w hw).2 d)
    _ ≤ _ := ENNReal.sum_le_tsum S

end QFS
