import QuadraticFormsSobolev.Density.DomainPartition
import QuadraticFormsSobolev.Density.Main
import QuadraticFormsSobolev.LemmaA1Domain

/-!
# `C^∞(Ω̄)` is dense in `H_k(Ω)` on a bounded Lipschitz domain

`C^∞(Ω̄)` is taken to be the restrictions to `Ω` of smooth compactly supported functions on
`ℝ^d`. A partition of unity subordinate to the boundary charts and an interior piece splits `f`;
near the boundary each piece is shifted into `Ω` along its chart direction and mollified
(`Density/DomainPiece.lean`), in the interior it is mollified. The errors are controlled by the
continuity of translation in `L²(ℝ^d)` and in `L²(ℝ^d × ℝ^d)`.
-/

open MeasureTheory Metric Set Filter Topology Finset
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

set_option hygiene false in
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma lintegral_sq_sum_le (Ω : Set 𝔼) (s : Finset ℕ) {w : ℕ → 𝔼 → ℝ}
    (hw : ∀ k, Measurable (w k)) :
    ∫⁻ x in Ω, ENNReal.ofReal ((∑ k ∈ s, w k x) ^ 2) ≤
      (s.card : ℝ≥0∞) * ∑ k ∈ s, ∫⁻ x in Ω, ENNReal.ofReal (w k x ^ 2) := by
  rw [← lintegral_finsetSum s (fun k _ => by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (sq_sum_le_card_mul_sum_sq)

lemma formHs_sum_le (Ω : Set 𝔼) (α : ℝ) (s : Finset ℕ) {w : ℕ → 𝔼 → ℝ}
    (hw : ∀ k, Measurable (w k)) :
    formHs Ω α (fun x => ∑ k ∈ s, w k x) ≤ (s.card : ℝ≥0∞) * ∑ k ∈ s, formHs Ω α (w k) := by
  have hk := measurable_jumpKernel d α
  unfold formHs form
  rw [← lintegral_finsetSum s (f := fun k (p : 𝔼 × 𝔼) =>
      ENNReal.ofReal ((w k p.2 - w k p.1) ^ 2) * jumpKernel d α p.1 p.2)
      (fun k _ => ((by fun_prop : Measurable fun p : 𝔼 × 𝔼 =>
        ENNReal.ofReal ((w k p.2 - w k p.1) ^ 2)).mul hk)),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_mono fun p => ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  gcongr
  rw [← sum_sub_distrib, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal sq_sum_le_card_mul_sum_sq

lemma hasCompactSupport_finset_sum (s : Finset ℕ) {w : ℕ → 𝔼 → ℝ}
    (hw : ∀ k ∈ s, HasCompactSupport (w k)) : HasCompactSupport fun x => ∑ k ∈ s, w k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp_rw [sum_insert ha]
    exact (hw a (mem_insert_self a s)).add (ih fun k hk => hw k (mem_insert_of_mem hk))

/-- The chart bump: `1` on `B(c, r₀/8)`, supported in `B(c, r₀/4)`. -/
noncomputable def chartBump {r₀ : ℝ} (hr₀ : 0 < r₀) (c : 𝔼) : ContDiffBump c :=
  ⟨r₀ / 8, r₀ / 4, by positivity, by linarith⟩

lemma chartBump_lip {r₀ : ℝ} (hr₀ : 0 < r₀) (c : 𝔼) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |chartBump hr₀ c x - chartBump hr₀ c y| ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
    (ContDiffBump.hasCompactSupport (chartBump hr₀ c))
    (ContDiffBump.contDiff (n := 1) (chartBump hr₀ c)) one_ne_zero
  refine ⟨C, C.2, fun x y => ?_⟩
  have := hC.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

lemma final_arith (M : ℕ) (hM : 1 ≤ M) {K : ℝ≥0∞} (hK : K ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    (M : ℝ≥0∞) * (K * ENNReal.ofReal (ε / (2 * (M : ℝ) * (K.toReal + 1)))) < ENNReal.ofReal ε := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hK0 := ENNReal.toReal_nonneg (a := K)
  have hKe : K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
  set k := K.toReal with hk
  rw [hKe, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hK0,
    ← ENNReal.ofReal_mul hM0.le, ENNReal.ofReal_lt_ofReal_iff hε]
  rw [show (M : ℝ) * (k * (ε / (2 * M * (k + 1)))) = ε * (k / (2 * (k + 1))) by field_simp]
  have : k / (2 * (k + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  nlinarith

set_option maxHeartbeats 800000 in
/-- **`C_c^∞(ℝ^d)|_Ω` is dense in `H^{α/2}(Ω)`** for a bounded Lipschitz domain. -/
theorem formHs_domain_dense (hd : 1 ≤ d) {Ω : Set 𝔼} (hΩ : IsBoundedLipschitzDomain Ω) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {f : 𝔼 → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.restrict Ω)) (hS : formHs Ω α f ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : 𝔼 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∫⁻ x in Ω, ENNReal.ofReal ((f x - g x) ^ 2)) + formHs Ω α (f - g) < ENNReal.ofReal ε := by
  classical
  obtain ⟨W⟩ := Dyda.exists_chartCover hΩ
  have hΩo : IsOpen Ω := hΩ.2.2.choose_spec.2.choose_spec.1
  have hb : Bornology.IsBounded Ω := hΩ.1
  have hΩm := hΩo.measurableSet
  have hr₀ := W.hr₀
  have hL0 : (0 : ℝ) ≤ W.L := W.L.2
  have hne : Ωᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have : Nontrivial 𝔼 := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by rw [finrank_euclideanSpace_fin]; omega)
    exact NormedSpace.unbounded_univ ℝ 𝔼 (h ▸ hb)
  -- enumerate the charts
  set m := W.t.card with hm
  set zs : ℕ → 𝔼 := fun j => if h : j < m then (W.t.equivFin.symm ⟨j, h⟩ : 𝔼) else 0 with hzs
  have hzs_mem : ∀ j < m, zs j ∈ W.t := fun j hj => by simp [zs, hj]
  have hzs_surj : ∀ z ∈ W.t, ∃ j < m, zs j = z := by
    intro z hz
    refine ⟨W.t.equivFin ⟨z, hz⟩, (W.t.equivFin ⟨z, hz⟩).2, ?_⟩
    simp only [zs, Fin.eta, Equiv.symm_apply_apply]
    exact dif_pos (W.t.equivFin ⟨z, hz⟩).2
  -- the bumps
  set χ : ℕ → 𝔼 → ℝ := fun j => chartBump hr₀ (zs j) with hχ
  have hχ0 : ∀ j x, 0 ≤ χ j x := fun j x => ContDiffBump.nonneg _
  have hχ1 : ∀ j x, χ j x ≤ 1 := fun j x => ContDiffBump.le_one _
  have hχs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) := fun j => ContDiffBump.contDiff _
  have hχc : ∀ j, HasCompactSupport (χ j) := fun j => ContDiffBump.hasCompactSupport _
  choose Lc hLc0 hLc using fun j => chartBump_lip hr₀ (zs j)
  have hχL : ∀ i x y, |χ i x - χ i y| ≤ Lc i * ‖x - y‖ := hLc
  -- the interior margin
  obtain ⟨d₀, hd₀, hmargin⟩ : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ x ∈ Ω,
      (∀ j < m, x ∉ ball (zs j) (W.r₀ / 8)) → d₀ ≤ infDist x Ωᶜ := by
    set K₀ := closure Ω \ ⋃ j ∈ range m, ball (zs j) (W.r₀ / 8) with hK₀
    have hK₀c : IsCompact K₀ := hb.isCompact_closure.diff
      (isOpen_biUnion fun j _ => isOpen_ball)
    have hK₀Ω : K₀ ⊆ Ω := by
      rintro x ⟨hxc, hxn⟩
      by_contra hxΩ
      have hxF : x ∈ frontier Ω := by rw [hΩo.frontier_eq]; exact ⟨hxc, hxΩ⟩
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (W.hcov hxF)
      obtain ⟨j, hj, rfl⟩ := hzs_surj z hz
      exact hxn (mem_iUnion₂.mpr ⟨j, mem_range.mpr hj, hxz⟩)
    rcases K₀.eq_empty_or_nonempty with hK | hK
    · refine ⟨1, one_pos, fun x hx hx' => absurd (show x ∈ K₀ from ⟨subset_closure hx, ?_⟩)
        (by rw [hK]; exact notMem_empty x)⟩
      simp only [mem_iUnion₂, not_exists]
      exact fun j hj => hx' j (mem_range.mp hj)
    obtain ⟨x₀, hx₀, hmin⟩ := hK₀c.exists_isMinOn hK
      ((continuous_infDist_pt (Ωᶜ)).continuousOn)
    refine ⟨infDist x₀ Ωᶜ, (hΩo.isClosed_compl.notMem_iff_infDist_pos hne).mp
      (fun h => h (hK₀Ω hx₀)), fun x hx hx' => hmin ⟨subset_closure hx, ?_⟩⟩
    simp only [mem_iUnion₂, not_exists]
    exact fun j hj => hx' j (mem_range.mp hj)
  -- the pieces
  set ψs : ℕ → 𝔼 → ℝ := fun k => if k < m then partPi χ k else partR χ m with hψs
  set Ls : ℕ → ℝ := fun k => if k < m then Lc k + ∑ i ∈ range k, Lc i else
    ∑ i ∈ range m, Lc i with hLs
  set δs : ℕ → ℝ := fun k => if k < m then W.r₀ / 4 else d₀ / 2 with hδs
  set Us : ℕ → Set 𝔼 := fun k => if k < m then Ω ∩ ball (zs k) (W.r₀ / 2) else
    Ω ∩ {x | d₀ / 2 < infDist x Ωᶜ} with hUs
  have hψ0 : ∀ k x, 0 ≤ ψs k x := fun k x => by
    by_cases hk : k < m
    · simp only [ψs, if_pos hk]; exact (partPi_mem hχ0 hχ1 k x).1
    · simp only [ψs, if_neg hk]; exact (partR_mem hχ0 hχ1 m x).1
  have hψ1 : ∀ k x, ψs k x ≤ 1 := fun k x => by
    by_cases hk : k < m
    · simp only [ψs, if_pos hk]; exact (partPi_mem hχ0 hχ1 k x).2
    · simp only [ψs, if_neg hk]; exact (partR_mem hχ0 hχ1 m x).2
  have hψL : ∀ k x y, |ψs k x - ψs k y| ≤ Ls k * ‖x - y‖ := fun k x y => by
    by_cases hk : k < m
    · simp only [ψs, Ls, if_pos hk]; exact partPi_lip hχ0 hχ1 hχL k x y
    · simp only [ψs, Ls, if_neg hk]; exact partR_lip hχ0 hχ1 hχL m x y
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψs k) := fun k => by
    by_cases hk : k < m
    · simp only [ψs, if_pos hk]; exact contDiff_partPi hχs k
    · simp only [ψs, if_neg hk]; exact contDiff_partR hχs m
  have hsum : ∀ x, ∑ k ∈ range (m + 1), ψs k x = 1 := fun x => by
    rw [sum_range_succ]
    have h1 : ψs m x = partR χ m x := by simp [ψs]
    rw [h1, show ∑ k ∈ range m, ψs k x = ∑ k ∈ range m, partPi χ k x from
      sum_congr rfl fun k hk => by simp [ψs, mem_range.mp hk]]
    exact partPi_sum_add_partR χ m x
  have hδs : ∀ k, 0 < δs k := fun k => by
    by_cases hk : k < m
    · simp only [δs, if_pos hk]; positivity
    · simp only [δs, if_neg hk]; positivity
  have hUsm : ∀ k, MeasurableSet (Us k) := fun k => by
    by_cases hk : k < m
    · simp only [Us, if_pos hk]; exact hΩm.inter measurableSet_ball
    · simp only [Us, if_neg hk]
      exact hΩm.inter (measurableSet_lt measurable_const (continuous_infDist_pt _).measurable)
  have hUsΩ : ∀ k, Us k ⊆ Ω := fun k => by
    by_cases hk : k < m
    · simp only [Us, if_pos hk]; exact inter_subset_left
    · simp only [Us, if_neg hk]; exact inter_subset_left
  have hsupp : ∀ k, ∀ x ∈ Ω, ψs k x ≠ 0 → ∀ y ∈ Ω, ‖x - y‖ < δs k → y ∈ Us k := by
    intro k x hx hψ y hy hxy
    by_cases hk : k < m
    · simp only [ψs, δs, Us, if_pos hk] at hψ hxy ⊢
      have hχx := partPi_ne_zero hψ
      have hxb : x ∈ ball (zs k) (W.r₀ / 4) := by
        have hs := ContDiffBump.support_eq (chartBump hr₀ (zs k))
        have hx' : x ∈ Function.support (chartBump hr₀ (zs k)) := hχx
        rw [hs] at hx'
        exact hx' 
      refine ⟨hy, ?_⟩
      rw [mem_ball] at hxb ⊢
      calc dist y (zs k) ≤ dist y x + dist x (zs k) := dist_triangle _ _ _
        _ < W.r₀ / 4 + W.r₀ / 4 := by rw [dist_eq_norm, norm_sub_rev]; exact add_lt_add hxy hxb
        _ = W.r₀ / 2 := by ring
    · simp only [ψs, δs, Us, if_neg hk] at hψ hxy ⊢
      have hfar : ∀ j < m, x ∉ ball (zs j) (W.r₀ / 8) := by
        intro j hj hxj
        exact hψ (partR_eq_zero hj (ContDiffBump.one_of_mem_closedBall _
          (ball_subset_closedBall hxj)))
      have h1 := hmargin x hx hfar
      have h2 := infDist_le_infDist_add_dist (x := x) (y := y) (s := Ωᶜ)
      rw [dist_eq_norm] at h2
      exact ⟨hy, by show d₀ / 2 < infDist y Ωᶜ; linarith⟩
  -- the constants
  set Kk : ℕ → ℝ≥0∞ := fun k => 3 + 2 * kerJ d α (Ls k) + 2 * kerT d α (δs k) with hKk
  have hKk : ∀ k, Kk k ≠ ⊤ := fun k => by
    simp only [Kk]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨by norm_num,
      ENNReal.mul_ne_top (by norm_num) (kerJ_lt_top hd hα0 hα2 _).ne⟩,
      ENNReal.mul_ne_top (by norm_num) (kerT_lt_top hd hα0 hα2 (hδs k)).ne⟩
  set Ksum := ∑ k ∈ range (m + 1), Kk k with hKsumdef
  have hKsum : Ksum ≠ ⊤ := ENNReal.sum_ne_top.mpr fun k _ => hKk k
  set e : ℝ := ε / (2 * ((m + 1 : ℕ) : ℝ) * (Ksum.toReal + 1)) with he
  have he0 : 0 < e := by positivity
  set δ := ENNReal.ofReal e with hδ
  have hδ0 : 0 < δ := ENNReal.ofReal_pos.mpr he0
  -- translation continuity
  have hF2 := memLp_F0 hΩm hf
  have hFm := measurable_F0 hΩm hfm
  have hGm := measurable_Gq hΩm α hfm
  have : (volume : Measure (𝔼 × 𝔼)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hG2 : MemLp (Gq Ω α f) 2 volume :=
    memLp_two_of_lintegral_sq volume hGm (by rw [lintegral_Gq_sq hΩm]; exact hS)
  obtain ⟨η₁, hη₁, hT1⟩ := Metric.eventually_nhds_iff.mp
    (ENNReal.tendsto_nhds_zero.mp (tendsto_translate' volume hF2 hFm) δ hδ0)
  obtain ⟨η₂, hη₂, hT2⟩ := Metric.eventually_nhds_iff.mp
    (ENNReal.tendsto_nhds_zero.mp (tendsto_translate' volume hG2 hGm) δ hδ0)
  set η := min η₁ η₂ with hη
  have hη0 : 0 < η := lt_min hη₁ hη₂
  -- the shift and the mollifier
  set sh := min (η / 2) (W.r₀ / 8) with hsh
  have hsh0 : 0 < sh := lt_min (by positivity) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < min (η / 2) (min (sh / (4 * (1 + W.L)))
    (d₀ / 2)) from lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hn1 : 1 / ((n : ℝ) + 1) < η / 2 := hn.trans_le (min_le_left _ _)
  have hn2 : 1 / ((n : ℝ) + 1) < sh / (4 * (1 + W.L)) :=
    hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hn3 : 1 / ((n : ℝ) + 1) < d₀ / 2 :=
    hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set vs : ℕ → 𝔼 := fun k => if k < m then sh • W.ν (zs k) else 0 with hvs
  have hvs : ∀ k, ‖vs k‖ ≤ sh := fun k => by
    by_cases hk : k < m
    · simp only [vs, if_pos hk, norm_smul, W.hν _ (hzs_mem k hk), Real.norm_of_nonneg hsh0.le,
        mul_one, le_refl]
    · simp only [vs, if_neg hk, norm_zero]; exact hsh0.le
  have hsmall : ∀ k, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)), ‖vs k - t‖ < η := fun k t ht => by
    rw [mem_ball, dist_zero_right] at ht
    calc ‖vs k - t‖ ≤ ‖vs k‖ + ‖t‖ := norm_sub_le _ _
      _ < sh + η / 2 := add_lt_add_of_le_of_lt (hvs k) (ht.trans hn1)
      _ ≤ η / 2 + η / 2 := by gcongr; exact min_le_left _ _
      _ = η := by ring
  have hT1' : ∀ k, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ x, ENNReal.ofReal ((F0 Ω f (x - -(vs k - t)) - F0 Ω f x) ^ 2) ≤ δ := fun k t ht =>
    hT1 (by rw [dist_zero_right, norm_neg]; exact (hsmall k t ht).trans_le (min_le_left _ _))
  have hT2' : ∀ k, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)),
      ∫⁻ p, ENNReal.ofReal ((Gq Ω α f (p - -((vs k - t, vs k - t) : 𝔼 × 𝔼)) - Gq Ω α f p) ^ 2)
        ≤ δ := fun k t ht =>
    hT2 (by
      rw [dist_zero_right, norm_neg, Prod.norm_def, max_self]
      exact (hsmall k t ht).trans_le (min_le_right _ _))
  have hshift : ∀ k, ∀ x ∈ Us k, ∀ t ∈ ball (0 : 𝔼) (1 / (n + 1)), x - -(vs k - t) ∈ Ω := by
    intro k x hx t ht
    rw [mem_ball, dist_zero_right] at ht
    by_cases hk : k < m
    · simp only [Us, vs, if_pos hk] at hx ⊢
      set z := zs k
      have hz := hzs_mem k hk
      have hν := W.hν z hz
      have hcone : sh • W.ν z ∈ Dyda.chartCone (W.ν z) W.L := by
        simpa using Dyda.add_mem_chartCone hν hL0 hsh0 (w := 0) (by simp; positivity)
      have hnorm : ‖sh • W.ν z‖ = sh := by rw [norm_smul, hν, mul_one, Real.norm_of_nonneg hsh0.le]
      have hball := Dyda.ball_subset_of_chart hν (W.hφ z hz) (W.hchart z hz) (subset_closure hx.1)
        (by rw [← dist_eq_norm]; exact hx.2) hcone
        (by rw [hnorm]; linarith [min_le_right (η / 2) (W.r₀ / 8)])
      refine hball ?_
      rw [mem_ball, dist_eq_norm, hnorm,
        show x - -(sh • W.ν z - t) - (x + sh • W.ν z) = -t by abel, norm_neg]
      exact ht.trans hn2
    · simp only [Us, vs, if_neg hk] at hx ⊢
      rw [show x - -(0 - t) = x - t by abel]
      refine ball_infDist_compl_subset (x := x) ?_
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact (ht.trans hn3).trans hx.2
  -- the approximation
  set mk : ℕ → 𝔼 → ℝ := fun k => mollify n (fun y => F0 Ω f (y + vs k)) with hmk
  have hloc : ∀ k, LocallyIntegrable (fun y => F0 Ω f (y + vs k)) := fun k =>
    (memLp_F0_shift hΩm hf (vs k)).locallyIntegrable (by norm_num)
  set g : 𝔼 → ℝ := fun x => ∑ k ∈ range (m + 1), ψs k x * mk k x with hg
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    ContDiff.sum fun k _ => (hψs k).mul (contDiff_mollify (hloc k) n)
  have hgc : HasCompactSupport g := by
    refine hasCompactSupport_finset_sum _ fun k hk => ?_
    by_cases hk' : k < m
    · simp only [ψs, if_pos hk']
      exact ((hχc k).mul_right (f' := partR χ k)).mul_right
    · refine HasCompactSupport.mul_left (hasCompactSupport_mollify ?_ n)
      simp only [vs, if_neg hk', add_zero]
      refine HasCompactSupport.intro' hb.isCompact_closure isClosed_closure fun x hx => ?_
      exact indicator_of_notMem (fun h => hx (subset_closure h)) f
  have hfg : f - g = fun x => ∑ k ∈ range (m + 1), ψs k x * pieceU Ω f (vs k) n x := by
    funext x
    show f x - ∑ k ∈ range (m + 1), ψs k x * mk k x =
      ∑ k ∈ range (m + 1), ψs k x * (f x - mk k x)
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hsum, one_mul]
  have hwm : ∀ k, Measurable fun x => ψs k x * pieceU Ω f (vs k) n x := fun k =>
    (hψs k).continuous.measurable.mul (hfm.sub (contDiff_mollify (hloc k) n).continuous.measurable)
  have hbound : ∀ k, (∫⁻ x in Ω, ENNReal.ofReal ((ψs k x * pieceU Ω f (vs k) n x) ^ 2)) +
      formHs Ω α (fun x => ψs k x * pieceU Ω f (vs k) n x) ≤ Kk k * δ := fun k =>
    piece_bound hΩm hfm hf α (hψ0 k) (hψ1 k) (hψL k) (hδs k) (hUsm k) (hUsΩ k) (hsupp k)
      (vs k) n (hshift k) (hT1' k) (hT2' k)
  refine ⟨g, hgs, hgc, ?_⟩
  have hL2 := lintegral_sq_sum_le Ω (range (m + 1)) hwm
  have hH := formHs_sum_le Ω α (range (m + 1)) hwm
  rw [card_range] at hL2 hH
  have hfgx : ∀ x, f x - g x = ∑ k ∈ range (m + 1), ψs k x * pieceU Ω f (vs k) n x :=
    fun x => congrFun hfg x
  simp_rw [hfgx]
  rw [hfg]
  calc (∫⁻ x in Ω, ENNReal.ofReal ((∑ k ∈ range (m + 1), ψs k x * pieceU Ω f (vs k) n x) ^ 2)) +
        formHs Ω α (fun x => ∑ k ∈ range (m + 1), ψs k x * pieceU Ω f (vs k) n x)
      ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ∑ k ∈ range (m + 1),
          ((∫⁻ x in Ω, ENNReal.ofReal ((ψs k x * pieceU Ω f (vs k) n x) ^ 2)) +
            formHs Ω α (fun x => ψs k x * pieceU Ω f (vs k) n x)) := by
        rw [sum_add_distrib, mul_add]; exact add_le_add hL2 hH
    _ ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ∑ k ∈ range (m + 1), Kk k * δ := by
        gcongr with k hk; exact hbound k
    _ = ((m + 1 : ℕ) : ℝ≥0∞) * (Ksum * δ) := by rw [← sum_mul]
    _ < ENNReal.ofReal ε := final_arith (m + 1) (by omega) hKsum hε

/-- **Theorem 1.4, density on a bounded Lipschitz domain**: restrictions of `C_c^∞(ℝ^d)` are dense
in `H_k(Ω)`. -/
theorem theoremOneFour_density_domain (d : ℕ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
    ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MemLp f 2 (volume.restrict Ω) → form Ω k f ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε →
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 2 (volume.restrict Ω) ^ 2 + form Ω k (f - g) < ENNReal.ofReal ε := by
  intro ϑ Λ α hϑ hΛ hα hα2 Γ hΓ k hk f hf hfk ε hε
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hf0 : f = fun _ => f 0 := funext fun x => by rw [Subsingleton.elim x 0]
    refine ⟨f, hf0 ▸ contDiff_const, HasCompactSupport.of_compactSpace f, ?_⟩
    have h0 : form Ω k 0 = 0 := by simp [form]
    rw [sub_self, h0]
    simpa using hε
  obtain ⟨c, -, hc⟩ := theoremOneFour_domain d hΩ ϑ Λ α hϑ hΛ hα hα2
  have hS : formHs Ω α f ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfk) ((hc Γ hΓ k hk).2 f hf).1
  obtain ⟨f₀, hf₀m, hff₀⟩ : ∃ f₀ : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f₀ ∧
      f =ᵐ[volume.restrict Ω] f₀ :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  have hf₀ : MemLp f₀ 2 (volume.restrict Ω) := hf.ae_eq hff₀
  have hS₀ : formHs Ω α f₀ ≠ ⊤ := by rwa [formHs, ← form_congr_ae _ hff₀]
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨g, hg1, hg2, hg⟩ := formHs_domain_dense hd hΩ hα hα2 hf₀m hf₀ hS₀ (div_pos hε hΛ0)
  refine ⟨g, hg1, hg2, ?_⟩
  have hae : ∀ᵐ x ∂(volume.restrict Ω), (f - g) x = (f₀ - g) x := by
    filter_upwards [hff₀] with x hx; simp [hx]
  rw [eLpNorm_congr_ae hae, eLpNorm_two_sq', form_congr_ae _ hae]
  have hsq : ∫⁻ x, ENNReal.ofReal ((f₀ - g) x ^ 2) ∂(volume.restrict Ω) =
      ∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2) := rfl
  rw [hsq]
  calc (∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2)) + form Ω k (f₀ - g)
      ≤ (∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2)) +
          ENNReal.ofReal Λ * formHs Ω α (f₀ - g) := by
        gcongr; exact form_le_formHs hk _ _
    _ ≤ ENNReal.ofReal Λ * ((∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2)) + formHs Ω α (f₀ - g)) := by
        rw [mul_add]
        gcongr
        calc (∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2))
            = 1 * ∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2) := (one_mul _).symm
          _ ≤ ENNReal.ofReal Λ * ∫⁻ x in Ω, ENNReal.ofReal ((f₀ x - g x) ^ 2) := by
              gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hΛ
    _ < ENNReal.ofReal Λ * ENNReal.ofReal (ε / Λ) :=
        ENNReal.mul_lt_mul_right (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hΛ0)
          ENNReal.ofReal_ne_top hg
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hΛ0.le]; congr 1; field_simp

end QFS
