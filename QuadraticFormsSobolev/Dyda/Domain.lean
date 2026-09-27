import QuadraticFormsSobolev.Dyda.ChainStep
import QuadraticFormsSobolev.Dyda.Sun
import QuadraticFormsSobolev.Dyda.Poincare
import QuadraticFormsSobolev.Dyda.LipschitzCone
import QuadraticFormsSobolev.Dyda.Uniform

/-! # Dyda's inequality (13) on bounded Lipschitz domains

B. Dyda, *On comparability of integral forms*, J. Math. Anal. Appl. 318 (2006) 564–577,
Theorem 1(c) with `p = 2`: on a bounded Lipschitz domain `Ω`,
`∫_Ω ∫_Ω U ≤ c ∫_Ω ∫_{B(x, η δ_x)} U`, with `U(x, y) = (u(x) − u(y))²/|x − y|^{d+α}` and
`δ_x = dist(x, Ωᶜ)`, and `c` uniform in `α ∈ [α₀, 2)`.

The proof here follows Dyda's plan with three substitutions.
* **Step 1** is `Dyda.chain_step`, run on two kinds of admissible tips: interior pairs
  (`|x − T| < δ_x / 2`) and pairs whose direction lies in the interior cone of one of finitely many
  boundary charts (`Dyda/LipschitzCone.lean`), in place of his Lipschitz boxes and norm family.
* **Step 2** is `Dyda.sun_bound`: pairs at distance less than `ρ` are averaged over a ball of
  admissible points, deep inside `Ω` or up the chart cone.
* **Case (c)**, Dyda's finite cover and chaining, is `Dyda.pairInt_le_near`: pairs at distance at
  least `ρ` are controlled by the pairs at distance less than `ρ`, by connectedness.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace Dyda

variable {d : ℕ}

/-- Finitely many Lipschitz charts whose centres' `r₀/8`-balls cover the frontier. -/
structure ChartCover (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  r₀ : ℝ
  hr₀ : 0 < r₀
  L : ℝ≥0
  ν : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  φ : ∀ z, (ℝ ∙ ν z)ᗮ → ℝ
  t : Finset (EuclideanSpace ℝ (Fin d))
  ht : ∀ z ∈ t, z ∈ frontier Ω
  hν : ∀ z ∈ t, ‖ν z‖ = 1
  hφ : ∀ z ∈ t, LipschitzWith L (φ z)
  hchart : ∀ z ∈ t, Ω ∩ ball z r₀ =
    {x | φ z ((ℝ ∙ ν z)ᗮ.orthogonalProjectionOnto (x - z)) < ⟪ν z, x - z⟫} ∩ ball z r₀
  hcov : frontier Ω ⊆ ⋃ z ∈ t, ball z (r₀ / 8)

lemma exists_chartCover {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : QFS.IsBoundedLipschitzDomain Ω) :
    Nonempty (ChartCover Ω) := by
  classical
  obtain ⟨hb, -, r₀, hr₀, L, -, hch⟩ := hΩ
  have hex : ∀ z : EuclideanSpace ℝ (Fin d), ∃ ν : EuclideanSpace ℝ (Fin d),
      ∃ φ : (ℝ ∙ ν)ᗮ → ℝ, z ∈ frontier Ω → ‖ν‖ = 1 ∧ LipschitzWith L φ ∧
        Ω ∩ ball z r₀ =
          {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < ⟪ν, x - z⟫} ∩ ball z r₀ := by
    intro z
    by_cases hz : z ∈ frontier Ω
    · obtain ⟨ν, hν, φ, hφ, h⟩ := hch z hz
      exact ⟨ν, φ, fun _ => ⟨hν, hφ, h⟩⟩
    · exact ⟨0, 0, fun h => absurd h hz⟩
  choose ν φ hνφ using hex
  have hcpt : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨s, hs, hsf, hcov⟩ :=
    finite_approx_of_totallyBounded hcpt.totallyBounded (r₀ / 8) (by positivity)
  exact ⟨{ r₀ := r₀, hr₀ := hr₀, L := L, ν := ν, φ := φ, t := hsf.toFinset
           ht := fun z hz => hs (hsf.mem_toFinset.mp hz)
           hν := fun z hz => (hνφ z (hs (hsf.mem_toFinset.mp hz))).1
           hφ := fun z hz => (hνφ z (hs (hsf.mem_toFinset.mp hz))).2.1
           hchart := fun z hz => (hνφ z (hs (hsf.mem_toFinset.mp hz))).2.2
           hcov := by
             intro x hx
             obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcov hx)
             exact mem_iUnion₂.mpr ⟨z, hsf.mem_toFinset.mpr hz, hxz⟩ }⟩

namespace ChartCover

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} (W : ChartCover Ω)

/-- Interior pairs: `x ∈ Ω` and `|x − T| < δ_x / 2`. -/
def Pint (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ Ω ∧ ‖p.1 - p.2‖ < infDist p.1 Ωᶜ / 2}

/-- Cone pairs of the chart at `z`, with tip in the closure. -/
def Pcone (z : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.2 ∈ closure Ω ∧ ‖p.2 - z‖ < W.r₀ / 2 ∧ p.1 - p.2 ∈ chartCone (W.ν z) W.L ∧
    ‖p.1 - p.2‖ < W.r₀ / 4}

/-- Cone pairs of the chart at `z`, with second point in `Ω`. -/
def Acone (z : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {p | p.2 ∈ Ω ∧ ‖p.2 - z‖ < W.r₀ / 2 ∧ p.1 - p.2 ∈ chartCone (W.ν z) W.L ∧
    ‖p.1 - p.2‖ < W.r₀ / 4}

/-- The admissible tips. -/
def P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  Pint Ω ∪ ⋃ z ∈ W.t, W.Pcone z

/-- The pairs handled by the chain. -/
def A : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  Pint Ω ∪ ⋃ z ∈ W.t, W.Acone z

/-- `1/(4(1 + L))`: the cone ball ratio. -/
noncomputable def cr : ℝ := 1 / (4 * (1 + (W.L : ℝ)))

lemma cr_pos : 0 < W.cr := by unfold cr; positivity

lemma cr_le : W.cr ≤ 1 / 4 := by
  unfold cr
  have : (0 : ℝ) ≤ W.L := W.L.2
  gcongr; linarith

lemma isOpen_Pint (hΩ : IsOpen Ω) : IsOpen (Pint Ω) := by
  have h : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      ‖p.1 - p.2‖ < infDist p.1 Ωᶜ / 2} :=
    isOpen_lt (by fun_prop) ((continuous_infDist_pt _).comp continuous_fst |>.div_const _)
  exact (hΩ.preimage continuous_fst).inter h

lemma isOpen_cone_pairs (z : EuclideanSpace ℝ (Fin d)) :
    IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      ‖p.2 - z‖ < W.r₀ / 2 ∧ p.1 - p.2 ∈ chartCone (W.ν z) W.L ∧ ‖p.1 - p.2‖ < W.r₀ / 4} := by
  have h1 : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      ‖p.2 - z‖ < W.r₀ / 2} := isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.1 - p.2 ∈ chartCone (W.ν z) W.L} :=
    (isOpen_chartCone _ _).preimage (continuous_fst.sub continuous_snd)
  have h3 : IsOpen {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      ‖p.1 - p.2‖ < W.r₀ / 4} := isOpen_lt (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

lemma measurableSet_P (hΩ : IsOpen Ω) : MeasurableSet W.P := by
  refine (isOpen_Pint hΩ).measurableSet.union (Finset.measurableSet_biUnion _ fun z _ => ?_)
  exact (isClosed_closure.measurableSet.preimage measurable_snd).inter
    (W.isOpen_cone_pairs z).measurableSet

lemma measurableSet_A (hΩ : IsOpen Ω) : MeasurableSet W.A := by
  refine (isOpen_Pint hΩ).measurableSet.union (Finset.measurableSet_biUnion _ fun z _ => ?_)
  exact ((hΩ.preimage continuous_snd).inter (W.isOpen_cone_pairs z)).measurableSet

lemma mem_of_infDist_pos {x : EuclideanSpace ℝ (Fin d)} (h : 0 < infDist x Ωᶜ) : x ∈ Ω := by
  by_contra hx
  rw [infDist_zero_of_mem (show x ∈ Ωᶜ from hx)] at h
  exact lt_irrefl _ h

/-- **The admissibility hypothesis of `chain_step`**, with `θ = η c / 2`. -/
lemma admissible (hΩ : IsOpen Ω) {η : ℝ} (hη : 0 < η) :
    ∀ p ∈ W.P, ∀ s : ℝ, 0 < s → s ≤ 1 →
      p.2 + s • (p.1 - p.2) ∈ Ω ∧
        η * W.cr / 2 * s * ‖p.1 - p.2‖ < η * distC Ω (p.2 + s • (p.1 - p.2)) := by
  have hc0 := W.cr_pos
  have hc1 := W.cr_le
  rintro ⟨x, T⟩ hp s hs0 hs1
  simp only
  set q := T + s • (x - T) with hq
  rcases hp with ⟨hx, hxT⟩ | hp
  · -- interior pairs
    simp only at hx hxT
    have hqx : dist x q = (1 - s) * ‖x - T‖ := by
      rw [dist_eq_norm, hq, show x - (T + s • (x - T)) = (1 - s) • (x - T) by module, norm_smul,
        Real.norm_of_nonneg (by linarith)]
    have hδ := infDist_le_infDist_add_dist (x := x) (y := q) (s := Ωᶜ)
    have hn := norm_nonneg (x - T)
    have hsa : s * ‖x - T‖ ≤ ‖x - T‖ := by nlinarith
    have e1 : (1 - s) * ‖x - T‖ = ‖x - T‖ - s * ‖x - T‖ := by ring
    have hlt : s * ‖x - T‖ < distC Ω q := by
      have h' : infDist x Ωᶜ ≤ infDist q Ωᶜ + (‖x - T‖ - s * ‖x - T‖) := by
        rw [← e1, ← hqx]; exact hδ
      show s * ‖x - T‖ < infDist q Ωᶜ
      linarith
    have hpos : 0 < distC Ω q := lt_of_le_of_lt (by positivity) hlt
    refine ⟨mem_of_infDist_pos hpos, ?_⟩
    have hc2 : W.cr / 2 ≤ 1 := by linarith
    have hsn := mul_nonneg hs0.le hn
    calc η * W.cr / 2 * s * ‖x - T‖ = η * (W.cr / 2) * (s * ‖x - T‖) := by ring
      _ ≤ η * 1 * (s * ‖x - T‖) := by gcongr
      _ = η * (s * ‖x - T‖) := by ring
      _ < η * distC Ω q := mul_lt_mul_of_pos_left hlt hη
  · -- cone pairs
    obtain ⟨z, hz, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨hT, hTz, hcone, hr⟩ := hp
    simp only at hT hTz hcone hr
    set v := s • (x - T) with hv
    have hvc : v ∈ chartCone (W.ν z) W.L := smul_mem_chartCone hcone hs0
    have hvn : ‖v‖ = s * ‖x - T‖ := by rw [hv, norm_smul, Real.norm_of_nonneg hs0.le]
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr (ne_zero_of_mem_chartCone hvc)
    have hvr : ‖v‖ < W.r₀ / 4 := by
      rw [hvn]; nlinarith [norm_nonneg (x - T)]
    have hball := ball_subset_of_chart (W.hν z hz) (W.hφ z hz) (W.hchart z hz) hT hTz hvc hvr
    have hne : Ωᶜ.Nonempty := ⟨z, fun h => (hΩ.frontier_eq ▸ W.ht z hz).2 h⟩
    have hδ : W.cr * ‖v‖ ≤ distC Ω q := by
      have := le_infDist_of_ball_subset hne hball
      unfold distC
      calc W.cr * ‖v‖ = ‖v‖ / (4 * (1 + (W.L : ℝ))) := by rw [cr]; ring
        _ ≤ _ := this
    refine ⟨hball (mem_ball_self (by positivity)), ?_⟩
    calc η * W.cr / 2 * s * ‖x - T‖ = η * (W.cr / 2 * ‖v‖) := by rw [hvn]; ring
      _ < η * (W.cr * ‖v‖) := by gcongr; nlinarith
      _ ≤ η * distC Ω q := by gcongr

lemma tendsto_tip {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x y : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun N : ℕ => tip q N x y) Filter.atTop (nhds y) := by
  have hpow : Filter.Tendsto (fun N : ℕ => q ^ N) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have : Filter.Tendsto (fun N : ℕ => (1 - q ^ N)⁻¹) Filter.atTop (nhds 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hpow).inv₀ (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simpa [tip] using (tendsto_const_nhds (x := x)).add (this.smul_const (y - x))

/-- **The pairs of `A` have eventually admissible tips.** -/
lemma eventually_admissible (hΩ : IsOpen Ω) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ p ∈ W.A, p.1 ≠ p.2 → ∀ᶠ N : ℕ in Filter.atTop, (p.1, tip q N p.1 p.2) ∈ W.P := by
  rintro ⟨x, y⟩ hp -
  have ht := tendsto_tip hq0 hq1 x y
  rcases hp with ⟨hx, hxy⟩ | hp
  · have hO : IsOpen {T : EuclideanSpace ℝ (Fin d) | ‖x - T‖ < infDist x Ωᶜ / 2} :=
      isOpen_lt (continuous_const.sub continuous_id).norm continuous_const
    filter_upwards [ht.eventually (hO.mem_nhds hxy)] with N hN
    exact Or.inl ⟨hx, hN⟩
  · obtain ⟨z, hz, hy, hyz, hcone, hr⟩ := by simpa only [mem_iUnion₂] using hp
    have hO : IsOpen {T : EuclideanSpace ℝ (Fin d) | T ∈ Ω ∧ ‖T - z‖ < W.r₀ / 2 ∧
        x - T ∈ chartCone (W.ν z) W.L ∧ ‖x - T‖ < W.r₀ / 4} :=
      hΩ.inter ((W.isOpen_cone_pairs z).preimage (continuous_const.prodMk continuous_id))
    filter_upwards [ht.eventually (hO.mem_nhds ⟨hy, hyz, hcone, hr⟩)] with N hN
    obtain ⟨h1, h2, h3, h4⟩ := hN
    exact Or.inr (mem_iUnion₂.mpr ⟨z, hz, subset_closure h1, h2, h3, h4⟩)

/-- `K = 4L + 8`: how far up the cone the sun sits, in units of `|x − y|`. -/
noncomputable def K : ℝ := 4 * (W.L : ℝ) + 8

/-- The scale below which pairs are averaged over a sun. -/
noncomputable def ρ : ℝ := W.r₀ / (8 * (W.K + 14))

lemma K_ge : 8 ≤ W.K := by
  unfold K; have : (0 : ℝ) ≤ W.L := W.L.2; linarith

lemma ρ_pos : 0 < W.ρ := by
  unfold ρ; have := W.K_ge; have := W.hr₀; positivity

lemma norm_add_ge (a e : EuclideanSpace ℝ (Fin d)) : ‖a‖ - ‖e‖ ≤ ‖a + e‖ := by
  have := norm_sub_le (a + e) e
  rw [add_sub_cancel_right] at this
  linarith

/-- **The sun exists.** Every near pair `(x, y)` of `Ω` has a ball of radius `|x − y|/2` of points
`z` with `(z, x)` and `(z, y)` handled: deep inside `Ω` if `x` is far from the boundary, up the
chart cone otherwise. -/
lemma sun (hb : Bornology.IsBounded Ω) :
    ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖x - y‖ < W.ρ →
      ∃ G, ball G (1 / 2 * ‖x - y‖) ⊆ sunSet W.A (W.K + 1) x y := by
  intro x hx y hy hxy hr
  set r := ‖x - y‖ with hr_def
  have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hK := W.K_ge
  have hKr : 9 * r ≤ (W.K + 1) * r := mul_le_mul_of_nonneg_right (by linarith) hr0.le
  by_cases hdeep : 13 * r ≤ infDist x Ωᶜ
  · refine ⟨x + (3 : ℝ) • (x - y), fun z hz => ?_⟩
    set e := z - (x + (3 : ℝ) • (x - y)) with he_def
    have he : ‖e‖ < r / 2 := by rw [mem_ball, dist_eq_norm] at hz; linarith
    have hzx : z - x = (3 : ℝ) • (x - y) + e := by rw [he_def]; abel
    have hzy : z - y = (4 : ℝ) • (x - y) + e := by rw [he_def]; module
    have n3 : ‖(3 : ℝ) • (x - y)‖ = 3 * r := by rw [norm_smul, ← hr_def]; norm_num
    have n4 : ‖(4 : ℝ) • (x - y)‖ = 4 * r := by rw [norm_smul, ← hr_def]; norm_num
    have hzx1 : ‖z - x‖ ≤ 3 * r + ‖e‖ := by rw [hzx, ← n3]; exact norm_add_le _ _
    have hzx2 : 3 * r - ‖e‖ ≤ ‖z - x‖ := by rw [hzx, ← n3]; exact norm_add_ge _ _
    have hzy1 : ‖z - y‖ ≤ 4 * r + ‖e‖ := by rw [hzy, ← n4]; exact norm_add_le _ _
    have hzy2 : 4 * r - ‖e‖ ≤ ‖z - y‖ := by rw [hzy, ← n4]; exact norm_add_ge _ _
    have hδ := infDist_le_infDist_add_dist (x := x) (y := z) (s := Ωᶜ)
    rw [dist_comm, dist_eq_norm] at hδ
    have hδz : 9 * r < infDist z Ωᶜ := by linarith
    have hzΩ : z ∈ Ω := mem_of_infDist_pos (by linarith)
    exact ⟨Or.inl ⟨hzΩ, by linarith⟩, Or.inl ⟨hzΩ, by linarith⟩, by linarith, by linarith,
      by linarith, by linarith⟩
  · push Not at hdeep
    have hne : Ω ≠ univ := by
      intro h
      have : Nontrivial (EuclideanSpace ℝ (Fin d)) := ⟨⟨x, y, hxy⟩⟩
      exact NormedSpace.unbounded_univ ℝ _ (h ▸ hb)
    obtain ⟨b, hbF, hbd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
    obtain ⟨zc, hzc, hbz⟩ := mem_iUnion₂.mp (W.hcov hbF)
    rw [mem_ball, dist_eq_norm] at hbz
    have hν := W.hν zc hzc
    have hρ : (W.K + 14) * r < W.r₀ / 8 := by
      have := W.hr₀
      have h1 : r < W.r₀ / (8 * (W.K + 14)) := hr
      rw [lt_div_iff₀ (by positivity)] at h1
      linarith
    have hxb : ‖x - b‖ < 13 * r := by rw [← dist_eq_norm, ← hbd]; exact hdeep
    have hxz : ‖x - zc‖ < W.r₀ / 4 := by
      have := norm_sub_le_norm_sub_add_norm_sub x b zc
      nlinarith
    have hyz : ‖y - zc‖ < W.r₀ / 4 := by
      have := norm_sub_le_norm_sub_add_norm_sub y x zc
      rw [norm_sub_rev y x] at this
      have := norm_sub_le_norm_sub_add_norm_sub x b zc
      nlinarith
    refine ⟨(1 / 2 : ℝ) • (x + y) + (W.K * r) • W.ν zc, fun z hz => ?_⟩
    set e := z - ((1 / 2 : ℝ) • (x + y) + (W.K * r) • W.ν zc) with he_def
    have he : ‖e‖ < r / 2 := by rw [mem_ball, dist_eq_norm] at hz; linarith
    have hKn : ‖(W.K * r) • W.ν zc‖ = W.K * r := by
      rw [norm_smul, hν, mul_one, Real.norm_of_nonneg (by nlinarith)]
    -- the two offsets from the cone axis
    have key : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ < r →
        (W.K * r) • W.ν zc + w ∈ chartCone (W.ν zc) W.L ∧
          r ≤ ‖(W.K * r) • W.ν zc + w‖ ∧ ‖(W.K * r) • W.ν zc + w‖ ≤ (W.K + 1) * r := by
      intro w hw
      refine ⟨add_mem_chartCone hν W.L.2 (mul_pos (by linarith) hr0) ?_, ?_, ?_⟩
      · calc ‖w‖ * (4 * (W.L : ℝ) + 8) ≤ r * (4 * (W.L : ℝ) + 8) :=
            mul_le_mul_of_nonneg_right hw.le (by have : (0 : ℝ) ≤ W.L := W.L.2; linarith)
          _ = W.K * r := by unfold K; ring
      · have := norm_add_ge ((W.K * r) • W.ν zc) w
        rw [hKn] at this; nlinarith
      · have := norm_add_le ((W.K * r) • W.ν zc) w
        rw [hKn] at this; nlinarith
    have hwx : ‖(1 / 2 : ℝ) • (y - x) + e‖ < r := by
      have := norm_add_le ((1 / 2 : ℝ) • (y - x)) e
      rw [norm_smul, norm_sub_rev y x] at this; norm_num at this; linarith
    have hwy : ‖(1 / 2 : ℝ) • (x - y) + e‖ < r := by
      have := norm_add_le ((1 / 2 : ℝ) • (x - y)) e
      rw [norm_smul] at this; norm_num at this; linarith
    have hzx : z - x = (W.K * r) • W.ν zc + ((1 / 2 : ℝ) • (y - x) + e) := by
      rw [he_def]; module
    have hzy : z - y = (W.K * r) • W.ν zc + ((1 / 2 : ℝ) • (x - y) + e) := by
      rw [he_def]; module
    obtain ⟨cx, lx, ux⟩ := key _ hwx
    obtain ⟨cy, ly, uy⟩ := key _ hwy
    rw [← hzx] at cx lx ux
    rw [← hzy] at cy ly uy
    have hsmall : (W.K + 1) * r < W.r₀ / 4 := by nlinarith
    exact ⟨Or.inr (mem_iUnion₂.mpr ⟨zc, hzc, hx, by linarith, cx, by linarith⟩),
      Or.inr (mem_iUnion₂.mpr ⟨zc, hzc, hy, by linarith, cy, by linarith⟩),
      lx, ux, ly, uy⟩

end ChartCover

/-- **Dyda (2006), inequality (13), on a bounded Lipschitz domain, uniformly in `α ∈ [α₀, 2)`.** -/
theorem lintegral_le_regional_lipschitz {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : QFS.IsBoundedLipschitzDomain Ω) {α₀ η : ℝ} (hα₀ : 0 < α₀) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 → ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in Ω, ∫⁻ y in Ω, U d α u x y
        ≤ ENNReal.ofReal c * ∫⁻ x in Ω, ∫⁻ y in ball x (η * infDist x Ωᶜ), U d α u x y := by
  obtain ⟨W⟩ := exists_chartCover hΩ
  obtain ⟨hb, hconn, -, -, -, hΩo, -⟩ := hΩ
  set θ := η * W.cr / 2 with hθ
  have hc0 := W.cr_pos
  have hc1 := W.cr_le
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    have : η * W.cr ≤ 1 * (1 / 4) := mul_le_mul hη1.le hc1 hc0.le zero_le_one
    linarith
  obtain ⟨KP, hKP, hPoinc⟩ := pairInt_le_near hΩo hb hconn.isPreconnected W.ρ_pos
  have hK := W.K_ge
  set S : ℝ := 4 * (W.K + 1) ^ d * (W.K + 1) ^ ((d : ℝ) + 2) / (1 / 2) ^ d with hS
  set B : ℝ := (1 + θ) ^ (2 : ℝ) / ((1 + θ) ^ α₀ - 1) *
    ((1 + θ) ^ (2 : ℝ) / (1 - (1 - θ ^ 2) ^ α₀)) with hB
  have hB0 : 0 < B := by
    have h1 : 0 < (1 + θ) ^ α₀ - 1 := by
      have := Real.one_lt_rpow (by linarith : 1 < 1 + θ) hα₀; linarith
    have h2 : 0 < 1 - (1 - θ ^ 2) ^ α₀ := by
      have := Real.rpow_lt_one (by nlinarith : (0:ℝ) ≤ 1 - θ ^ 2) (by nlinarith) hα₀; linarith
    positivity
  have hS0 : 0 < S := by positivity
  refine ⟨(1 + KP.toReal) * S * B, by positivity, fun α hα hα2 u hu => ?_⟩
  have hα0 : 0 < α := hα₀.trans_le hα
  -- Step 1 and the sun
  have hchain := chain_step (u := u) hΩo (W.measurableSet_P hΩo) hα0 hθ0 hθ1 (W.admissible hΩo hη)
    (W.eventually_admissible hΩo (q := 1 - θ) (by linarith) (by linarith)) hu (η := η)
  have hsun := sun_bound hΩo.measurableSet (W.measurableSet_A hΩo) (ρ := W.ρ) (ε := 1 / 2)
    (C := W.K + 1) (by norm_num) (by linarith) hα0 hα2.le (W.sun hb) hu
  have hcc : chainConst α θ ≤ B := dyu_step1_const_le hα₀ hα hα2 hθ0 hθ1
  set R := ∫⁻ x in Ω, ∫⁻ y in ball x (η * infDist x Ωᶜ), U d α u x y
  set near := ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x W.ρ, U d α u x y
  have hnear : near ≤ ENNReal.ofReal (S * B) * R := by
    calc near ≤ ENNReal.ofReal S * ∫⁻ z, ∫⁻ w, W.A.indicator (fun p => U d α u p.1 p.2) (z, w) :=
          hsun
      _ ≤ ENNReal.ofReal S * (ENNReal.ofReal B * R) :=
          mul_le_mul_of_nonneg_left
            (hchain.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcc) zero_le)) zero_le
      _ = ENNReal.ofReal (S * B) * R := by rw [ENNReal.ofReal_mul hS0.le, mul_assoc]
  -- the far pairs
  set e : ℝ := (d : ℝ) + α
  have hρ := W.ρ_pos
  have hfar : ∫⁻ x in Ω, ∫⁻ y in Ω \ ball x W.ρ, U d α u x y ≤ KP * near := by
    have h1 : ∀ x y, y ∉ ball x W.ρ →
        U d α u x y ≤ ENNReal.ofReal (1 / W.ρ ^ e) * ENNReal.ofReal ((u x - u y) ^ 2) := by
      intro x y hy
      rw [mem_ball, not_lt, dist_eq_norm, norm_sub_rev] at hy
      rw [← ENNReal.ofReal_mul (by positivity), U]
      apply ENNReal.ofReal_le_ofReal
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow hρ.le hy (by positivity))
    have h2 : ∀ x y, y ∈ ball x W.ρ →
        ENNReal.ofReal ((u x - u y) ^ 2) ≤ ENNReal.ofReal (W.ρ ^ e) * U d α u x y := by
      intro x y hy
      rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
      rw [U, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hxy : x = y
      · subst hxy; simp
      have hs : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      rw [mul_div_assoc', le_div_iff₀ (by positivity), mul_comm (W.ρ ^ e)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hy.le (by positivity))
        (sq_nonneg _)
    have hne : ENNReal.ofReal (1 / W.ρ ^ e) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ∫⁻ x in Ω, ∫⁻ y in Ω \ ball x W.ρ, U d α u x y
        ≤ ∫⁻ x in Ω, ∫⁻ y in Ω, ENNReal.ofReal (1 / W.ρ ^ e) * ENNReal.ofReal ((u x - u y) ^ 2) :=
          lintegral_mono fun x => (setLIntegral_mono' (hΩo.measurableSet.diff measurableSet_ball)
            fun y hy => h1 x y hy.2).trans (lintegral_mono_set sdiff_subset)
      _ = ENNReal.ofReal (1 / W.ρ ^ e) * pairInt u Ω Ω := by
          rw [pairInt, ← lintegral_const_mul' _ _ hne]
          exact lintegral_congr fun x => lintegral_const_mul' _ _ hne
      _ ≤ ENNReal.ofReal (1 / W.ρ ^ e) * (KP * ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x W.ρ,
            ENNReal.ofReal ((u x - u y) ^ 2)) := by gcongr; exact hPoinc u hu
      _ ≤ ENNReal.ofReal (1 / W.ρ ^ e) * (KP * ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x W.ρ,
            ENNReal.ofReal (W.ρ ^ e) * U d α u x y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lintegral_mono fun x =>
            setLIntegral_mono' (hΩo.measurableSet.inter measurableSet_ball)
              fun y hy => h2 x y hy.2) zero_le) zero_le
      _ = ENNReal.ofReal (1 / W.ρ ^ e) * ENNReal.ofReal (W.ρ ^ e) * KP * near := by
          have hne' : ENNReal.ofReal (W.ρ ^ e) ≠ ⊤ := ENNReal.ofReal_ne_top
          have : ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x W.ρ, ENNReal.ofReal (W.ρ ^ e) * U d α u x y
              = ENNReal.ofReal (W.ρ ^ e) * near := by
            rw [← lintegral_const_mul' _ _ hne']
            exact lintegral_congr fun x => lintegral_const_mul' _ _ hne'
          rw [this]; ring
      _ = KP * near := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel (by positivity),
            ENNReal.ofReal_one, one_mul]
  have hsplit : ∫⁻ x in Ω, ∫⁻ y in Ω, U d α u x y ≤
      near + ∫⁻ x in Ω, ∫⁻ y in Ω \ ball x W.ρ, U d α u x y := by
    have hm : Measurable fun x => ∫⁻ y in Ω \ ball x W.ρ, U d α u x y := by
      have : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          (Ω \ ball p.1 W.ρ).indicator (U d α u p.1) p.2 := by
        have hset : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ Ω \ ball p.1 W.ρ} :=
          (hΩo.measurableSet.preimage measurable_snd).diff
            (measurableSet_lt (by fun_prop) measurable_const)
        exact ((measurable_U α hu).indicator hset)
      simpa [← lintegral_indicator (hΩo.measurableSet.diff measurableSet_ball)] using
        this.lintegral_prod_right'
    rw [← lintegral_add_right _ hm]
    refine lintegral_mono fun x => ?_
    calc ∫⁻ y in Ω, U d α u x y
        = ∫⁻ y in (Ω ∩ ball x W.ρ) ∪ (Ω \ ball x W.ρ), U d α u x y := by
          rw [inter_union_sdiff]
      _ ≤ _ := lintegral_union_le _ _ _
  calc ∫⁻ x in Ω, ∫⁻ y in Ω, U d α u x y
      ≤ near + KP * near := hsplit.trans (add_le_add le_rfl hfar)
    _ = (1 + KP) * near := by ring
    _ ≤ ENNReal.ofReal (1 + KP.toReal) * (ENNReal.ofReal (S * B) * R) := by
        gcongr
        rw [ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
          ENNReal.ofReal_toReal hKP]
    _ = ENNReal.ofReal ((1 + KP.toReal) * S * B) * R := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_assoc]

end Dyda
