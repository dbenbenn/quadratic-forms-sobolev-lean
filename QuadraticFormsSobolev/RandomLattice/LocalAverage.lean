import QuadraticFormsSobolev.Section1

/-!
# From the regional form to the `H_k` form, by averaging over small balls

For `z ∈ B = B_R(x₀)` put `δ_z = dist(z, Bᶜ)` and `Q_z = B(z, δ_z/(2κ))`, so that
`B(z, κ · δ_z/(2κ)) ⊆ B`. Averaging an enlarged-ball comparability
`formHs(Q) ≤ C form(κQ)` over `z ∈ B` against the weight `δ_z^{-d}` and exchanging the order of
integration (Tonelli):

* every pair `(x, y)` with `|x − y| < η δ_x`, `η = 1/(8κ)`, lies in `Q_z × Q_z` for all
  `z ∈ B(x, η δ_x)`, a set of weighted measure at least `(η/2)^d |B_1|`;
* every pair `(x, y)` lies in `B(z, δ_z/2)²` only for `z ∈ B(x, δ_x)` with `δ_z > 2δ_x/3`,
  a set of weighted measure at most `(3/2)^d |B_1|`.

So the regional form is at most `C (3/η)^d = C (24κ)^d` times the `H_k` form of `B`. This replaces
the Whitney decomposition of Lemma A.1's proof.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- The set of triples `(z, x, y)` with `z ∈ B` and `x, y ∈ ball z (r z)` is measurable. -/
lemma locAvg_measurableSet {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B)
    {r : EuclideanSpace ℝ (Fin d) → ℝ} (hr : Continuous r) :
    MeasurableSet {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < r q.1 ∧ dist q.2.2 q.1 < r q.1} := by
  refine IsOpen.measurableSet ?_
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) => dist q.2.1 q.1 :=
    (continuous_fst.comp continuous_snd).dist continuous_fst
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) => dist q.2.2 q.1 :=
    (continuous_snd.comp continuous_snd).dist continuous_fst
  have h3 : Continuous fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) => r q.1 := hr.comp continuous_fst
  have h := (hB.preimage continuous_fst).inter ((isOpen_lt h1 h3).inter (isOpen_lt h2 h3))
  exact h

/-- The kernel integrand of `formHs` is measurable. -/
lemma locAvg_measurable_F {α : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 := by
  unfold jumpKernel
  exact (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal.mul
    ((measurable_fst.sub measurable_snd).norm.pow_const _).ennreal_ofReal

/-- Tonelli: averaging the forms on the balls `ball z (r z)` over `z ∈ B` against `w`. -/
lemma locAvg_swap {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B)
    {r : EuclideanSpace ℝ (Fin d) → ℝ} (hr : Continuous r)
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hw : Measurable w) (hwt : ∀ z, w z ≠ ⊤)
    {g : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z in B, w z * ∫⁻ p in ball z (r z) ×ˢ ball z (r z), g p
      = ∫⁻ p, g p * ∫⁻ z, {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < r q.1 ∧ dist q.2.2 q.1 < r q.1}.indicator
        (fun q => w q.1) (z, p) := by
  set U := {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < r q.1 ∧ dist q.2.2 q.1 < r q.1}
  have hU : MeasurableSet U := locAvg_measurableSet hB hr
  have hΨ : Measurable (U.indicator fun q => w q.1) := (hw.comp measurable_fst).indicator hU
  rw [← lintegral_indicator hB.measurableSet]
  calc _ = ∫⁻ z, ∫⁻ p, U.indicator (fun q => w q.1) (z, p) * g p := by
        congr 1; funext z
        by_cases hz : z ∈ B
        · rw [indicator_of_mem hz,
            ← lintegral_indicator (measurableSet_ball.prod measurableSet_ball),
            ← lintegral_const_mul' _ _ (hwt z)]
          congr 1; funext p
          by_cases hp : p ∈ ball z (r z) ×ˢ ball z (r z)
          · have hq : (z, p) ∈ U := ⟨hz, hp.1, hp.2⟩
            rw [indicator_of_mem hp, indicator_of_mem hq]
          · have hq : (z, p) ∉ U := fun h => hp ⟨h.2.1, h.2.2⟩
            rw [indicator_of_notMem hp, indicator_of_notMem hq]; simp
        · rw [indicator_of_notMem hz]
          have h0 : ∀ p, U.indicator (fun q => w q.1) (z, p) * g p = 0 := fun p => by
            rw [indicator_of_notMem (fun h => hz h.1), zero_mul]
          simp only [h0, lintegral_zero]
    _ = ∫⁻ p, ∫⁻ z, U.indicator (fun q => w q.1) (z, p) * g p :=
        lintegral_lintegral_swap ((hΨ.mul (hg.comp measurable_snd)).aemeasurable)
    _ = _ := by
        congr 1; funext p
        have hm : Measurable fun z => U.indicator (fun q => w q.1) (z, p) :=
          hΨ.comp measurable_prodMk_right
        rw [lintegral_mul_const (g p) hm, mul_comm]

/-- Measurability of the weighted-count function. -/
lemma locAvg_measurable_H {B : Set (EuclideanSpace ℝ (Fin d))} (hB : IsOpen B)
    {r : EuclideanSpace ℝ (Fin d) → ℝ} (hr : Continuous r)
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hw : Measurable w) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z, {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < r q.1 ∧ dist q.2.2 q.1 < r q.1}.indicator
        (fun q => w q.1) (z, p) :=
  ((hw.comp measurable_fst).indicator (locAvg_measurableSet hB hr)).lintegral_prod_left'

/-- **The regional form is controlled by the `H_k` form of any open set**, given an enlarged-ball
comparability for `f` on all balls. No Whitney decomposition is needed: the averaging uses only that
balls near `x` of radius comparable to `δ_x = dist(x, Ωᶜ)` lie in `Ω`. -/
theorem regional_le_form_of_ballComparability_open {α κ C : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ C)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (hball : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      formHs (ball z r) α f ≤ ENNReal.ofReal C * form (ball z (κ * r)) k f)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω) :
    ∫⁻ x in Ω, ∫⁻ y in ball x ((8 * κ)⁻¹ * infDist x Ωᶜ),
        ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y
      ≤ ENNReal.ofReal (C * (24 * κ) ^ d) * form Ω k f := by
  classical
  by_cases hΩne : Ω.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hΩne
    simp [hΩne]
  set B := Ω with hBdef
  by_cases hne : Bᶜ.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [hne]
  have hBo : IsOpen B := hΩ
  have hκ0 : 0 < κ := by linarith
  set δ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => infDist z Bᶜ with hδdef
  have hδc : Continuous δ := continuous_infDist_pt _
  have hδ0 : ∀ z, 0 ≤ δ z := fun z => infDist_nonneg
  have hδpos : ∀ x ∈ B, 0 < δ x := fun x hx =>
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hx)
  have hδlip : ∀ x z, δ x ≤ δ z + dist x z := fun x z => infDist_le_infDist_add_dist
  have hsub : ∀ x, ∀ r ≤ δ x, ball x r ⊆ B := fun x r hr =>
    (ball_subset_ball hr).trans ball_infDist_compl_subset
  -- nontriviality and the volume of balls
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨x₁, hx₁⟩ := hΩne
    exact ⟨⟨x₁, y, fun h => hy (h ▸ hx₁)⟩⟩
  set V := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hVdef
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hvol : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 ≤ r →
      volume (ball x r) = ENNReal.ofReal (r ^ d) * V := fun x r hr => by
    rw [Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin]
  set w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun z => ENNReal.ofReal ((δ z)⁻¹ ^ d) with hwdef
  have hw : Measurable w := ((hδc.measurable.inv).pow_const d).ennreal_ofReal
  have hwt : ∀ z, w z ≠ ⊤ := fun z => ENNReal.ofReal_ne_top
  set F : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2 with hFdef
  have hF : Measurable F := locAvg_measurable_F hf
  set G : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2 with hGdef
  set η : ℝ := (8 * κ)⁻¹ with hηdef
  have hηκ : η * κ = 1 / 8 := by rw [hηdef]; field_simp
  have hη0 : 0 < η := by positivity
  have hη8 : η ≤ 1 / 8 := by nlinarith
  set ρ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => δ z / (2 * κ) with hρdef
  have hρc : Continuous ρ := hδc.div_const _
  have hsc : Continuous fun z => κ * ρ z := continuous_const.mul hρc
  set c : ℝ≥0∞ := ENNReal.ofReal ((η / 2) ^ d) * V with hcdef
  set c' : ℝ≥0∞ := ENNReal.ofReal ((3 / 2) ^ d) * V with hc'def
  have hc0 : c ≠ 0 := mul_ne_zero (by simp; positivity) hV0
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  have hc't : c' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  set U₁ := {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < ρ q.1 ∧ dist q.2.2 q.1 < ρ q.1}
    with hU₁
  set U₂ := {q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) | q.1 ∈ B ∧ dist q.2.1 q.1 < κ * ρ q.1 ∧
        dist q.2.2 q.1 < κ * ρ q.1} with hU₂
  set H₁ := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    ∫⁻ z, U₁.indicator (fun q => w q.1) (z, p) with hH₁def
  set H₂ := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    ∫⁻ z, U₂.indicator (fun q => w q.1) (z, p) with hH₂def
  have hH₁m : Measurable H₁ := locAvg_measurable_H hBo hρc hw
  -- the two averaged quantities
  set I₁ := ∫⁻ z in B, w z * formHs (ball z (ρ z)) α f with hI₁
  set I₂ := ∫⁻ z in B, w z * form (ball z (κ * ρ z)) k f with hI₂
  have hI₁eq : I₁ = ∫⁻ p, F p * H₁ p := locAvg_swap hBo hρc hw hwt hF
  have hI₂eq : I₂ = ∫⁻ p, G p * H₂ p := locAvg_swap hBo hsc hw hwt hG
  -- lower bound on the weighted count
  have hlow : ∀ x ∈ B, ∀ y ∈ ball x (η * δ x), c ≤ H₁ (x, y) := by
    intro x hx y hy
    have hx0 := hδpos x hx
    have hpt : ∀ z ∈ ball x (η * δ x),
        ENNReal.ofReal ((2 * δ x)⁻¹ ^ d) ≤ U₁.indicator (fun q => w q.1) (z, (x, y)) := by
      intro z hz
      rw [mem_ball] at hz hy
      have hzB : z ∈ B := hsub x (η * δ x) (by nlinarith) (mem_ball.2 hz)
      have h1 := hδlip x z
      have h2 := hδlip z x
      have hxz : dist x z = dist z x := dist_comm _ _
      have hηx : η * δ x ≤ δ x / 8 := by nlinarith
      have hz0 : δ x * (7 / 8) < δ z := by linarith
      have hzle : δ z ≤ 2 * δ x := by linarith
      have hk1 : dist z x * (2 * κ) < η * δ x * (2 * κ) := mul_lt_mul_of_pos_right hz (by linarith)
      have hk2 : η * δ x * (2 * κ) = δ x / 4 := by linear_combination (2 * δ x) * hηκ
      have hyz : dist y z ≤ dist y x + dist z x := by
        have := dist_triangle y x z; rw [dist_comm x z] at this; exact this
      have hk3 : dist y z * (2 * κ) ≤ (dist y x + dist z x) * (2 * κ) :=
        mul_le_mul_of_nonneg_right hyz (by linarith)
      have hk4 : (dist y x + dist z x) * (2 * κ) < (η * δ x + η * δ x) * (2 * κ) :=
        mul_lt_mul_of_pos_right (by linarith) (by linarith)
      have hmem : (z, (x, y)) ∈ U₁ := by
        refine ⟨hzB, ?_, ?_⟩
        · show dist x z < δ z / (2 * κ)
          rw [lt_div_iff₀ (by linarith), hxz]; linarith
        · show dist y z < δ z / (2 * κ)
          rw [lt_div_iff₀ (by linarith)]; linarith
      rw [indicator_of_mem hmem]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
      exact inv_anti₀ (by linarith) hzle
    have hηx0 : 0 ≤ η * δ x := by positivity
    calc c = ENNReal.ofReal ((2 * δ x)⁻¹ ^ d) * volume (ball x (η * δ x)) := by
          rw [hcdef, hvol x _ hηx0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 3; field_simp
      _ = ∫⁻ z in ball x (η * δ x), ENNReal.ofReal ((2 * δ x)⁻¹ ^ d) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in ball x (η * δ x), U₁.indicator (fun q => w q.1) (z, (x, y)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ ≤ H₁ (x, y) := setLIntegral_le_lintegral _ _
  -- upper bound on the weighted count
  have hup : ∀ p ∈ B ×ˢ B, H₂ p ≤ c' := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    have hx0 := hδpos x hx
    have hpt : ∀ z, U₂.indicator (fun q => w q.1) (z, (x, y)) ≤
        (ball x (δ x)).indicator (fun _ => ENNReal.ofReal ((3 / (2 * δ x)) ^ d)) z := by
      intro z
      by_cases hmem : (z, (x, y)) ∈ U₂
      · obtain ⟨hzB, hxz, -⟩ := id hmem
        have hz0 := hδpos z hzB
        have hκρ : κ * ρ z = δ z / 2 := by
          show κ * (δ z / (2 * κ)) = δ z / 2; field_simp
        simp only at hxz
        rw [hκρ] at hxz
        have h1 := hδlip x z
        have h2 := hδlip z x
        have hxz' : dist z x = dist x z := dist_comm _ _
        have hzb : z ∈ ball x (δ x) := by rw [mem_ball]; linarith
        rw [indicator_of_mem hmem, indicator_of_mem hzb]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
        rw [inv_eq_one_div, div_le_div_iff₀ hz0 (by linarith)]; linarith
      · rw [indicator_of_notMem hmem]; positivity
    calc H₂ (x, y) ≤ ∫⁻ z, (ball x (δ x)).indicator
          (fun _ => ENNReal.ofReal ((3 / (2 * δ x)) ^ d)) z := lintegral_mono hpt
      _ = c' := by
          rw [lintegral_indicator_const measurableSet_ball, hvol x _ hx0.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 3; field_simp
  have hzero : ∀ p ∉ B ×ˢ B, H₂ p = 0 := by
    intro p hp
    have h0 : ∀ z, U₂.indicator (fun q => w q.1) (z, p) = 0 := by
      intro z
      refine indicator_of_notMem ?_ _
      rintro ⟨hzB, h1, h2⟩
      have hz0 := hδpos z hzB
      have hκρ : κ * ρ z = δ z / 2 := by
        show κ * (δ z / (2 * κ)) = δ z / 2; field_simp
      simp only at h1 h2
      rw [hκρ] at h1 h2
      exact hp ⟨hsub z (δ z) le_rfl (mem_ball.2 (by linarith)),
        hsub z (δ z) le_rfl (mem_ball.2 (by linarith))⟩
    simp only [hH₂def, h0, lintegral_zero]
  -- step 1: lower bound
  have step1 : c * ∫⁻ x in B, ∫⁻ y in ball x ((8 * κ)⁻¹ * infDist x Bᶜ),
      ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y ≤ I₁ := by
    rw [hI₁eq, ← lintegral_const_mul' _ _ hct]
    calc ∫⁻ x in B, c * ∫⁻ y in ball x (η * δ x), F (x, y)
        = ∫⁻ x in B, ∫⁻ y in ball x (η * δ x), c * F (x, y) := by
          congr 1; funext x; rw [lintegral_const_mul' _ _ hct]
      _ ≤ ∫⁻ x in B, ∫⁻ y in ball x (η * δ x), F (x, y) * H₁ (x, y) := by
          refine setLIntegral_mono' hBo.measurableSet fun x hx => ?_
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          rw [mul_comm]; exact mul_le_mul_right (hlow x hx y hy) _
      _ ≤ ∫⁻ x, ∫⁻ y, F (x, y) * H₁ (x, y) :=
          (setLIntegral_le_lintegral _ _).trans
            (lintegral_mono fun x => setLIntegral_le_lintegral _ _)
      _ = ∫⁻ p, F p * H₁ p := by
          rw [Measure.volume_eq_prod]
          exact (lintegral_prod (fun p => F p * H₁ p) (hF.mul hH₁m).aemeasurable).symm
  -- step 2: the ball comparability
  have step2 : I₁ ≤ ENNReal.ofReal C * I₂ := by
    rw [hI₂, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [mul_left_comm]
    refine mul_le_mul_right ?_ _
    rcases (hδ0 z).eq_or_lt with h | h
    · have : ball z (ρ z) = ∅ := by
        apply ball_eq_empty.2; show δ z / (2 * κ) ≤ 0; rw [← h]; simp
      simp [this, formHs, form]
    · exact hball z (ρ z) (by positivity)
  -- step 3: upper bound
  have step3 : I₂ ≤ c' * form B k f := by
    rw [hI₂eq, form, ← lintegral_indicator (hBo.measurableSet.prod hBo.measurableSet),
      ← lintegral_const_mul' _ _ hc't]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ B ×ˢ B
    · rw [indicator_of_mem hp, mul_comm]; exact mul_le_mul_left (hup p hp) _
    · rw [hzero p hp, mul_zero]; positivity
  -- combine
  have hconst : c * (ENNReal.ofReal (C * (24 * κ) ^ d) * form B k f)
      = ENNReal.ofReal C * (c' * form B k f) := by
    have h24 : η / 2 * (24 * κ) = 3 / 2 := by rw [hηdef]; field_simp; norm_num
    have : ENNReal.ofReal ((η / 2) ^ d) * ENNReal.ofReal (C * (24 * κ) ^ d)
        = ENNReal.ofReal C * ENNReal.ofReal ((3 / 2) ^ d) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC]
      congr 1
      rw [← h24, mul_pow (η / 2) (24 * κ)]; ring
    rw [hcdef, hc'def]
    calc ENNReal.ofReal ((η / 2) ^ d) * V * (ENNReal.ofReal (C * (24 * κ) ^ d) * form B k f)
        = (ENNReal.ofReal ((η / 2) ^ d) * ENNReal.ofReal (C * (24 * κ) ^ d)) * V
            * form B k f := by ring
      _ = _ := by rw [this]; ring
  rw [← ENNReal.mul_le_mul_iff_right hc0 hct, hconst]
  exact step1.trans (step2.trans (mul_le_mul_right step3 _))


/-- **The regional form is controlled by the `H_k` form of the ball**, given an enlarged-ball
comparability for `f` on all balls. The case `Ω = B_R(x₀)` of
`regional_le_form_of_ballComparability_open`. -/
theorem regional_le_form_of_ballComparability {α κ C : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ C)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (hball : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      formHs (ball z r) α f ≤ ENNReal.ofReal C * form (ball z (κ * r)) k f)
    (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (_hR : 0 < R) :
    ∫⁻ x in ball x₀ R, ∫⁻ y in ball x ((8 * κ)⁻¹ * infDist x (ball x₀ R)ᶜ),
        ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y
      ≤ ENNReal.ofReal (C * (24 * κ) ^ d) * form (ball x₀ R) k f :=
  regional_le_form_of_ballComparability_open hκ hC hf hG hball (ball x₀ R) isOpen_ball

end QFS
