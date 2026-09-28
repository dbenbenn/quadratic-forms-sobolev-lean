import QuadraticFormsSobolev.RandomLattice.Basic
import QuadraticFormsSobolev.RandomLattice.Tiling
import QuadraticFormsSobolev.RandomLattice.TheoremOneThreeNonneg
import QuadraticFormsSobolev.ConeGap
import QuadraticFormsSobolev.ThinCones

/-!
# Random lattice sampling: the inequality for one lattice

For a fixed lattice `x ↦ T x = h · A_Q (x + η)`, Theorem 1.3 (in the form
`theoremOneThree_of_nonneg`) applies to `f ∘ T`, to the configuration `Γ'(x)` that halves the
aperture of `Γ(T x)`, and to the kernel `ω(x, y) = h^{d+α} k(T x, T y)`. Because
`KernelBounds` holds at every pair of points, this needs no measurability of `Γ`. The result
is an inequality between sums over the sample points:

  `∑_{n,m} (f(T m) − f(T n))² |T n − T m|^{-d-α} ≤ c ∑_{n,m} (f(T m) − f(T n))² k(T n, T m)`.
-/

open MeasureTheory Set Metric Real
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

/-- A linear map within `ε < sin(ϑ/2)` of the identity maps the half-aperture double cone
into the full one. -/
lemma mem_doubleCone_of_near {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {ϑ θ ε : ℝ}
    (hϑ : 0 < ϑ) (hϑθ : ϑ ≤ θ) (hθ : θ ≤ π / 2) (hε : ε < Real.sin (ϑ / 2))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : ∀ u, ‖A u - u‖ ≤ ε * ‖u‖) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ doubleCone v (θ / 2)) : A w ∈ doubleCone v θ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hϑ hϑθ
  have hsin : Real.sin (ϑ / 2) ≤ Real.sin (θ / 2) :=
    Real.strictMonoOn_sin.monotoneOn ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (by linarith)
  -- the one-sided statement
  have key : ∀ u ∈ cone v (θ / 2), A u ∈ cone v θ := by
    intro u hu
    have hu0 : u ≠ 0 := hu.1
    have hgap := coneGap_ge_of_mem_half hv hθ0 hθ hu
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hlt : ε * ‖u‖ < coneGap v θ u := by nlinarith
    refine closedBall_subset_cone hv hθ0 hθ hlt ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hA u
  rcases hw with hw | hw
  · exact Or.inl (key w hw)
  · right
    rw [Set.mem_neg] at hw ⊢
    have := key (-w) hw
    rwa [map_neg] at this

/-- Kernel comparison: if `a ≤ c b` then `b^{-s} ≤ c^s a^{-s}` for `s ≥ 0`. -/
lemma rpow_neg_le_of_le {a b c s : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 ≤ s)
    (hab : a ≤ c * b) : b ^ (-s) ≤ c ^ s * a ^ (-s) := by
  have h1 : (c * b) ^ (-s) ≤ a ^ (-s) := Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  rw [Real.mul_rpow hc.le hb.le] at h1
  have hcs : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  have : c ^ (-s) = (c ^ s)⁻¹ := Real.rpow_neg hc.le s
  rw [this] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hcs.le
  rwa [← mul_assoc, mul_inv_cancel₀ hcs.ne', one_mul] at h2

/-- Two-sided norm bounds for a near-identity map. -/
lemma norm_near_bounds {ε : ℝ} (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : ∀ u, ‖A u - u‖ ≤ ε * ‖u‖) (u : EuclideanSpace ℝ (Fin d)) :
    (1 - ε) * ‖u‖ ≤ ‖A u‖ ∧ ‖A u‖ ≤ (1 + ε) * ‖u‖ := by
  have h := hA u
  have h1 : ‖u‖ - ‖A u‖ ≤ ‖A u - u‖ := by
    have := norm_sub_norm_le u (A u); rw [norm_sub_rev] at this; linarith
  have h2 : ‖A u‖ - ‖u‖ ≤ ‖A u - u‖ := norm_sub_norm_le (A u) u
  constructor <;> nlinarith

/-- The pulled-back configuration: at `x`, the axis of `Γ(T x)` with half its aperture. -/
noncomputable def halfConfig (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Configuration (EuclideanSpace ℝ (Fin d)) := fun x =>
  { axis := (Γ (T x)).axis
    norm_axis := (Γ (T x)).norm_axis
    apex := (Γ (T x)).apex / 2
    apex_pos := half_pos (Γ (T x)).apex_pos
    apex_le := by linarith [(Γ (T x)).apex_le, (Γ (T x)).apex_pos] }

lemma apexLowerBound_halfConfig {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {ϑ : ℝ}
    (hΓ : ApexLowerBound Γ ϑ) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    ApexLowerBound (halfConfig Γ T) (ϑ / 2) :=
  ⟨half_pos hΓ.1, fun x => by
    show ϑ / 2 ≤ (Γ (T x)).apex / 2
    linarith [hΓ.2 (T x)]⟩

/-- The lattice map `x ↦ h · A (x + η)`. -/
noncomputable def latMap (h : ℝ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := h • A (x + η)

lemma latMap_sub (h : ℝ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η x y : EuclideanSpace ℝ (Fin d)) :
    latMap h A η y - latMap h A η x = h • A (y - x) := by
  simp only [latMap, ← smul_sub, ← map_sub]
  congr 2; abel

/-- The pulled-back kernel satisfies the hypotheses of Theorem 1.3 with `Λ' = Λ 2^{d+α}`. -/
lemma discreteKernelBounds_pullback {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {ϑ α Λ ε h : ℝ} (hΓ : ApexLowerBound Γ ϑ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hεs : ε < Real.sin (ϑ / 2))
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hh : 0 < h)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : ∀ u, ‖A u - u‖ ≤ ε * ‖u‖) (η : EuclideanSpace ℝ (Fin d)) :
    DiscreteKernelBounds (halfConfig Γ (latMap h A η)) α (Λ * 2 ^ ((d : ℝ) + α)) (1 / 2)
      (lattice d) (fun x y => ENNReal.ofReal (h ^ ((d : ℝ) + α)) *
        k (latMap h A η x) (latMap h A η y)) := by
  set T := latMap h A η with hT
  set s : ℝ := (d : ℝ) + α with hs
  have hs0 : 0 ≤ s := by positivity
  have hΛ : 1 ≤ Λ := hk.one_le
  have hΛ0 : 0 < Λ := by linarith
  have h2s : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos two_pos s
  have hexp : -(d : ℝ) - α = -s := by rw [hs]; ring
  -- distances
  have hdist : ∀ x y : EuclideanSpace ℝ (Fin d), x ≠ y →
      0 < ‖T x - T y‖ ∧ ‖T x - T y‖ ≤ (2 * h) * ‖x - y‖ ∧ ‖x - y‖ ≤ (2 / h) * ‖T x - T y‖ := by
    intro x y hxy
    have hr : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hxy
    have heq : ‖T x - T y‖ = h * ‖A (x - y)‖ := by
      rw [hT, latMap_sub, norm_smul, Real.norm_of_nonneg hh.le]
    obtain ⟨hlo, hhi⟩ := norm_near_bounds A hA (x - y)
    refine ⟨?_, ?_, ?_⟩
    · rw [heq]; have : 0 < (1 - ε) * ‖x - y‖ := by nlinarith
      exact mul_pos hh (lt_of_lt_of_le this hlo)
    · have h2 : ‖A (x - y)‖ ≤ 2 * ‖x - y‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hε2 hr.le]
      rw [heq]
      calc h * ‖A (x - y)‖ ≤ h * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 hh.le
        _ = 2 * h * ‖x - y‖ := by ring
    · have h2 : ‖x - y‖ ≤ 2 * ‖A (x - y)‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hε2 hr.le]
      rw [heq, div_mul_eq_mul_div, le_div_iff₀ hh]
      calc ‖x - y‖ * h ≤ (2 * ‖A (x - y)‖) * h := mul_le_mul_of_nonneg_right h2 hh.le
        _ = 2 * (h * ‖A (x - y)‖) := by ring
  -- indicators
  have hind : ∀ x y : EuclideanSpace ℝ (Fin d),
      indE (coneAt (halfConfig Γ T) x) y ≤ indE (coneAt Γ (T x)) (T y) := by
    intro x y
    by_cases hy : y ∈ coneAt (halfConfig Γ T) x
    · have hmem : T y ∈ coneAt Γ (T x) := by
        rw [mem_coneAt] at hy ⊢
        have hy' : y - x ∈ doubleCone (Γ (T x)).axis ((Γ (T x)).apex / 2) := hy
        have hAm := mem_doubleCone_of_near (Γ (T x)).norm_axis hΓ.1 (hΓ.2 (T x))
          (Γ (T x)).apex_le hεs A hA hy'
        have hsm := smul_mem_doubleCone (Γ (T x)).norm_axis (Γ (T x)).apex_pos
          (Γ (T x)).apex_le hh hAm
        show T y - T x ∈ doubleCone (Γ (T x)).axis (Γ (T x)).apex
        rw [hT, latMap_sub]; exact hsm
      simp [indE, Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
    · simp [indE, Set.indicator_of_notMem hy]
  refine ⟨by nlinarith [Real.one_le_rpow (one_le_two : (1:ℝ) ≤ 2) hs0], ?_, ?_, ?_⟩
  · intro x _ y _
    simp only [hk.symm (T x) (T y)]
  · intro x _ y _ hxy
    have hne : x ≠ y := by
      intro he; rw [he, sub_self, norm_zero] at hxy; norm_num at hxy
    obtain ⟨hR, hup, _⟩ := hdist x y hne
    have hr : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hne
    have hJ : ‖x - y‖ ^ (-s) ≤ (2 * h) ^ s * ‖T x - T y‖ ^ (-s) :=
      rpow_neg_le_of_le hR hr (by positivity) hs0 hup
    have hJe : jumpKernel d α x y ≤ ENNReal.ofReal ((2 * h) ^ s) * jumpKernel d α (T x) (T y) := by
      simp only [jumpKernel, hexp]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hJ
    have hsum : indE (coneAt (halfConfig Γ T) x) y + indE (coneAt (halfConfig Γ T) y) x
        ≤ indE (coneAt Γ (T x)) (T y) + indE (coneAt Γ (T y)) (T x) :=
      add_le_add (hind x y) (hind y x)
    have hconst : ENNReal.ofReal (Λ * 2 ^ s)⁻¹ * ENNReal.ofReal ((2 * h) ^ s)
        = ENNReal.ofReal (h ^ s) * ENNReal.ofReal Λ⁻¹ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow two_pos.le hh.le]
      field_simp
    calc ENNReal.ofReal (Λ * 2 ^ s)⁻¹ * ((indE (coneAt (halfConfig Γ T) x) y
            + indE (coneAt (halfConfig Γ T) y) x) * jumpKernel d α x y)
        ≤ ENNReal.ofReal (Λ * 2 ^ s)⁻¹ * ((indE (coneAt Γ (T x)) (T y)
            + indE (coneAt Γ (T y)) (T x)) *
            (ENNReal.ofReal ((2 * h) ^ s) * jumpKernel d α (T x) (T y))) := by
          gcongr
      _ = ENNReal.ofReal (h ^ s) * (ENNReal.ofReal Λ⁻¹ * ((indE (coneAt Γ (T x)) (T y)
            + indE (coneAt Γ (T y)) (T x)) * jumpKernel d α (T x) (T y))) := by
          rw [show ∀ X J : ℝ≥0∞, ENNReal.ofReal (Λ * 2 ^ s)⁻¹ *
                (X * (ENNReal.ofReal ((2 * h) ^ s) * J))
              = (ENNReal.ofReal (Λ * 2 ^ s)⁻¹ * ENNReal.ofReal ((2 * h) ^ s)) * (X * J)
              from fun X J => by ring, hconst]; ring
      _ ≤ ENNReal.ofReal (h ^ s) * k (T x) (T y) := by
          gcongr; exact hk.lower (T x) (T y)
  · intro x _ y _ hxy
    have hne : x ≠ y := by
      intro he; rw [he, sub_self, norm_zero] at hxy; norm_num at hxy
    obtain ⟨hR, _, hlo⟩ := hdist x y hne
    have hr : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hne
    have hJ : ‖T x - T y‖ ^ (-s) ≤ (2 / h) ^ s * ‖x - y‖ ^ (-s) :=
      rpow_neg_le_of_le hr hR (by positivity) hs0 hlo
    have hreal : h ^ s * ‖T x - T y‖ ^ (-s) ≤ 2 ^ s * ‖x - y‖ ^ (-s) := by
      have := mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hh.le s)
      rw [← mul_assoc, ← Real.mul_rpow hh.le (by positivity), mul_div_cancel₀ _ hh.ne'] at this
      exact this
    calc ENNReal.ofReal (h ^ s) * k (T x) (T y)
        ≤ ENNReal.ofReal (h ^ s) * (ENNReal.ofReal Λ * jumpKernel d α (T x) (T y)) := by
          gcongr; exact hk.upper _ _ (norm_sub_pos_iff.mp hR)
      _ = ENNReal.ofReal Λ * ENNReal.ofReal (h ^ s * ‖T x - T y‖ ^ (-s)) := by
          simp only [jumpKernel, hexp]
          rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (2 ^ s * ‖x - y‖ ^ (-s)) := by
          gcongr
      _ = ENNReal.ofReal (Λ * 2 ^ s) * jumpKernel d α x y := by
          simp only [jumpKernel, hexp]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hΛ0.le]; ring

/-- A point of `ℤ^d` is the lattice point of its rounded coordinates. -/
lemma latticePt_round {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ lattice d) :
    latticePt d 1 (fun j => round (v j)) = v := by
  ext j
  obtain ⟨n, hn⟩ := hv j
  simp [latticePt, hn, round_intCast]

/-- Distinct points of `ℤ^d` are at distance at least one. -/
lemma one_le_norm_latticePt_sub {n m : Fin d → ℤ} (hnm : n ≠ m) :
    1 ≤ ‖latticePt d 1 n - latticePt d 1 m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
    by_contra hcon; push_neg at hcon; exact hnm (funext hcon)
  have h1 : (1 : ℝ) ≤ |((n i - m i : ℤ) : ℝ)| := by
    have : (n i - m i) ≠ 0 := sub_ne_zero.mpr hi
    exact_mod_cast Int.one_le_abs this
  calc (1 : ℝ) ≤ |((n i - m i : ℤ) : ℝ)| := h1
    _ = ‖(latticePt d 1 n - latticePt d 1 m) i‖ := by
        simp [latticePt, Real.norm_eq_abs]
    _ ≤ ‖latticePt d 1 n - latticePt d 1 m‖ := PiLp.norm_apply_le _ i

/-- A discrete form is bounded by the sum over all pairs of integer vectors. -/
lemma discreteForm_le_tsum (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteForm S R₀ ω f ≤ ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
      ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
        ω (latticePt d 1 p.1) (latticePt d 1 p.2) := by
  classical
  set X := {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ S ∩ lattice d ∧ p.2 ∈ S ∩ lattice d ∧ R₀ < ‖p.1 - p.2‖}
  let i : X → (Fin d → ℤ) × (Fin d → ℤ) :=
    fun x => (fun j => round (x.1.1 j), fun j => round (x.1.2 j))
  have hi1 : ∀ x : X, latticePt d 1 (i x).1 = x.1.1 := fun x => latticePt_round x.2.1.2
  have hi2 : ∀ x : X, latticePt d 1 (i x).2 = x.1.2 := fun x => latticePt_round x.2.2.1.2
  have hinj : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    have h1 := hi1 x; have h2 := hi2 x
    rw [hxy] at h1 h2
    exact Prod.ext (h1.symm.trans (hi1 y)) (h2.symm.trans (hi2 y))
  set g : (Fin d → ℤ) × (Fin d → ℤ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
      ω (latticePt d 1 p.1) (latticePt d 1 p.2)
  calc discreteForm S R₀ ω f = ∑' x : X, g (i x) := by
        unfold discreteForm
        refine tsum_congr (fun x => ?_)
        simp only [g, hi1, hi2]
    _ ≤ ∑' p, g p := ENNReal.tsum_comp_le_tsum_of_injective hinj g

/-- A finite sum over pairs of distinct integer vectors in a ball is bounded by the discrete
form of that ball. -/
lemma sum_le_discreteForm (s : Finset ((Fin d → ℤ) × (Fin d → ℤ))) {R : ℝ}
    (hR : ∀ p ∈ s, latticePt d 1 p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
      latticePt d 1 p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∑ p ∈ s.filter (fun p => p.1 ≠ p.2),
        ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
          ω (latticePt d 1 p.1) (latticePt d 1 p.2)
      ≤ discreteForm (ball 0 R) (1 / 2) ω f := by
  classical
  set X := {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∩ lattice d ∧
      p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∩ lattice d ∧ 1 / 2 < ‖p.1 - p.2‖}
  set t := s.filter (fun p => p.1 ≠ p.2)
  have hmem : ∀ p ∈ t, (latticePt d 1 p.1, latticePt d 1 p.2) ∈ {q :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      q.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∩ lattice d ∧
      q.2 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∩ lattice d ∧ 1 / 2 < ‖q.1 - q.2‖} := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨h1, h2⟩ := hR p hp.1
    refine ⟨⟨h1, latticePt_mem_scaledLattice 1 p.1⟩, ⟨h2, latticePt_mem_scaledLattice 1 p.2⟩, ?_⟩
    have := one_le_norm_latticePt_sub hp.2
    show (1 : ℝ) / 2 < ‖latticePt d 1 p.1 - latticePt d 1 p.2‖
    linarith
  let ι : t → X := fun p => ⟨(latticePt d 1 p.1.1, latticePt d 1 p.1.2), hmem p.1 p.2⟩
  have hinj : Function.Injective ι := by
    intro p q hpq
    have := congrArg Subtype.val hpq
    simp only [ι, Prod.mk.injEq] at this
    apply Subtype.ext
    exact Prod.ext (latticePt_injective one_ne_zero this.1)
      (latticePt_injective one_ne_zero this.2)
  set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal ((f x.1.1 - f x.1.2) ^ 2) * ω x.1.1 x.1.2
  calc ∑ p ∈ t, ENNReal.ofReal ((f (latticePt d 1 p.1) - f (latticePt d 1 p.2)) ^ 2) *
          ω (latticePt d 1 p.1) (latticePt d 1 p.2)
      = ∑' p : t, g (ι p) := by
        rw [Finset.tsum_subtype t (fun p => ENNReal.ofReal ((f (latticePt d 1 p.1) -
          f (latticePt d 1 p.2)) ^ 2) * ω (latticePt d 1 p.1) (latticePt d 1 p.2))]
    _ ≤ ∑' x : X, g x := ENNReal.tsum_comp_le_tsum_of_injective hinj g
    _ = discreteForm (ball 0 R) (1 / 2) ω f := rfl

/-- The jump kernel at the images of two points under the lattice map. -/
lemma jumpKernel_latMap_le {α ε h : ℝ} (hα : 0 ≤ α) (hε2 : ε ≤ 1 / 2) (hh : 0 < h)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : ∀ u, ‖A u - u‖ ≤ ε * ‖u‖) (η : EuclideanSpace ℝ (Fin d))
    {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
    jumpKernel d α (latMap h A η x) (latMap h A η y)
      ≤ ENNReal.ofReal ((2 / h) ^ ((d : ℝ) + α)) * jumpKernel d α x y := by
  set s : ℝ := (d : ℝ) + α
  have hs0 : 0 ≤ s := by positivity
  have hexp : -(d : ℝ) - α = -s := by ring
  have hr : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hxy
  have heq : ‖latMap h A η x - latMap h A η y‖ = h * ‖A (x - y)‖ := by
    rw [latMap_sub, norm_smul, Real.norm_of_nonneg hh.le]
  obtain ⟨hlo, -⟩ := norm_near_bounds A hA (x - y)
  have h2 : ‖x - y‖ ≤ 2 * ‖A (x - y)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hε2 hr.le]
  have hR : 0 < ‖latMap h A η x - latMap h A η y‖ := by
    rw [heq]; exact mul_pos hh (by linarith)
  have hle : ‖x - y‖ ≤ (2 / h) * ‖latMap h A η x - latMap h A η y‖ := by
    rw [heq, div_mul_eq_mul_div, le_div_iff₀ hh]; nlinarith
  have hJ := rpow_neg_le_of_le hr hR (by positivity) hs0 hle
  simp only [jumpKernel, hexp]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hJ

/-- **The inequality for one lattice.** For every `ε`-distortion `A`, scale `h` and shift `η`,
the sum over the sample points `T n = h A (n + η)` of the `H^{α/2}` integrand is at most a
constant multiple of the sum of the `H_k` integrand, the constant depending only on
`d, ϑ, Λ, α`. -/
theorem latticeSum_le {ϑ Λ α : ℝ} (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 → ε < Real.sin (ϑ / 2) →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexLowerBound Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (h : ℝ), 0 < h →
      ∀ A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ u, ‖A u - u‖ ≤ ε * ‖u‖) → ∀ η : EuclideanSpace ℝ (Fin d),
      ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
          ENNReal.ofReal ((f (latMap h A η (latticePt d 1 p.2)) -
            f (latMap h A η (latticePt d 1 p.1))) ^ 2) *
          jumpKernel d α (latMap h A η (latticePt d 1 p.1)) (latMap h A η (latticePt d 1 p.2))
        ≤ ENNReal.ofReal c * ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
          ENNReal.ofReal ((f (latMap h A η (latticePt d 1 p.2)) -
            f (latMap h A η (latticePt d 1 p.1))) ^ 2) *
          k (latMap h A η (latticePt d 1 p.1)) (latMap h A η (latticePt d 1 p.2)) := by
  classical
  set s : ℝ := (d : ℝ) + α with hs
  have hs0 : 0 ≤ s := by positivity
  have hΛ' : 1 ≤ Λ * 2 ^ s := by nlinarith [Real.one_le_rpow (one_le_two : (1:ℝ) ≤ 2) hs0]
  obtain ⟨κ, c, hκ, hc, H13⟩ := theoremOneThree_of_nonneg (d := d) (ϑ / 2) (Λ * 2 ^ s) α (1 / 2)
    (half_pos hϑ) hΛ' hα (by norm_num)
  refine ⟨c * 2 ^ s, by positivity, ?_⟩
  intro ε hε hε2 hεs Γ hΓ k hk f h hh A hA η
  set T := latMap h A η with hT
  set L : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) := latticePt d 1 with hL
  set f' : EuclideanSpace ℝ (Fin d) → ℝ := fun x => f (T x) with hf'
  set ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal (h ^ s) * k (T x) (T y) with hω
  have hωb : DiscreteKernelBounds (halfConfig Γ T) α (Λ * 2 ^ s) (1 / 2) (lattice d) ω :=
    discreteKernelBounds_pullback hΓ hα hε hε2 hεs hk hh A hA η
  set Gs := ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
    ENNReal.ofReal ((f (T (L p.2)) - f (T (L p.1))) ^ 2) * k (T (L p.1)) (T (L p.2)) with hGs
  -- Theorem 1.3 on every ball about the origin
  have hball : ∀ R : ℝ, 0 < R → discreteForm (ball 0 R) (1 / 2) (jumpKernel d α) f'
      ≤ ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs) := by
    intro R hR
    calc discreteForm (ball 0 R) (1 / 2) (jumpKernel d α) f'
        ≤ ENNReal.ofReal c * discreteForm (ball 0 (κ * R)) (1 / 2) ω f' :=
          H13 (halfConfig Γ T) (apexLowerBound_halfConfig hΓ T) ω hωb 0 R f' hR
      _ ≤ ENNReal.ofReal c * ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
            ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * ω (L p.1) (L p.2) := by
          gcongr; exact discreteForm_le_tsum _ _ _ _
      _ = ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs) := by
          congr 1
          rw [hGs, ← ENNReal.tsum_mul_left]
          refine tsum_congr (fun p => ?_)
          simp only [hf', hω]
          rw [show (f (T (L p.1)) - f (T (L p.2))) ^ 2 = (f (T (L p.2)) - f (T (L p.1))) ^ 2
            by ring]
          ring
  refine tsum_le_of_sum_le' (by positivity) (fun t => ?_)
  -- the diagonal terms vanish
  have hdiag : ∀ p ∈ t, p ∉ t.filter (fun p => p.1 ≠ p.2) →
      ENNReal.ofReal ((f (T (L p.2)) - f (T (L p.1))) ^ 2) * jumpKernel d α (T (L p.1)) (T (L p.2))
        = 0 := by
    intro p hp hnot
    have : p.1 = p.2 := by
      by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨hp, hne⟩)
    rw [this, sub_self]; simp
  rw [← Finset.sum_subset (Finset.filter_subset _ t) hdiag]
  -- a ball containing every point of `t`
  set R : ℝ := 1 + ∑ p ∈ t, (‖L p.1‖ + ‖L p.2‖) with hRdef
  have hRpos : 0 < R := by
    have : 0 ≤ ∑ p ∈ t, (‖L p.1‖ + ‖L p.2‖) := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hRmem : ∀ p ∈ t, L p.1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R ∧
      L p.2 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) R := by
    intro p hp
    have hle := Finset.single_le_sum (f := fun p => ‖L p.1‖ + ‖L p.2‖)
      (fun _ _ => by positivity) hp
    simp only [mem_ball, dist_zero_right]
    constructor <;> linarith [norm_nonneg (L p.1), norm_nonneg (L p.2)]
  have hpow : ENNReal.ofReal ((2 / h) ^ s) * (ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs))
      = ENNReal.ofReal (c * 2 ^ s) * Gs := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow two_pos.le hh.le]
    field_simp
  calc ∑ p ∈ t.filter (fun p => p.1 ≠ p.2),
        ENNReal.ofReal ((f (T (L p.2)) - f (T (L p.1))) ^ 2) * jumpKernel d α (T (L p.1)) (T (L p.2))
      ≤ ∑ p ∈ t.filter (fun p => p.1 ≠ p.2), ENNReal.ofReal ((2 / h) ^ s) *
          (ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (L p.1) (L p.2)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hne : L p.1 ≠ L p.2 := fun he =>
          (Finset.mem_filter.mp hp).2 (latticePt_injective one_ne_zero he)
        rw [show (f (T (L p.2)) - f (T (L p.1))) ^ 2 = (f' (L p.1) - f' (L p.2)) ^ 2 by
          simp only [hf']; ring]
        calc ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (T (L p.1)) (T (L p.2))
            ≤ ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) *
                (ENNReal.ofReal ((2 / h) ^ s) * jumpKernel d α (L p.1) (L p.2)) := by
              gcongr; exact jumpKernel_latMap_le hα hε2 hh A hA η hne
          _ = _ := by ring
    _ = ENNReal.ofReal ((2 / h) ^ s) * ∑ p ∈ t.filter (fun p => p.1 ≠ p.2),
          ENNReal.ofReal ((f' (L p.1) - f' (L p.2)) ^ 2) * jumpKernel d α (L p.1) (L p.2) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((2 / h) ^ s) * discreteForm (ball 0 R) (1 / 2) (jumpKernel d α) f' := by
        gcongr; exact sum_le_discreteForm t hRmem _ f'
    _ ≤ ENNReal.ofReal ((2 / h) ^ s) * (ENNReal.ofReal c * (ENNReal.ofReal (h ^ s) * Gs)) := by
        gcongr; exact hball R hRpos
    _ = ENNReal.ofReal (c * 2 ^ s) * Gs := hpow

end QFS
