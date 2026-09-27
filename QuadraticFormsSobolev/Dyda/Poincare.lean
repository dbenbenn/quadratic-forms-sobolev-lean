import Mathlib

/-! # A Poincaré inequality by chaining

On a bounded connected open set `Ω`, the double integral of `(u(x) − u(y))²` over `Ω × Ω` is
controlled by its part over the pairs at distance less than `ρ`, for any `ρ > 0`. The proof
covers `Ω` by finitely many pieces `Ω ∩ B(c, ρ/4)` and averages across overlapping pieces;
connectedness makes every pair of pieces reachable. No exponent enters, so the constant serves
every `α` at once. -/

open MeasureTheory Metric
open scoped ENNReal

namespace Dyda

variable {d : ℕ}

/-- `D(S, T) = ∫_S ∫_T (u(x) − u(y))²`. -/
noncomputable def pairInt (u : EuclideanSpace ℝ (Fin d) → ℝ) (S T : Set (EuclideanSpace ℝ (Fin d))) :
    ℝ≥0∞ :=
  ∫⁻ x in S, ∫⁻ y in T, ENNReal.ofReal ((u x - u y) ^ 2)

lemma measurable_sqDiff {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u) :
    Measurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((u x - u y) ^ 2)) := by
  unfold Function.uncurry; fun_prop

lemma pairInt_comm {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u)
    (S T : Set (EuclideanSpace ℝ (Fin d))) : pairInt u S T = pairInt u T S := by
  unfold pairInt
  rw [lintegral_lintegral_swap ((measurable_sqDiff hu).aemeasurable)]
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  rw [show (u x - u y) ^ 2 = (u y - u x) ^ 2 by ring]

lemma sqDiff_le (a b c : ℝ) :
    ENNReal.ofReal ((a - c) ^ 2) ≤ 2 * ENNReal.ofReal ((a - b) ^ 2) + 2 * ENNReal.ofReal ((b - c) ^ 2) := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - 2 * b + c)])

/-- **Averaging over a third set.** -/
lemma pairInt_triangle {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : Measurable u)
    (S T W : Set (EuclideanSpace ℝ (Fin d))) :
    volume W * pairInt u S T ≤ 2 * volume T * pairInt u S W + 2 * volume S * pairInt u W T := by
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun x y => ENNReal.ofReal ((u x - u y) ^ 2) with hg
  have hgm : Measurable (Function.uncurry g) := measurable_sqDiff hu
  have hgx : ∀ x, Measurable (g x) := fun x => hgm.of_uncurry_left
  have hgy : ∀ y, Measurable fun x => g x y := fun y => hgm.of_uncurry_right
  -- pointwise in `(x, y)`
  have hpt : ∀ x y, volume W * g x y ≤ 2 * (∫⁻ w in W, g x w) + 2 * ∫⁻ w in W, g w y := by
    intro x y
    calc volume W * g x y = ∫⁻ _ in W, g x y := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ w in W, (2 * g x w + 2 * g w y) := lintegral_mono fun w => sqDiff_le _ _ _
      _ = 2 * (∫⁻ w in W, g x w) + 2 * ∫⁻ w in W, g w y := by
          rw [lintegral_add_left ((hgx x).const_mul _), lintegral_const_mul _ (hgx x),
            lintegral_const_mul _ (hgy y)]
  have hA : Measurable fun x => ∫⁻ w in W, g x w := hgm.lintegral_prod_right'
  have hB : Measurable fun y => ∫⁻ w in W, g w y :=
    (hgm.comp measurable_swap).lintegral_prod_right'
  calc volume W * pairInt u S T
      ≤ ∫⁻ x in S, volume W * ∫⁻ y in T, g x y := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x in S, ∫⁻ y in T, volume W * g x y :=
        lintegral_mono fun x => lintegral_const_mul_le _ _
    _ ≤ ∫⁻ x in S, ∫⁻ y in T, (2 * (∫⁻ w in W, g x w) + 2 * ∫⁻ w in W, g w y) :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = ∫⁻ x in S, (2 * volume T * (∫⁻ w in W, g x w) +
          2 * ∫⁻ y in T, ∫⁻ w in W, g w y) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_add_left measurable_const, setLIntegral_const,
          lintegral_const_mul _ hB]
        ring
    _ = 2 * volume T * pairInt u S W + 2 * volume S * pairInt u W T := by
        rw [lintegral_add_left (hA.const_mul _), lintegral_const_mul _ hA,
          setLIntegral_const, pairInt, pairInt,
          lintegral_lintegral_swap (f := fun y w => g w y)
            ((hgm.comp measurable_swap).aemeasurable)]
        ring

/-- The property "bounded by a finite multiple of `N`, uniformly in `u`" is closed under finite
sums. -/
lemma exists_sum_le {ι U : Type*} (s : Finset ι) (X : ι → U → ℝ≥0∞) (N : U → ℝ≥0∞)
    (h : ∀ i ∈ s, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u, X i u ≤ K * N u) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u, ∑ i ∈ s, X i u ≤ K * N u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, ENNReal.zero_ne_top, fun u => by simp⟩
  | insert a s ha ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨K₂, hK₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨K₁ + K₂, ENNReal.add_ne_top.mpr ⟨hK₁, hK₂⟩, fun u => ?_⟩
    rw [Finset.sum_insert ha, add_mul]
    exact add_le_add (h₁ u) (h₂ u)

/-- **Poincaré by chaining.** -/
theorem pairInt_le_near {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      pairInt u Ω Ω ≤ K * ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x ρ, ENNReal.ofReal ((u x - u y) ^ 2) := by
  classical
  set Nf : (EuclideanSpace ℝ (Fin d) → ℝ) → ℝ≥0∞ := fun u =>
    ∫⁻ x in Ω, ∫⁻ y in Ω ∩ ball x ρ, ENNReal.ofReal ((u x - u y) ^ 2) with hNf
  have htb : TotallyBounded Ω := hΩb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨t, htΩ, htf, hcov⟩ := finite_approx_of_totallyBounded htb (ρ / 4) (by positivity)
  set T := htf.toFinset
  set E : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)) := fun c => Ω ∩ ball c (ρ / 4)
  have hEo : ∀ c, IsOpen (E c) := fun c => hΩo.inter isOpen_ball
  have hEm : ∀ c, MeasurableSet (E c) := fun c => (hEo c).measurableSet
  have hEpos : ∀ c ∈ t, volume (E c) ≠ 0 := fun c hc =>
    ((hEo c).measure_pos volume ⟨c, htΩ hc, mem_ball_self (by positivity)⟩).ne'
  have hEfin : ∀ c, volume (E c) ≠ ⊤ := fun c =>
    (measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top |>.ne
  -- overlapping pieces: all their pairs are near
  have hnear : ∀ b c, (E b ∩ E c).Nonempty → ∀ u, Measurable u → pairInt u (E b) (E c) ≤ Nf u := by
    rintro b c ⟨w, ⟨-, hwb⟩, ⟨-, hwc⟩⟩ u hu
    unfold pairInt
    refine (setLIntegral_mono' (hEm b) fun x hx => lintegral_mono_set ?_).trans
      (lintegral_mono_set Set.inter_subset_left)
    rintro y ⟨hyΩ, hyc⟩
    refine ⟨hyΩ, ?_⟩
    have hxb : dist x b < ρ / 4 := hx.2
    rw [mem_ball] at hwb hwc hyc ⊢
    have h1 := dist_triangle y c w
    have h2 := dist_triangle y w x
    have h3 := dist_triangle w b x
    rw [dist_comm c w] at h1
    rw [dist_comm b x] at h3
    linarith
  -- reachability from a fixed piece
  set Reach : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Prop := fun b c =>
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u, Measurable u → pairInt u (E b) (E c) ≤ K * Nf u
  have hstep : ∀ b c c', c ∈ t → Reach b c → (E c ∩ E c').Nonempty → Reach b c' := by
    rintro b c c' hct ⟨K, hK, hbc⟩ hcc'
    refine ⟨(volume (E c))⁻¹ * (2 * volume (E c') * K + 2 * volume (E b)),
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (hEpos c hct))
        (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (hEfin _)) hK,
          ENNReal.mul_ne_top (by norm_num) (hEfin _)⟩), fun u hu => ?_⟩
    have h := pairInt_triangle hu (E b) (E c') (E c)
    calc pairInt u (E b) (E c')
        = (volume (E c))⁻¹ * (volume (E c) * pairInt u (E b) (E c')) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (hEpos c hct) (hEfin c), one_mul]
      _ ≤ (volume (E c))⁻¹ * (2 * volume (E c') * (K * Nf u) + 2 * volume (E b) * Nf u) := by
          gcongr
          exact h.trans (add_le_add (by gcongr; exact hbc u hu)
            (by gcongr; exact hnear c c' hcc' u hu))
      _ = _ := by ring
  have hall : ∀ b ∈ t, ∀ c ∈ t, Reach b c := by
    intro b hb
    have hbb : Reach b b := ⟨1, ENNReal.one_ne_top, fun u hu => by
      rw [one_mul]; exact hnear b b ⟨b, ⟨htΩ hb, mem_ball_self (by positivity)⟩,
        ⟨htΩ hb, mem_ball_self (by positivity)⟩⟩ u hu⟩
    set R := {c | c ∈ t ∧ Reach b c}
    have hsub := (isPreconnected_iff_subset_of_disjoint.mp hΩc) (⋃ c ∈ R, E c)
      (⋃ c ∈ {c | c ∈ t ∧ ¬ Reach b c}, E c)
      (isOpen_biUnion fun c _ => hEo c) (isOpen_biUnion fun c _ => hEo c)
      (by
        intro x hx
        obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
        by_cases hr : Reach b c
        · exact Or.inl (Set.mem_iUnion₂.mpr ⟨c, ⟨hct, hr⟩, hx, hxc⟩)
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, ⟨hct, hr⟩, hx, hxc⟩))
      (by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨c, ⟨hct, hr⟩, hxc⟩, ⟨c', ⟨-, hr'⟩, hxc'⟩⟩
        exact hr' (hstep b c c' hct hr ⟨x, hxc, hxc'⟩))
    have hΩR : Ω ⊆ ⋃ c ∈ R, E c := by
      refine hsub.resolve_right fun h => ?_
      obtain ⟨c', ⟨-, hr'⟩, hbc'⟩ := Set.mem_iUnion₂.mp (h (htΩ hb))
      exact hr' (hstep b b c' hb hbb ⟨b, ⟨htΩ hb, mem_ball_self (by positivity)⟩, hbc'⟩)
    intro c' hc'
    obtain ⟨c, ⟨hct, hr⟩, hc'c⟩ := Set.mem_iUnion₂.mp (hΩR (htΩ hc'))
    exact hstep b c c' hct hr ⟨c', hc'c, htΩ hc', mem_ball_self (by positivity)⟩
  -- sum over pairs of pieces
  have hsum : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ u : {u : EuclideanSpace ℝ (Fin d) → ℝ // Measurable u},
      ∑ b ∈ T, ∑ c ∈ T, pairInt u.1 (E b) (E c) ≤ K * Nf u.1 := by
    refine exists_sum_le T _ _ fun b hb => exists_sum_le T _ _ fun c hc => ?_
    obtain ⟨K, hK, h⟩ := hall b (htf.mem_toFinset.mp hb) c (htf.mem_toFinset.mp hc)
    exact ⟨K, hK, fun u => h u.1 u.2⟩
  obtain ⟨K, hK, hKu⟩ := hsum
  refine ⟨K, hK, fun u hu => le_trans ?_ (hKu ⟨u, hu⟩)⟩
  -- `Ω × Ω` is covered by the products of pieces
  have hΩcov : Ω ⊆ ⋃ c ∈ T, E c := fun x hx => by
    obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact Set.mem_iUnion₂.mpr ⟨c, htf.mem_toFinset.mpr hct, hx, hxc⟩
  have hU : ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      ∫⁻ x in Ω, F x ≤ ∑ c ∈ T, ∫⁻ x in E c, F x := fun F => by
    refine (lintegral_mono_set hΩcov).trans ?_
    rw [← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion]
    refine (lintegral_iUnion_le _ _).trans (le_of_eq ?_)
    rw [tsum_fintype]
    exact Finset.sum_coe_sort T fun c => ∫⁻ x in E c, F x
  unfold pairInt
  calc ∫⁻ x in Ω, ∫⁻ y in Ω, ENNReal.ofReal ((u x - u y) ^ 2)
      ≤ ∫⁻ x in Ω, ∑ c ∈ T, ∫⁻ y in E c, ENNReal.ofReal ((u x - u y) ^ 2) :=
        lintegral_mono fun x => hU _
    _ ≤ ∑ b ∈ T, ∫⁻ x in E b, ∑ c ∈ T, ∫⁻ y in E c, ENNReal.ofReal ((u x - u y) ^ 2) := hU _
    _ = ∑ b ∈ T, ∑ c ∈ T, ∫⁻ x in E b, ∫⁻ y in E c, ENNReal.ofReal ((u x - u y) ^ 2) := by
        refine Finset.sum_congr rfl fun b _ => lintegral_finsetSum _ fun c _ => ?_
        exact (measurable_sqDiff hu).lintegral_prod_right'

end Dyda
