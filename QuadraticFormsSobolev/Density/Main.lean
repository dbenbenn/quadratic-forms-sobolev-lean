import QuadraticFormsSobolev.Density.Mollify
import QuadraticFormsSobolev.Density.Cutoff
import QuadraticFormsSobolev.RandomLattice.Faithful

/-! # `C_c^∞(ℝ^d)` is dense in `H^{α/2}(ℝ^d)` and in `H_k(ℝ^d)`

Cut off (`Density/Cutoff.lean`), then mollify (`Density/Mollify.lean`). For `H_k(ℝ^d)` the norms
are comparable (Theorem 1.4 on `ℝ^d`), so density transfers.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

lemma formHs_neg (g : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ) :
    formHs univ α (-g) = formHs univ α g := by
  unfold formHs form
  refine lintegral_congr fun p => ?_
  simp only [Pi.neg_apply]
  congr 2; ring

lemma formHs_add_le {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Measurable a) (hb : Measurable b)
    (α : ℝ) : formHs univ α (a + b) ≤ 2 * formHs univ α a + 2 * formHs univ α b := by
  rw [formHs_univ_eq (ha.add hb), formHs_univ_eq ha, formHs_univ_eq hb]
  have hD : ∀ h, diffInt (a + b) h ≤ 2 * diffInt a h + 2 * diffInt b h := by
    intro h
    have := diffInt_sub_le (a := a) (b := -b) ha h
    have hneg : diffInt (-b) h = diffInt b h := by
      unfold diffInt; refine lintegral_congr fun x => ?_; simp only [Pi.neg_apply]; congr 1; ring
    simpa [sub_neg_eq_add, hneg] using this
  have hma := (measurable_wK d α).mul (measurable_diffInt ha)
  calc ∫⁻ h, wK d α h * diffInt (a + b) h
      ≤ ∫⁻ h, (2 * (wK d α h * diffInt a h) + 2 * (wK d α h * diffInt b h)) :=
        lintegral_mono fun h => by
          calc wK d α h * diffInt (a + b) h ≤ wK d α h * (2 * diffInt a h + 2 * diffInt b h) :=
                mul_le_mul_of_nonneg_left (hD h) zero_le
            _ = _ := by ring
    _ = _ := by
        rw [lintegral_add_left (f := fun h => 2 * (wK d α h * diffInt a h)) (by exact hma.const_mul 2),
          lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]

/-- **`C_c^∞(ℝ^d)` is dense in `H^{α/2}(ℝ^d)`.** -/
theorem formHs_univ_dense {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f 2 volume) (hS : formHs univ α f ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 2 volume ^ 2 + formHs univ α (f - g) < ENNReal.ofReal ε := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `ℝ^0` is a point: `f` itself is smooth with compact support
    have hf0 : f = fun _ => f 0 := funext fun x => by rw [Subsingleton.elim x 0]
    refine ⟨f, hf0 ▸ contDiff_const, HasCompactSupport.of_compactSpace f, ?_⟩
    rw [sub_self, formHs_dim_zero]
    simpa using hε
  -- a measurable representative
  obtain ⟨f₀, hf₀m, hff₀⟩ : ∃ f₀ : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f₀ ∧ f =ᵐ[volume] f₀ :=
    ⟨hf.1.mk f, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  have hae : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ᵐ x ∂(volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d)))), (f - g) x = (f₀ - g) x := by
    intro g
    rw [Measure.restrict_univ]
    filter_upwards [hff₀] with x hx
    simp [hx]
  have hf₀ : MemLp f₀ 2 volume := hf.ae_eq hff₀
  have hS₀ : formHs univ α f₀ ≠ ⊤ := by
    have : ∀ᵐ x ∂(volume.restrict (univ : Set (EuclideanSpace ℝ (Fin d)))), f x = f₀ x := by
      rw [Measure.restrict_univ]; exact hff₀
    rwa [formHs, ← form_congr_ae _ this]
  have hε8 : 0 < ENNReal.ofReal (ε / 8) := by rw [ENNReal.ofReal_pos]; positivity
  -- cut off
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp
    ((tendsto_sqInt_tail hf₀m hf₀).add (tendsto_formHs_tail hd hα0 hα2 hf₀m hf₀ hS₀)
      |> fun h => by simpa using h) _ hε8
  have hNN := hN N le_rfl
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => cutFun N x * f₀ x with hg
  have hgm : Measurable g := (measurable_cutFun N).mul hf₀m
  have htm : Measurable (tail N f₀) := ((measurable_const.sub (measurable_cutFun N)).mul hf₀m)
  have hsplit : f₀ = tail N f₀ + g := by funext x; simp [tail, g]; ring
  have hg2 : MemLp g 2 volume := by
    refine hf₀.mono hgm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp only [g, norm_mul, Real.norm_eq_abs]
    have := cutFun_nonneg N x
    have := cutFun_le_one N x
    rw [abs_of_nonneg (cutFun_nonneg N x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (cutFun_le_one N x)
  have hgS : formHs univ α g ≠ ⊤ := by
    have hgeq : g = f₀ + -tail N f₀ := by
      funext x; simp only [g, tail, Pi.add_apply, Pi.neg_apply]; ring
    have ht : formHs univ α (tail N f₀) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) (le_trans le_add_self hNN)
    refine ne_top_of_le_ne_top ?_ (hgeq ▸ formHs_add_le hf₀m htm.neg α)
    rw [formHs_neg]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hS₀,
      ENNReal.mul_ne_top (by norm_num) ht⟩
  have hgc : HasCompactSupport g := (hasCompactSupport_cutFun N).mul_right
  -- mollify
  have hloc := hg2.locallyIntegrable (by norm_num)
  obtain ⟨n, hn⟩ := ENNReal.tendsto_atTop_zero.mp
    ((tendsto_sqInt_mollify_sub hgm hg2).add (tendsto_formHs_mollify_sub hgm hg2 hgS)
      |> fun h => by simpa using h) _ hε8
  have hnn := hn n le_rfl
  set m := mollify n g with hm
  have hmm : Measurable m := (contDiff_mollify hloc n).continuous.measurable
  refine ⟨m, contDiff_mollify hloc n, hasCompactSupport_mollify hgc n, ?_⟩
  have e1 : f₀ - m = tail N f₀ + -(m - g) := by
    funext x; simp only [g, tail, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring
  have hQ : sqInt (f₀ - m) ≤ 2 * sqInt (tail N f₀) + 2 * sqInt (m - g) := by
    rw [e1, ← sqInt_neg (m - g)]; exact sqInt_add_le htm
  have hF : formHs univ α (f₀ - m) ≤ 2 * formHs univ α (tail N f₀) + 2 * formHs univ α (m - g) := by
    rw [e1, ← formHs_neg (m - g)]; exact formHs_add_le htm (hmm.sub hgm).neg α
  rw [eLpNorm_congr_ae (hff₀.sub (Filter.EventuallyEq.refl _ m)), eLpNorm_two_sq,
    formHs, form_congr_ae _ (hae m), ← formHs]
  calc sqInt (f₀ - m) + formHs univ α (f₀ - m)
      ≤ 2 * (sqInt (tail N f₀) + formHs univ α (tail N f₀)) +
          2 * (sqInt (m - g) + formHs univ α (m - g)) := by
        calc _ ≤ (2 * sqInt (tail N f₀) + 2 * sqInt (m - g)) +
              (2 * formHs univ α (tail N f₀) + 2 * formHs univ α (m - g)) := add_le_add hQ hF
          _ = _ := by ring
    _ ≤ 2 * ENNReal.ofReal (ε / 8) + 2 * ENNReal.ofReal (ε / 8) := by gcongr
    _ = ENNReal.ofReal (ε / 2) := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- **Theorem 1.4, density on `ℝ^d`: `C_c^∞(ℝ^d)` is dense in `H_k(ℝ^d)`.** -/
theorem theoremOneFour_density_univ (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexAdmissible Γ ϑ →
    ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MemLp f 2 volume → form univ k f ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε →
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) 2 volume ^ 2 + form univ k (f - g) < ENNReal.ofReal ε := by
  intro ϑ Λ α hϑ hΛ hα hα2 Γ hΓ k hk f hf hfk ε hε
  obtain ⟨c, -, hc⟩ := theoremOneFour_univ d ϑ Λ α hϑ hΛ hα hα2
  have hS : formHs univ α f ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfk)
      ((hc Γ hΓ k hk).2 f hf).1
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨g, hg1, hg2, hg⟩ := formHs_univ_dense hα hα2 hf hS (div_pos hε hΛ0)
  refine ⟨g, hg1, hg2, ?_⟩
  calc eLpNorm (f - g) 2 volume ^ 2 + form univ k (f - g)
      ≤ eLpNorm (f - g) 2 volume ^ 2 + ENNReal.ofReal Λ * formHs univ α (f - g) := by
        gcongr; exact form_le_formHs hk _ _
    _ ≤ ENNReal.ofReal Λ * (eLpNorm (f - g) 2 volume ^ 2 + formHs univ α (f - g)) := by
        rw [mul_add]
        gcongr
        calc eLpNorm (f - g) 2 volume ^ 2 = 1 * eLpNorm (f - g) 2 volume ^ 2 := (one_mul _).symm
          _ ≤ ENNReal.ofReal Λ * eLpNorm (f - g) 2 volume ^ 2 := by
              gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hΛ
    _ < ENNReal.ofReal Λ * ENNReal.ofReal (ε / Λ) :=
        ENNReal.mul_lt_mul_right (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hΛ0)
          ENNReal.ofReal_ne_top hg
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hΛ0.le]; congr 1; field_simp

end QFS
