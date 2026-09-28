/-
Section 1 of Bux–Kassmann–Schulze: the quadratic forms, the function spaces
`H_k(Ω)` and `H^{α/2}(Ω)`, assumption (2) on the kernel, the reverse
inequality of Theorem 1.1 (which "trivially holds"), and the inclusion (5).

The discrete form of Theorem 1.3 is defined here too, and the file ends with basic facts about
the forms. The paper's results are stated in `Paper.lean`.
-/
import QuadraticFormsSobolev.Section5

open Real Set Metric MeasureTheory ENNReal

namespace QFS

variable {d : ℕ}

/-! ## The kernels and the quadratic forms -/

/-- The kernel `|x − y|^{-d-α}` of the `H^{α/2}` seminorm (1). -/
noncomputable def jumpKernel (d : ℕ) (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (‖x - y‖ ^ (-(d : ℝ) - α))

/-- The indicator of a set, valued in `ℝ≥0∞`. -/
noncomputable def indE (S : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ≥0∞ := S.indicator (fun _ => 1) x

/-- Smaller cones give smaller cone indicators. -/
lemma indE_coneAt_mono {Γ Γ' : Configuration (EuclideanSpace ℝ (Fin d))}
    (h : ∀ x, (Γ x).carrier ⊆ (Γ' x).carrier) (x y : EuclideanSpace ℝ (Fin d)) :
    indE (coneAt Γ x) y ≤ indE (coneAt Γ' x) y :=
  Set.indicator_le_indicator_of_subset (shift_mono (h x) x) (fun _ => zero_le) y

/-- The quadratic form `∫_{Ω×Ω} (f(y) − f(x))² k(x,y) d(x,y)` of Section 1.

The paper writes this integral as `|f|_{H_k(Ω)}` and then uses `|f|²_{H_k(Ω)}`
in the definition of the norm; we name the integral itself, which is the
quantity both readings agree on. -/
noncomputable def form (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2

/-- The `H^{α/2}(Ω)` form, i.e. the seminorm (1) restricted to `Ω`. -/
noncomputable def formHs (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  form Ω (jumpKernel d α) f

/-! ## Assumption (2) -/

/-- Assumption (2) of Theorem 1.1: `k` is symmetric and satisfies

  `Λ⁻¹ (1_{V^Γ[x]}(y) + 1_{V^Γ[y]}(x)) |x−y|^{-d-α} ≤ k(x,y) ≤ Λ |x−y|^{-d-α}`. -/
structure KernelBounds (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (α Λ : ℝ)
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : Prop where
  /-- The constant `Λ` is at least one. -/
  one_le : 1 ≤ Λ
  /-- `k` is symmetric. -/
  symm : ∀ x y, k x y = k y x
  /-- The lower bound, which sees only the double cones of `Γ`. -/
  lower : ∀ x y, ENNReal.ofReal Λ⁻¹ *
      ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y) ≤ k x y
  /-- The upper bound, off the diagonal. On the diagonal the paper's bound `Λ|x − y|^{−d−α}` is
  `+∞` and says nothing, so `k(x, x)` is left free. (`jumpKernel` uses the real power, which is `0`
  at `x = y`; asking the bound there would force `k(x, x) = 0`.) -/
  upper : ∀ x y, x ≠ y → k x y ≤ ENNReal.ofReal Λ * jumpKernel d α x y

/-! ## The reverse inequality, and the inclusion (5) -/

/-- The upper bound in (2) makes the `H^{α/2}` form dominate the `H_k` form on
every set. This is both the "reverse inequality in (3)", which the paper notes
"trivially holds true", and the inequality behind the inclusion (5). -/
theorem form_le_formHs {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    form Ω k f ≤ ENNReal.ofReal Λ * formHs Ω α f := by
  have hstep : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2
        ≤ ENNReal.ofReal Λ *
          (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by
    intro p
    -- on the diagonal the difference vanishes, whatever `k(x, x)` is
    by_cases hp : p.1 = p.2
    · rw [hp, sub_self]; simp
    calc ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2
        ≤ ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
            (ENNReal.ofReal Λ * jumpKernel d α p.1 p.2) :=
          mul_le_mul' (le_refl _) (hk.upper _ _ hp)
      _ = ENNReal.ofReal Λ *
            (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) := by ring
  calc form Ω k f
      ≤ ∫⁻ p in Ω ×ˢ Ω, ENNReal.ofReal Λ *
          (ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2) :=
        lintegral_mono (fun p => hstep p)
    _ = ENNReal.ofReal Λ * formHs Ω α f :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `H_k(Ω) = {f ∈ L²(Ω) | |f|_{H_k(Ω)} < ∞}`. -/
def Hk (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | MemLp f 2 (volume.restrict Ω) ∧ form Ω k f ≠ ⊤}

/-- `H^{α/2}(Ω) = {f ∈ L²(Ω) | |f|_{H^{α/2}(Ω)} < ∞}`. -/
def Hs (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | MemLp f 2 (volume.restrict Ω) ∧ formHs Ω α f ≠ ⊤}

/-- **Equation (5)**: `H^{α/2}(Ω) ⊆ H_k(Ω)`. -/
theorem Hs_subset_Hk {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Hs Ω α ⊆ Hk Ω k := by
  rintro f ⟨hmem, hfin⟩
  refine ⟨hmem, ?_⟩
  refine ne_top_of_le_ne_top ?_ (form_le_formHs hk Ω f)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin

/-! ## The discrete form of Theorem 1.3 -/

/-- The discrete quadratic form of Theorem 1.3: the sum over pairs of lattice
points of `S` at distance more than `R₀`. -/
noncomputable def discreteForm (S : Set (EuclideanSpace ℝ (Fin d))) (R₀ : ℝ)
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∑' p : {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) //
      p.1 ∈ S ∩ lattice d ∧ p.2 ∈ S ∩ lattice d ∧ R₀ < ‖p.1 - p.2‖},
    ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) * ω p.1.1 p.1.2

/-- Assumption (4) of Theorem 1.3: the two-sided bound on `ω`, imposed only for
`|x − y| > R₀` **and only at pairs of points of the lattice `L`**. The paper's `ω`
is a function on `ℤ^d × ℤ^d` (on `hℤ^d × hℤ^d` in Corollary 3.1), so asking the
bounds off the lattice would be a genuine strengthening of the hypothesis: at a
pair where both indicators fire the two bounds force `Λ ≥ √2`, so for
`Λ ∈ [1, √2)` an off-lattice mutually-coned pair would make the hypothesis
unsatisfiable. -/
structure DiscreteKernelBounds (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (α Λ R₀ : ℝ) (L : Set (EuclideanSpace ℝ (Fin d)))
    (ω : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    Prop where
  /-- The constant `Λ` is at least one. -/
  one_le : 1 ≤ Λ
  /-- `ω` is symmetric on `L`. -/
  symm : ∀ x ∈ L, ∀ y ∈ L, ω x y = ω y x
  /-- The lower bound, for `|x − y| > R₀`. -/
  lower : ∀ x ∈ L, ∀ y ∈ L, R₀ < ‖x - y‖ → ENNReal.ofReal Λ⁻¹ *
      ((indE (coneAt Γ x) y + indE (coneAt Γ y) x) * jumpKernel d α x y) ≤ ω x y
  /-- The upper bound, for `|x − y| > R₀`. -/
  upper : ∀ x ∈ L, ∀ y ∈ L, R₀ < ‖x - y‖ → ω x y ≤ ENNReal.ofReal Λ * jumpKernel d α x y

/-- The statement of **Theorem 1.3**, the discrete main theorem. The paper
quantifies over functions on `B_{κR}(x₀) ∩ ℤ^d`; since both forms read `f` only
at lattice points of the relevant balls, quantifying over functions on all of
`ℝ^d` is equivalent. -/
def TheoremOneThree (d : ℕ) : Prop :=
  ∀ ϑ Λ α R₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 → 0 < R₀ →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), ApexLowerBound Γ ϑ →
      ∀ ω, DiscreteKernelBounds Γ α Λ R₀ (lattice d) ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ), 0 < R →
        discreteForm (ball x₀ R) R₀ (jumpKernel d α) f
          ≤ ENNReal.ofReal c * discreteForm (ball x₀ (κ * R)) R₀ ω f

/-! ## Basic facts about the forms -/

theorem measurable_jumpKernel (d : ℕ) (α : ℝ) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      jumpKernel d α p.1 p.2 := by
  unfold jumpKernel
  exact ENNReal.measurable_ofReal.comp
    ((measurable_fst.sub measurable_snd).norm.pow_const _)

/-- The form does not see a change of `f` on a null set of the domain. -/
theorem form_congr_ae {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfg : ∀ᵐ x ∂(volume.restrict Ω), f x = g x) : form Ω k f = form Ω k g := by
  have hmeas : volume.restrict (Ω ×ˢ Ω)
      = (volume.restrict Ω).prod (volume.restrict Ω) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [form, form, hmeas]
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict Ω)), f p.1 = g p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hfg
  have h2 : ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict Ω)), f p.2 = g p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hfg
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]

/-- In dimension zero every `H^{α/2}` form vanishes. -/
lemma formHs_dim_zero (Ω : Set (EuclideanSpace ℝ (Fin 0))) (α : ℝ)
    (f : EuclideanSpace ℝ (Fin 0) → ℝ) : formHs Ω α f = 0 := by
  have h : ∀ p : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel 0 α p.1 p.2 = 0 := by
    intro p
    have : p.2 = p.1 := Subsingleton.elim _ _
    rw [this, sub_self]; simp
  simp only [formHs, form, h, lintegral_zero]

end QFS
