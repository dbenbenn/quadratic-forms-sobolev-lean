import QuadraticFormsSobolev.Density.DomainPiece

/-! # A telescoping partition of unity

For cutoffs `χ_0, χ_1, …` with values in `[0, 1]`, put `R_j = ∏_{i<j} (1 − χ_i)` and
`π_j = χ_j R_j`. Then `∑_{j<m} π_j + R_m = 1` everywhere, every `π_j` and `R_j` has values in
`[0, 1]`, is Lipschitz when the `χ_i` are, and is smooth when they are; `π_j` vanishes where `χ_j`
does, and `R_m` vanishes where some `χ_i`, `i < m`, equals `1`.
-/

open MeasureTheory Metric Set Filter Topology Finset
open scoped ENNReal NNReal

namespace QFS

variable {d : ℕ}

set_option hygiene false in
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- `R_j = ∏_{i<j} (1 − χ_i)`. -/
noncomputable def partR (χ : ℕ → 𝔼 → ℝ) (j : ℕ) (x : 𝔼) : ℝ := ∏ i ∈ range j, (1 - χ i x)

/-- `π_j = χ_j R_j`. -/
noncomputable def partPi (χ : ℕ → 𝔼 → ℝ) (j : ℕ) (x : 𝔼) : ℝ := χ j x * partR χ j x

lemma partPi_sum_add_partR (χ : ℕ → 𝔼 → ℝ) (m : ℕ) (x : 𝔼) :
    ∑ j ∈ range m, partPi χ j x + partR χ m x = 1 := by
  induction m with
  | zero => simp [partR]
  | succ m ih =>
    rw [sum_range_succ, partR, prod_range_succ, ← partR, partPi]
    linarith [show partR χ m x * (1 - χ m x) = partR χ m x - χ m x * partR χ m x by ring]

variable {χ : ℕ → 𝔼 → ℝ}

lemma partR_mem (h0 : ∀ i x, 0 ≤ χ i x) (h1 : ∀ i x, χ i x ≤ 1) (j : ℕ) (x : 𝔼) :
    0 ≤ partR χ j x ∧ partR χ j x ≤ 1 := by
  induction j with
  | zero => simp [partR]
  | succ j ih =>
    rw [partR, prod_range_succ, ← partR]
    have := h0 j x; have := h1 j x
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · nlinarith [ih.1, ih.2]

lemma partPi_mem (h0 : ∀ i x, 0 ≤ χ i x) (h1 : ∀ i x, χ i x ≤ 1) (j : ℕ) (x : 𝔼) :
    0 ≤ partPi χ j x ∧ partPi χ j x ≤ 1 := by
  have hR := partR_mem h0 h1 j x
  have := h0 j x; have := h1 j x
  exact ⟨mul_nonneg (h0 j x) hR.1, by unfold partPi; nlinarith⟩

/-- A product of `[0, 1]`-valued Lipschitz functions is Lipschitz with the sum of constants. -/
lemma abs_mul_sub_le {a b : 𝔼 → ℝ} (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1) {La Lb : ℝ}
    (ha : ∀ x y, |a x - a y| ≤ La * ‖x - y‖) (hb : ∀ x y, |b x - b y| ≤ Lb * ‖x - y‖) (x y : 𝔼) :
    |a x * b x - a y * b y| ≤ (La + Lb) * ‖x - y‖ := by
  have e : a x * b x - a y * b y = a x * (b x - b y) + b y * (a x - a y) := by ring
  rw [e]
  calc |a x * (b x - b y) + b y * (a x - a y)|
      ≤ |a x * (b x - b y)| + |b y * (a x - a y)| := abs_add_le _ _
    _ = a x * |b x - b y| + b y * |a x - a y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (ha0 x), abs_of_nonneg (hb0 y)]
    _ ≤ 1 * (Lb * ‖x - y‖) + 1 * (La * ‖x - y‖) := by
        gcongr
        · exact ha1 x
        · exact hb x y
        · exact hb1 y
        · exact ha x y
    _ = (La + Lb) * ‖x - y‖ := by ring

lemma partR_lip (h0 : ∀ i x, 0 ≤ χ i x) (h1 : ∀ i x, χ i x ≤ 1) {L : ℕ → ℝ}
    (hL : ∀ i x y, |χ i x - χ i y| ≤ L i * ‖x - y‖) (j : ℕ) (x y : 𝔼) :
    |partR χ j x - partR χ j y| ≤ (∑ i ∈ range j, L i) * ‖x - y‖ := by
  induction j generalizing x y with
  | zero => simp [partR]
  | succ j ih =>
    have e : ∀ x, partR χ (j + 1) x = partR χ j x * (1 - χ j x) := fun x => by
      simp [partR, prod_range_succ]
    rw [e, e, sum_range_succ]
    refine abs_mul_sub_le (b := fun x => 1 - χ j x) (fun x => (partR_mem h0 h1 j x).1)
      (fun x => (partR_mem h0 h1 j x).2)
      (fun x => by have := h1 j x; linarith) (fun x => by have := h0 j x; linarith) ih
      (fun x y => ?_) x y
    rw [show 1 - χ j x - (1 - χ j y) = -(χ j x - χ j y) by ring, abs_neg]
    exact hL j x y

lemma partPi_lip (h0 : ∀ i x, 0 ≤ χ i x) (h1 : ∀ i x, χ i x ≤ 1) {L : ℕ → ℝ}
    (hL : ∀ i x y, |χ i x - χ i y| ≤ L i * ‖x - y‖) (j : ℕ) (x y : 𝔼) :
    |partPi χ j x - partPi χ j y| ≤ (L j + ∑ i ∈ range j, L i) * ‖x - y‖ :=
  abs_mul_sub_le (h0 j) (h1 j) (fun x => (partR_mem h0 h1 j x).1)
    (fun x => (partR_mem h0 h1 j x).2) (hL j) (partR_lip h0 h1 hL j) x y

lemma contDiff_partR (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (partR χ j) := by
  unfold partR
  exact contDiff_prod fun i _ => contDiff_const.sub (hs i)

lemma contDiff_partPi (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (partPi χ j) :=
  (hs j).mul (contDiff_partR hs j)

lemma partPi_ne_zero {j : ℕ} {x : 𝔼} (h : partPi χ j x ≠ 0) : χ j x ≠ 0 :=
  fun h' => h (by simp [partPi, h'])

lemma partR_eq_zero {m i : ℕ} (hi : i < m) {x : 𝔼} (h : χ i x = 1) : partR χ m x = 0 := by
  unfold partR
  exact prod_eq_zero (mem_range.mpr hi) (by rw [h]; ring)

end QFS
