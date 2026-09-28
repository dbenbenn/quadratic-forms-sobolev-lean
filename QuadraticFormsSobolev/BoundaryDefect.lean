/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import Mathlib

/-! # The limit step of §3.2 fails as printed for `α > 1`

In the proof of Lemma 3.7 (p. 15) Bux, Kassmann and Schulze put
`f_h(x) = h^{-d} ∫_{A_h(x) ∩ B*} f` for `x ∈ hℤ^d ∩ B*`, and on p. 16 assert that the right-hand
side of (15),
`∑_{x, y ∈ B* ∩ hℤ^d, |x − y| > √d h} (f_h(x) − f_h(y))² ∫_{A_h(x) × A_h(y)} k`,
converges to `∫_{B* × B*} (f(s) − f(t))² k`.

Here `d = 1`, `B* = (−1, 1)`, `f ≡ 1` and `k(s, t) = |s − t|^{−1−α}`. The limit is `0`, but for
`α > 1` the right-hand side of (15) tends to `∞` along `h = 1/(n + 1/4)`: the end cell of
`nh = 1 − h/4` sticks out of `B*`, so `f_h(nh) = 3/4`, and the single pair `(nh, nh − 2h)` already
contributes `h^{1−α} / (16 · 3^{1+α})`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace QFS.BoundaryDefect

/-- The cell `A_h(x)` of side `h` about `x`. -/
def cell (h x : ℝ) : Set ℝ := Icc (x - h / 2) (x + h / 2)

/-- `f_h(x) = h⁻¹ ∫_{A_h(x) ∩ B*} f` for `f ≡ 1` and `B* = (−1, 1)`. -/
noncomputable def fh (h x : ℝ) : ℝ := h⁻¹ * (volume (cell h x ∩ Ioo (-1) 1)).toReal

/-- The right-hand side of (15) for `f ≡ 1`, `B* = (−1, 1)` and `k(s, t) = |s − t|^{−1−α}`. -/
noncomputable def rhs15 (α h : ℝ) : ℝ≥0∞ :=
  ∑' p : ℤ × ℤ,
    if |(p.1 : ℝ) * h| < 1 ∧ |(p.2 : ℝ) * h| < 1 ∧ h < |(p.1 : ℝ) * h - p.2 * h| then
      ENNReal.ofReal ((fh h (p.1 * h) - fh h (p.2 * h)) ^ 2) *
        ∫⁻ q in cell h (p.1 * h) ×ˢ cell h (p.2 * h), ENNReal.ofReal (|q.1 - q.2| ^ (-1 - α))
    else 0

/-- The continuous form the limit should be: `∫_{B* × B*} (f(s) − f(t))² k = 0` for `f ≡ 1`. -/
theorem limit_eq_zero (α : ℝ) :
    ∫⁻ q in Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1,
      ENNReal.ofReal (((1 : ℝ) - 1) ^ 2) * ENNReal.ofReal (|q.1 - q.2| ^ (-1 - α)) = 0 := by
  simp

section

variable {n : ℕ} (hn : 3 ≤ n)
include hn

lemma h_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1 / 4) := by positivity

lemma nh_eq : (n : ℝ) * (1 / ((n : ℝ) + 1 / 4)) = 1 - (1 / ((n : ℝ) + 1 / 4)) / 4 := by
  field_simp; ring

lemma h_small : 1 / ((n : ℝ) + 1 / 4) ≤ 1 / 3 := by
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

lemma fh_end : fh (1 / ((n : ℝ) + 1 / 4)) (n * (1 / ((n : ℝ) + 1 / 4))) = 3 / 4 := by
  set h := 1 / ((n : ℝ) + 1 / 4)
  have h0 := h_pos hn
  have hs := h_small hn
  have hcell : cell h (n * h) ∩ Ioo (-1) 1 = Ico (1 - 3 * h / 4) 1 := by
    rw [cell, nh_eq hn]
    ext t; simp only [mem_inter_iff, mem_Icc, mem_Ioo, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by linarith, h4⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, h2⟩
  have hne : h ≠ 0 := ne_of_gt h0
  rw [fh, hcell, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  field_simp; ring

lemma fh_interior : fh (1 / ((n : ℝ) + 1 / 4)) ((n - 2 : ℤ) * (1 / ((n : ℝ) + 1 / 4))) = 1 := by
  set h := 1 / ((n : ℝ) + 1 / 4)
  have h0 := h_pos hn
  have hs := h_small hn
  have hnh := nh_eq hn
  have hx : ((n - 2 : ℤ) : ℝ) * h = n * h - 2 * h := by push_cast; ring
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcell : cell h ((n - 2 : ℤ) * h) ∩ Ioo (-1) 1 = cell h ((n - 2 : ℤ) * h) := by
    refine inter_eq_left.mpr fun t ht => ?_
    rw [cell, hx, hnh] at ht
    have : 0 ≤ n * h - 2 * h - h / 2 := by nlinarith
    rw [hnh] at this
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hne : h ≠ 0 := ne_of_gt h0
  rw [fh, hcell, cell, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  field_simp; ring

/-- The pair `(nh, nh − 2h)` alone: the right-hand side of (15) is at least
`h² (3h)^{−1−α} / 16`. -/
lemma rhs15_ge {α : ℝ} (hα : -1 ≤ α) :
    ENNReal.ofReal ((1 / ((n : ℝ) + 1 / 4)) ^ 2 * (3 * (1 / ((n : ℝ) + 1 / 4))) ^ (-1 - α) / 16)
      ≤ rhs15 α (1 / ((n : ℝ) + 1 / 4)) := by
  set h := 1 / ((n : ℝ) + 1 / 4) with hdef
  have h0 : 0 < h := h_pos hn
  have hs : h ≤ 1 / 3 := h_small hn
  have hnh : (n : ℝ) * h = 1 - h / 4 := nh_eq hn
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : ((n - 2 : ℤ) : ℝ) * h = n * h - 2 * h := by push_cast; ring
  refine le_trans ?_ (ENNReal.le_tsum ((n : ℤ), (n : ℤ) - 2))
  simp only [Int.cast_natCast]
  have hcond : |(n : ℝ) * h| < 1 ∧ |((n - 2 : ℤ) : ℝ) * h| < 1 ∧
      h < |(n : ℝ) * h - ((n - 2 : ℤ) : ℝ) * h| := by
    rw [hx, hnh]
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> nlinarith
    · rw [show 1 - h / 4 - (1 - h / 4 - 2 * h) = 2 * h by ring, abs_of_pos (by linarith)]
      linarith
  rw [if_pos hcond, fh_end hn, fh_interior hn]
  -- the integrand is at least `(3h)^{−1−α}` on the pair of cells
  have hpt : ∀ q ∈ cell h (n * h) ×ˢ cell h ((n - 2 : ℤ) * h),
      ENNReal.ofReal ((3 * h) ^ (-1 - α)) ≤ ENNReal.ofReal (|q.1 - q.2| ^ (-1 - α)) := by
    rintro ⟨s, t⟩ ⟨hs', ht'⟩
    rw [cell, hnh] at hs'
    rw [cell, hx, hnh] at ht'
    obtain ⟨hs1, hs2⟩ := hs'
    obtain ⟨ht1, ht2⟩ := ht'
    have hlo : h ≤ s - t := by linarith
    have hhi : s - t ≤ 3 * h := by linarith
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hhi (by linarith)
  have hmeas : MeasurableSet (cell h (n * h) ×ˢ cell h ((n - 2 : ℤ) * h)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hint := setLIntegral_mono' (μ := volume) hmeas hpt
  rw [setLIntegral_const, Measure.volume_eq_prod, Measure.prod_prod, cell, cell, Real.volume_Icc,
    Real.volume_Icc] at hint
  rw [← Measure.volume_eq_prod] at hint
  calc ENNReal.ofReal (h ^ 2 * (3 * h) ^ (-1 - α) / 16)
      = ENNReal.ofReal ((3 / 4 - 1) ^ 2) *
          (ENNReal.ofReal ((3 * h) ^ (-1 - α)) *
            (ENNReal.ofReal (n * h + h / 2 - (n * h - h / 2)) *
              ENNReal.ofReal ((n - 2 : ℤ) * h + h / 2 - ((n - 2 : ℤ) * h - h / 2)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by gcongr; exact hint

end

lemma bound_eq (n : ℕ) (α : ℝ) :
    (1 / ((n : ℝ) + 1 / 4)) ^ 2 * (3 * (1 / ((n : ℝ) + 1 / 4))) ^ (-1 - α) / 16
      = (3 : ℝ) ^ (-1 - α) / 16 * ((n : ℝ) + 1 / 4) ^ (α - 1) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  set x := (n : ℝ) + 1 / 4
  rw [Real.mul_rpow (by norm_num) (by positivity), one_div, Real.inv_rpow hx.le,
    ← Real.rpow_neg hx.le, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hx.le]
  have : x ^ (-((2 : ℕ) : ℝ)) * x ^ (-(-1 - α)) = x ^ (α - 1) := by
    rw [← Real.rpow_add hx]; congr 1; push_cast; ring
  rw [← this]; ring

/-- **The limit step of §3.2 fails as printed for `α > 1`.** For `d = 1`, `B* = (−1, 1)`,
`f ≡ 1` and `k(s, t) = |s − t|^{−1−α}`, the right-hand side of (15) tends to `∞` along
`h = 1/(n + 1/4)`, while the limit asserted on p. 16 is `0` (`limit_eq_zero`). -/
theorem rhs15_tendsto_top {α : ℝ} (hα : 1 < α) :
    Tendsto (fun n : ℕ => rhs15 α (1 / ((n : ℝ) + 1 / 4))) atTop (𝓝 ⊤) := by
  have hreal : Tendsto (fun n : ℕ => (3 : ℝ) ^ (-1 - α) / 16 * ((n : ℝ) + 1 / 4) ^ (α - 1))
      atTop atTop :=
    ((tendsto_rpow_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)).const_mul_atTop
      (by positivity)
  refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hreal) ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp only [Function.comp_apply]
  rw [← bound_eq]
  exact rhs15_ge hn (by linarith)

end QFS.BoundaryDefect
