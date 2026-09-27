import QuadraticFormsSobolev.Section5

/-! # Lemma 5.7 as printed: δ from Lemma 5.6, strictly increasing radii -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QFS

theorem lemmaFiveSeven {d : ℕ} {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex → ∀ x ∈ lattice d, x ∈ V.carrier →
        (∃ z ∈ lattice d, z ∈ V.carrier ∧ ‖z‖ < ‖x‖) →
        ∃ y ∈ lattice d, y ∈ V.carrier ∧ ‖y‖ < ‖x‖ ∧ ‖y - x‖ < δ) ∧
      ∃ r ρ R : ℕ → ℝ, δ < r 1 ∧
        (∀ i : ℕ, 1 ≤ i → r i ≤ ρ i ∧ ρ i ≤ R i ∧
          r i < r (i + 1) ∧ ρ i < ρ (i + 1) ∧ R i < R (i + 1)) ∧
        ∀ k : ℕ, 1 ≤ k → ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), (∀ z, ϑ ≤ (Γ z).apex) →
          ∀ x ∈ lattice d, (typesIn Γ (Metric.ball x (ρ k))).encard ≤ (k : ℕ∞) →
            RRConnected Γ (r k) (R k) x := by
  obtain ⟨δ, hδ0, h56⟩ := exists_closer_lattice_nearby (d := d) hϑ hϑ'
  obtain ⟨δc, -, hcore⟩ := core_induction (d := d) (ϑ := ϑ) hϑ hϑ'
  choose rr ρρ RR _hδc hkr hrρ hρR hconn using hcore
  -- reindex: use the constants for a larger number `m i` of types
  let m : ℕ → ℕ := fun i => Nat.rec 0 (fun j mj => ⌈RR mj⌉₊ + ⌈δ⌉₊ + j + 1) i
  have hm : ∀ j, m (j + 1) = ⌈RR (m j)⌉₊ + ⌈δ⌉₊ + j + 1 := fun j => rfl
  have hRR : ∀ j, RR (m j) < rr (m (j + 1)) := by
    intro j
    have h1 := Nat.le_ceil (RR (m j))
    have h2 := hkr (m (j + 1))
    rw [hm] at h2 ⊢
    push_cast at h2
    have : (0:ℝ) ≤ ⌈δ⌉₊ := Nat.cast_nonneg _
    have : (0:ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  have hmk : ∀ k, 1 ≤ k → k ≤ m k := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hm]; omega
  refine ⟨δ, hδ0, h56, fun i => rr (m i), fun i => ρρ (m i), fun i => RR (m i), ?_, ?_, ?_⟩
  · have hmδ : ∀ j, δ < (m (j + 1) : ℝ) := by
      intro j
      have h1 := Nat.le_ceil δ
      rw [hm]; push_cast
      have : (0:ℝ) ≤ ⌈RR (m j)⌉₊ := Nat.cast_nonneg _
      have : (0:ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    exact lt_of_lt_of_le (hmδ 0) (hkr (m (0 + 1)))
  · intro i _
    have a := hRR i
    have b := hrρ (m (i + 1))
    have c := hρR (m (i + 1))
    have b' := hrρ (m i)
    have c' := hρR (m i)
    refine ⟨b', c', ?_, ?_, ?_⟩ <;> simp only <;> linarith
  · intro k hk Γ hb x hx hcard
    exact hconn (m k) Γ hb x hx (hcard.trans (by exact_mod_cast hmk k hk))

end QFS
