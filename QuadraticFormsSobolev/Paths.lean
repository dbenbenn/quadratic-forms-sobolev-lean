/-
Turning the reachability relations of Sections 4 and 5 into honest walks, with
length bounds, and concatenating them.

`Relation.ReflTransGen` records that a path exists, not which one, so it carries
no length. But a walk confined to a *finite* vertex set can be shortened to a
path, whose length is bounded by the size of that set — which is where all the
length bounds of Theorem 5.15 come from.
-/
import QuadraticFormsSobolev.Counting
import QuadraticFormsSobolev.FirstJump

open Real Set Metric

namespace QFS

variable {V : Type*} {G : SimpleGraph V}

/-- A reachability chain confined to `S` gives a walk whose support lies in `S`. -/
theorem exists_walk_of_reflTransGen {r : V → V → Prop} {S : Set V}
    (hadj : ∀ a b, r a b → a = b ∨ G.Adj a b)
    (hmem : ∀ a b, r a b → a ∈ S ∧ b ∈ S)
    {a b : V} (ha : a ∈ S) (h : Relation.ReflTransGen r a b) :
    ∃ w : G.Walk a b, ∀ v ∈ w.support, v ∈ S := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simpa using ha⟩
  | @tail p c hpre hstep ih =>
      obtain ⟨w, hw⟩ := ih
      rcases hadj p c hstep with heq | hAdj
      · rw [← heq]
        exact ⟨w, hw⟩
      · refine ⟨w.append (SimpleGraph.Walk.cons hAdj SimpleGraph.Walk.nil), fun v hv => ?_⟩
        rw [SimpleGraph.Walk.mem_support_append_iff] at hv
        rcases hv with hv | hv
        · exact hw v hv
        · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h1 | h1
          · rw [h1]; exact (hmem _ _ hstep).1
          · rw [h1]; exact (hmem _ _ hstep).2

/-- A walk confined to a finite set can be replaced by one of length less than the
size of that set: delete the cycles. -/
theorem exists_walk_length_lt {S : Set V} (hSfin : S.Finite)
    {a b : V} {w : G.Walk a b} (hw : ∀ v ∈ w.support, v ∈ S) :
    ∃ w' : G.Walk a b, (∀ v ∈ w'.support, v ∈ S) ∧ w'.length < S.ncard := by
  classical
  refine ⟨w.bypass, fun v hv => hw v (SimpleGraph.Walk.support_bypass_subset_support w hv), ?_⟩
  have hnodup : w.bypass.support.Nodup := (SimpleGraph.Walk.bypass_isPath w).support_nodup
  have hsub : w.bypass.support.toFinset ⊆ hSfin.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv
    rw [Set.Finite.mem_toFinset]
    exact hw v (SimpleGraph.Walk.support_bypass_subset_support w hv)
  have hcard : w.bypass.support.length ≤ hSfin.toFinset.card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hsub
  have hlen : w.bypass.support.length = w.bypass.length + 1 :=
    SimpleGraph.Walk.length_support w.bypass
  have hSn : hSfin.toFinset.card = S.ncard := by
    rw [← Set.ncard_coe_finset, hSfin.coe_toFinset]
  omega

/-- **The bridge**: a reachability chain confined to a finite set `S` yields a walk
inside `S` of length less than `#S`. -/
theorem exists_walk_of_reflTransGen_lt {r : V → V → Prop} {S : Set V}
    (hSfin : S.Finite) (hadj : ∀ a b, r a b → a = b ∨ G.Adj a b)
    (hmem : ∀ a b, r a b → a ∈ S ∧ b ∈ S)
    {a b : V} (ha : a ∈ S) (h : Relation.ReflTransGen r a b) :
    ∃ w : G.Walk a b, (∀ v ∈ w.support, v ∈ S) ∧ w.length < S.ncard := by
  classical
  obtain ⟨w, hw⟩ := exists_walk_of_reflTransGen hadj hmem ha h
  exact exists_walk_length_lt hSfin hw

/-! ## Instantiation for the graph `G` -/

section Lattice

variable {d : ℕ}

/-- The lattice-point count, for open balls and in `ncard` form. -/
lemma ncard_lattice_inter_ball_le (a : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (ball a R ∩ lattice d).ncard ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
  have hfin : (ball a R ∩ lattice d).Finite :=
    (lattice_inter_closedBall_finite a R).subset
      (fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩)
  have hsub : ball a R ∩ lattice d ⊆ lattice d ∩ closedBall a R :=
    fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
  have hle : (ball a R ∩ lattice d).encard ≤ (((2 * ⌈R⌉₊ + 1) ^ d : ℕ) : ℕ∞) :=
    le_trans (Set.encard_mono hsub) (encard_lattice_inter_closedBall_le a R)
  rw [← hfin.cast_ncard_eq] at hle
  exact_mod_cast hle

end Lattice

/-! ## Step 1 of Theorem 5.15: one walk through all the blocks of a ball -/

section Step1

variable {d : ℕ}

lemma ncard_lattice_inter_closedBall_le' (a : EuclideanSpace ℝ (Fin d)) (M : ℝ) :
    (lattice d ∩ closedBall a M).ncard ≤ (2 * ⌈M⌉₊ + 1) ^ d := by
  have hfin := lattice_inter_closedBall_finite a M
  have hle := encard_lattice_inter_closedBall_le a M
  rw [← hfin.cast_ncard_eq] at hle
  exact_mod_cast hle

lemma townBall_eq_image (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    townBall h ℓ z R = (fun p => townIndex h ℓ p) '' (lattice d ∩ ball z R) := by
  have hset : {p : EuclideanSpace ℝ (Fin d) | p ∈ lattice d ∧ ‖p - z‖ < R}
      = lattice d ∩ ball z R := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_ball, dist_eq_norm]
  rw [townBall, hset]

lemma townBall_finite (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (townBall h ℓ z R).Finite := by
  rw [townBall_eq_image]
  exact Set.Finite.image _ ((lattice_inter_closedBall_finite z R).subset
    (fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩))

lemma ncard_townBall_le (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    (townBall h ℓ z R).ncard ≤ (2 * ⌈R⌉₊ + 1) ^ d := by
  have hfin : (lattice d ∩ ball z R).Finite :=
    (lattice_inter_closedBall_finite z R).subset
      (fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩)
  rw [townBall_eq_image]
  refine le_trans (Set.ncard_image_le hfin) (le_trans (Set.ncard_le_ncard ?_
    (lattice_inter_closedBall_finite z R)) (ncard_lattice_inter_closedBall_le' z R))
  exact fun p hp => ⟨hp.1, ball_subset_closedBall hp.2⟩

lemma townBall_mono (h ℓ : ℝ) (z : EuclideanSpace ℝ (Fin d)) {R R' : ℝ} (hRR : R ≤ R') :
    townBall h ℓ z R ⊆ townBall h ℓ z R' := by
  rintro _ ⟨p, ⟨hplat, hpR⟩, rfl⟩
  exact ⟨p, ⟨hplat, lt_of_lt_of_le hpR hRR⟩, rfl⟩

end Step1

end QFS
