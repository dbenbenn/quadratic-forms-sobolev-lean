# quadratic-forms-sobolev-lean

A Lean 4 / Mathlib formalization of

> Kai-Uwe Bux, Moritz Kassmann and Tim Schulze,
> *Quadratic forms and Sobolev spaces of fractional order*,
> Proc. London Math. Soc. 119 (2019) 841–866,
> [doi:10.1112/plms.12246](https://doi.org/10.1112/plms.12246)
> ([arXiv:1707.09277](https://arxiv.org/abs/1707.09277v1)).

Result, page and equation numbers refer to arXiv:1707.09277v1 (see *Citations*).

## What is proved

The paper studies quadratic forms on `L²(ℝ^d)` in which a difference `f(y) − f(x)` counts only
when `y` lies in a double cone `V^Γ[x]` with apex `x`, the cones varying from point to point with
no regularity at all. Its main result, **Theorem 1.1**, says that such a form is nevertheless
comparable, on every ball, to the Gagliardo seminorm of `H^{α/2}`:

    ∫_{B×B} (f(x) − f(y))² |x − y|^{−d−α} ≤ c ∫_{B×B} (f(x) − f(y))² k(x, y),

with `c` depending only on `d`, `ϑ`, `Λ` and, for `α ∈ [α₀, 2)`, on `α₀`.

**Theorem 1.1 is proved here in full**, including the uniformity in `α`. So are:
- the discrete comparability **Theorem 1.3**;
- **Theorem 1.4 on `ℝ^d`**, including the density of `C_c^∞(ℝ^d)`;
- **Theorem 1.4 on bounded Lipschitz domains**, including the density of `C^∞(Ω̄)`;
- **Lemma A.1 on bounded Lipschitz domains**, with its scaling and `α₀` clauses;
- every numbered result of Sections 2–5 and of the appendix that the proofs rest on.

Start with **[`QuadraticFormsSobolev/Paper.lean`](QuadraticFormsSobolev/Paper.lean)**. It states
every result covered, in the paper's order, each proved by citing the development; its docstrings
say how each statement relates to the paper's sentence. It has 52 theorems, no `sorry`, and each
depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The gap in §3.2, and how it is closed

The paper derives Theorem 1.1 from Theorem 1.3 by discretization: §3.2 applies Theorem 1.3 on
`hℤ^d` and lets `h → 0`. The limit is taken with dominated convergence, and the dominating function
is integrable only if `f ∈ H^{α/2}` of a larger ball, which is what is being proved. The step then
from the enlarged ball to the ball itself (Lemma A.1) rests on a Whitney decomposition and on
Dyda's inequality (13), both quoted.

This formalization closes the argument by a different route.

1. **Random lattice sampling** (`RandomLattice/`). `f` is sampled on random affine lattices
   `h·A_Q(ℤ^d + η)`, with a random shift `η` and a small random distortion `Q`. Theorem 1.3 is
   applied on each lattice, and the lattice sums are averaged. The average reproduces the two double
   integrals up to constants, and no a priori finiteness is needed. This gives §3.2's conclusion
   (`section_3_2`) and Theorem 1.4 on `ℝ^d`. The gap and this repair are written up in the note
   [`paper/gap-note.pdf`](paper/gap-note.pdf), whose headline results are stated exactly in
   [`QuadraticFormsSobolev/GapNote.lean`](QuadraticFormsSobolev/GapNote.lean).
2. **Dyda's inequality (13)** is proved for the unit ball (`dyda_13`, `Dyda/`). Step 1 follows
   Dyda's proof. Step 2, Dyda's case (c), uses a pulled-in midpoint instead. It then moves to every
   ball by scaling (`dyda_13_ball`). It is also proved on every bounded Lipschitz domain
   (`dyda_13_lipschitz`):
   - Step 1 runs along chains toward admissible tips, which are either interior or in the interior
     cone of a boundary chart.
   - Step 2 averages each near pair over a ball of such points.
   - Dyda's case (c) becomes a Poincaré inequality obtained by chaining through a finite cover.
3. **No Whitney decomposition.** On any open set, an average over small balls bounds the regional
   form by the kernel's form (`regional_le_form`). With Dyda's inequality this gives Lemma A.1 for
   balls (`lemma_A_1`), and with it Theorem 1.1. On bounded Lipschitz domains it gives Lemma A.1
   in full (`lemma_A_1_lipschitz`) and the domain half of Theorem 1.4 (`theorem_1_4_domain`).

The constants are chosen before `α`, so the uniformity for `α ∈ [α₀, 2)` comes out directly.

## Where the paper is wrong as printed

- **Lemma 3.3 fails in dimension one** (`lemma_3_3_false_dim_one`). It is proved for `d ≥ 2`
  (`lemma_3_3`).
- **Lemma 3.4 is false as printed** (`lemma_3_4_false_as_printed`). The form the proof uses, on
  `hℤ^d`, is `lemma_3_4`.
- **Lemma 5.9's threshold is too small** (`lemma_5_9_threshold_too_small`). `lemma_5_9` uses
  `(√d + 1)/sin(ϑ/2)` instead.

Smaller slips, and hypotheses the paper leaves implicit, are listed under *Deviations*.

## Scope

- **Not formalized:**
  - Corollary 1.5, which needs Dirichlet-form theory;
  - Corollary 1.6, which the paper quotes from Dyda and Kassmann.
- **Density in Theorem 1.4** is density in the norm of `H_k`, stated with an explicit `ε`. On a
  domain, `C^∞(Ω̄)` is read as the restrictions to `Ω` of smooth compactly supported functions on
  `ℝ^d`.
- **Bounded Lipschitz domains.** The paper uses the term without defining it. The definition is
  Dyda's (§3, p. 568), in `LipschitzDomain.lean` (`QFS.IsBoundedLipschitzDomain`): a bounded,
  connected open set that, near each boundary point, is the region above the graph of a Lipschitz
  function in some direction. Every ball is one (`QFS.isBoundedLipschitzDomain_ball`).
- **Lemma A.1 for bounded Lipschitz domains** is proved unconditionally (`lemma_A_1_lipschitz`).
  One constant serves every dilate of the domain and every `α ∈ [α₀, 2)`. The earlier conditional
  forms, which take the Whitney decomposition and Dyda's inequality on the domain as hypotheses
  (as the paper quotes them), remain as `lemma_A_1_domain`, `lemma_A_1_scaling` and
  `lemma_A_1_alpha_uniform`; they assume only that the domain is measurable.
- **Proposition 3.5 and Corollary 3.6** assume measurability of `{x : V ⊆ Γ(x)}` for every `V`
  in place of condition (M); the paper obtains it from (M) by quoting Debreu. They hold in every
  dimension: the paper's proof needs `d ≥ 2`, since Lemma 3.3 fails for `d = 1`, and `d = 1` is
  proved directly (`DimOne`). The proof of Theorem 1.1 here does not use them.

## The results, one by one

| Result | `Paper.lean` |
| --- | --- |
| **Section 1** | |
| Theorem 1.1 — comparability on every ball | `theorem_1_1` |
| Theorem 1.3 — the discrete comparability | `theorem_1_3` |
| Theorem 1.4 — $H_k = H^{\alpha/2}$ on $\mathbb{R}^d$ | `theorem_1_4` |
| Theorem 1.4 — $H_k(\Omega) = H^{\alpha/2}(\Omega)$ on a bounded Lipschitz domain | `theorem_1_4_domain` |
| Theorem 1.4 — $C_c^\infty(\mathbb{R}^d)$ is dense in $H_k(\mathbb{R}^d)$ | `theorem_1_4_density_univ` |
| Theorem 1.4 — $C^\infty(\overline\Omega)$ is dense in $H_k(\Omega)$ on a bounded Lipschitz domain | `theorem_1_4_density_domain` |
| Equation (5) — the fractional Sobolev space sits inside the kernel space | `equation_5` |
| **Section 2** | |
| Lemma 2.2 — finitely many reference cones | `lemma_2_2` |
| Corollary 2.4 — Reduction of a bounded configuration to a finite family of reference cones | `corollary_2_4` |
| Lemma 2.7 — Nested shifted shrinkings of a set across a cube | `lemma_2_7` |
| **Section 3** | |
| Corollary 3.1 — the discrete result at every lattice spacing | `corollary_3_1` |
| Lemma 3.2 for arbitrary sets and the full unit cubes | `lemma_3_2` |
| Lemma 3.2 — the indicator inequality at favoured indices | `lemma_3_2_as_printed` |
| Lemma 3.3 (d ≥ 2) — Existence of a thin lattice cone inside a shrunken reference cone in dimension at least two | `lemma_3_3` |
| Lemma 3.3 fails for d = 1 — Lemma 3.3 is false in dimension one | `lemma_3_3_false_dim_one` |
| Lemma 3.4 — Two-sided comparison of distances between points of well-separated lattice cubes | `lemma_3_4` |
| Lemma 3.4 is false as printed — The literal statement of Lemma 3.4 is false | `lemma_3_4_false_as_printed` |
| Proposition 3.5 — the discretised kernel dominates a cone kernel | `proposition_3_5` |
| Corollary 3.6 — the discretised kernel, two-sided and uniform in the spacing | `corollary_3_6` |
| §3.2 — the limiting argument, enlarged-ball form | `section_3_2` |
| **Section 4** | |
| Theorem 4.1 — connectivity in the continuum | `theorem_4_1` |
| Lemma 4.3 as a connectivity statement | `lemma_4_3` |
| Lemma 4.5 (1) — points of a cone are well-connected | `lemma_4_5_1` |
| Lemma 4.5 (2) — well-connectedness passes to a larger set | `lemma_4_5_2` |
| Lemma 4.5 (3) — every nonempty open set has a well-connected point | `lemma_4_5_3` |
| Lemma 4.5 (3) — the well-connected points are dense | `lemma_4_5_3_dense` |
| Lemma 4.6 — “über Bande” | `lemma_4_6` |
| **Section 5** | |
| Lemma 5.1 (1) — A lattice point deep inside a cone, at controlled distance from the apex | `lemma_5_1_1` |
| Lemma 5.1 (2) — a lattice point in the intersection of two nearby cones | `lemma_5_1_2` |
| Corollary 5.2 as connectivity within a ball | `corollary_5_2` |
| Lemma 5.4 — discrete density of well-connected lattice points | `lemma_5_4` |
| Lemma 5.5 — Connecting two lattice points via a third of the same cone type | `lemma_5_5` |
| Lemma 5.6 — bounded jumps toward the tip of a cone | `lemma_5_6` |
| Lemma 5.6 in full — the descent chain to a point of minimum distance | `lemma_5_6_chain` |
| Lemma 5.7 — the core induction on cone types | `lemma_5_7` |
| Corollary 5.8 — Uniform outer radius for lattice connectivity of bounded configurations | `corollary_5_8` |
| Lemma 5.9 — A cube at the shrunk aperture is seen in the full cone from an entire cube | `lemma_5_9` |
| Lemma 5.9's threshold in the source is too small, for every apex angle | `lemma_5_9_threshold_too_small` |
| Proposition 5.14 — connectivity in the favored graph of a sparsely populated town | `proposition_5_14` |
| Theorem 5.15 — the path properties | `theorem_5_15` |
| Theorem 5.15 — the path properties, with only the lower bound on the apex angles | `theorem_5_15_as_printed` |
| Lemma 5.16 — The first jump: connecting an arbitrary point to a block at each scale | `lemma_5_16` |
| **Appendix A** | |
| Lemma A.1 for balls — the enlarged-ball bound gives the same-ball bound | `lemma_A_1` |
| Lemma A.1 — bounded Lipschitz domains, with the scaling and $\alpha_0$ clauses | `lemma_A_1_lipschitz` |
| Lemma A.1 — the domain conclusion, the ball clause, and the scaling remark | `lemma_A_1_domain` |
| Lemma A.1's constant depends on the domain only up to scaling | `lemma_A_1_scaling` |
| Lemma A.1's constant depends on α only through a lower bound α₀ | `lemma_A_1_alpha_uniform` |
| Lemma A.2 — differentiation along shrinking cubes | `lemma_A_2` |
| **Cited, and beyond the paper** | |
| Dyda 2006, (13), p. 572 — on the unit ball the $H^{\alpha/2}$ seminorm is bounded by the regional form | `dyda_13` |
| Dyda 2006, (13), p. 572 — on a bounded Lipschitz domain, uniformly in $\alpha \in [\alpha_0, 2)$ | `dyda_13_lipschitz` |
| Beyond the paper — Dyda's inequality (13) on every ball | `dyda_13_ball` |
| Beyond the paper — the regional form is bounded by the $H_k$ form | `regional_le_form` |

## Deviations

Each departure from the paper, and why.

1. **Lemma 2.7 is proved for an arbitrary set.** The paper states it for "a cone
   `V` with apex angle `ϑ`", but the proof it gives — equations (⋆) and (✝) —
   never uses that `V` is a cone, only that it is a subset of `ℝ^d`. The Lean
   proof follows the paper's argument verbatim; the statement it proves is
   therefore about an arbitrary `V : Set (EuclideanSpace ℝ (Fin d))`. The
   paper's own reading is the special case where `V` is a double cone.

2. **Corollary 2.4: the apex angle of `Γ̃` is `ϑ/3`, not `ϑ`.** The corollary's
   last sentence reads "The minimum of apex angles of cones in `Γ̃(ℝ^d)` is
   `ϑ`". But `Γ̃` is built from the reference cones of Lemma 2.2, whose apex
   angle is `θ = ϑ/3`. `QFS.ref_config` proves `(Γ' x).apex = ϑ/3`, so `Γ'` is
   `(ϑ/3)`-bounded (`corollary_2_4`). This is a slip in the paper with no consequences: every
   later use of Corollary 2.4 needs only that the angle is positive and depends
   on `d` and `ϑ` alone.

3. **Corollary 2.4: the sets `M_i` in the paper's proof.** The displayed
   definition ends with `M_L = {x | V^L ⊆ Γ(x)} \ M_{L-1}`, which does not make
   the union `⋃ M_i` disjoint (it should subtract `M_1 ∪ ⋯ ∪ M_{L-1}`). The Lean
   proof takes the equivalent and cleaner route of choosing, for each `x`, some
   index with `V^m ⊆ Γ(x)`; the paper's `M_i` are exactly the fibres of that
   choice.

4. **Lemma 3.4 is stated with `ℤ^d` but proved for `hℤ^d` — the literal
   statement is false.** The lemma reads "For every `h > 0`, all `x, y ∈ ℤ^d`
   with `|x − y| > √d·h` …". Its proof, however, treats the case `h = 1` and
   closes with "The general case for arbitrary `h > 0` follows by scaling" —
   and scaling `ℤ^d` by `h` produces `hℤ^d`, not `ℤ^d`. With `x, y` ranging
   over `ℤ^d` for arbitrary `h` the lower bound genuinely fails:

   > `d = 1`, `h = 3/2`, `x = 0`, `y = 2`, `s = 7/10`, `t = 13/10`.
   > Then `|x − y| = 2 > 3/2 = √d·h`, `s ∈ A_h(x)` and `t ∈ A_h(y)` (both
   > coordinates are within `h/2 = 3/4` of their centres), yet
   > `|s − t| = 3/5` while `(2√d)⁻¹|x − y| = 1`.

   `QFS.lemma_cubes_literal_false` is a Lean proof of exactly this. The
   corrected statement — `x, y ∈ hℤ^d`, which is what the paper's own scaling
   argument yields and what the applications (Proposition 3.5 with `h = 1`,
   Corollary 3.6 on `hℤ^d`) actually use — is `QFS.lemma_cubes`.

5. **Lemma 3.2 needs neither the lattice nor the favouring.** The lemma is
   stated for `x, y ∈ ℤ^d` and `1`-favoured indices `m` at `x`, `n` at `y`, with
   `s ∈ A_1^m(x)` and `t ∈ A_1^n(y)`. Its proof uses only `s ∈ A_1(x)` and
   `t ∈ A_1(y)`. `QFS.lemma_min_dist` proves that (more general) statement;
   `QFS.lemma_min_dist_favoured` is the paper's exact form, deduced from it.

6. **Lemma 3.3 is false in dimension one**, at the radius `r = √d` at which
   Proposition 3.5 applies it. The paper introduces it with "The assertion of
   the following lemma is obviously true". In `d = 1` every double cone
   `V(v, θ)` with `θ ∈ (0, π/2]` is all of `ℝ \ {0}`, so
   `V(v, θ) ∩ ℤ = ℤ \ {0}`, whereas `V^m_r ∩ ℤ = {n ∈ ℤ : |n| > r}` omits `±1`
   once `r ≥ 1`. Since `√d = 1` when `d = 1`, no `θ` and no axis `v` can give
   `V(v,θ) ∩ ℤ ⊆ V^m_{√d} ∩ ℤ`. `QFS.lemma_new_config_false_dim_one` is a Lean
   proof of this, for every `θ ∈ (0, π/2]`, every unit axis `v`, and every
   reference cone.

   This is a defect in the statement, not in the paper's results: for `d = 1`
   there is only one double cone, so `V^Γ[x] = ℝ \ {x}` and Theorems 1.1 and
   1.3 hold trivially.

   **For `d ≥ 2` the lemma is true, and it is proved here** — but not obviously,
   and the argument is not in the paper. `QFS.exists_thin_cone_subset` is the
   single-cone version and `QFS.lemma_new_config` the paper's form, with one
   apex angle for the whole family. The construction:

   * `V^m_r` omits every point within `r` of the boundary of `V^m`, in
     particular every point of norm at most `r/sin θ_m`. Only finitely many
     lattice points are that short (`QFS.lattice_inter_closedBall_finite`), so
     the axis must avoid their directions.
   * `QFS.exists_orthogonal_unit` produces a unit vector orthogonal to the axis.
     **This is the only place `d ≥ 2` is used**, and it is exactly what fails in
     `d = 1`: with no orthogonal direction the cone cannot be made thin.
   * `QFS.rotAxis u w t = cos t · u + sin t · w` rotates the axis inside the
     cone, with `angle u (rotAxis u w t) = t` (`QFS.angle_rotAxis`). Each short
     lattice point is parallel to at most one rotation, because a rotation is
     determined by its angle to `u`; an interval of rotations is infinite
     (`Set.Ioo_infinite`) while the short lattice points are finite, so some
     rotation avoids all of them.
   * The apex angle is then taken below the least of the resulting angles. A
     lattice point of the resulting thin cone is therefore *long* — longer than
     `r/sin(ϑ/4)` — and *nearly parallel* to `u`, and
     `QFS.coneGap_eq_norm_mul_sin` turns that into a gap of more than `r` to the
     boundary of `V^m`, which is membership in `V^m_r`
     (`QFS.closedBall_subset_cone`).

7. **Lemma 4.6 needs `z ∈ U`, which the paper does not state.** The lemma reads
   "Assume that the translated double cone `V[x]` contains a point `z` of type
   `V`. Then `x` and `y` are connected." The proof uses the edge from `z` to
   `x`, which exists in `G[U]` only if `z ∈ U`. `QFS.ueber_bande` therefore
   takes `z ∈ U` as a hypothesis. This costs nothing: Theorem 4.1 applies the
   lemma to a point of `U ∩ V[x]`. (Conversely, the hypothesis `x ∈ U` that the
   paper does state is not needed; it is kept for fidelity.)

8. **Theorem 4.1: the induction is run on a different open set.** The paper's
   induction is on the number of cone types realised in `U`, and in the
   inductive step it applies the inductive hypothesis to

   > `U' = U ∩ V[x]`, concluding "all points in `U'` are mutually connected in
   > `G[U']`".

   But `V[x]` is a *double* cone — the disjoint union of two open half-cones —
   so `U'` is in general not connected, while the inductive hypothesis is
   Theorem 4.1, a statement about *connected* open sets. As stated the step does
   not go through.

   The formalisation repairs this by running the induction on

   > `U'' = B_r(x) ∩ Ṽ[x]`, with the *half*-cone `Ṽ`,

   which does everything the argument needs and is connected:

   - `U''` is convex, hence preconnected (`QFS.convex_cone` shows a cone of apex
     angle at most `π/2` is convex — the "ice cream cone");
   - `U'' ⊆ U ∩ V[x]`, so the cone type `V` is still not realised in `U''` and
     the induction still descends (`Set.ncard_lt_ncard`);
   - the point supplied by the `λ`-observation is `x + (r/2)·v`, which lies in
     the *half*-cone, hence in `U''` (this is why
     `QFS.exists_mem_ball_inter_shift` is stated with `cone` rather than
     `doubleCone`; `QFS.exists_mem_ball_inter_shift'` is the paper's weaker
     form);
   - `U''` contains the points `x + t·v` for all small `t > 0`, hence points
     arbitrarily close to `x`, which is what the appeal to well-connectedness of
     `x` needs.

   The paper's closing sentence — "density of well-connected points implies that
   `U` is covered by overlapping open well-connected subsets" — is made precise
   as `QFS.conn_of_wellConnected_of_isPreconnected`: once every point of `U` is
   well-connected the connectivity classes are open, so a preconnected `U` is a
   single class.

9. **Lemma 5.6 is not obvious.** The paper introduces it with "The assertion of
   the following lemma is obvious." The natural first attempt — step from `x`
   radially inward toward the tip — fails: scaling does not change the *angle*
   to the cone axis, so a lattice point close to the boundary of the cone stays
   close to it, and no ball of radius `√d/2` fits, so no lattice point is
   produced. The proof formalised here steps radially inward by a fixed amount
   *and* along the cone axis; the second move raises the distance to the cone
   boundary by exactly `a sin ϑ` (`QFS.coneGap_add_smul_axis`), which is what
   makes room for a lattice point.

   This motivated the auxiliary notion `QFS.coneGap v ϑ p = ⟪v,p⟫ sin ϑ −
   ‖p − ⟪v,p⟫v‖ cos ϑ`, the signed distance from `p` to the cone boundary. It is
   positive exactly on the cone, `1`-Lipschitz, and positively homogeneous, and
   `QFS.closedBall_subset_cone` subsumes the earlier
   `QFS.mem_cone_of_norm_sub_lt` (which is the case `p = t·v`, where the gap is
   `t sin ϑ`).

10. **Lemma 5.7's monotonicity clause is proved separately — and is not what is
    needed.** The lemma asserts `r_i < r_{i+1}`, `ρ_i < ρ_{i+1}`, `R_i < R_{i+1}`
    and `δ < r_1`. The induction (`QFS.core_induction`) gives each `k` its own
    `r_k ≤ ρ_k ≤ R_k` with `δ < r_k`, which is all the proof of Lemma 5.7 itself
    uses — the monotonicity is never invoked there, and with `δ < r_k` for every
    `k` it is not needed to carry the invariant. Lemma 5.7 as printed, monotonicity
    included and with Lemma 5.6's `δ`, is `lemma_5_7` in `Paper.lean`: the
    constants of the induction are re-indexed along a fast-growing subsequence.

    Corollary 5.8 is the natural consumer, and it turns out monotonicity would
    not suffice there either: reaching an arbitrary `r` needs the radii to be
    *unbounded*, which strict monotonicity alone does not give. What Corollary
    5.8 actually needs is the growth bound `k ≤ r_k`, and that is recorded by
    `QFS.core_induction` and falls out of the construction
    (`r_{k+1} > ρ_k + 1 ≥ r_k + 1`).

11. **Lemma 5.9's constant is too small, and its intermediate estimate fails for
    every admissible apex angle.** The proof passes through

    > if `y ∈ Ṽ[x]` and `|x − y| ≥ ℓ√d/(2 sin ϑ)`, then `B_{ℓ√d/2}(y) ⊆ V̄[x]`,

    and concludes with `δ = 3√d/(2 sin ϑ)`. By `QFS.coneGap_eq_norm_mul_sin` the
    distance from `y` to the boundary of `V̄[x]` is exactly
    `‖y − x‖ sin(ϑ − ∠(v, y−x))`, and `y ∈ Ṽ[x]` bounds `∠(v, y−x)` only by
    `ϑ/2` — not by `0`. At the paper's threshold distance the guaranteed gap is
    therefore only

    > `ℓ√d sin(ϑ/2) / (2 sin ϑ) = ℓ√d / (4 cos(ϑ/2))`,

    which is less than the required `ℓ√d/2` precisely when `cos(ϑ/2) > 1/2`,
    i.e. for every `ϑ ≤ π/2`. `QFS.paper_threshold_insufficient` is a Lean proof
    of this. The same slip costs the final constant: `3√d/(2 sin ϑ)` is at least
    the necessary `√d/sin(ϑ/2)` only when `cos(ϑ/2) ≤ 3/4`, i.e. for
    `ϑ ≳ 82.8°`. Since `ϑ` is an infimum of apex angles and may be arbitrarily
    small, this is not a harmless slack.

    `QFS.renormalization_apex_shrink` proves the lemma with
    `δ = (√d + 1)/sin(ϑ/2)`, which is the sharp `√d/sin(ϑ/2)` plus enough to make
    the inequalities strict. Nothing downstream needs the particular value.

12. **Section 5.2 uses closed cubes, Definition 2.5 open ones.** The paper
    "recalls" the cube notation as `A_ℓ(x) = {y : ‖y−x‖_∞ ≤ ℓ/2}`, but
    Definition 2.5 defines `A_h(u)` with a strict inequality. `QFS.cube` and
    `QFS.closedCube` are both provided; Lemma 5.9 is proved for the closed cube,
    as Section 5.2 states it, which is the stronger reading.

13. **Step 2's assignment `φ_z` is too weak for Step 6, and the paper's own
    scheme repairs it.** This is the one substantive gap found in Section 5.

    Step 2 asks only that `φ_z : A → M` be *globally* balanced,
    `#φ_z⁻¹(p) ≤ K`, and Step 6 then asserts that "the usage of paths that start
    in some point `x` and end in some other point `y` … is bounded by `K`". That
    does not follow. Consider the **first-jump edge** `{x, q}`, where `q` is the
    vertex of `φ_z(x, y)` lying in `x`'s own block. It is used by every partner
    `y` of `x` whose assigned walk carries `q`'s index at `x`'s position along
    the block walk. The walks with a fixed index at a fixed position number `a`,
    so their total capacity under a merely balanced `φ_z` is `K a`, which is
    larger than the `≍ Δ^{nd}` partners `x` has. An adversarial balanced `φ_z`
    may therefore route all of them through the single edge `{x, q}`, and its
    multiplicity is unbounded in the scale. Claim (3) fails for that `φ_z`.

    The repair stays inside the paper's scheme and only *fixes its parameters*.
    Take two maps `f, g` of the ball to `ZMod a`, each with fibres of size at
    most `K₁` (`QFS.exists_hash`), and set

    > `i = f(y) + g(x)` and `i + j = g(x)`,

    so that the scheme's alternating labels are `α = f(y) + g(x)` at odd
    positions and `β = g(x)` at even ones. Then

    * every consecutive pair `{α, β}` determines `g(x) = β` and
      `f(y) = α − β`, so an interior edge is used by at most `K₁²` pairs;
    * at `x`'s end the label is a translate of `f`, hence balanced in `y` for
      fixed `x`, bounding the first-jump edge at `x` by `K₁`;
    * at `y`'s end the label is `α` or `β`, and *both* are translates of `g`,
      hence balanced in `x` for fixed `y`, bounding the first-jump edge at `y` —
      **whatever the parity** of the block walk's length.

    The last point is why `α` must carry both hashes. With the more obvious
    choice `α = f(y)`, `β = g(x)` an even-length block walk ends on `α`, which
    is constant in `x`, and the multiplicity at `y`'s end is again unbounded.
    Since the choice-graph may be bipartite, one cannot arrange the parity away.

    `QFS.encard_reveals_le` is the resulting count: whichever of the three
    shapes an edge has, it confines `g(x)` to eight values and `f(y)` to nine,
    all computed from the edge alone, so at most `72 K₁²` pairs used it.

    A second, purely simplifying consequence: once the scheme's parameters are
    functions of `x` and `y` alone, the walk for a pair need not be a sub-walk
    of one *global* covering walk, so Step 1 is used only in its pairwise form
    (Proposition 5.14 plus `QFS.exists_choiceWalk_of_choiceConn`).

14. **Section 6's chaining needs edges longer than `R₀`, and claim (4) does not
    give it.** The computation displayed in Section 6 applies the *lower* bound
    of assumption (4) at each edge `{z_i, z_{i+1}}` of `p_xy`, to replace
    `|z_{i+1} − z_i|^{-d-α}` by `Λ ω(z_i, z_{i+1})`. That bound is only assumed
    for `|x − y| > R₀`. But claim (4) of Theorem 5.15 bounds an edge below only
    by `λ^{-1}|x − y|`, and `λ ≥ R₀`, so for a pair with `|x − y|` just above
    `R₀` the guaranteed edge length is about `R₀/λ ≤ 1` — well short of `R₀`.
    Restricting to pairs with `|x − y| > λR₀` does not help either: the pairs
    with `R₀ < |x − y| ≤ λR₀` still need chains, and `ω(x, y)` may vanish for
    them, since the indicator in (4) is `0` unless one point lies in the
    other's cone.

    The repair is in the construction, not in the estimate. Theorem 5.15 routes
    a pair at the scale `n` with `|x − y| ∈ [Δ^{n-1}, Δ^n)`, and at the bottom
    scale `n = 1` the town is `T(Δ, 1)`, whose edges can be as short as `1`.
    Routing **one scale up** — the admissible window becomes `[Δ^{m-1}, Δ^m)`
    with `m ≥ 1`, which is `QFS.Admissible` — makes every edge at least
    `Δ^m ≥ Δ` long, and `Δ > R₀` by `QFS.ScaleStep`. The cost is a factor `Δ` in
    `λ`, which becomes `2Δ²R`.

    `QFS.PathPropsLong` is Theorem 5.15 with the extra clause `R₀ < |edge|`, and
    `QFS.path_props_long` proves it; `QFS.PathPropsLong.toPathProps` forgets the
    clause, so `QFS.path_props_of_pos` still records exactly the paper's statement.

15. **The `λ`-observation in the proof of Theorem 4.1 is false as printed.** The
    proof opens the case `#Γ(U) > 1` with

    > There is a constant `λ > 0` depending only on the minimum apex angle `ϑ`
    > such that for **any double cone `V ∈ 𝒱`** and any two points `x, y ∈ ℝ^d`
    > of distance `|x − y| < λ`, the intersection `V[x] ∩ V[y]` contains a point
    > in `B_1(x)`.

    But `𝒱 = (0, π/2] × ℙ^{d-1}` contains cones of arbitrarily small apex, and
    for a cone of apex `ε` the points of `V[x] ∩ V[y]` are at distance about
    `|x − y| / (2 sin ε)` from `x`. With `λ` fixed in advance by `ϑ`, no such
    `λ` works for all `V ∈ 𝒱`. The observation is only ever *applied* to
    `V = Γ(y)`, whose apex is at least `ϑ`, so the repair is to say so:
    `QFS.exists_mem_ball_inter_shift` carries `ϑ ≤ V.apex`, and with it the
    paper's constant `λ = (sin ϑ)/2` is correct.

16. **Four smaller slips in printed statements, each repaired silently.**

    * **Definition 2.3** writes `V^m_r = {u ∈ V^m | B̄_r ⊂ V^m}` — the ball has
      no centre, so read literally `V^m_r` is `V^m` or `∅`. Definition 2.1
      writes the same condition correctly as `B̄_r(y) ⊂ V`.
      `QFS.RefFamily.shrunk` uses the centred version.
    * **Lemma 5.9** says "there is a constant `δ = δ(ϑ)`", but its own value
      `3√d/(2 sin ϑ)` depends on `d` as well. `QFS.apexShrinkConst d ϑ` takes
      both, as it must.
    * **Proposition 5.14** says "there exists `R ≥ r` depending only on `ϑ` and
      `d`", but `R ≥ r` cannot be independent of `r`. `QFS.renormalization`
      takes `r` first, as Corollary 5.8 correctly states.
    * **Corollary 5.2** prints `R = (r + √d)/sin ϑ`, which is the radius of
      Lemma 5.1 **(1)**. A two-edge path needs Lemma 5.1 **(2)**, whose own
      hypothesis is `R > (r + √d)/sin ϑ + r`: the extra `r` is what translating
      the cone from `x` to `y` costs, and 5.1(1) alone does not put its lattice
      point in the second cone. `QFS.discr_connect_two_of_same_type_two` uses
      the larger radius. The corollary may still be true as printed by a sharper
      argument; what fails is that the stated constant follows from the input the
      paper cites.

    One more note, not a defect: `QFS.RefFamily` does not constrain its apex
    angle `θ` to `(0, π/2]`, which only weakens the hypothesis of everything
    proved from it.

17. **Two further notes on hypotheses, neither a defect.** Theorem 1.3's
    dependency sentence — "the constant `c` depends on `Λ`, `ϑ`, `R₀` and on the
    dimension `d`" — omits `α`, and rightly: the proof produces `λ^{d+α}`, which is
    at most `λ^{d+2}` because `λ ≥ 1` and `α < 2`. So `κ` and `c` can be chosen
    before `α`, and `theorem_1_3` does so. And Proposition 3.5 assumes `k`
    measurable; `QFS.KernelBounds` does not, because the argument runs entirely
    through the lower Lebesgue integral and never needs it — a weaker hypothesis,
    hence a stronger result. That omission does bite once, and only once:
    `QFS.formHs_le_form_of_ballComparability` carries measurability of the
    integrand as an explicit hypothesis, because summing the forms over a Whitney
    family goes through `lintegral_tsum`, which needs it.

18. **Lemma A.1's overlap constant can be `M`, not `M²`.** Display (18) bounds
    `∑_{B∈ℬ} ∫_{B*×B*} … ≤ M² ∫_{Ω×Ω} …` from the finite-overlap property
    "each point of `Ω` belongs to at most `M` balls `B*`". One factor suffices: a
    pair `(x,y)` lies in `B* × B*` only for those `B` with `x ∈ B*`, of which
    there are at most `M`. `QFS.tsum_setLIntegral_le_of_overlap` proves the sharper
    form. Nothing
    downstream depends on the difference.

19. **Where the constant sits.** The paper puts the comparability constant
    sometimes on the left (`c Σ ≤ Σ` in Corollary 3.1 and in Lemma A.1's chain)
    and sometimes on the right (`∫ ≤ c ∫` in Theorems 1.1 and 1.3). Each Lean
    statement follows the orientation of the result it is used with, so
    `corollary_3_1` is stated as `Σ ≤ c Σ` — the same assertion with `c`
    replaced by `c⁻¹` — to match Theorem 1.3, while Lemma A.1 keeps the constant
    on the left, as (18) has it.

20. **The norms of `H_k(Ω)` and `H^{α/2}(Ω)` (p. 4).** The paper defines the
    seminorm as the integral itself, `|f|_{H_k(Ω)} = ∫_{Ω×Ω} (f(y) − f(x))² k`,
    with no square root, and then the norm by
    `‖f‖²_{H_k(Ω)} = ‖f‖²_{L²(Ω)} + |f|²_{H_k(Ω)}`, and the same for `H^{α/2}(Ω)`.
    Read literally, the integral is squared a second time. That is not a norm (it
    is not homogeneous), let alone the Hilbert norm the paper intends, so this is
    a slip. We read it in the standard way: `QFS.form Ω k f` is the integral, the
    paper's `|f|_{H_k(Ω)}` as printed. The squared norm is
    `‖f‖²_{L²(Ω)} + form Ω k f`, which is how the norm comparabilities of
    Theorem 1.4 are stated. The seminorm statements, including inequality (3) of
    Theorem 1.1, involve only the integral and read the same either way.

## Citations

Every reference to a numbered result or equation cites **arXiv:1707.09277v1**,
the only version on arXiv as of this writing. Two conventions in that paper are
easy to get wrong, and both were got wrong here until they were checked against
the typeset PDF:

**Results are numbered within sections; equations are not.** `\newtheorem` is
declared with `[section]`, so theorems, lemmas, corollaries, propositions,
definitions and remarks share one counter per section and print as `1.1`, `3.2`,
`5.15`. Equations take `amsart`'s default and run **flat through the whole
paper**, `(1)` to `(18)` — there is no equation `(1.4)` or `(6.14)`. The two
displays carrying `\tag{M}` print as `(M)` and consume no number.

The equations this formalisation refers to:

| Printed | Source label | What it is |
| --- | --- | --- |
| `(1)` | `eq:seminorm_Hs` | the `H^{α/2}` seminorm |
| `(M)` | `eq:mbc` | the measurability condition on `Γ` |
| `(2)` | `assum:main` | the bound on the kernel `k` |
| `(3)` | `eq:main-result` | the comparability asserted by Theorem 1.1 |
| `(4)` | `assum:main_discrete` | the bound on the discrete kernel `ω` |
| `(5)` | `eq:one-direction` | `H^{α/2}(Ω) ⊆ H_k(Ω)` |
| `(9)` | `eq:norms-on-R-n` | `‖v‖_∞ ≤ ‖v‖ ≤ √d ‖v‖_∞` |
| `(15)` | `discret` | the discrete inequality of §3.2 |
| `(18)` | `6.14` | the chain inside the appendix lemma |

**The auxiliary results are an appendix, not a section 7.** The paper ends with
`\appendix`, so its last section prints as **Appendix A** and its two lemmas as
**Lemma A.1** and **Lemma A.2**. The module is named `AppendixA` accordingly, and
holds only appendix material.

Two source labels are traps for anyone reading the `.tex` rather than the PDF.
The appendix chain is written `\begin{align}\label{6.14}` — a leftover from a
draft, since it prints as `(18)`. And three displays in §3 are labelled `1`, `2`
and `7`, which print as `(11)`, `(12)` and `(13)`. A label is not a number.

## Notation

The paper's letters are used throughout. Where the paper defines a symbol by a
semantic macro, the Lean name is given beside it.

| Paper | Lean | |
| --- | --- | --- |
| `Γ` | `Γ` | a configuration; `Γ'` where a second one is quantified over |
| `G` | — | the paper's **directed graph**; never used here for a configuration |
| `ϑ` | `ϑ` | the apex bound: `IsThetaBounded Γ ϑ` in the statements, `ApexLowerBound Γ ϑ` in the proofs |
| `α`, `Λ`, `c`, `κ`, `λ` | same | order, kernel constant, comparability constant, ball enlargement, factor |
| `k(x,y)` | `k` | the kernel of `(2)` |
| `ω(x,y)` | `ω` | the discrete kernel of `(4)` |
| `δ` | `δ` | the jump bound, `\JumpMax` |
| `r`, `ρ`, `R` | `r`, `ρ`, `R` | small radius, chromatic bound, large radius — the indexed families of Lemma 5.7 |
| `V`, `Ṽ`, `V_r` | `doubleCone`, `cone`, `shrink` | double cones, cones, the `r`-shrinking; `coneAt Γ x` is `V^Γ[x]` |
| `A` | `cube` | the cubes of Definition 2.5 |
| `Q`, `P` | `block` | blocks; `ℓ` is the block length in both |
| `U`, `W`, `U'` | `U` | open sets |
| `x`, `y`, `z` | same | points; `B_r(x)` is `ball x r`, `ℤ^d` is `lattice d` |
| `(M)` | `CondM` | the measurability condition on `Γ` |

One note. The paper **overloads `k`**: it is the kernel `k(x,y)` of `(2)` in
Theorem 1.1, and the *number of cone types* in §5's core induction (Lemma 5.7).
The two never occur together, and the Lean inherits both uses.

## Verification

```
lake build                                              # no errors
grep -rn 'sorry' --include='*.lean' QuadraticFormsSobolev   # no occurrences
#print axioms QFS.Paper.theorem_1_1                     # [propext, Classical.choice, Quot.sound]
```

and the same `#print axioms` for every theorem of `Paper.lean` and `GapNote.lean`.

## The files

| File | Contents |
| --- | --- |
| `Paper` | **the paper's results, stated in full, in order** |
| `Translate` | shifting and shrinking sets; the steps (⋆) and (✝) of Lemma 2.7 |
| `Defs` | Definition 2.1: cones, double cones, configurations, condition (M) |
| `ConeGap`, `ConeGeometry` | the signed distance `coneGap` to a cone's boundary |
| `Cubes` | the maximum norm, cubes, Lemma 2.7 |
| `RefCones` | Lemma 2.2 and Corollary 2.4: finitely many reference cones |
| `Section1` | the quadratic forms and function spaces, assumption (2), equation (5), the discrete form of Theorem 1.3, basic facts about the forms |
| `Section3` | lattices, Lemmas 3.2 and 3.4 (and the counterexample to 3.4), cube volumes, the tiling |
| `ThinCones` | Lemma 3.3 for `d ≥ 2`, and its failure for `d = 1` |
| `Section3Kernel` | the discrete kernel, Proposition 3.5, Corollary 3.6 |
| `DimOne` | Proposition 3.5 and Corollary 3.6 for `d = 1`, where Lemma 3.3 fails, and both in every dimension |
| `Rescaling` | Corollary 3.1 |
| `Section4` | the continuous prelude; Theorem 4.1 |
| `Section5` | Lemmas 5.1–5.7, Corollary 5.8 |
| `Renormalization` | Lemma 5.9 (and the paper's threshold), Definitions 5.10–5.13, Proposition 5.14 |
| `Counting`, `Paths`, `CyclicScheme`, `Multiplicity`, `Assembly` | the ingredients of Theorem 5.15's Steps 1, 2 and 6 |
| `FirstJump` | the scale step, Lemma 5.16, the statement of Theorem 5.15 |
| `PathAssembly`, `BlockPaths` | Steps 1–6, and Theorem 5.15 |
| `Section6` | Theorem 1.3 |
| `LebesgueDiff` | Lemma A.2, in general and in the paper's form |
| `AppendixA` | Lemma A.1 given the Whitney family and Dyda's inequality as hypotheses: for a ball and for a domain |
| `RandomLattice/` | random lattice sampling: Theorem 1.3 for every `α ≥ 0` and with uniform constants, the lattice averages, the whole-space and enlarged-ball comparabilities, the averaging over small balls, Lemma 5.7 as printed, Theorem 1.1 |
| `LipschitzDomain` | bounded Lipschitz domains (Dyda's definition); every ball is one |
| `Dyda/` | Dyda's inequality (13) on the unit ball, uniformly in `α`, and on bounded Lipschitz domains: the abstract Step 1 (`ChainStep`), the averaging over a sun (`Sun`), the Poincaré inequality by chaining (`Poincare`), the interior cones of a chart (`LipschitzCone`), the assembly (`Domain`) |
| `Density/` | density of smooth functions in `H_k`: on `ℝ^d` (the seminorm as an average of `L²` differences, continuity of translation, mollification, cutting off) and on a bounded Lipschitz domain (a partition of unity over the boundary charts, translation into the domain along each chart direction before mollifying) |
| `LemmaA1Domain` | Dyda's inequality on dilates of a domain in the paper's forms; Lemma A.1 and Theorem 1.4 on bounded Lipschitz domains |
| `Nonvacuous` | witnesses that the hypotheses are satisfiable |
| `GapNote` | the note's Theorem A and Remark 3.7, stated exactly as in the note |
| `paper/` | the note on the §3.2 gap and its repair by random lattice sampling (LaTeX source and PDF) |

## Building

Lean `v4.33.1` with Mathlib `v4.33.1` (both pinned in `lean-toolchain` and `lakefile.toml`).

```
lake exe cache get   # or reuse an existing Mathlib build
lake build
```

## References

- K.-U. Bux, M. Kassmann, T. Schulze, *Quadratic forms and Sobolev spaces of fractional order*,
  Proc. London Math. Soc. 119 (2019) 841–866. [doi:10.1112/plms.12246](https://doi.org/10.1112/plms.12246),
  [arXiv:1707.09277](https://arxiv.org/abs/1707.09277v1)
- B. Dyda, *On comparability of integral forms*, J. Math. Anal. Appl. 318 (2006) 564–577.
  [doi:10.1016/j.jmaa.2005.06.021](https://doi.org/10.1016/j.jmaa.2005.06.021)
- M. Prats, E. Saksman, *A T(1) theorem for fractional Sobolev spaces on domains*, J. Geom. Anal. 27
  (2017) 2490–2538. [doi:10.1007/s12220-017-9770-y](https://doi.org/10.1007/s12220-017-9770-y)

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
