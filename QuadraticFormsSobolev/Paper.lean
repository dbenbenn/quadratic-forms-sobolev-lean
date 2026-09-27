/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadraticFormsSobolev.DimOne
import QuadraticFormsSobolev.AppendixA
import QuadraticFormsSobolev.BlockPaths
import QuadraticFormsSobolev.Cubes
import QuadraticFormsSobolev.Density.Main
import QuadraticFormsSobolev.Density.DomainMain
import QuadraticFormsSobolev.Dyda.Main
import QuadraticFormsSobolev.FirstJump
import QuadraticFormsSobolev.LemmaA1Domain
import QuadraticFormsSobolev.LebesgueDiff
import QuadraticFormsSobolev.RandomLattice.DydaScaling
import QuadraticFormsSobolev.RandomLattice.Faithful
import QuadraticFormsSobolev.RandomLattice.GoalUniform
import QuadraticFormsSobolev.RandomLattice.LemmaFiveSeven
import QuadraticFormsSobolev.RandomLattice.LocalAverage
import QuadraticFormsSobolev.RandomLattice.TheoremOneThreeUniform
import QuadraticFormsSobolev.RefCones
import QuadraticFormsSobolev.Renormalization
import QuadraticFormsSobolev.Rescaling
import QuadraticFormsSobolev.Section1
import QuadraticFormsSobolev.Section3
import QuadraticFormsSobolev.Section3Kernel
import QuadraticFormsSobolev.Section4
import QuadraticFormsSobolev.Section5
import QuadraticFormsSobolev.ThinCones

/-! ## Section 1 -/

section
open scoped ENNReal

namespace QFS.Paper

/-- **Theorem 1.1 — comparability on every ball**

“Let $\Gamma$ be a $\vartheta$-admissible configuration and $\alpha \in (0,2)$. Let $k : \mathbb{R}^d \times \mathbb{R}^d \to [0,\infty]$ be a measurable function satisfying $k(x,y) = k(y,x)$ and
$$\Lambda^{-1}\big(\mathbb{1}_{V^\Gamma[x]}(y) + \mathbb{1}_{V^\Gamma[y]}(x)\big)|x-y|^{-d-\alpha} \le k(x,y) \le \Lambda |x-y|^{-d-\alpha}, \qquad (2)$$
for all $x$ and $y$, where $\Lambda \ge 1$ is some constant. Then there is a constant $c \ge 1$ such that for every ball $B \subset \mathbb{R}^d$ and for every $f \in L^2(B)$, the inequality
$$\int_{B\times B} (f(x)-f(y))^2 |x-y|^{-d-\alpha}\,\mathrm{d}(x,y) \le c \int_{B\times B} (f(x)-f(y))^2 k(x,y)\,\mathrm{d}(x,y) \qquad (3)$$
holds.

The constant $c$ depends on $\Lambda$, the dimension $d$ and $\vartheta$. It is independent of $k$ and $\Gamma$. For $0 < \alpha_0 \le \alpha < 2$, the constant $c$ depends on $\alpha_0$ but not on $\alpha$.” (p. 2)

*Differences from the paper.* Measurability of $k$ is not assumed; the integrals are lower Lebesgue integrals. As in the paper, the upper bound in (2) says nothing on the diagonal, so $k(x,x)$ is free. The statement is vacuous for $d = 0$ and for $\vartheta > \pi/2$, since there are no configurations there. -/
theorem theorem_1_1 (d : ℕ) :
    ∀ ϑ Λ α₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α₀ →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ R)) →
        formHs (Metric.ball x₀ R) α f ≤ ENNReal.ofReal c * form (Metric.ball x₀ R) k f :=
  QFS.theoremOneOne_uniform d

end QFS.Paper

end

section

namespace QFS.Paper

/-- **Theorem 1.3 — the discrete comparability**

“Let $\Gamma$ be a $\vartheta$-bounded configuration and $\alpha \in (0,2)$. Let $\omega : \mathbb{Z}^d \times \mathbb{Z}^d \to [0,\infty]$ be a function satisfying $\omega(x,y) = \omega(y,x)$ and
$$\Lambda^{-1}\big(\mathbb{1}_{V^\Gamma[x]}(y) + \mathbb{1}_{V^\Gamma[y]}(x)\big)|x-y|^{-d-\alpha} \le \omega(x,y) \le \Lambda|x-y|^{-d-\alpha} \qquad (4)$$
for $|x-y| > R_0$, where $R_0 > 0$, $\Lambda \ge 1$ are some constants. There exist constants $\kappa \ge 1$, $c \ge 1$ such that for every $R > 0$, $x_0 \in \mathbb{R}^d$ and every function $f : (B_{\kappa R}(x_0) \cap \mathbb{Z}^d) \to \mathbb{R}$, the inequality
$$\sum_{\substack{x,y \in B_R(x_0)\cap\mathbb{Z}^d\\ |x-y|>R_0}} (f(x)-f(y))^2|x-y|^{-d-\alpha} \le c \sum_{\substack{x,y\in B_{\kappa R}(x_0)\cap\mathbb{Z}^d\\ |x-y|>R_0}} (f(x)-f(y))^2\omega(x,y)$$
holds. The constant $c$ depends on $\Lambda, \vartheta, R_0$ and on the dimension $d$. It does not depend on $\omega$ and $\Gamma$.” (p. 3) -/
theorem theorem_1_3 (d : ℕ) :
    ∀ ϑ Λ R₀ : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < R₀ →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧ ∀ α : ℝ, 0 < α → α < 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ ω, DiscreteKernelBounds Γ α Λ R₀ (lattice d) ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ), 0 < R →
        discreteForm (Metric.ball x₀ R) R₀ (jumpKernel d α) f
          ≤ ENNReal.ofReal c * discreteForm (Metric.ball x₀ (κ * R)) R₀ ω f :=
  QFS.theoremOneThree_uniform d

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **Theorem 1.4 — $H_k = H^{\alpha/2}$ on $\mathbb{R}^d$**

“Let $\Omega \subset \mathbb{R}^d$ be a bounded Lipschitz domain. Then $H_k(\Omega) = H^{\frac{\alpha}{2}}(\Omega)$. The seminorms $|\cdot|_{H_k(\Omega)}$ and $|\cdot|_{H^{\frac{\alpha}{2}}(\Omega)}$ and the corresponding norms are comparable on $H_k(\Omega)$. Moreover, the subspace $C^\infty(\overline{\Omega})$ is dense in $H_k(\Omega)$. In addition $H_k(\mathbb{R}^d) = H^{\frac{\alpha}{2}}(\mathbb{R}^d)$ and the seminorms $|\cdot|_{H_k(\mathbb{R}^d)}$ and $|\cdot|_{H^{\frac{\alpha}{2}}(\mathbb{R}^d)}$ and the corresponding norms are comparable on $H_k(\mathbb{R}^d)$. The subspace $C_c^\infty(\mathbb{R}^d)$ of smooth functions with compact support in $\mathbb{R}^d$ is dense in $H_k(\mathbb{R}^d)$.” (p. 4) -/
theorem theorem_1_4 (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 MeasureTheory.volume ∧ form Set.univ k g ≠ ⊤}
          = {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 MeasureTheory.volume ∧
              formHs Set.univ α g ≠ ⊤} ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 MeasureTheory.volume →
        formHs Set.univ α f ≤ ENNReal.ofReal c * form Set.univ k f ∧
        form Set.univ k f ≤ ENNReal.ofReal Λ * formHs Set.univ α f ∧
        MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + formHs Set.univ α f
          ≤ ENNReal.ofReal c * (MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + form Set.univ k f) ∧
        MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + form Set.univ k f
          ≤ ENNReal.ofReal Λ *
            (MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ 2 + formHs Set.univ α f) :=
  QFS.theoremOneFour_univ d

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **Theorem 1.4 — $H_k(\Omega) = H^{\alpha/2}(\Omega)$ on a bounded Lipschitz domain**

“Let $\Omega \subset \mathbb{R}^d$ be a bounded Lipschitz domain. Then $H_k(\Omega) = H^{\frac{\alpha}{2}}(\Omega)$. The seminorms $|\cdot|_{H_k(\Omega)}$ and $|\cdot|_{H^{\frac{\alpha}{2}}(\Omega)}$ and the corresponding norms are comparable on $H_k(\Omega)$. Moreover, the subspace $C^\infty(\overline{\Omega})$ is dense in $H_k(\Omega)$. In addition $H_k(\mathbb{R}^d) = H^{\frac{\alpha}{2}}(\mathbb{R}^d)$ and the seminorms $|\cdot|_{H_k(\mathbb{R}^d)}$ and $|\cdot|_{H^{\frac{\alpha}{2}}(\mathbb{R}^d)}$ and the corresponding norms are comparable on $H_k(\mathbb{R}^d)$. The subspace $C_c^\infty(\mathbb{R}^d)$ of smooth functions with compact support in $\mathbb{R}^d$ is dense in $H_k(\mathbb{R}^d)$.” (p. 4)

This is the first half of the theorem: the equality of the two spaces on a bounded Lipschitz
domain $\Omega$ and the comparability of their seminorms and norms. `theorem_1_4` is the half on
$\mathbb{R}^d$. The density assertions are `theorem_1_4_density_domain` and
`theorem_1_4_density_univ`.

A bounded Lipschitz domain is `QFS.IsBoundedLipschitzDomain`: Dyda's definition, which the paper
uses without stating it — a bounded connected open set that near each boundary point is the
region above the graph of a Lipschitz function, in some direction. The constant $c$ may depend on
$\Omega$, as in the paper, where it comes from Lemma A.1. -/
theorem theorem_1_4_domain (d : ℕ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ c : ℝ, 1 ≤ c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict Ω) ∧
          form Ω k g ≠ ⊤}
          = {g : EuclideanSpace ℝ (Fin d) → ℝ | MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict Ω) ∧
              formHs Ω α g ≠ ⊤} ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Ω) →
        formHs Ω α f ≤ ENNReal.ofReal c * form Ω k f ∧
        form Ω k f ≤ ENNReal.ofReal Λ * formHs Ω α f ∧
        MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict Ω) ^ 2 + formHs Ω α f
          ≤ ENNReal.ofReal c *
            (MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict Ω) ^ 2 + form Ω k f) ∧
        MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict Ω) ^ 2 + form Ω k f
          ≤ ENNReal.ofReal Λ *
            (MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict Ω) ^ 2 + formHs Ω α f) :=
  QFS.theoremOneFour_domain d hΩ

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **Theorem 1.4 — $C_c^\infty(\mathbb{R}^d)$ is dense in $H_k(\mathbb{R}^d)$**

“The subspace $C_c^\infty(\mathbb{R}^d)$ of smooth functions with compact support in $\mathbb{R}^d$ is dense in $H_k(\mathbb{R}^d)$.” (p. 4)

Density is in the norm of $H_k(\mathbb{R}^d)$: for every $f \in H_k(\mathbb{R}^d)$, that is $f \in L^2$
with $\mathcal E_{\mathbb{R}^d}[k, f] < \infty$, and every $\varepsilon > 0$ there is a smooth
compactly supported $g$ with
$\|f - g\|_{L^2}^2 + \mathcal E_{\mathbb{R}^d}[k, f - g] < \varepsilon$.

*Route.* By the comparability of `theorem_1_4` it suffices to approximate in $H^{\alpha/2}(\mathbb{R}^d)$.
There $f$ is cut off by $\chi(x/n)$ and then mollified. The seminorm is written as
$\int |h|^{-d-\alpha} \|f(\cdot + h) - f\|_{L^2}^2 \,dh$, and both steps converge by dominated
convergence in $h$. Cutting off needs $\int \min(1, |h|^2)|h|^{-d-\alpha}\,dh < \infty$, that is
$0 < \alpha < 2$; mollifying needs the continuity of translation in $L^2$. -/
theorem theorem_1_4_density_univ (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
    ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 MeasureTheory.volume →
      form Set.univ k f ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε →
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      MeasureTheory.eLpNorm (f - g) 2 MeasureTheory.volume ^ 2 + form Set.univ k (f - g)
        < ENNReal.ofReal ε :=
  QFS.theoremOneFour_density_univ d

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **Theorem 1.4 — $C^\infty(\overline\Omega)$ is dense in $H_k(\Omega)$**

“Moreover, the subspace $C^\infty(\overline{\Omega})$ is dense in $H_k(\Omega)$.” (p. 4)

$\Omega$ is a bounded Lipschitz domain (`QFS.IsBoundedLipschitzDomain`). $C^\infty(\overline\Omega)$ is
read as the restrictions to $\Omega$ of smooth compactly supported functions on $\mathbb{R}^d$. Density
is in the norm of $H_k(\Omega)$: for every $f \in L^2(\Omega)$ with $\mathcal E_\Omega[k, f] < \infty$
and every $\varepsilon > 0$ there is such a $g$ with
$\|f - g\|_{L^2(\Omega)}^2 + \mathcal E_\Omega[k, f - g] < \varepsilon$.

*Route.* By the comparability of `theorem_1_4_domain` it suffices to approximate in
$H^{\alpha/2}(\Omega)$. A partition of unity splits $f$ into pieces near the boundary charts and an
interior piece. Each boundary piece is translated a distance $t$ into $\Omega$ along its chart
direction and mollified at a scale below $t$; the interior cone of the chart keeps every value
used inside $\Omega$, so no extension of $f$ is needed. The interior piece is mollified. The errors
are controlled by the continuity of translation in $L^2(\mathbb{R}^d)$ for $f\,1_\Omega$ and in
$L^2(\mathbb{R}^d \times \mathbb{R}^d)$ for $1_{\Omega\times\Omega}(x,y)(f(y) - f(x))|x-y|^{-(d+\alpha)/2}$. -/
theorem theorem_1_4_density_domain (d : ℕ) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
    ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Ω) →
      form Ω k f ≠ ⊤ →
    ∀ ε : ℝ, 0 < ε →
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      MeasureTheory.eLpNorm (f - g) 2 (MeasureTheory.volume.restrict Ω) ^ 2 + form Ω k (f - g)
        < ENNReal.ofReal ε :=
  QFS.theoremOneFour_density_domain d hΩ

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory ENNReal
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Equation (5) — the fractional Sobolev space sits inside the kernel space**

**Equation (5) of Bux–Kassmann–Schulze.** For a kernel $k$ satisfying the two-sided bounds (2)
for a configuration $\Gamma$, and for **every** set $\Omega$,

$$H^{\alpha/2}(\Omega) \;\subseteq\; H_k(\Omega).$$

The source derives it in one sentence: "Note that $|\cdot|_{H^{\alpha/2}(\Omega)}$ dominates
$|\cdot|_{H_k(\Omega)}$ because of (2). Hence $\|\cdot\|_{H^{\alpha/2}(\Omega)}$ dominates
$\|\cdot\|_{H_k(\Omega)}$ and we can deduce the following inclusion." Only the **upper** half
of (2) is used — $k(x,y) \le \Lambda \|x-y\|^{-d-\alpha}$ — through
`QFS.form_le_formHs`; the full `KernelBounds` is taken as the hypothesis because that is the
assumption the source is quoting.

**This is the cheap half of Theorem 1.4.** That theorem asserts $H_k(\Omega) = H^{\alpha/2}(\Omega)$
for a bounded Lipschitz domain; (5) is the inclusion that costs nothing, and the reverse is what
Sections 3 to 5 are for. On $\mathbb{R}^d$ the reverse is `theorem_1_4`; on a bounded Lipschitz
domain it is `theorem_1_4_domain`.

Membership in either space means square-integrability on $\Omega$ together with finiteness of the
corresponding seminorm, both seminorms being lower Lebesgue integrals in $[0,\infty]$. No
measurability of $k$, no cone hypothesis beyond what `KernelBounds` carries, and no restriction
on $\Omega$ — it need not be open, bounded, or measurable. -/
theorem equation_5 {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {α Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Hs Ω α ⊆ Hk Ω k :=
  QFS.Hs_subset_Hk hk Ω

end QFS.Paper

end

/-! ## Section 2 -/

section
open Real Set Metric InnerProductGeometry

namespace QFS.Paper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 2.2 — finitely many reference cones**

For a `ϑ`-bounded configuration `Γ` there are finitely many double cones `V¹, …, V^L` centred at
`0`, with common apex angle `θ = ϑ/3` and unit axes, such that every `Γ(x)` contains one of them.
The finite family of axes is produced before `Γ` is mentioned: it depends only on the space and on
`ϑ`, exactly as the paper asserts. -/
theorem lemma_2_2 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ S : Finset E, (∀ v ∈ S, ‖v‖ = 1) ∧
      ∀ Γ : Configuration E, IsBounded Γ ϑ →
        ∀ x : E, ∃ v ∈ S, doubleCone v (ϑ / 3) ⊆ (Γ x).carrier :=
  QFS.ref_cones hϑ hϑ'

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric InnerProductGeometry
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace QFS.Paper

/-- **Corollary 2.4 — Reduction of a bounded configuration to a finite family of reference cones**

Let $E$ be a finite-dimensional real inner product space and let $\vartheta$ satisfy $0 < \vartheta \le \pi/2$. A *configuration* is a map $\Gamma$ assigning to each $x \in E$ a double cone $\Gamma(x)$, given by a unit axis and an apex angle in $(0,\pi/2]$; it is *$\vartheta$-bounded* when $\vartheta > 0$ and every apex angle $\Gamma(x).\mathrm{apex}$ is at least $\vartheta$. Let $\Gamma$ be $\vartheta$-bounded. Then there is a configuration $\Gamma'$ such that

$$\text{(i) } \{\Gamma'(x) : x \in E\} \text{ is finite}; \qquad
\text{(ii) } \Gamma'(x) \subseteq \Gamma(x) \text{ for every } x; \qquad
\text{(iii) } \Gamma'(x).\mathrm{apex} = \vartheta/3 \text{ for every } x;$$
$$\text{(iv) } \Gamma' \text{ is } (\vartheta/3)\text{-bounded}.$$
In (ii) the inclusion is between the underlying subsets of $E$ carried by the two double cones.

The point is that an arbitrary bounded configuration, which may use uncountably many axes, can be replaced by a subconfiguration taking only finitely many values, at the price of shrinking each aperture to $\vartheta/3$. Every argument that must treat cone types one at a time — decomposing space into the finitely many sets where a given reference cone is available — rests on this reduction. -/
theorem corollary_2_4 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    (Γ : Configuration E) (hΓ : IsBounded Γ ϑ) :
    ∃ Γ' : Configuration E, (Set.range Γ').Finite ∧
      (∀ x, (Γ' x).carrier ⊆ (Γ x).carrier) ∧
      (∀ x, (Γ' x).apex = ϑ / 3) ∧ IsBounded Γ' (ϑ / 3) :=
  QFS.ref_config hϑ hϑ' Γ hΓ

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric Finset
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 2.7 — Nested shifted shrinkings of a set across a cube**

Let $d \in \mathbb{N}$, let $V \subseteq \mathbb{R}^d$ be an arbitrary set, let $h \in \mathbb{R}$ with $h \ge 0$, and let $x \in \mathbb{R}^d$. For $r \in \mathbb{R}$ write
$$V_r = \{\, y \in V : \bar B(y,r) \subseteq V \,\}$$
for the shrinking of $V$ by $r$, and $V[\xi] = \xi + V$ for the translate of $V$ to the point $\xi$ (Definition 2.1: applied to a double cone these are the paper's double half-cone $V_r$ and shifted cone $V[\xi]$). If $\xi$ lies in the cube $A_h(x)$ of side $h$ centred at $x$, then both

$$\bigl(V_{h\sqrt d}\bigr)[\xi] \;\subseteq\; \bigl(V_{\frac{h}{2}\sqrt d}\bigr)[x] \qquad\text{and}\qquad \bigl(V_{\frac{h}{2}\sqrt d}\bigr)[x] \;\subseteq\; V[\xi].$$

Chained together these give $\bigl(V_{h\sqrt d}\bigr)[\xi] \subseteq V[\xi]$ through an intermediate set based at the *centre* $x$ rather than at $\xi$. This is Lemma 2.7 in the concrete form used in the paper: it is what lets a condition imposed once, at the centre of a cube, be used at every point of that cube, and conversely lets a condition holding at every point of the cube be summarized by one condition at the centre. It is the geometric device that makes the discretization of the cone structure over a lattice of cubes possible.

**Formalization Note.** The statement is proved for an arbitrary set $V$; nothing about cones is used, only the normed structure. The radii $h\sqrt d$ and $\tfrac h2\sqrt d$ are the diameter and the half-diagonal of a cube of side $h$, which is where the hypothesis $\xi \in A_h(x)$ enters. -/
theorem lemma_2_7 (V : Set (EuclideanSpace ℝ (Fin d))) {h : ℝ} (hh : 0 ≤ h)
    (x : EuclideanSpace ℝ (Fin d)) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ξ ∈ cube h x) :
    shift (shrink V (h * Real.sqrt d)) ξ ⊆ shift (shrink V (h / 2 * Real.sqrt d)) x ∧
      shift (shrink V (h / 2 * Real.sqrt d)) x ⊆ shift V ξ :=
  QFS.cone_in_intersection V hh x hξ

end QFS.Paper

end

/-! ## Section 3 -/

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric ENNReal
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Corollary 3.1 — the discrete result at every lattice spacing**

“Let $\Gamma$ be a $\vartheta$-bounded configuration and let $h > 0$. Let $\omega : h\mathbb{Z}^d \times h\mathbb{Z}^d \to [0,\infty]$ be a function satisfying $\omega(x,y) = \omega(y,x)$ and
$$\Lambda^{-1}\big(\mathbb{1}_{V^\Gamma[x]}(y) + \mathbb{1}_{V^\Gamma[y]}(x)\big)|x-y|^{-d-\alpha} \le \omega(x,y) \le \Lambda|x-y|^{-d-\alpha} \qquad (8)$$
for $|x-y| > R_0h$, where $R_0 > 0$, $\Lambda \ge 1$ are some constants. There exist constants $\kappa \ge 1$ and $c > 0$, such that for every $R > 0$, every $x_0 \in \mathbb{R}^d$, and every function $f : (B_{\kappa R} \cap h\mathbb{Z}^d) \to \mathbb{R}$, the inequality
$$c\sum_{\substack{x,y\in B_R\cap h\mathbb{Z}^d\\ |x-y|>R_0h}}(f(x)-f(y))^2|x-y|^{-d-\alpha} \le \sum_{\substack{x,y\in B_{\kappa R}\cap h\mathbb{Z}^d\\ |x-y|>R_0h}}(f(x)-f(y))^2\omega(x,y)$$
holds. The constant $c$ depends on $\Lambda, \vartheta, R_0$ and on the dimension $d$. It does not depend on $\omega, \Gamma$ and $h$.” (p. 10) -/
theorem corollary_3_1 (ϑ Λ α R₀ : ℝ) (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 < α)
    (hα2 : α < 2) (hR₀ : 0 < R₀) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 1 ≤ c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h : ℝ, 0 < h →
      ∀ ω, DiscreteKernelBounds Γ α Λ (R₀ * h) (scaledLattice d h) ω →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
        0 < R →
        discreteFormOn (scaledLattice d h) (ball x₀ R) (R₀ * h) (jumpKernel d α) f
          ≤ ENNReal.ofReal c *
            discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (R₀ * h) ω f :=
  QFS.corollaryThreeOne ϑ Λ α R₀ hϑ hΛ hα hα2 hR₀

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
variable {E : Type*}

namespace QFS.Paper

/-- **Lemma 3.2 for arbitrary sets and the full unit cubes**

The general form of **Lemma 3.2 of Bux–Kassmann–Schulze**. For arbitrary sets $V, W$ and
any $s \in A_1(x)$, $t \in A_1(y)$ — the full open unit cubes centred at $x$ and $y$ —

$$\mathbf 1_{V_{\sqrt d/2}[x]}(t) + \mathbf 1_{W_{\sqrt d/2}[y]}(s)
\;\ge\;
\mathbf 1_{V_{\sqrt d}[x]}(y) + \mathbf 1_{W_{\sqrt d}[y]}(x),$$

where $V_r = \{u \in V : \bar B(u,r) \subseteq V\}$ is the $r$-shrinking of Definition 2.1
and $V[x] = V + x$.

The source states Lemma 3.2 for the reference cones $V^m$, $V^n$ at $1$-favoured indices
$m$ at $x$ and $n$ at $y$, with $s$ and $t$ confined to the cone-cut parts $A_1^m(x)$ and
$A_1^n(y)$ of the cubes. None of that is needed: the argument uses only that $A_1(y)$ lies
in the ball $B_{\sqrt d/2}(y)$, so that shrinking by $\sqrt d$ at the lattice point leaves
room to shrink by $\sqrt d/2$ at the running point. Since $A_1^m(x) \subseteq A_1(x)$ and
the reference cones are particular sets, this statement implies the source's, which is
stated as printed in `lemma_3_2_as_printed`.

The indicators are real-valued (`QFS.ind`); `QFS.lemma_min_dist_E` is the same inequality
in `ℝ≥0∞`, which is the form Proposition 3.5's integral estimate consumes. -/
theorem lemma_3_2 {V W : Set (EuclideanSpace ℝ (Fin d))}
    {x y s t : EuclideanSpace ℝ (Fin d)} (hs : s ∈ cube 1 x) (ht : t ∈ cube 1 y) :
    ind (shift (shrink V (Real.sqrt d / 2)) x) t
        + ind (shift (shrink W (Real.sqrt d / 2)) y) s
      ≥ ind (shift (shrink V (Real.sqrt d)) x) y
        + ind (shift (shrink W (Real.sqrt d)) y) x :=
  QFS.lemma_min_dist hs ht

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
variable {E : Type*}

namespace QFS.Paper

/-- **Lemma 3.2 — the indicator inequality at favoured indices**

**Lemma 3.2 of Bux–Kassmann–Schulze.** Let $m$ be a $1$-favoured index at $x$ and $n$ a
$1$-favoured index at $y$, and let $s \in A_1^m(x)$, $t \in A_1^n(y)$. Then

$$\mathbf 1_{V^m_{\sqrt d/2}[x]}(t) + \mathbf 1_{V^n_{\sqrt d/2}[y]}(s)
\;\ge\;
\mathbf 1_{V^m_{\sqrt d}[x]}(y) + \mathbf 1_{V^n_{\sqrt d}[y]}(x).$$

Here $V_r = \{u \in V : \bar B(u,r) \subseteq V\}$ is the $r$-shrinking of Definition 2.1,
$V[x] = V + x$, and $A_1^m(x)$ is the part of the unit cube at $x$ cut out by the
reference cone $V^m$. The point is that the right-hand side involves only the lattice
points $x, y$, while the left-hand side involves the running variables $s, t$: the
inequality is what lets Proposition 3.5 pull a bound depending on $x$ and $y$ out of an
integral over $A_1^m(x) \times A_1^n(y)$.

**Why it is true**, in the source's words: if $y \in V^m_{\sqrt d}[x]$ then
$B_{\sqrt d/2}(y) \subseteq V^m_{\sqrt d/2}[x]$, and $A_1^n(y) \subseteq A_1(y) \subseteq
B_{\sqrt d/2}(y)$, so every $t$ in range contributes on the left whenever $y$ contributes
on the right.

Two points of exactness. The hypotheses that $x$ and $y$ be lattice points and that $v, w$
be favoured indices are carried in the statement, exactly as the source states them, but
are **not used** by the proof — the inequality holds for any $s, t$ in the respective
cone-cubes. `QFS.lemma_min_dist` is the corresponding general statement: arbitrary sets
$V, W$ in place of the reference cones, and $s, t$ ranging over the *full* unit cubes
$A_1(x)$, $A_1(y)$ rather than the cone-cut parts. Since $A_1^m(x) \subseteq A_1(x)$ that
is a weaker hypothesis, so the general form implies this one. Both are `Proved`. The
indicators are real-valued (`QFS.ind`); the $[0,\infty]$-valued transcription used once the
estimate moves into `ℝ≥0∞` is `QFS.lemma_min_dist_E`. -/
theorem lemma_3_2_as_printed {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
    (F : RefFamily Γ θ) {x y v w s t : EuclideanSpace ℝ (Fin d)}
    (_hx : x ∈ lattice d) (_hy : y ∈ lattice d)
    (_hv : IsFavoured F 1 x v) (_hw : IsFavoured F 1 y w)
    (hs : s ∈ cubeCone Γ (F.cone v) 1 x) (ht : t ∈ cubeCone Γ (F.cone w) 1 y) :
    ind (shift (shrink (F.cone v) (Real.sqrt d / 2)) x) t
        + ind (shift (shrink (F.cone w) (Real.sqrt d / 2)) y) s
      ≥ ind (shift (shrink (F.cone v) (Real.sqrt d)) x) y
        + ind (shift (shrink (F.cone w) (Real.sqrt d)) y) x :=
  QFS.lemma_min_dist_favoured F _hx _hy _hv _hw hs ht

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric InnerProductGeometry
open RealInnerProductSpace
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 3.3 (d ≥ 2) — Existence of a thin lattice cone inside a shrunken reference cone in dimension at least two**

Assume $d \ge 2$. Let $r > 0$, let $\vartheta$ satisfy $0 < \vartheta \le \pi/2$, and let $A$ be a **finite** set of unit vectors of $\mathbb{R}^d$. Then there exists an apex angle $\theta$ with

$$0 < \theta \le \frac{\pi}{2}$$

such that for every $u \in A$ there is a unit vector $v \in \mathbb{R}^d$ with

$$V(v,\theta) \cap \mathbb{Z}^d \;\subseteq\; \big(V(u,\vartheta)\big)_r \cap \mathbb{Z}^d .$$

Here $V(w,\psi) = $ `doubleCone w ψ` is the double cone with axis $w$ and apex angle $\psi$, $(S)_r = $ `shrink S r` is the inner $r$-shrinking of a set $S$ (the paper's $V^m_r$: the points of $S$ that survive removing an $r$-neighbourhood of the boundary), and $\mathbb{Z}^d = $ `lattice d` is the integer lattice. Note the order of the quantifiers: the single angle $\theta$ is uniform over all $u \in A$, while the axis $v$ may depend on $u$.

This is Lemma 3.3, the step that replaces a finite family of reference cones by a family of *thin* cones whose lattice points are safely interior to the originals. It is the mechanism by which the discrete argument keeps a positive margin between the cone in which the kernel is large and the cone actually used, and its restriction to $d \ge 2$ is genuine: in dimension one every double cone is $\mathbb{R} \setminus \{0\}$, and the shrinking on the right removes $\pm 1$ while the thin cone on the left cannot.

**Formalization Note.** The conclusion is an inclusion of *lattice* points only; nothing is claimed about $V(v,\theta) \subseteq (V(u,\vartheta))_r$ as sets of $\mathbb{R}^d$, and indeed that inclusion is false near the apex. The hypothesis $\|u\| = 1$ is imposed on every element of $A$, and the produced $v$ is also a unit vector. -/
theorem lemma_3_3 (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (A : Finset (EuclideanSpace ℝ (Fin d))) (hA : ∀ u ∈ A, ‖u‖ = 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ π / 2 ∧ ∀ u ∈ A, ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
      doubleCone v θ ∩ lattice d ⊆ shrink (doubleCone u ϑ) r ∩ lattice d :=
  QFS.lemma_new_config hd hr hϑ hϑ' A hA

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {θ : ℝ}
variable {E : Type*}

namespace QFS.Paper

/-- **Lemma 3.3 fails for d = 1 — Lemma 3.3 is false in dimension one**

A counterexample showing that Lemma 3.3 of the source fails as stated when $d = 1$, at the radius $r = \sqrt d = 1$ at which Proposition 3.5 invokes it.

Lemma 3.3 asserts that for every $r > 0$ there is an apex angle $\theta > 0$ such that each reference cone $V$ admits a unit axis $v$ with

$$V(v,\theta) \cap \mathbb{Z}^d \;\subseteq\; V_r \cap \mathbb{Z}^d ,$$

where $V_r = \{y \in V : \overline B(y,r) \subseteq V\}$ is the $r$-shrinking. The theorem below states that in dimension one no such $\theta$ and $v$ exist: for **every** unit axis $v$, every $\theta \in (0,\pi/2]$, and every reference cone $V(u,\vartheta)$,

$$V(v,\theta) \cap \mathbb{Z} \;\not\subseteq\; \bigl(V(u,\vartheta)\bigr)_1 \cap \mathbb{Z}.$$

The obstruction is that in one dimension a double cone of any positive aperture is all of $\mathbb{R}\setminus\{0\}$, so the left-hand side is $\mathbb{Z}\setminus\{0\}$ and contains the point $1$; but the closed unit ball about $1$ contains the origin, which no double cone contains, so $1$ is not in the $1$-shrinking.

For $d \ge 2$ the lemma is proved (`QFS.exists_thin_cone_subset`). The paper's proof of Proposition 3.5 and Corollary 3.6 uses it; for $d = 1$ they are proved directly instead (`QFS.prop_test_fct_dim_one`, `QFS.cor_rescaled_kernel_uniform_dim_one`), so both hold in every dimension.

**Formalization Note** The statement is a negation, so it asserts the non-existence of the inclusion for every choice of the quantified data rather than exhibiting a single failing configuration; the reference cone $V(u,\vartheta)$ is arbitrary and unconstrained. -/
theorem lemma_3_3_false_dim_one
    (u : EuclideanSpace ℝ (Fin 1)) (ϑ : ℝ)
    (v : EuclideanSpace ℝ (Fin 1)) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ π / 2) :
    ¬ (doubleCone v θ ∩ lattice 1 ⊆ shrink (doubleCone u ϑ) 1 ∩ lattice 1) :=
  QFS.lemma_new_config_false_dim_one u ϑ v hv θ hθ hθ'

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 3.4 — Two-sided comparison of distances between points of well-separated lattice cubes**

Fix a mesh $h > 0$ and let $h\mathbb{Z}^d = $ `scaledLattice d h` be the scaled lattice in $\mathbb{R}^d$. For a lattice point $x \in h\mathbb{Z}^d$ let
$$A_h(x) \;=\; \bigl\{z \in \mathbb{R}^d : \|z-x\|_\infty < \tfrac h2\bigr\}, \qquad \|z\|_\infty = \sup_i |z_i|,$$
be the **open** cube `cube h x` of centre $x$ and side $h$ (Definition 2.5). The open cubes about the lattice points are pairwise disjoint and cover everything except the shared faces; it is the half-closed variant $\widetilde A_h(x) = \prod_i [x_i - h/2, x_i + h/2)$, a different set, that tiles $\mathbb{R}^d$ exactly.

Let $x, y \in h\mathbb{Z}^d$ be lattice points that are well separated, in the sense that

$$\sqrt{d}\,h \;<\; \|x - y\|,$$

and let $s \in A_h(x)$ and $t \in A_h(y)$ be arbitrary points of the two corresponding open cubes. Then the distance between $s$ and $t$ is comparable to the distance between the two lattice points, with explicit dimensional constants:

$$\frac{1}{2\sqrt{d}}\,\|x-y\| \;<\; \|s-t\| \;<\; 2\sqrt{d}\,\|x-y\|.$$

Here $\|\cdot\|$ is the Euclidean norm on $\mathbb{R}^d$ and both inequalities are strict.

This is the transfer device between the lattice and the continuum: a kernel of the form $\|s-t\|^{-d-\alpha}$ evaluated at arbitrary points of two separated cubes is, up to the fixed factor $(2\sqrt d)^{\,d+\alpha}$, the same as the kernel evaluated at the two lattice points. Every comparison between a discrete sum over $h\mathbb{Z}^d \times h\mathbb{Z}^d$ and the corresponding double integral passes through it.

**Formalization Note.** The separation hypothesis $\sqrt d\,h < \|x-y\|$ is exactly what rules out equal or touching cubes, where no lower bound of this shape can hold, since $s$ and $t$ could then coincide. -/
theorem lemma_3_4 {h : ℝ} (hh : 0 < h) {x y s t : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ scaledLattice d h) (hy : y ∈ scaledLattice d h)
    (hxy : Real.sqrt d * h < ‖x - y‖) (hs : s ∈ cube h x) (ht : t ∈ cube h y) :
    1 / (2 * Real.sqrt d) * ‖x - y‖ < ‖s - t‖ ∧ ‖s - t‖ < 2 * Real.sqrt d * ‖x - y‖ :=
  QFS.lemma_cubes hh hx hy hxy hs ht

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 3.4 is false as printed — The literal statement of Lemma 3.4 is false**

A witness for a defect in the source. Lemma 3.4 is stated for all $x, y \in \mathbb{Z}^d$ and all $h > 0$; read literally, with the lattice fixed at $\mathbb{Z}^d$ independently of $h$, the statement is false. This theorem exhibits the failure.

The intended reading — which the rest of the development uses and which is true — scales the lattice with $h$. Recorded so the discrepancy between the printed statement and the intended one is on the record rather than silently repaired. -/
theorem lemma_3_4_false_as_printed :
    ¬ ∀ (d : ℕ) (h : ℝ), 0 < h → ∀ x y s t : EuclideanSpace ℝ (Fin d),
        x ∈ lattice d → y ∈ lattice d → Real.sqrt d * h < ‖x - y‖ →
        s ∈ cube h x → t ∈ cube h y →
        1 / (2 * Real.sqrt d) * ‖x - y‖ < ‖s - t‖ :=
  QFS.lemma_cubes_literal_false

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory ENNReal
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Proposition 3.5 — the discretised kernel dominates a cone kernel**

“Let $k : \mathbb{R}^d \times \mathbb{R}^d \to [0,\infty]$ be a symmetric and measurable function satisfying (2) for a $\vartheta$-admissible configuration $\Gamma$. Then there are constants $C = C(d,\vartheta) > 0$ and $\vartheta' \in (0, \frac{\pi}{2}]$ and a $\vartheta'$-bounded configuration $\Gamma'$ such that for all $x, y \in \mathbb{Z}^d$ with $|x-y| > \sqrt{d}$:
$$C\Lambda^{-1}\big(\mathbb{1}_{V^{\Gamma'}[x]}(y) + \mathbb{1}_{V^{\Gamma'}[y]}(x)\big)|x-y|^{-d-\alpha} \le \omega_1^k(x,y)$$
The angle $\vartheta'$ does only depend on $\theta$ and on the infimum $\vartheta$ of the apex angles of all cones in $\Gamma$. There is no further dependence on $\Gamma$.” (p. 12)

*Differences from the paper.* This statement differs from the sentence in one way. It assumes `CondMeas` (for every $V$, the set $\{x : V \subseteq \Gamma(x)\}$ is measurable) in place of condition (M): this is the measurability that the paper obtains from (M) by citing Debreu (p. 8). It holds in every dimension: for $d = 1$, where Lemma 3.3 (which the paper's proof uses) is false, it is proved directly, since every double cone in $\mathbb{R}$ is $\mathbb{R} \setminus \{0\}$. Its constants are chosen before $\alpha$, as the paper's are. The proof of Theorem 1.1 here does not use this statement. -/
theorem proposition_3_5 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ C θ' : ℝ, 0 < C ∧ 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ (Λ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        KernelBounds Γ α Λ k →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ' θ' ∧
        ∀ x ∈ lattice d, ∀ y ∈ lattice d, Real.sqrt d < ‖x - y‖ →
          ENNReal.ofReal (C * Λ⁻¹) *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k 1 x y :=
  QFS.prop_test_fct hϑ hϑ'

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory ENNReal
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Corollary 3.6 — the discretised kernel, two-sided and uniform in the spacing**

“Let $k : \mathbb{R}^d \times \mathbb{R}^d \to [0,\infty]$ be a symmetric and measurable function satisfying (2) for a $\vartheta$-admissible configuration $\Gamma$. Then there are $\vartheta' > 0$ and $C > 0$ so that for each $h > 0$ there is a configuration $\Gamma^h$ on $\mathbb{R}^d$ with the following properties: (i) The infimum of the apex angles of all cones in $\Gamma^h(\mathbb{R}^d)$ equals $\vartheta'$. (ii) For all $x, y \in h\mathbb{Z}^d$ with $|x-y| > \sqrt{d}h$, the inequalities
$$C^{-1}\big(\mathbb{1}_{V^{\Gamma^h}[x]}(y) + \mathbb{1}_{V^{\Gamma^h}[y]}(x)\big)|x-y|^{-d-\alpha} \le \omega_h^k(x,y) \le C|x-y|^{-d-\alpha} \qquad (10)$$
hold.” (p. 13)

*Differences from the paper.* This statement differs from the sentence in one way. It assumes `CondMeas` (for every $V$, the set $\{x : V \subseteq \Gamma(x)\}$ is measurable) in place of condition (M): this is the measurability that the paper obtains from (M) by citing Debreu (p. 8). It holds in every dimension: for $d = 1$, where Lemma 3.3 (which the paper's proof uses) is false, it is proved directly, since every double cone in $\mathbb{R}$ is $\mathbb{R} \setminus \{0\}$. Its constants are chosen before $\alpha$, as the paper's are. The proof of Theorem 1.1 here does not use this statement. -/
theorem corollary_3_6 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ π / 2 ∧
      ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ C : ℝ, 0 < C ∧
      ∀ α : ℝ, 0 < α → α ≤ 2 →
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ → CondMeas Γ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        KernelBounds Γ α Λ k →
      ∀ h : ℝ, 0 < h →
      ∃ Γ' : Configuration (EuclideanSpace ℝ (Fin d)),
        (∀ u, (Γ' u).apex = θ') ∧ IsBounded Γ' θ' ∧
        ∀ x ∈ scaledLattice d h, ∀ y ∈ scaledLattice d h, Real.sqrt d * h < ‖x - y‖ →
          ENNReal.ofReal C⁻¹ *
              ((indE (coneAt Γ' x) y + indE (coneAt Γ' y) x) * jumpKernel d α x y)
            ≤ discreteKernel d k h x y ∧
          discreteKernel d k h x y ≤ ENNReal.ofReal C * jumpKernel d α x y :=
  QFS.cor_rescaled_kernel_uniform hϑ hϑ'

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **§3.2 — the limiting argument, enlarged-ball form**

“In conclusion, we have shown that the discrete inequality (15) yields the continuous version
$$c|f|_{H^{\frac{\alpha}{2}}(B)} \le |f|_{H_k(B^*)} \quad \text{for all } f \in H_k(B^*).$$
This is true for every ball $B$, since $c$ is independent of $B$.” (p. 16; here $B = B_R(x_0)$ and $B^* = B_{\kappa R}(x_0)$, p. 14) -/
theorem section_3_2 (d : ℕ) :
    ∀ ϑ Λ α : ℝ, 0 < ϑ → 1 ≤ Λ → 0 < α → α < 2 →
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 < c ∧ ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsAdmissible Γ ϑ →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞, KernelBounds Γ α Λ k →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ (κ * R)) k f :=
  QFS.formHs_ball_le_form_enlargedBall d

end QFS.Paper

end

/-! ## Section 4 -/

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Theorem 4.1 — connectivity in the continuum**

“For any connected open set $U \subset \mathbb{R}^d$, any two points $x, y \in U$ are vertices in the same connected component of $G_U$.” (p. 17; $G_U$ has vertex set $\mathbb{R}^d$ and an edge from $x$ to $y$ when $x \in U$ and $y \in V^\Gamma[x]$, and “vertices outside $U$ still can be used in edge paths”, p. 17) -/
theorem theorem_4_1 [FiniteDimensional ℝ E] {ϑ : ℝ} (hΓ : IsBounded Γ ϑ)
    {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : Conn Γ U x y :=
  QFS.cont_connectivity hΓ hU hUc hx hy

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.3 as a connectivity statement**

**Lemma 4.3 of Bux–Kassmann–Schulze**, with the conclusion recorded as connectivity rather
than as an explicit two-edge path: if $x, y \in U$ have the same cone type, then $x$ and $y$ are
connected in $G[U]$.

Connectivity here is the reflexive-transitive closure of the symmetrised edge relation, so it
forgets the length bound. `QFS.connect_two_of_same_type_two` is the source's own statement —
"an edge path in $G_U$ of length at most two" — exhibiting the intermediate point explicitly.
This form is what Lemma 4.6 and Theorem 4.1 chain with, where only reachability matters. Both
are `Proved`.

As in the two-edge form, the intermediate point need not lie in $U$ — the source notes this
explicitly — and "the same type" is taken as equality of the underlying sets rather than of the
cone data, which is the weaker hypothesis. -/
theorem lemma_4_3 {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    (h : (Γ x).carrier = (Γ y).carrier) : Conn Γ U x y :=
  QFS.connect_two_of_same_type hx hy h

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.5 (1) — points of a cone are well-connected**

**Lemma 4.5 (1) of Bux–Kassmann–Schulze.** For $y \in U$, every point
$x \in U \cap V^\Gamma[y]$ is well-connected in $U$.

Definition 4.4: $x$ is *well-connected in $U$* when some open neighbourhood $W$ of $x$ lies
entirely in one connected component of $G[U]$ — equivalently, $x$ is joined by edge paths in
$G[U]$ to every point of some open neighbourhood of itself.

The proof is the source's: take $U \cap V^\Gamma[y]$ itself as the neighbourhood. Any two of
its points are joined by an edge path of length two with $y$ as the middle vertex, since each
of them receives an edge from $y$.

$U$ is required to be open, which Section 4 assumes throughout — it is what makes
$U \cap V^\Gamma[y]$ an admissible neighbourhood.

This is the engine of Lemma 4.5: the source derives part (3) from it, and part (3)'s density
from (2). The other three parts are `QFS.wellConnected_mono` (2),
`QFS.exists_wellConnected` (3, existence) and `QFS.wellConnected_dense` (3, density). All are
`Proved`. -/
theorem lemma_4_5_1 (hU : IsOpen U) {x y : E} (hy : y ∈ U)
    (hx : x ∈ U ∩ coneAt Γ y) : WellConnected Γ U x :=
  QFS.wellConnected_of_mem_coneAt hU hy hx

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.5 (2) — well-connectedness passes to a larger set**

**Lemma 4.5 (2) of Bux–Kassmann–Schulze.** If $U' \subseteq U$ and $x$ is well-connected in
$U'$, then $x$ is well-connected in $U$.

Definition 4.4: $x$ is *well-connected in $U$* when some open neighbourhood $W$ of $x$ lies
entirely in one connected component of $G[U]$.

The reason is the source's, in one line: enlarging the open set only adds edges to the graph,
so connectivity can only improve — the neighbourhood that works for $U'$ works for $U$.

**Neither set is required to be open here.** The source states the lemma for "an inclusion of
open sets"; the argument needs only the inclusion, since $\mathrm{Edge}\ \Gamma\ U'$ implies
$\mathrm{Edge}\ \Gamma\ U$ whenever $U' \subseteq U$, and the witnessing neighbourhood carries
over unchanged. This is therefore slightly more general than the source's statement.

The other parts of Lemma 4.5 are `QFS.wellConnected_of_mem_coneAt` (1),
`QFS.exists_wellConnected` and `QFS.wellConnected_dense` (3). -/
theorem lemma_4_5_2 (h : U' ⊆ U) {x : E} (hx : WellConnected Γ U' x) :
    WellConnected Γ U x :=
  QFS.wellConnected_mono h hx

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.5 (3) — every nonempty open set has a well-connected point**

**Lemma 4.5 (3) of Bux–Kassmann–Schulze, the existence half.** Any nonempty open set $U$
contains a point that is well-connected in $U$.

Definition 4.4: $x$ is *well-connected in $U$* when some open neighbourhood $W$ of $x$ lies
entirely in one connected component of $G[U]$.

The proof is the source's: pick any $y \in U$; the cone $V^\Gamma[y]$ has points arbitrarily
close to its apex $y$, so $U \cap V^\Gamma[y]$ is nonempty, and part (1)
(`QFS.wellConnected_of_mem_coneAt`) makes each of its points well-connected in $U$.

The density half of part (3) — that the well-connected points are dense in $U$ — is
`QFS.wellConnected_dense`, which the source obtains by applying this existence statement to
smaller open sets and lifting with part (2). Both are `Proved`. -/
theorem lemma_4_5_3 (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, WellConnected Γ U x :=
  QFS.exists_wellConnected hU hne

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.5 (3) — the well-connected points are dense**

**Lemma 4.5 (3) of Bux–Kassmann–Schulze, the density half.** In an open set $U$, the points
well-connected in $U$ are dense: for every $y \in U$ and every $\varepsilon > 0$ there is a
point $x \in U \cap B_\varepsilon(y)$ that is well-connected in $U$.

Definition 4.4: $x$ is *well-connected in $U$* when some open neighbourhood $W$ of $x$ lies
entirely in one connected component of $G[U]$.

The proof is the source's: apply the existence statement (`QFS.exists_wellConnected`) to the
smaller open set $U \cap B_\varepsilon(y)$, then lift the conclusion to $U$ with part (2)
(`QFS.wellConnected_mono`), which is legitimate because well-connectedness only improves as
the ambient set grows.

Density is stated here in its $\varepsilon$-ball form rather than as a topological closure
statement, which is how Theorem 4.1's proof consumes it — it needs a well-connected point
*near a given point*, not merely somewhere in $U$. -/
theorem lemma_4_5_3_dense (hU : IsOpen U) {y : E} (hy : y ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ U ∩ ball y ε, WellConnected Γ U x :=
  QFS.wellConnected_dense hU hy hε

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Γ : Configuration E} {U U' : Set E}

namespace QFS.Paper

/-- **Lemma 4.6 — “über Bande”**

**Lemma 4.6 of Bux–Kassmann–Schulze**, the "über Bande" (off-the-cushion) step. Let
$x, y \in U$ and let $V = \Gamma(y)$ be the cone type of $y$. If the translated double cone
$V[x]$ contains a point $z$ of type $V$, then $x$ and $y$ are connected in $G[U]$.

Note, with the source, that $\Gamma(x)$ is **not** assumed to equal $V$: the connection is
made by bouncing off the third point $z$, which is where the name comes from.

The proof is the source's: $y$ and $z$ have the same type, so Lemma 4.3 joins them by an edge
path of length at most two; and $z \in V[x]$ gives $x \in V[z] = V^\Gamma[z]$, hence an edge
from $z$ to $x$.

**One hypothesis the source does not state: $z \in U$.** The source says only that $V[x]$
"contains a point $z$ of type $V$". But the edge from $z$ to $x$ requires $z$ to be a vertex
with an outgoing edge in $G[U]$, and the edge relation constrains the source of an edge to lie
in $U$; without $z \in U$ the conclusion does not follow from the argument given. It is
carried here explicitly. See the README's *Deviations*.

The hypothesis $x \in U$ is present, matching the source's "two points $x, y \in U$", but is
not used by the proof. As in Lemma 4.3, "of type $V$" is taken as equality of the underlying
sets rather than of the cone data, which is the weaker assumption. -/
theorem lemma_4_6 {x y z : E} (_hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U)
    (htype : (Γ z).carrier = (Γ y).carrier) (hzx : z ∈ shift (Γ y).carrier x) :
    Conn Γ U x y :=
  QFS.ueber_bande _hx hy hz htype hzx

end QFS.Paper

end

/-! ## Section 5 -/

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}

namespace QFS.Paper

/-- **Lemma 5.1 (1) — A lattice point deep inside a cone, at controlled distance from the apex**

Let $v \in \mathbb{R}^d$ be a unit vector, $\lVert v\rVert = 1$, and let $\vartheta, \vartheta_V$ be angles with

$$0 < \vartheta \le \vartheta_V \le \pi/2 .$$

Write $\tilde V(v,\vartheta_V) = \{ h \ne 0 : \cos \vartheta_V < \langle v, h\rangle / \lVert h\rVert \}$ for the (one-sided, open) cone with axis $v$ and apex angle $\vartheta_V$, and $\tilde V(v,\vartheta_V)[x] = x + \tilde V(v,\vartheta_V)$ for the same cone based at a point $x$. Let $r > 0$ and let $R$ satisfy

$$R \;>\; \frac{r + \sqrt{d}}{\sin \vartheta}.$$

Then for **every** apex $x \in \mathbb{R}^d$ there is a lattice point $y \in \mathbb{Z}^d$ that is simultaneously

$$\lVert y - x\rVert < R, \qquad y \in \tilde V(v,\vartheta_V)[x], \qquad \overline{B}(y, r) \subseteq \tilde V(v,\vartheta_V)[x] .$$

That is: not merely does the cone based at any point contain a lattice point within distance $R$ of the apex, but it contains one whose entire closed $r$-ball still lies in the cone — a lattice point at depth $r$ inside the cone.

The role of the hypothesis $\vartheta \le \vartheta_V$ is to make the radius threshold uniform: $R$ is chosen once from the *smallest* admissible aperture $\vartheta$ and then works for every cone of aperture at least $\vartheta$, and for every apex, which is what allows a single radius to serve an entire $\vartheta$-bounded configuration.

**Formalization Note.** The cone is the open one from the strict inequality $\cos\vartheta_V < \langle v,h\rangle/\lVert h\rVert$ with $0$ excluded, and the shift is `shift S x = {y | y - x ∈ S}`. The threshold on $R$ is strict, and $\sin \vartheta > 0$ by $0 < \vartheta \le \pi/2$. -/
theorem lemma_5_1_1 {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ ϑV : ℝ} (hϑ : 0 < ϑ) (hϑV : ϑ ≤ ϑV) (hϑV' : ϑV ≤ π / 2)
    {r R : ℝ} (hr : 0 < r) (hR : (r + Real.sqrt d) / Real.sin ϑ < R)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∃ y ∈ lattice d, ‖y - x‖ < R ∧ y ∈ shift (cone v ϑV) x ∧
      closedBall y r ⊆ shift (cone v ϑV) x :=
  QFS.exists_lattice_mem_cone hv hϑ hϑV hϑV' hr hR x

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}

namespace QFS.Paper

/-- **Lemma 5.1 (2) — a lattice point in the intersection of two nearby cones**

**Lemma 5.1 (2) of Bux–Kassmann–Schulze.** Let $\tilde V$ be a cone of apex angle at least
$\vartheta$, and let $x, y$ satisfy $\lVert x - y\rVert < r$. If
$R > \frac{r + \sqrt d}{\sin\vartheta} + r$, then

$$B_R(x) \cap \tilde V[x] \cap B_R(y) \cap \tilde V[y]$$

contains a lattice point.

The proof is the source's: part (1) supplies a lattice point $z$ with
$B_r(z) \subseteq B_{(r+\sqrt d)/\sin\vartheta}(x) \cap \tilde V[x]$; then $z \in \tilde V[y]$
because $\tilde V[y]$ is a translate of $\tilde V[x]$ by less than $r$, and $z \in B_R(y)$ by
the triangle inequality.

**The bound at $x$ is sharper than stated.** The conclusion here gives
$\lVert z - x\rVert < R - r$, not merely $< R$ — the $r$ of the triangle-inequality step is
spent only at $y$. That extra room is what Corollary 5.2 needs.

Part (1) of Lemma 5.1 is `QFS.exists_lattice_mem_cone`. Both are `Proved`. The cone is a
single half-cone with unit axis and apex angle between $\vartheta$ and $\pi/2$, matching the
source's "a cone $\tilde V$ of apex angle at least $\vartheta$"; nothing ties it to a
configuration. -/
theorem lemma_5_1_2 {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ ϑV : ℝ} (hϑ : 0 < ϑ) (hϑV : ϑ ≤ ϑV) (hϑV' : ϑV ≤ π / 2)
    {r R : ℝ} {x y : EuclideanSpace ℝ (Fin d)} (hxy : ‖x - y‖ < r)
    (hR : (r + Real.sqrt d) / Real.sin ϑ + r < R) :
    ∃ z ∈ lattice d, ‖z - x‖ < R - r ∧ ‖z - y‖ < R ∧
      z ∈ shift (cone v ϑV) x ∧ z ∈ shift (cone v ϑV) y :=
  QFS.exists_lattice_mem_inter hv hϑ hϑV hϑV' hxy hR

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}

namespace QFS.Paper

/-- **Corollary 5.2 as connectivity within a ball**

**Corollary 5.2 of Bux–Kassmann–Schulze**, with the conclusion recorded as connectivity
confined to a ball rather than as an explicit two-edge path: two lattice points of the same cone
type at distance less than $r$ are joined by an edge path staying inside
$B_R(x) \cap \mathbb{Z}^d$.

`QFS.discr_connect_two_of_same_type_two` is the quantitative form, exhibiting the single
intermediate lattice point and bounding each of the two edges by $R$. This form is what
Lemma 5.7's induction chains with, where the confinement is what matters and the length bound is
not reused. Both are `Proved`.

**The radius is $R > \frac{r+\sqrt d}{\sin\vartheta} + r$, where the source prints
$R = \frac{r+\sqrt d}{\sin\vartheta}$** — the radius of Lemma 5.1 (1) rather than of
Lemma 5.1 (2), which is what a two-edge path needs. -/
theorem corollary_5_2 (hϑ : 0 < ϑ) (hb : ∀ z, ϑ ≤ (Γ z).apex)
    {r R : ℝ} {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ lattice d) (hy : y ∈ lattice d)
    (htype : (Γ x).carrier = (Γ y).carrier) (hxy : ‖x - y‖ < r)
    (hR : (r + Real.sqrt d) / Real.sin ϑ + r < R) :
    ConnWithin Γ (ball x R ∩ lattice d) x y :=
  QFS.discr_connect_two_of_same_type hϑ hb hx hy htype hxy hR

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}

namespace QFS.Paper

/-- **Lemma 5.4 — discrete density of well-connected lattice points**

**Lemma 5.4 of Bux–Kassmann–Schulze**, the discrete counterpart of Lemma 4.5 (3). For any
$r \ge 0$, any $R > \frac{\sqrt d + r}{\sin\vartheta}$, and any lattice point $x$, there is an
$r$-$R$-connected lattice point $y$ with $\lVert y - x \rVert < R$.

Definition 5.3: $y$ is *$r$-$R$-connected* when every lattice point of $B_r(y)$ is joined to
$y$ by an edge path that stays inside $B_R(y) \cap \mathbb{Z}^d$.

The proof is the source's: $R$ is large enough that $B_R(x) \cap V^\Gamma[x]$ contains a
lattice point $y$ whose $r$-ball lies inside $V^\Gamma[x]$; then any two points of $B_r(y)$
are joined through $x$, and $x$ is within $R$ of $y$.

The hypotheses and the constant are the source's exactly, including the non-strict $r \ge 0$
and the strict inequality on $R$. The configuration is required only to have apex angles
bounded below by $\vartheta > 0$; no upper bound on $\vartheta$ is assumed. -/
theorem lemma_5_4 (hϑ : 0 < ϑ) (hb : ∀ z, ϑ ≤ (Γ z).apex) {r R : ℝ} (hr : 0 ≤ r)
    (hR : (Real.sqrt d + r) / Real.sin ϑ < R) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) :
    ∃ y ∈ lattice d, ‖y - x‖ < R ∧ RRConnected Γ r R y :=
  QFS.exists_rrConnected hϑ hb hr hR hx

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}

namespace QFS.Paper

/-- **Lemma 5.5 — Connecting two lattice points via a third of the same cone type**

Work in Euclidean space $\mathbb{R}^d$ with the integer lattice $\mathbb{Z}^d$. Let $\Gamma$ be a configuration, assigning to each point $w$ a double cone $\Gamma(w)$ with apex angle $(\Gamma w).\mathrm{apex} \in (0,\pi/2]$, unit axis $v_w$ and carrier
$$(\Gamma w).\mathrm{carrier} \;=\; \tilde V\bigl(v_w, (\Gamma w).\mathrm{apex}\bigr) \cup \bigl(-\tilde V(v_w, (\Gamma w).\mathrm{apex})\bigr), \qquad \tilde V(v,\vartheta) = \Bigl\{h \ne 0 : \cos\vartheta < \tfrac{\langle v,h\rangle}{\lVert h\rVert}\Bigr\}.$$
Write $S[x] = x + S$ for the translate of a set $S$ by $x$, and $V^{\Gamma}[a] = a + (\Gamma a).\mathrm{carrier}$. Finally, $\mathrm{ConnWithin}(\Gamma, T, y, x)$ is the reflexive–transitive closure of the relation "$a, b \in T$ and ($b \in V^\Gamma[a]$ or $a \in V^\Gamma[b]$)", i.e. the property that $y$ and $x$ are joined by an edge path all of whose vertices lie in the set $T$.

Assume $\vartheta > 0$ and that every cone of the configuration is at least this wide:
$$\vartheta \le (\Gamma w).\mathrm{apex} \quad \text{for all } w \in \mathbb{R}^d .$$
Let $r, R \in \mathbb{R}$ and let $x, y, z \in \mathbb{Z}^d$ be lattice points such that

- $\|x - y\| < r$ and $\|z - x\| < r$;
- $z$ lies in the cone of $y$ translated to have apex $x$, i.e. $z \in x + (\Gamma y).\mathrm{carrier}$;
- $z$ and $y$ carry the *same* cone type, $(\Gamma z).\mathrm{carrier} = (\Gamma y).\mathrm{carrier}$;
- the outer radius satisfies
$$r + \frac{2r + \sqrt{d}}{\sin \vartheta} < R .$$

Then
$$\mathrm{ConnWithin}\big(\Gamma,\; B_R(x) \cap \mathbb{Z}^d,\; y,\; x\big),$$
that is, $y$ and $x$ are connected by an edge path whose vertices are lattice points of the open ball $B_R(x)$.

This is the "bank shot" step of the discrete chaining: two nearby lattice points that are not directly joined are connected by routing through a third point of a common cone type, and the whole detour is confined to a ball whose radius is controlled explicitly by $r$, $d$ and the aperture bound $\vartheta$. Confinement, not mere connectedness, is the point: the later multiplicity counts need to know how far a path may wander.

**Formalization Note.** The quantitative hypothesis mixes $r$ and $\sqrt{d}$ in the numerator $2r + \sqrt{d}$, the $\sqrt{d}$ accounting for the density of the lattice (every closed ball of radius $\sqrt d/2$ contains a lattice point); the division by $\sin \vartheta$ is legitimate because $\vartheta > 0$, and the hypothesis is stated as a strict inequality, so $R$ is genuinely larger than the detour bound. -/
theorem lemma_5_5 (hϑ : 0 < ϑ) (hb : ∀ w, ϑ ≤ (Γ w).apex)
    {r R : ℝ} {x y z : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ lattice d) (hy : y ∈ lattice d) (hz : z ∈ lattice d)
    (hxy : ‖x - y‖ < r) (hzx : ‖z - x‖ < r) (hzV : z ∈ shift (Γ y).carrier x)
    (htype : (Γ z).carrier = (Γ y).carrier)
    (hR : r + (2 * r + Real.sqrt d) / Real.sin ϑ < R) :
    ConnWithin Γ (ball x R ∩ lattice d) y x :=
  QFS.discr_ueber_bande hϑ hb hx hy hz hxy hzx hzV htype hR

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}

namespace QFS.Paper

/-- **Lemma 5.6 — bounded jumps toward the tip of a cone**

**Lemma 5.6 of Bux–Kassmann–Schulze.** There is a constant $\delta > 0$, depending only on
$\vartheta$ and the dimension, such that for every double cone $V$ with apex angle at least
$\vartheta$: if $x$ is a lattice point of $V$ and $V$ contains a lattice point closer to the
origin than $x$, then it contains such a point **within distance $\delta$ of $x$**.

$\delta$ is produced before $V$ and before $x$, which is the content of "depending only on
$\vartheta$ and the dimension $d$".

**The cone is any double cone with apex angle at least $\vartheta$**, where the source says
"any double cone $V \in \Gamma(\mathbb{Z}^d)$" — a cone realised by the configuration. Since
every realised cone of a $\vartheta$-bounded configuration has apex angle at least
$\vartheta$, this is the weaker hypothesis and so the more general statement; nothing ties
$V$ to a configuration.

The source calls the assertion obvious and states the consequence it wants in the following
sentence: one can descend from $x$ within $V$ to a lattice point of minimum distance to the
tip by a chain of jumps each of length at most $\delta$. That consequence is
`QFS.exists_min_chain_in_cone`. Both are `Proved`.

"Closer to the tip" is measured by the norm, the tip being the origin: the cone is centred at
$0$ and translated where it is used. -/
theorem lemma_5_6 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex →
      ∀ x ∈ lattice d, x ∈ V.carrier →
        (∃ z ∈ lattice d, z ∈ V.carrier ∧ ‖z‖ < ‖x‖) →
        ∃ y ∈ lattice d, y ∈ V.carrier ∧ ‖y‖ < ‖x‖ ∧ ‖y - x‖ < δ :=
  QFS.exists_closer_lattice_nearby hϑ hϑ'

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}

namespace QFS.Paper

/-- **Lemma 5.6 in full — the descent chain to a point of minimum distance**

**Lemma 5.6 of Bux–Kassmann–Schulze, the "I.e." clause.** There is a constant $\delta > 0$
depending only on $\vartheta$ and the dimension such that for every double cone $V$ with apex
angle at least $\vartheta$ and every lattice point $x \in V$, there is a lattice point
$m \in V$ **of minimum norm among the lattice points of $V$**, reachable from $x$ by a chain
of steps inside $V$ each of length at most $\delta$.

This is the source's own restatement of Lemma 5.6: "we can go from $x$ within $V$ to a lattice
point of minimum distance to the tip via a chain of jumps each bounded in length from above by
$\delta$." The single-step form is `QFS.exists_closer_lattice_nearby`.

Two things the phrase "of minimum distance" hides and this statement makes explicit. The
minimum is **attained** — $m$ satisfies $\lVert m \rVert \le \lVert w \rVert$ for every
lattice point $w$ of $V$, which requires an argument since $V \cap \mathbb{Z}^d$ is infinite.
And the chain is a reflexive-transitive closure, so $x$ itself may already be minimal and the
chain empty.

$\delta$ is produced before $V$ and $x$. As in the single-step form, $V$ is any double cone
with apex angle at least $\vartheta$, not only one realised by a configuration. -/
theorem lemma_5_6_chain {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex →
      ∀ x ∈ V.carrier ∩ lattice d,
        ∃ m ∈ V.carrier ∩ lattice d,
          (∀ w ∈ V.carrier ∩ lattice d, ‖m‖ ≤ ‖w‖) ∧
          Relation.ReflTransGen (Jump V.carrier 0 δ) x m :=
  QFS.exists_min_chain_in_cone hϑ hϑ'

end QFS.Paper

end

section

namespace QFS.Paper

/-- **Lemma 5.7 — the core induction on cone types**

“There are constants $r_1 \le \rho_1 \le R_1$, $r_2 \le \rho_2 \le R_2, \ldots$, depending only on $\vartheta$ and $d$, with $\delta < r_1$ and $r_i < r_{i+1}$, $\rho_i < \rho_{i+1}$, $R_i < R_{i+1}$ for every $i \in \mathbb{N}$ such that any lattice point $x \in \mathbb{Z}^d$ is $r_k$-$R_k$-connected provided at most $k$ cone types are realized at the lattices points in $B_{\rho_k}(x)$.” (p. 21) -/
theorem lemma_5_7 {d : ℕ} {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ V : DCone (EuclideanSpace ℝ (Fin d)), ϑ ≤ V.apex → ∀ x ∈ lattice d, x ∈ V.carrier →
        (∃ z ∈ lattice d, z ∈ V.carrier ∧ ‖z‖ < ‖x‖) →
        ∃ y ∈ lattice d, y ∈ V.carrier ∧ ‖y‖ < ‖x‖ ∧ ‖y - x‖ < δ) ∧
      ∃ r ρ R : ℕ → ℝ, δ < r 1 ∧
        (∀ i : ℕ, 1 ≤ i → r i ≤ ρ i ∧ ρ i ≤ R i ∧
          r i < r (i + 1) ∧ ρ i < ρ (i + 1) ∧ R i < R (i + 1)) ∧
        ∀ k : ℕ, 1 ≤ k → ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), (∀ z, ϑ ≤ (Γ z).apex) →
          ∀ x ∈ lattice d, (typesIn Γ (Metric.ball x (ρ k))).encard ≤ (k : ℕ∞) →
            RRConnected Γ (r k) (R k) x :=
  QFS.lemmaFiveSeven hϑ hϑ'

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
  {S S' : Set (EuclideanSpace ℝ (Fin d))}
variable {ϑ : ℝ}
variable {Γ : Configuration (EuclideanSpace ℝ (Fin d))}

namespace QFS.Paper

/-- **Corollary 5.8 — Uniform outer radius for lattice connectivity of bounded configurations**

Work in Euclidean space $\mathbb{R}^d$ with the integer lattice $\mathbb{Z}^d$. Call a configuration $\Gamma'$ *$\vartheta$-bounded* (`IsBounded Γ' ϑ`) when $0 < \vartheta$ and every double cone it assigns has apex angle at least $\vartheta$, i.e. $\vartheta \le (\Gamma' z).\mathrm{apex}$ for all $z$. Write $V^{\Gamma'}[a] = a + (\Gamma' a).\mathrm{carrier}$, let $\mathrm{ConnWithin}(\Gamma', T, a, b)$ be the reflexive–transitive closure of "$a,b \in T$ and ($b \in V^{\Gamma'}[a]$ or $a \in V^{\Gamma'}[b]$)", and let
$$\mathrm{RRConnected}(\Gamma', r, R, x) \quad :\Longleftrightarrow \quad \forall\, y \in B_r(x) \cap \mathbb{Z}^d, \ \ \mathrm{ConnWithin}\bigl(\Gamma',\ B_R(x) \cap \mathbb{Z}^d,\ x,\ y\bigr)$$
be Definition 5.3: every lattice point within distance $r$ of $x$ is joined to $x$ by an edge path whose vertices are all lattice points of $B_R(x)$.

Let $\vartheta$ satisfy $0 < \vartheta \le \pi/2$ and let $r \in \mathbb{R}$. Then there exists $R \in \mathbb{R}$ with $r \le R$ such that
$$\text{for every }\vartheta\text{-bounded configuration }\Gamma' \text{ and every } x \in \mathbb{Z}^d: \quad \mathrm{RRConnected}(\Gamma', r, R, x).$$

The essential feature is the order of the quantifiers: the outer radius $R$ is produced *before* the configuration is named, so it depends only on the dimension $d$, the aperture bound $\vartheta$ and the inner radius $r$ — never on $\Gamma'$ or on the point $x$. This uniformity is what makes the discrete connectivity usable as a template: a single constant serves all admissible configurations simultaneously, which is exactly what the later multiplicity counts and renormalization arguments require.

**Formalization Note.** The hypothesis $0 < r$ is present in the statement but is marked as unused (`_hr`), so the conclusion is in fact established without it; it is retained only to match the shape in which the result is applied. Note also that no lower bound of the form $r \le R$ beyond the stated one, and no positivity of $R$, is asserted. -/
theorem corollary_5_8 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {r : ℝ} (_hr : 0 < r) :
    ∃ R : ℝ, r ≤ R ∧ ∀ Γ' : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ' ϑ →
      ∀ x ∈ lattice d, RRConnected Γ' r R x :=
  QFS.discrete_template hϑ hϑ' _hr

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 5.9 — A cube at the shrunk aperture is seen in the full cone from an entire cube**

Fix a dimension $d$ and an angle $\vartheta$ with $0 < \vartheta \le \pi/2$, let $v \in \mathbb{R}^d$ be a unit vector, and let $\ell > 0$. Write
$$\tilde V(v,\vartheta) = \{\,h \ne 0 : \langle v,h\rangle/\|h\| > \cos\vartheta\,\}$$
for the (single) cone with axis $v$ and apex angle $\vartheta$, write $S[z] = z + S$ for the translate of a set, write
$$\bar A_\ell(u) = \{\,y : \|y-u\|_\infty \le \ell/2\,\}$$
for the closed cube of side $\ell$ centred at $u$, and put
$$\delta \;=\; \frac{\sqrt{d}+1}{\sin(\vartheta/2)} .$$
Let $x, y \in \mathbb{R}^d$ satisfy the separation condition $\|x-y\| \ge \delta\,\ell$ and the cone condition $y \in \tilde V(v,\vartheta/2)[x]$, i.e. $y$ lies in the *half-aperture* cone based at $x$. Then
$$\bar A_\ell(y) \;\subseteq\; \bigcap_{z \in \bar A_\ell(x)} \tilde V(v,\vartheta)[z] ,$$
that is, every point of the cube of side $\ell$ around $y$ lies in the full-aperture cone based at **every** point of the cube of side $\ell$ around $x$.

This is the renormalisation step that lets whole blocks replace single points: if two points are far apart relative to the block size and one sees the other in the shrunk cone, then the entire block at $y$ is seen in the full cone from the entire block at $x$. It is precisely what turns a cone relation between lattice points into an edge between blocks.

**Formalization Note.** The constant $\delta = (\sqrt{d}+1)/\sin(\vartheta/2)$ is used here in place of the smaller value $3\sqrt{d}/(2\sin\vartheta)$; the cubes are closed cubes for the maximum norm, so $\bar A_\ell(u)$ is the closed $\ell/2$-ball of $\|\cdot\|_\infty$. -/
theorem lemma_5_9 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hdist : apexShrinkConst d ϑ * ℓ ≤ ‖x - y‖) (hy : y ∈ shift (cone v (ϑ / 2)) x) :
    closedCube ℓ y ⊆ ⋂ z ∈ closedCube ℓ x, shift (cone v ϑ) z :=
  QFS.renormalization_apex_shrink hϑ hϑ' hv hℓ hdist hy

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 5.9's threshold in the source is too small, for every apex angle**

A witness for a defect in the source. The proof of Lemma 5.9 uses a threshold distance below which an apex-shrinking estimate is claimed to apply. This theorem shows that threshold is insufficient **for every admissible apex angle** $\vartheta \in (0,\pi/2]$: the gap it guarantees, $\ell\sqrt d\,\sin(\vartheta/2)/(2\sin\vartheta)$, is strictly less than the $\ell\sqrt d/2$ the estimate requires.

The formalization therefore uses the corrected constant $(\sqrt d + 1)/\sin(\vartheta/2)$ in place of the source's $3\sqrt d/(2\sin\vartheta)$. This is not a counterexample to Lemma 5.9 itself, which is true; it shows the stated proof does not establish it at the stated threshold. -/
theorem lemma_5_9_threshold_too_small {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {c : ℝ} (hc : 0 < c) :
    c * Real.sin (ϑ / 2) / (2 * Real.sin ϑ) < c / 2 :=
  QFS.paper_threshold_insufficient hϑ hϑ' hc

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Proposition 5.14 — connectivity in the favored graph of a sparsely populated town**

**Proposition 5.14 of Bux–Kassmann–Schulze**, on the *favored graph* of Definition 5.13.

Fix $d$ and an angle $0 < \vartheta \le \pi/2$, and let $r > 0$. Then there is a radius
$R \ge r$ — depending on $r$, $\vartheta$ and $d$ only, and in particular on neither the
configuration nor the town — such that for every $\vartheta$-bounded configuration
$\Gamma$, all scales $h, \ell > 0$ with the town $T(h,\ell)$ *sparsely populated*, and all
index-lattice points $z, x, y$ with $\lVert x - z\rVert \le r$ and $\lVert y - z\rVert \le r$,
the blocks $Q_\ell(hx)$ and $Q_\ell(hy)$ are joined by an undirected edge path in the
favored graph, all of whose blocks lie in the town ball
$\{\,Q_\ell(hp) : p \in \mathbb{Z}^d,\ \lVert p - z\rVert < R\,\}$.

Here $Q_\ell(u) = \mathbb{Z}^d \cap \bar A_\ell(u)$ is the block of lattice points in the
closed cube of edge $\ell$ centred at $u$. A cone $V$ is **favored by majority** in a block
$Q$ (Definition 5.11) when its fibre $\{x \in Q : \Gamma(x) = V\}$ is of maximal size among
all cones. Definition 5.13's **favored graph** puts an edge from $Q$ to $P$ when *some* cone
$V$ favored by majority in $Q$ satisfies $y \in V[x]$ for all $x \in Q$, $y \in P$; this
statement uses the undirected graph, so the step relation is `FavoredEdge Γ Q P ∨ FavoredEdge Γ P Q`.

**The existential over favored cones is inside the edge relation**, which is the point of
Definition 5.13 and of Remark 5.12: the majority cone of a block is in general *not unique*,
and the favored graph lets each edge pick its own. A variant of this proposition,
`QFS.renormalization_choice`, first fixes one favored cone per block globally and concludes
connectivity in the resulting smaller *choice* graph; whenever $W$ picks majority cones its edges are
edges of this graph, so its conclusion is stronger — but it
also assumes $\ell \ge 1$, which the source does not, so neither statement implies the other. The choice
graph is not in the source; it was introduced to carry a later step that needs one
representative per block to serve both of its incident edges. **This statement is the
source's Proposition 5.14.**

*Sparse population* is `apexShrinkConst d ϑ < h / ℓ`, where the constant is
$(\sqrt d + 1)/\sin(\vartheta/2)$. The source's Definition 5.10 puts the constant $\delta$ of
its Lemma 5.9 here, but that $\delta = 3\sqrt d/(2\sin\vartheta)$ is too small for Lemma 5.9's
own proof, for every admissible $\vartheta$ — see `QFS.paper_threshold_insufficient`. The
corrected constant is used throughout.

Two points of exactness. The endpoints are required within distance $r$ of $z$ **non-strictly**,
while the path is confined to the ball of radius $R$ **strictly** — a slightly stronger
confinement than the source's "not farther away from $z$ than $hR$". And distances are between
*indices*: $\lVert x - z\rVert \le r$ means the block centres $hx$ and $hz$ are within $hr$,
which is how the source phrases it. The connectivity is a
reflexive-transitive closure, so a block is trivially connected to itself, and the step
relation carries no $Q \ne P$ condition. -/
theorem proposition_5_14 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, r ≤ R ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h ℓ : ℝ, 0 < h → 0 < ℓ → SparselyPopulated d ϑ h ℓ →
      ∀ z ∈ lattice d, ∀ x ∈ lattice d, ∀ y ∈ lattice d,
        ‖x - z‖ ≤ r → ‖y - z‖ ≤ r →
        FavoredConn Γ (townBall h ℓ z R) (townIndex h ℓ x) (townIndex h ℓ y) :=
  QFS.renormalization hϑ hϑ' hr

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Theorem 5.15 — the path properties**

“Let $\Gamma : \mathbb{Z}^d \to \mathcal{V}$ be a configuration with apex angles bounded from below by $\vartheta > 0$. Let $R_0 > 0$. There exist positive numbers $N$ and $M$ and a constant $\lambda \ge R_0$, all independent of $\Gamma$, and a collection $(p_{xy})_{x,y\in\mathbb{Z}^d}$ of unoriented edge paths in $G$ such that the following holds: (1) The path $p_{xy}$ starts at $x$ and ends at $y$. (2) Any path $p_{xy}$ has at most $N$ edges. (3) Any edge of $G$ is used in at most $M$ paths $p_{xy}$. (4) Any edge in $p_{xy}$ has length comparable to $|x-y|$ with constant $\lambda$.” (pp. 24–25) -/
theorem theorem_5_15 (hd : 1 ≤ d) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (R₀ : ℝ) :
    PathPropsHolds d ϑ R₀ :=
  QFS.path_props hd hϑ hϑ' R₀

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Theorem 5.15 — the path properties, with only the lower bound on the apex angles**

**Theorem 5.15 of Bux–Kassmann–Schulze**, hypothesised exactly as the source states it:
"Let $\Gamma : \mathbb{Z}^d \to \mathcal V$ be a configuration with apex angles bounded from
below by $\vartheta > 0$." Only $\vartheta > 0$ is assumed — no upper bound.

For $d \ge 1$, any $\vartheta > 0$ and any real $R_0$, there exist $N \ge 1$, $M \ge 1$ and
$\lambda \ge R_0$ such that **for every** $\vartheta$-bounded configuration $\Gamma$ there is
a family of walks $p_{x,y}$ in the lattice graph of $\Gamma$, one for each ordered pair of
lattice points, with:

- **(1)** $p_{x,y}$ runs from $x$ to $y$ — carried by the type of the walk;
- **(2)** $\operatorname{length}(p_{x,y}) \le N$, one bound for all pairs, with no dependence
  on $\lVert x-y\rVert$;
- **(3)** every unordered pair $e$ lies on at most $M$ of the walks, counted over **ordered**
  pairs $(x,y)$;
- **(4)** every edge of $p_{x,y}$ has length comparable to the endpoints' separation:
  $\lambda^{-1}\lVert x-y\rVert \le \lVert u-w\rVert \le \lambda\lVert x-y\rVert$.

$N$, $M$ and $\lambda$ are chosen **before** $\Gamma$ — "all independent of $\Gamma$" in the
source — so they are uniform over all $\vartheta$-bounded configurations; the family $p$ is
chosen after and may depend on $\Gamma$. Edges join lattice points, at least one of which
sees the other inside its own double cone.

**Why this form and not `QFS.path_props`.** That statement carries the extra hypothesis
$\vartheta \le \pi/2$, which the source does not state. Since every double cone here has apex
angle at most $\pi/2$ by construction (Definition 2.1), a $\vartheta$ above $\pi/2$ bounds no
configuration at all; but the conclusion `PathPropsHolds` still asserts the existence of
$N, M, \lambda$ with $R_0 \le \lambda$, so the uncapped statement is genuinely more general
and is obtained from the capped one by replacing $\vartheta$ with $\min(\vartheta, \pi/2)$.

$R_0$ enters the conclusion **only** through $R_0 \le \lambda$; it puts no lower bound on
edge lengths. The development also proves a strictly stronger form, `PathPropsLong`, which
adds $R_0 < \lVert e\rVert$ for every edge — an extra clause the source does not state, and
which Section 6 needs; see `QFS.path_props_long`. -/
theorem theorem_5_15_as_printed (hd : 1 ≤ d) {ϑ : ℝ} (hϑ : 0 < ϑ) (R₀ : ℝ) :
    PathPropsHolds d ϑ R₀ :=
  QFS.path_props_of_pos hd hϑ R₀

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma 5.16 — The first jump: connecting an arbitrary point to a block at each scale**

Let $d \in \mathbb{N}$ and let $\vartheta \in \mathbb{R}$ with $0 < \vartheta \le \pi/2$. Let $\Delta \in \mathbb{R}$ be a scale step satisfying both
$$\delta(d,\vartheta) \;=\; \frac{\sqrt{d} + 1}{\sin(\vartheta/2)} \;<\; \Delta \qquad\text{and}\qquad 1 \le \Delta,$$
where $\delta(d,\vartheta)$ is the apex-shrinking constant of Lemma 5.9 — the corrected one, the paper's $3\sqrt{d}/(2\sin\vartheta)$ being too small. Then there exists a radius $R_1 \ge 1$ with the following property.

For every configuration $\Gamma$ on $\mathbb{R}^d$ that is $\vartheta$-bounded, meaning $0 < \vartheta$ and $\vartheta \le (\Gamma x).\mathrm{apex}$ for every $x$, for every point $x \in \mathbb{R}^d$ and every $n \in \mathbb{N}$, there is a lattice point $w \in \mathbb{Z}^d$ such that the block
$$Q_{\Delta^n}\bigl(\Delta^{n+1} w\bigr) \;=\; \mathbb{Z}^d \cap \Bigl\{y : \lVert y - \Delta^{n+1}w\rVert_\infty \le \tfrac{\Delta^n}{2}\Bigr\}$$
of side $\Delta^n$ centred at $\Delta^{n+1} w$ satisfies

$$Q_{\Delta^n}\bigl(\Delta^{n+1} w\bigr) \;\subseteq\; B\bigl(x,\ \Delta^{n+1} R_1\bigr) \,\cap\, V^{\Gamma}[x],$$

and moreover every point $q$ of that block is far from $x$:
$$\lVert q - x\rVert \;\ge\; \Delta^{n} \qquad \text{for all } q \in Q_{\Delta^n}\bigl(\Delta^{n+1}w\bigr).$$

Here $B(x, r)$ is the open Euclidean ball, $\lVert u\rVert_\infty = \sup_i |u_i|$, and $V^\Gamma[x] = x + |\Gamma(x)|$ is the (double) cone of the configuration translated so that its apex sits at $x$.

This is Lemma 5.16, the "first jump": it shows that from an arbitrary starting point one can always reach an entire block of the town at scale $n$ in a single step of the graph — every point of the block is visible from $x$ inside its cone — while paying a bounded price, the block sitting within distance $\Delta^{n+1}R_1$ of $x$ and no closer than $\Delta^n$. The two-sided distance control is what makes the jump usable as the first and last edge of the walks assembled at each scale, since the lower bound is exactly what the kernel comparison requires and the upper bound is what keeps the walk's edges proportional to $\lVert x-y\rVert$.

**Formalization Note.** The radius $R_1$ is chosen *before* the configuration, the point and the scale, so it is uniform in all three; it depends only on $d$, $\vartheta$ and $\Delta$. The whole family of blocks is indexed by lattice points $w \in \mathbb{Z}^d$ rescaled by $\Delta^{n+1}$, so the centre $\Delta^{n+1}w$ ranges over the lattice at the coarser scale while the block itself has the finer side $\Delta^n$. -/
theorem lemma_5_16 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {Δ : ℝ} (hΔδ : apexShrinkConst d ϑ < Δ) (hΔ1 : 1 ≤ Δ) :
    ∃ R₁ : ℝ, 1 ≤ R₁ ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ (x : EuclideanSpace ℝ (Fin d)) (n : ℕ),
        ∃ w ∈ lattice d,
          block (Δ ^ n) (Δ ^ (n + 1) • w) ⊆ ball x (Δ ^ (n + 1) * R₁) ∩ coneAt Γ x ∧
          ∀ q ∈ block (Δ ^ n) (Δ ^ (n + 1) • w), Δ ^ n ≤ ‖q - x‖ :=
  QFS.connect_first_jump hϑ hϑ' hΔδ hΔ1

end QFS.Paper

end

/-! ## Appendix A -/

section
open scoped ENNReal

namespace QFS.Paper

/-- **Lemma A.1 for balls — the enlarged-ball bound gives the same-ball bound**

“Let $\alpha \in (0,2)$ and $\kappa \ge 1$. For $B = B_R(x_0)$, $R > 0$, $x_0 \in \mathbb{R}^d$ we set $B^* = B_{\kappa R}(x_0)$. Let $k : \mathbb{R}^d \times \mathbb{R}^d \to \mathbb{R}$ be a symmetric kernel that satisfies (2). Suppose that for some $c > 0$
$$c\int_{B\times B}(f(x)-f(y))^2|x-y|^{-d-\alpha}\,\mathrm{d}(x,y) \le \int_{B^*\times B^*}(f(x)-f(y))^2k(x,y)\,\mathrm{d}(x,y)$$
for every ball $B \subset \mathbb{R}^d$ and every $f \in H_k(B^*)$. Then for every bounded Lipschitz domain $\Omega \subset \mathbb{R}^d$ there exists a constant $\tilde c = \tilde c(d,\kappa,\alpha,\Omega) > 0$ such that for every $f \in H_k(\Omega)$
$$\tilde c\,c\int_{\Omega\times\Omega}(f(x)-f(y))^2|x-y|^{-d-\alpha}\,\mathrm{d}(x,y) \le \int_{\Omega\times\Omega}(f(x)-f(y))^2k(x,y)\,\mathrm{d}(x,y).$$
The constant $\tilde c$ depends on the domain $\Omega$ only up to scaling. In particular, if $\Omega$ is a ball, the constant can be chosen independently of $\Omega$. For $0 < \alpha_0 \le \alpha < 2$, the constant $\tilde c$ depends on $\alpha_0$ but not on $\alpha$.” (pp. 29–30)

**No measurability of $k$ is assumed.** Both forms are lower Lebesgue integrals, and along a fixed
function the kernel's form agrees on every set with the form of a measurable kernel
(`QFS.exists_measurable_kernel_form_eq`), which is all the proof needs. -/
theorem lemma_A_1 (d : ℕ) :
    ∀ α₀ κ : ℝ, 0 < α₀ → 1 ≤ κ →
    ∃ c' : ℝ, 0 < c' ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ (Λ : ℝ) (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      KernelBounds Γ α Λ k →
      ∀ c : ℝ, 0 < c →
      (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ (κ * R)) k f) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ R)) →
        ENNReal.ofReal (c' * c) * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ R) k f :=
  QFS.lemmaAOne_ball d

end QFS.Paper

namespace QFS.Paper

open scoped Pointwise

/-- **Lemma A.1 — bounded Lipschitz domains, with the scaling and $\alpha_0$ clauses**

“Let $\alpha \in (0,2)$ and $\kappa \ge 1$. For $B = B_R(x_0)$, $R > 0$, $x_0 \in \mathbb{R}^d$ we set $B^* = B_{\kappa R}(x_0)$. Let $k : \mathbb{R}^d \times \mathbb{R}^d \to \mathbb{R}$ be a symmetric kernel that satisfies (2). Suppose that for some $c > 0$
$$c\int_{B\times B}(f(x)-f(y))^2|x-y|^{-d-\alpha}\,\mathrm{d}(x,y) \le \int_{B^*\times B^*}(f(x)-f(y))^2k(x,y)\,\mathrm{d}(x,y)$$
for every ball $B \subset \mathbb{R}^d$ and every $f \in H_k(B^*)$. Then for every bounded Lipschitz domain $\Omega \subset \mathbb{R}^d$ there exists a constant $\tilde c = \tilde c(d,\kappa,\alpha,\Omega) > 0$ such that for every $f \in H_k(\Omega)$
$$\tilde c\,c\int_{\Omega\times\Omega}(f(x)-f(y))^2|x-y|^{-d-\alpha}\,\mathrm{d}(x,y) \le \int_{\Omega\times\Omega}(f(x)-f(y))^2k(x,y)\,\mathrm{d}(x,y).$$
The constant $\tilde c$ depends on the domain $\Omega$ only up to scaling. In particular, if $\Omega$ is a ball, the constant can be chosen independently of $\Omega$. For $0 < \alpha_0 \le \alpha < 2$, the constant $\tilde c$ depends on $\alpha_0$ but not on $\alpha$.” (pp. 29–30)

For a bounded Lipschitz domain $\Omega$ (`QFS.IsBoundedLipschitzDomain`), one constant $\tilde c$
serves every dilate $a\cdot\Omega$, $a > 0$, and every $\alpha \in [\alpha_0, 2)$: the lemma's
conclusion, its scaling sentence and its $\alpha_0$ sentence at once. The case $a = 1$ is the
conclusion on $\Omega$ itself. The ball sentence is `lemma_A_1`.

**No measurability of $k$ is assumed.** Both forms are lower Lebesgue integrals, and along a fixed
function the kernel's form agrees on every set with the form of a measurable kernel
(`QFS.exists_measurable_kernel_form_eq`), which is all the proof needs.

The source's proof quotes the Whitney decomposition and Dyda's inequality (13) on $\Omega$. Here
(13) is proved on $\Omega$ (`dyda_13_lipschitz`), and the Whitney decomposition is replaced by an
average over the balls $B(z, \delta_z/(8\kappa))$, as for balls. -/
theorem lemma_A_1_lipschitz {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsBoundedLipschitzDomain Ω) :
    ∀ α₀ κ : ℝ, 0 < α₀ → 1 ≤ κ →
    ∃ c' : ℝ, 0 < c' ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 →
      ∀ (Λ : ℝ) (Γ : Configuration (EuclideanSpace ℝ (Fin d))) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      KernelBounds Γ α Λ k →
      ∀ c : ℝ, 0 < c →
      (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Metric.ball x₀ (κ * R))) →
        ENNReal.ofReal c * formHs (Metric.ball x₀ R) α f ≤ form (Metric.ball x₀ (κ * R)) k f) →
      ∀ a : ℝ, 0 < a → ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (a • Ω)) →
        ENNReal.ofReal (c' * c) * formHs (a • Ω) α f ≤ form (a • Ω) k f :=
  QFS.lemmaAOne_domain hΩ

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma A.1 — the domain conclusion, the ball clause, and the scaling remark**

**Lemma A.1 of Bux–Kassmann–Schulze, with the three assertions it makes for a fixed $\alpha$.**

Fix $\alpha$, $\kappa \ge 1$, $c_0 \ge 1$, a kernel $k$ and a function $f$, and assume the
**ball comparability hypothesis**: for every ball $B = B_S(y_0)$ and every $f$ square-integrable
on $B^* = B_{\kappa S}(y_0)$,

$$\lvert f\rvert^2_{H^{\alpha/2}(B)} \;\le\; c_0\,\mathcal E_{B^*}[k,f].$$

Then, writing $c(W) = W.\mathrm{dydaConst}/(c_0\,W.\mathrm{overlapBound})$:

1. **for every measurable $\Omega$ with a Whitney family $W$**, and every $f \in L^2(\Omega)$,
   $c(W)\,\lvert f\rvert^2_{H^{\alpha/2}(\Omega)} \le \mathcal E_{\Omega}[k,f]$;
2. **for every Whitney family for balls $W$**, the same on *every* ball $B_R(x_0)$ with one and
   the same $c(W)$ — independent of $x_0$ and $R$;
3. **for every $a > 0$**, the inequality on the dilate $a\cdot\Omega$ holds with *literally the
   same* $c(W)$ as on $\Omega$.

**These are the source's own three sentences.** The conclusion is claim 1, with
$\tilde c = \tilde c(d,\kappa,\alpha,\Omega)$ allowed to depend on the domain. Then: "The
constant $\tilde c$ depends on the domain $\Omega$ only up to scaling" — claim 3. "In
particular, if $\Omega$ is a ball, the constant can be chosen independently of $\Omega$" —
claim 2. None of the three implies another: claim 1's constant comes from a family attached to
the single $\Omega$, and the difference is visible in the types, `QFS.WhitneyDomainData` being
indexed by $\Omega$ where `QFS.WhitneyBallData` carries one overlap bound and one Dyda constant
for every ball at once.

**Claim 3 is not free.** It rests on `QFS.WhitneyDomainData.smul`, which transports a Whitney
family along a dilation with its overlap bound and Dyda constant unchanged, and that in turn on
a change of variables for the Gagliardo seminorm: dilating the domain by $a$ multiplies
$\lvert\cdot\rvert^2_{H^{\alpha/2}}$ by $a^{d-\alpha}$ once the function is precomposed. Both
sides of Dyda's inequality pick up the same factor, which is why the constant survives.

**The lemma's fourth assertion is stated separately.** "For $0 < \alpha_0 \le \alpha < 2$, the
constant $\tilde c$ depends on $\alpha_0$ but not on $\alpha$" is
`QFS.lemma_appendixA_alpha_uniform`. It is not a conjunct here because it needs a Whitney family
for *every* $\alpha$ in the range sharing one overlap bound and one Dyda constant; requiring
that would burden the three claims above with a hypothesis the source does not ask of them.

**Both quoted inputs are hypotheses, not theorems.** The source's proof quotes the Whitney
decomposition for properties (i)–(iii) and [Dyda06] for inequality (13), and proves neither.
Both are fields of $W$ here. For bounded Lipschitz domains, `lemma_A_1_lipschitz` needs no such
family, and for balls, `lemma_A_1` needs none either. **Lipschitz regularity of $\Omega$ is not assumed**, only
measurability — it enters the source solely through the Whitney decomposition.

`QFS.lemma_appendixA` is claims 1 and 2 alone. -/
theorem lemma_A_1_domain {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, MemLp f 2 (volume.restrict Ω) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs Ω α f
          ≤ form Ω k f)
      ∧ (∀ W : WhitneyBallData d α κ,
        ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
        MemLp f 2 (volume.restrict (ball x₀ R)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs (ball x₀ R) α f
          ≤ form (ball x₀ R) k f)
      ∧ (∀ Ω : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Ω →
        ∀ W : WhitneyDomainData d α κ Ω, ∀ a : ℝ, 0 < a →
        MemLp f 2 (volume.restrict ((a • ·) '' Ω)) →
        ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ))
            * formHs ((a • ·) '' Ω) α f
          ≤ form ((a • ·) '' Ω) k f) :=
  QFS.lemma_appendixA_stated hc₀ H hFmeas

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma A.1's constant depends on the domain only up to scaling**

**"The constant $\tilde c$ depends on the domain $\Omega$ only up to scaling"** — the remark
following Lemma A.1 of Bux–Kassmann–Schulze.

Under Lemma A.1's hypotheses, if $\Omega$ is measurable and carries a Whitney family $W$, then
for every $a > 0$ the conclusion holds on the dilate $a\cdot\Omega$ with **literally the same
constant** $W.\mathrm{dydaConst}/(c_0\,W.\mathrm{overlapBound})$ built from $\Omega$'s own
family:

$$\frac{W.\mathrm{dydaConst}}{c_0\,W.\mathrm{overlapBound}}\;
\lvert f\rvert^2_{H^{\alpha/2}(a\cdot\Omega)} \;\le\; \mathcal E_{a\cdot\Omega}[k,f].$$

Since the same holds with $a^{-1}$, the constants achievable on $\Omega$ and on $a\cdot\Omega$
are the same set: the constant is a function of the dilation class of $\Omega$, which is what
the source's sentence asserts.

**How it is proved.** `QFS.WhitneyDomainData.smul` transports a Whitney family along
$x \mapsto a x$ — centres scale, radii scale, and properties (ii) and (iii) transport because a
dilation is a bijection carrying balls to balls. The one substantive field is Dyda's inequality
(13), and it survives because of a change of variables for the Gagliardo seminorm: dilating the
domain by $a$ multiplies $\lvert\cdot\rvert^2_{H^{\alpha/2}}$ by exactly $a^{d-\alpha}$ once the
function is precomposed with the dilation, so **both sides of (13) acquire the same factor** and
the constant is unchanged. That scaling law is new to this formalization — the development had
otherwise avoided change of variables for Lebesgue measure, proving §3.2's estimates at scale
$h$ directly instead.

The full statement of Lemma A.1 for a fixed $\alpha$, with this as its third conjunct, is
`QFS.lemma_appendixA_stated`. -/
theorem lemma_A_1_scaling {α κ c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (H : ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : MeasurableSet Ω)
    (W : WhitneyDomainData d α κ Ω) {a : ℝ} (ha : 0 < a)
    (hf : MemLp f 2 (volume.restrict ((a • ·) '' Ω))) :
    ENNReal.ofReal (c₀⁻¹ * W.dydaConst / (W.overlapBound : ℝ)) * formHs ((a • ·) '' Ω) α f
      ≤ form ((a • ·) '' Ω) k f :=
  QFS.lemma_appendixA_scaling hc₀ H hFmeas Ω hΩ W ha hf

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
open QFS
variable {d : ℕ}

namespace QFS.Paper

/-- **Lemma A.1's constant depends on α only through a lower bound α₀**

**"For $0 < \alpha_0 \le \alpha < 2$, the constant $\tilde c$ depends on $\alpha_0$ but not on
$\alpha$"** — the last sentence of Lemma A.1 of Bux–Kassmann–Schulze.

Suppose the Whitney family for $\Omega$ can be chosen, for **every** $\alpha \in [\alpha_0, 2)$,
with one and the same overlap bound $M$ and one and the same Dyda constant $\gamma$, and suppose
the ball comparability hypothesis holds throughout that range with one $c_0$. Then Lemma A.1's
conclusion holds for every such $\alpha$ with the single constant

$$\frac{\gamma}{c_0\,M},$$

which does not mention $\alpha$.

**This is a transfer, not a strengthening, and deliberately so.** The $\alpha$-dependence of the
constant sits entirely in Dyda's inequality (13), which the source quotes from [Dyda06] and this
development carries as a hypothesis rather than proving. The overlap bound is purely geometric
and $\alpha$-free, but the Dyda constant is not ours to control — so uniformity over
$[\alpha_0, 2)$ is a property *of the quoted input*, and this statement says exactly that if the
input has it, so does the conclusion. That is the same epistemic status the source's own sentence
has: a remark about what the quoted decomposition delivers.

$\alpha_0$ enters only by delimiting the range on which the uniform family is assumed, which is
why the constant "depends on $\alpha_0$".

This is Lemma A.1's fourth assertion. The three it makes for a fixed $\alpha$ — the domain
conclusion, the "in particular, for a ball" clause, and the scaling remark — are
`QFS.lemma_appendixA_stated`. It is not a conjunct there because it needs this family over the
whole range, a hypothesis the other three do not require. -/
theorem lemma_A_1_alpha_uniform {κ c₀ α₀ γ : ℝ} {M : ℕ} (hc₀ : 1 ≤ c₀)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (W : ∀ α, α₀ ≤ α → α < 2 → WhitneyDomainData d α κ Ω)
    (hM : ∀ α h₁ h₂, (W α h₁ h₂).overlapBound = M)
    (hγ : ∀ α h₁ h₂, (W α h₁ h₂).dydaConst = γ)
    (H : ∀ α, α₀ ≤ α → α < 2 → ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (S : ℝ), 0 < S →
      MemLp f 2 (volume.restrict (ball y₀ (κ * S))) →
      formHs (ball y₀ S) α f ≤ ENNReal.ofReal c₀ * form (ball y₀ (κ * S)) k f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hFmeas : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    ∀ α, α₀ ≤ α → α < 2 →
      ENNReal.ofReal (c₀⁻¹ * γ / (M : ℝ)) * formHs Ω α f ≤ form Ω k f :=
  QFS.lemma_appendixA_alpha_uniform hc₀ hΩ W hM hγ H hf hFmeas

end QFS.Paper

end

section
set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Real Set Metric MeasureTheory ENNReal Filter Topology

namespace QFS.Paper

/-- **Lemma A.2 — differentiation along shrinking cubes**

“Let $\varphi : \mathbb{R}^d \to \mathbb{R}$ be locally integrable. The following holds for almost every $s \in \mathbb{R}^d$. If $(x_h)_{h>0}$ is a sequence in $h\mathbb{Z}^d$ such that $s \in \widetilde{A}_h(x_h)$ for every $h > 0$, then
$$\frac{1}{\lambda_d(A_h(x_h))}\int_{A_h(x_h)}\varphi(t)\,\mathrm{d}t \xrightarrow{h\to 0} \varphi(s).$$” (p. 30) -/
theorem lemma_A_2 {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : LocallyIntegrable φ volume) :
    ∀ᵐ s : EuclideanSpace ℝ (Fin d),
      ∀ x : ℝ → EuclideanSpace ℝ (Fin d),
        (∀ h : ℝ, 0 < h → x h ∈ QFS.scaledLattice d h) →
        (∀ h : ℝ, 0 < h → s ∈ QFS.halfClosedCube h (x h)) →
        Tendsto (fun h => ⨍ y in QFS.cube h (x h), φ y) (𝓝[>] (0:ℝ)) (𝓝 (φ s)) :=
  QFS.lemma_lebesgue_diff_paper hφ

end QFS.Paper

end

/-! ## Cited, and beyond the paper -/

section

namespace Dyda.Paper

/-- **Dyda 2006, (13), p. 572 — on the unit ball the $H^{\alpha/2}$ seminorm is bounded by the regional form**

“To verify (b)–(d), by Lemma 4 it is enough to prove the inequality
$$\int_D\!\int_D \frac{|u(x)-u(y)|^p}{|x-y|^{d+\alpha}}\,dy\,dx \le c\int_D\!\int_{B(x,\eta\delta_x)} \frac{|u(x)-u(y)|^p}{|x-y|^{d+\alpha}}\,dy\,dx \qquad (13)$$
for all $u : D \to \mathbb{R}$, see (1) and (4).” — B. Dyda, *On comparability of integral forms*, J. Math. Anal. Appl. 318 (2006), pp. 572–573, [doi:10.1016/j.jmaa.2005.06.021](https://doi.org/10.1016/j.jmaa.2005.06.021). Here $\delta_x = \operatorname{dist}(x, D^c)$.

*External.* This statement takes $D$ to be the unit ball, which falls under case (c) of Theorem 1 (a bounded connected Lipschitz domain), and $p = 2$. It states (13) for every $\eta \in (0,1)$, because the proof of case (c) uses $\eta$ only through Proposition 5, which is stated for every $0<\eta<1$. Bux–Kassmann–Schulze quote this inequality in the proof of their Lemma A.1 (“inequality (13) in [5, proof of Theorem 1]”). It is proved here (Step 1 follows Dyda's proof; Step 2, Dyda's case (c), is done with a pulled-in midpoint instead). With the enlarged-ball form (`section_3_2`) and an averaging over small balls that replaces the Whitney decomposition (`regional_le_form`), it gives Lemma A.1 for balls. -/
theorem dyda_13 {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α))
        ≤ ENNReal.ofReal c * ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∫⁻ y in Metric.ball x (η * Metric.infDist x (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ),
            ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)) :=
  Dyda.lintegral_le_regional_unitBall hd hα hη hη1

/-- **Dyda 2006, (13), p. 572 — on a bounded Lipschitz domain, uniformly in $\alpha \in [\alpha_0, 2)$**

Inequality (13) of Dyda's proof of Theorem 1, case (c) (a bounded connected Lipschitz domain), with
$p = 2$: for every $\eta \in (0, 1)$ there is $c$ with
$$\int_\Omega\int_\Omega \frac{(u(x)-u(y))^2}{|x-y|^{d+\alpha}}\,dy\,dx \le c\int_\Omega\int_{B(x,\eta\,\delta_x)} \frac{(u(x)-u(y))^2}{|x-y|^{d+\alpha}}\,dy\,dx,$$
$\delta_x$ the distance from $x$ to $\Omega^c$, and one $c$ serves every $\alpha \in [\alpha_0, 2)$.

*Route.* Dyda's Step 1 is run along chains whose tips are admissible: either interior, or in the
interior cone of one of finitely many boundary charts; this replaces his Lipschitz boxes and his
family of norms. Step 2 averages each near pair over a ball of admissible points. Case (c), his
finite cover and chaining, becomes a Poincaré inequality for the pairs at distance at least $\rho$,
from the connectedness of $\Omega$. -/
theorem dyda_13_lipschitz {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : QFS.IsBoundedLipschitzDomain Ω) {α₀ η : ℝ} (hα₀ : 0 < α₀) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, α₀ ≤ α → α < 2 → ∀ u : EuclideanSpace ℝ (Fin d) → ℝ, Measurable u →
      ∫⁻ x in Ω, ∫⁻ y in Ω, ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α))
        ≤ ENNReal.ofReal c * ∫⁻ x in Ω, ∫⁻ y in Metric.ball x (η * Metric.infDist x Ωᶜ),
            ENNReal.ofReal ((u x - u y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + α)) :=
  Dyda.lintegral_le_regional_lipschitz hΩ hα₀ hη hη1

end Dyda.Paper

end

section

namespace QFS.Paper

/-- **Beyond the paper — Dyda's inequality (13) on every ball**

Dyda's inequality (13), stated in `dyda_13` for the unit ball, holds on every ball $B_R(x_0)$ with the same constant. The substitution $x = x_0 + R x'$ multiplies both sides by $R^{d-\alpha}$, and it scales the distance to the complement by $R$. -/
theorem dyda_13_ball {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ), 0 < R →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Measurable f →
      formHs (Metric.ball x₀ R) α f ≤ ENNReal.ofReal c *
        ∫⁻ x in Metric.ball x₀ R, ∫⁻ y in Metric.ball x (η * Metric.infDist x (Metric.ball x₀ R)ᶜ),
          ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y :=
  QFS.formHs_ball_le_regional hd hα hη hη1

end QFS.Paper

end

section
open scoped ENNReal

namespace QFS.Paper

/-- **Beyond the paper — the regional form is bounded by the $H_k$ form**

New mathematics, not in the paper. Lemma A.1 passes from the enlarged ball to the same ball using a Whitney decomposition (its properties (i)–(iii)) and Dyda's inequality (13). This step replaces the Whitney decomposition by averaging over the balls $B(z, \delta_z/(2\kappa))$, $z \in B$, where $\delta_z = \operatorname{dist}(z, B^c)$. Averaging an enlarged-ball comparability $|f|^2_{H^{\alpha/2}(Q)} \le C\,|f|^2_{H_k(\kappa Q)}$ over these balls, against the weight $\delta_z^{-d}$, bounds the regional form $\int_B\int_{B(x,\eta\delta_x)}$ with $\eta = 1/(8\kappa)$ by $C(24\kappa)^d\,|f|^2_{H_k(B)}$. -/
theorem regional_le_form {d : ℕ} {α κ C : ℝ} (hκ : 1 ≤ κ) (hC : 0 ≤ C)
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hG : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2)
    (hball : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      formHs (Metric.ball z r) α f ≤ ENNReal.ofReal C * form (Metric.ball z (κ * r)) k f)
    (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hR : 0 < R) :
    ∫⁻ x in Metric.ball x₀ R, ∫⁻ y in Metric.ball x ((8 * κ)⁻¹ * Metric.infDist x (Metric.ball x₀ R)ᶜ),
        ENNReal.ofReal ((f y - f x) ^ 2) * jumpKernel d α x y
      ≤ ENNReal.ofReal (C * (24 * κ) ^ d) * form (Metric.ball x₀ R) k f :=
  QFS.regional_le_form_of_ballComparability hκ hC hf hG hball x₀ R hR

end QFS.Paper

end
