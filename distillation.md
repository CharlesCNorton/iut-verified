# IUT Distillation: The Disputed Core

This document extracts the essential mathematical content from the source papers, focusing on the disputed Corollary 3.12 and the Scholze-Stix critique.

---

## 1. The Claimed Result

### Corollary 3.12 (IUT-III, p.173-174)

**Statement**: Suppose we are in the situation of Theorem 3.11. Write

```
- |log(θ)| ∈ ℝ ∪ {+∞}
```

for the procession-normalized mono-analytic log-volume of the holomorphic hull of the union of possible images of a **θ-pilot object**, subject to indeterminacies (Ind1), (Ind2), (Ind3).

Write

```
- |log(q)| ∈ ℝ
```

for the procession-normalized mono-analytic log-volume of the image of a **q-pilot object**, NOT subject to those indeterminacies.

**The Inequality**:
```
- |log(θ)| ≤ - |log(q)|
```

Equivalently: `C ≥ -1` for any real number C such that `- |log(θ)| ≤ C · |log(q)|`.

---

## 2. What This Means for abc

### From IUT-III to Vojta's Inequality

The inequality (1.4) from the Scholze-Stix paper translates Corollary 3.12 as:

```
- |log(q)| ≤ - |log(θ)|
```

Where the left side encodes:
```
- |log(q)| = - deg(q_E^{1/2ℓ}) = - (1/2ℓ) deg(q_E)
```

And the right side (equation 1.5), in Mochizuki's interpretation:
```
- |log(θ)| ≈ Σ_v Σ_{j=1}^{ℓ} j² · δ(P)_v - (1/2)[k:ℚ] Σ_v v(q_v) log N(v)
           = (ℓ(ℓ+1)(2ℓ+1)/6) · δ(P) - ((ℓ(ℓ+1)(2ℓ+1))/12) · deg(q_E)
```

Solving yields the Szpiro-type inequality that implies abc.

---

## 3. The Scholze-Stix Objection

### The Scaling Problem

Scholze-Stix argue the right side should be (equation 1.6):

```
- |log(θ)| ≈ Σ_v Σ_{j=1}^{ℓ} j · δ(P)_v - (1/2)[k:ℚ] Σ_v v(q_v) log N(v)
           = ((ℓ+1)/2) · δ(P) - (1/2) · deg(q_E)
```

**The missing j² factors**: To encode the arithmetic degree of the j-th concrete θ-pilot object in the abstract θ-pilot object, one must scale the identification `ℝ ≅ ℝ_{Θ,j}` by j².

### The Diagram with Monodromy

```
     ℝ_{Θ,Θ}  ----Θ-link---->  ℝ_{Θ,q}
        ↑                         ↘
  (ℝ^c_{Θ,j})_{j=1,...,ℓ}          ℝ^c_{Θ,q}
        ↘                         ↙
         ℝ_Θ  -------=------->  ℝ_q
```

**The problem**: The j² scalings on the left create **monodromy** (inconsistency) when composed around the diagram. With consistent identifications, you must omit j², yielding:

```
0 ≤ δ(P)
```

This is vacuous.

### Mochizuki's Defense

Mochizuki claims the "blurring" from indeterminacies makes the diagram commute. Scholze-Stix counter: this blurring must be at least O(ℓ²), rendering the inequality useless.

---

## 4. Key Definitions

### Hodge Theater (IUT-III §2.1.2)

Up to equivalence of categories, choosing a Hodge theater is equivalent to choosing a once-punctured elliptic curve abstractly isomorphic to X.

The "étale-like data" (D or D⊢): the abstract topological group π₁(X), up to inner automorphism.

The "Frobenius-like picture": enhancement with a monoid action, e.g., π₁(X) acting on k̄×.

### F^{⊢×μ}-prime strips (IUT-III §2.1.5)

At nonarchimedean places, data of the form:
```
(G_v ↷ O_{k̄_v}^{×μ}) × ℕ
```

The global realified Frobenioid factors through trivialized global realified Frobenioids.

### Pilot Objects (IUT-III Definition 3.8)

**q-pilot object**: Collection indexed by v ∈ V^{bad} of generators (up to torsion) of splitting monoids, concretely the `q_v^{1/2ℓ}`.

**θ-pilot object**: Collection of `(q_v^{j²/2ℓ})_{j=1,...,ℓ}` — the θ-values.

The **Θ-link** identifies the abstract θ-pilot (F^{⊢×μ}_{Θ,1}) with the abstract q-pilot (F^{⊢×μ}_{q,2}).

### The log-link (IUT-III §2.1.3)

Based on the p-adic logarithm:
```
log: O_K^{×μ} → K
```

Defines an endofunctor on topological fields isomorphic to algebraic closures of nonarchimedean local fields, naturally equivalent to the identity via log itself.

---

## 5. The Indeterminacies

### (Ind1) - Unit group indeterminacy

Automorphisms of F^{⊢×}-prime-strips act on units.

### (Ind2) - Galois indeterminacy

Upper semi-compatibility of Kummer isomorphisms with iterates of the log-link.

### (Ind3) - Label indeterminacy

As m varies over ℤ, isomorphisms are "upper semi-compatible" relative to log-links, involving natural inclusions ⊆ at non-archimedean places and surjections ↠ at archimedean places.

---

## 6. Multiradial Representation (Theorem 3.11)

The algorithm describes θ-values `q_v^{j²}` for `j=1,...,ℓ` from one arithmetic holomorphic structure in terms of an "alien" arithmetic holomorphic structure, up to indeterminacies (Ind1), (Ind2), (Ind3).

**Key properties**:
- **IPL** (Input Prime-strip Link): Output data is linked to input F^{⊢×}-prime-strip via full poly-isomorphisms
- **SHE** (Simultaneous Holomorphic Expressibility): Construction is valid relative to both domain and codomain arithmetic holomorphic structures

---

## 7. The Critical Step (IUT-III, Proof of Cor. 3.12, Step xi)

> "If one interprets the above discussion in terms of the notation introduced in the statement of Corollary 3.12, then one concludes [...] that −|log(q)| ≤ −|log(Θ)| ∈ ℝ."

Scholze-Stix's interpretation: This step conflates abstract and concrete pilot objects. The multiradial algorithm yields possible regions for abstract pilots, but comparing to concrete q-pilots requires consistent identification of real number copies — which fails due to j² scaling.

---

## 8. Joshi's Analysis (2025)

Kirti Joshi's "Final Report" attempts to resolve the controversy by:
1. Clarifying the role of arithmetic holomorphic structures
2. Arguing the indeterminacies are not as problematic as Scholze-Stix claim
3. Proposing that formalization would definitively settle the dispute

---

## 9. Formalization Target

To verify or refute IUT in Coq/Rocq, one must formalize:

1. **Prerequisites**:
   - Anabelian geometry (Mochizuki's Theorem 7: π₁ determines curves of Belyi type)
   - Frobenioids (categories abstracting divisor arithmetic)
   - Mono-theta environments
   - p-adic Hodge theory basics

2. **Core IUT structures**:
   - Hodge theaters and their equivalence to curve data
   - Prime strips (F^{⊢×μ}, F^{⊢×}, F^{⊢⊛})
   - The Θ-link and log-link
   - Log-theta-lattice

3. **The disputed step**:
   - Multiradial representation (Theorem 3.11)
   - Log-volume computations
   - The passage from abstract to concrete pilots
   - Corollary 3.12 and its proof

**The test**: Either the j² factors emerge correctly from the formalized proof (vindicating Mochizuki), or a type error / failed proof obligation occurs at Step xi (vindicating Scholze-Stix).

---

## 10. Key Quotes

### Scholze-Stix (p.9-10):
> "The conclusion of this discussion is that with consistent identifications of copies of real numbers, one must in (1.5) omit the scalars j² that appear, which leads to an empty inequality."

### Mochizuki (IUT-III, Remark 3.11.1 iv):
> "Unlike Corollary 3.12 below, which only concerns qualitative logical aspects/consequences of the construction algorithm of Theorem 3.11, the explicit computation to be performed in [IUTchIV], §1, of the log-volumes that occur in the statement of Corollary 3.12 makes essential use of the way in which theta values occur in the construction algorithm of Theorem 3.11."

### On formalization (Mochizuki, October 2025):
> After attending the Lean 4 workshop in Tokyo, Mochizuki explicitly stated he now views formalization as a legitimate and useful way to clarify IUT.

---

*This distillation is for formalization reference. All mathematics belongs to the respective authors.*
