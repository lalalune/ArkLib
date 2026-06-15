# wf407 / T357-12-inverse — the inverse-theorem unification bet: REFUTED (premise) + WALLED (tool)

**Date:** 2026-06-14 · **Verdict: refuted** (premise false) — and independently **walled**
to a Sidon/high-doubling obstruction at prize ε*. Honesty contract held: no fabricated closure.

## The bet (357-T12 / 334-T07, ranked #8 in `UNFINISHED_THREADS_407.md` §(d))

"Every ε*-bad family for δ* lives on coset/orbit (affine-subgroup) structure. If any ε*-bad
stack is poly(1/ε)-covered by affine-subgroup-structured families, δ* stops being analytic and
becomes a FINITE ENUMERATION; import Bogolyubov-Ruzsa/Sanders to close it." Three sub-tasks:
(1) catalogue all known bad families & verify each lives on coset/orbit structure; (2) state the
structure conjecture as a Lean Prop; (3) assess whether Sanders' quantitative B-R is strong
enough at prize parameters.

## Verdict: the bet dies on BOTH axes (each independently fatal)

### Axis 1 — the PREMISE is false: the worst-case bad config is NOT coset/orbit structured

The catalogue splits into two radius regimes, and the bet conflates them:

- **Johnson regime (the LOWER-bound / ceiling families):** O137/O138 (DISPROOF_LOG) showed the
  *extremal lower-bound* family at exactly-solved instances IS the twisted-monomial orbit of the
  KKH26 stack (`ε_mca` attained on the orbit; census = `−{subset sums}`). So the *known
  counterexample/ceiling* families (CS25, KK25, KKH26, prime-field) genuinely live on coset/orbit
  structure. The bet's catalogue claim is TRUE — but only for the ceiling, not the binding object.

- **Window-interior regime (the BINDING worst case that actually pins δ*):** the object that
  determines δ* is the *maximum* list / densest bad cluster, not the algebraic ceiling family.
  `probe wf407_T357-12-inverse_unification.py` (exact enumeration, proper subgroups = prize shape):

  | p | n | k | radius δ | best coset/power-word list | hill-climb TRUE max | orbit-coverage of true max |
  |---|---|---|---|---|---|---|
  | 17 | 8 | 2 | 0.625 | 2 | **7** | 0.14 |
  | 41 | 8 | 2 | 0.625 | 2 | **7** | 0.14 |
  | 97 | 16 | 2 | 0.500 | 4 | **6** | 0.17 |

  The true max-list word BEATS every coset/power-word construction, and its achieving list is
  **only 14–17% covered by the largest single rotation-orbit** — it is a heterogeneous
  combinatorial cluster, NOT an orbit. This independently reproduces DISPROOF_LOG O161/O162/O163
  ("H-MAX is a combinatorial densest codeword cluster, NOT the algebraic power-word fibre").

  Radius sweep (`/tmp/johnson_boundary.py`, p=17,n=8,k=2): the structured/unstructured boundary is
  clean — at the window-interior radius δ=0.625 the true max (7) crushes coset (2) =
  **UNSTRUCTURED**; the deeper "structured" rows (δ≤0.375) are below the budget where lists are
  0–1 = *vacuously* structured (nothing to enumerate). The prize window is exactly the
  unstructured regime.

  **Conclusion (axis 1):** the premise "every ε*-bad family lives on coset/orbit structure" is
  FALSE for the binding worst case. There exist unstructured bad configs, so NO structure theorem
  can enumerate them.

### Axis 2 — even granting structure, Sanders B-R is VACUOUS at prize ε*

The self-consistency check the thread itself flagged is decisive. For B-R/Sanders to bite, the
bad list `A` (set of bad scalars / agreeing codewords) must have SMALL doubling `|A+A| ≤ K|A|`
with K small; Sanders 2012 then covers `A` by `exp(O(log⁴ K))` translates of a subspace.

But the worst-case list from axis 1 is a **densest cluster of pairwise-low-agreement (≤1)
codewords** — its difference set is near-all-distinct, i.e. it is **Sidon-like = MAXIMAL
doubling `K ~ |A|`**, the exact opposite of the small-doubling hypothesis. The inverse theorem's
hypothesis `|A+A| ≤ K|A|` with small K is simply FALSE for this set.

Plugging prize ε*=2⁻¹²⁸ directly: an ε*-thin bad set has density parameter K = 1/ε* = 2¹²⁸; the
Sanders coset-progression rank ~ K·polylog K ⟹ log₂(#families) ≳ 2¹²⁸, against a poly(1/ε*)
enumeration target of log₂ ~ 21 (= log₂(128³)). **Gap ≈ 2¹²⁸** — the covering is super-polynomial
by a factor 2¹²⁸; the "finite enumeration" is not finite.

**Premise and tool are mutually exclusive:** a bad list that is NOT coset-structured is exactly a
high-doubling / energy-deficit set, which B-R cannot certify as structured; a bad list that IS
low-doubling would already be the harmless KKH26 orbit ceiling (silent at production budget,
O159). The "random sparse killer" the thread anticipated is real: the binding worst case is the
unstructured high-doubling cluster.

## Where this lands relative to the named walls

The bet collapses onto the **same wall the whole campaign bottoms out at**: the explicit-smooth-RS
sub-Johnson list-decoding bound / additive-energy core (W2-adjacent, the `E_Fp(μ_n)=n^{2+o(1)}`
Shkredov open problem). O162 already proved "H-MAX, the subset-sum fibre supply, and `E=O(n²)`
are the SAME irreducible core." The inverse-theorem route does not bypass it — it *requires*
the same energy/structure dichotomy it was hoping to supply, circularly.

## Artifacts

- `scripts/probes/wf407_T357-12-inverse_unification.py` — exact axis-1 enumeration + structure
  test (orbit-coverage of the achieving list) + axis-2 Sanders/B-R prize-parameter computation +
  self-consistency (Sidon doubling) check.
- `/tmp/johnson_boundary.py` — radius sweep locating the structured/unstructured boundary
  (reproduce in-tree as a probe if desired).

## What remains (honest)

Nothing actionable on THIS route — it is a clean kill. The genuine open core is unchanged: the
explicit-smooth-RS beyond-Johnson worst-case list bound = the recognized additive-energy /
Paley-eigenvalue wall. No Lean brick (the verdict is a refutation by exact numerics, not a clean
provable statement; a `*_REFUTED` brick would just restate the probe and is not worth the
olean-load cost).
