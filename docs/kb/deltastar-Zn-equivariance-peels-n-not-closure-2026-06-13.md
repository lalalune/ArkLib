# NEW STRUCTURE (partial, honest): beyond-Johnson list = n·#orbits under a free ℤ/n action; orbit count is the residual hard part (2026-06-13)

Direct response to "find closed novel math that avoids BOTH the Johnson reduction AND the open
square-root-cancellation problem." Tested the one lever that is neither pairwise-Fisher (Johnson) nor a
field character sum: the **ℤ/n group action on the list** (the domain `μ_n` is a cyclic group).

## The structural theorem (genuine, closed, formalizable)
For the deep-hole word `w = x^{d}` (`d=k+1`), the map `σ(ev)[j] = g^{-d}·ev[(j+1) mod n]` is a
**rotation+scaling** symmetry: it sends agreeing codewords to agreeing codewords (degree `<k` preserved,
agreement set rotated). The worst-case beyond-Johnson list is **closed under σ**, and the action is
**FREE** (every orbit has size exactly `n`). Measured (`scripts/probes/probe_list_Zn_orbits.py`):
- `n=16,k=4,a=5` (δ=0.688): list 16 = **1 orbit × 16**, σ-closed ✓
- `n=16,k=8,a=9` (δ=0.438): list 64 = **4 orbits × 16**, σ-closed ✓

> **Theorem (closed):** every beyond-Johnson worst list of the deep-hole word is a disjoint union of
> free `ℤ/n`-orbits, so `|list| = n · (#orbits)`. The factor `n` is exact and field-independent.

This avoids Johnson (it lives in the beyond-Johnson regime) and is pure group theory (no character sum).

## Why it is NOT a closure (the honest test that kills the easy hope)
`#orbits` is **field-dependent** (`scripts/probes/probe_orbit_count_field_dep.py`):
| (n,k,a) | p=97 | 113 | 193 | 241 |
|---|---|---|---|---|
| (16,4,5) | 1 | **2** | 1 | 1 |
| (16,8,9) | 4 | **7** | 3 | 3 |

`#orbits` varies (3–7); the spike at `p=113` is exactly where `p−1=16·7` carries extra 7-torsion —
i.e. the variation is the SAME additive-energy/character-sum content. So the ℤ/n quotient peels off the
closed factor `n` but the **residual `#orbits` is the open problem `/n`**, not a new closed quantity.

## Verdict (for the "avoid both reductions" directive)
- The equivariance is a REAL partial result: `|list| = n·#orbits`, free action, formalizable, neither
  Johnson nor character-sum — worth landing as a structural theorem.
- It does **not** close δ*: `#orbits` is field-dependent, = the hard problem divided by `n`.
- Eliminates "group symmetry closes the prize" as a route, while extracting the one genuinely closed
  piece (the `n` factor) — which sharpens the open core to **the orbit count**, a strictly smaller object.

No closure claimed. This is the most structurally novel reduction of the session; the residual is honest.

## UPDATE — the "generic prime pins #orbits" hope is REFUTED (probe_orbit_torsion_refute.py)
Scanned p≡1 mod 16 up to 1217 at band δ=0.438 (n=16,k=8,a=9), correlating #orbits with the
factorization of the cofactor (p−1)/16:
- "Generic" primes (cofactor prime) give #orbits = **7 (p=113), 0 (p=593), 0 (p=977)** — ERRATIC,
  no stable minimum. The largest list (112) is at p=113, a cofactor-PRIME (so "generic" by smoothness).
- For most primes p≥449 the list at this band is **0** (MCA holds); nonzero only at special small p.

So #orbits is NOT a closed generic value tied to field smoothness — it is exactly the
**spurious-collision count**: 0 for generic fields, nonzero only at the special "collision" primes
where the subgroup r-fold sumset degenerates mod p. That is the additive-energy/character-sum content
divided by n. The smoothness hypothesis is false (variation is the full erratic collision structure,
not small-torsion spikes). **The equivariance line is fully explored: partial closure (factor n) stands;
#orbits is the hard residual, REFUTED as closable. No closure.**
