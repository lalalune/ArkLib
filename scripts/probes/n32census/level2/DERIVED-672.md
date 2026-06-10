# The C1379 count is DERIVED: 1,344 = 2·672 from antipodal balance — the level-2 count law is a theorem

Lane `nubs/issue232-effective-pa`, 2026-06-10. Completes `RESULTS-LEVEL2.md`'s named remaining
step ("derive 672 from the equation"). Adversarially audited (sound, 0.94) including a fully
independent brute-force char-0 enumeration in C that uses **none** of the derivation's rules and
reproduces 672 / 0-for-every-other-pattern / the 35-witness layer, with three-way exact set
equality (audit enumeration ≡ raw-data extraction ≡ derivation classes).

## The theorem (char-0 count law, level 2)

With ζ a primitive 32nd root of unity, z* = ζ⁸, λ = −z*, w = X¹⁸ + λX¹⁶ on H = μ₃₂, code =
degree-<16 polynomials: the agree-≥17 list is **exactly** ℓ₌₁₈ = 35 = C(7,4) and
ℓ₌₁₇ = 1,344 = 2·672, with the full fixed anatomy — and the whole count is *derived*:

1. **Reduction** (hand algebra, machine-asserted at every step, 1344/1344): the consistency
   equation `e₂(x⃗) − e₁(x⃗)² = λ + e₁(B_z)` is equivalent, via `e₁² = Σxᵢ² + 2e₂` and
   `xᵢ² = z_{oᵢ}`, to the vanishing of the 14-term μ₃₂-multiset
   `{x₁x₂, x₁x₃, x₂x₃} ⊎ B_z ⊎ O_z ⊎ {−z*}` — and vanishing in ℤ[ζ₃₂] = ℤ[X]/(X¹⁶+1) is
   **antipodal balance**: mult(ζ^m) = mult(−ζ^m) for every m (the 2-power Lam–Leung principle,
   in multiset form — immediate from power-basis freeness).
2. **Six structural lemmas** (L1 parity: O is parity-pure; L2 the three products occupy three
   distinct antipodal axes, P|P forbidden; L3 no product reaches the −z* slot; L4
   ξ = −Σxᵢ ∉ μ₃₂ ∪ {0} — hence agreement is *exactly* 17, never accidentally 18; L5 at most
   one sign-class per (B,O); L6 negation acts freely).
3. **The counting engine**: per (O,σ)-class, the B-placement rule gives exactly `C(v,(7−h)/2)`
   completions (h forced single fibers, v free axes); the event taxonomy E1 (antipodal pair in
   O), E2 (product on the third O-axis), E3 (product on the z*-axis), E4 (O-fiber on the
   z*-axis, ε=0) has closed-form u-triple censuses: ε=1 splits C(8,3) = 56 perfectly into
   7 events × 8; ε=0 has 38 live + 18 dead. The node table sums to **672 = 368 (ε=1) +
   304 (ε=0)**, hence **1,344 elements**; the dual-B census gives **92 = 20+24+24+16+8** via
   five identified mechanisms, hence **580 = 488 + 92** and `488·2 + 92·4 = 1,344` ✓. The
   z*-axis strata are 224 B|L + 96 L|O + 160 L|P + 192 mega = 672 ✓, generating exactly the
   19 realized slot-types with matching class counts.
4. **Completeness**: pattern (8,1) is excluded a priori (it *is* the witness layer — whose
   count 35 = C(7,4) falls out of the same balance law: S ∋ z* plus 4 of 7 antipodal pairs);
   all patterns with |O| ∈ {5,7,…,15} enumerate to **zero**.

## Effective characteristic transfer (closes the audit's minor #2)

Every non-solution configuration's 14-term sum is a nonzero α ∈ ℤ[ζ₃₂] with power-basis
coefficients bounded by 14, so Σc² ≤ 196 and, by the E1 norm bound (`EffectivePerPrimeExactness`,
E1: `N(α) ≤ (Σc²)^{m/4}` at m = 32), `N(α) ≤ 196⁸ < 2^61`. A split prime p can create a
spurious mod-p solution only if p ∣ N(α) for one of the finitely many configurations (or moves
ξ into μ₃₂ mod p, bounded identically). Hence **for every split prime p > 2^61 the theorem
holds verbatim mod p**; the two verified primes (2^30.9, 2^31.6) sit below that crude threshold
and are covered by their exhaustive censuses instead.

## Provenance grading (honest)

Steps 1–5 and the closed-form censuses are hand-derived and machine-asserted; the dual-B
five-family mechanism and the |O| ≥ 5 exclusion are established by exact finite ℤ₁₆-enumeration
(machine-checked char-0 combinatorics — the same epistemic grade as C19's own proof). Named
Lean follow-ups: the multiset form of `LamLeungTwoPow.vanishing_sum_antipodal` (the set form is
in-tree; the multiset form is immediate from freeness), then the balance criterion + L1–L6.

## Why this matters for the upper half

The per-level branch-count law now has **two proven rungs with the same engine**: level 1
(C19: 16, exhaustive consistency) and level 2 (this: 1,344, antipodal-balance combinatorics) —
and the level-2 proof is *structured* (reduction → balance → taxonomy → placement rule), not
just enumerated. The visible conjecture for the general rung: every level's marginal layer is
the solution set of one balance condition whose count is a sum of `C(v,·)` placement terms over
a finite event taxonomy — exactly the shape a per-level induction (Conjecture D) can consume.

Scripts: `deriver_step1_reduction.py` … `deriver_step4_otherpatterns.py` (this dir).
