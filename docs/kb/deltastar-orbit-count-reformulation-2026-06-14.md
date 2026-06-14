# δ* = the orbit-count crossing law (Action–Orbit reformulation, #407, 2026-06-14)

Combining the **governing law** `δ* = sup{δ : I(δ) ≤ q·ε* ≈ n}` (`I(δ)=max_pencil #{α: x^a+αx^b is
δ-close to RS[k]}`, exact identity in-tree) with the **Action–Orbit factorization** (Chai–Fan
2026/861, `ActionOrbitFRI.agreement_orbit_invariance`, proven axiom-clean): the bad-α set of a
monomial pencil `(X^a,X^b)` is a union of `⟨ω^{b−a}⟩`-orbits of size `S = n/gcd(b−a,n)`, so

  `I_pencil(δ) = N_pencil(δ) · S`,   `S = n/gcd(b−a,n)`.

Hence `I_pencil ≤ n ⟺ N_pencil ≤ gcd(b−a,n)`, and the governing law becomes a clean **orbit-count
crossing law**:

> **`δ* = sup{ δ : ∀ far pencil (a,b),  N_pencil(δ) ≤ gcd(b−a,n) }`.**

At the threshold `I = budget = n`, the orbit count is `N = I/S = gcd(b−a,n) = O(1)` for coprime
`b−a` — the poly/bounded orbit count BridgeLoop44 needs (the prize requires only `N ≤ poly(n)`,
already a theorem above Johnson; the open residual is the small-gap window band).

## Numerical validation (probe_orbit_count_prize_regime, true prize regime, proper μ_n ⊊ F_q*)
- n=8, far pencil (6,7), q=521 (n³): δ=0.375 → |bad|=40, N=5, S=8 (40=5·8); δ=0.25 → |bad|=4, N=1.
- N is SMALL (1–5) for far pencils even when |bad| is larger — orbit structure compresses by S.
- Correlated pencils (a or b = n/2, where `x^{n/2}=±1`) give degenerate I=q−1 — correctly excluded
  (matches the prize's "subgroup directions excluded" warning).

## The open core (now an orbit count, not a character sum)
`N_pencil(δ)` = #achievable maximal agreement sets A (size ≥(1−δ)n) mod ω-rotation, where
`∏_{i∈A}(x−ζ^i) | (x^b+αx^a−g(x))` (g deg<k) — the **sparse pencil polynomial** (support
⊆{0..k−1,a,b}). NOVEL CLOSED-ARGUMENT TARGET: bound `N ≤ poly(n)` via **Mann's theorem on large
cyclotomic factors of a sparse polynomial** (the RungSparseDivisor / vanishing-sums-of-roots-of-unity
lane). This is the non-BGK, non-character-sum route; whether N stays poly at constant rate (vs the
beyond-Johnson list explosion) is the live question — testing n=8→12→… for the scaling.
