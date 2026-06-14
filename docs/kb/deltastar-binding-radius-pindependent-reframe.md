# δ* at the binding radius: a p-INDEPENDENT combinatorial incidence (possible decoupling from BGK) — #407

**Status: genuine structural reframe, NOT a closure, with limited evidence and a clear open test.**

## The observation

The exact far-line incidence `I(a,b;r)` (FarCosetExplosion, axiom-clean) is computed WITHOUT character-sum
cancellation: for each witness set `R` (|R|=n−r), the condition "the line `u0+γu1` restricted to R lies in
RS[R,k]" is affine in γ, so each non-heavy R contributes ≤1 γ and `I = |union of those γ|` (or `p` if some
R is heavy). This count is **p-INDEPENDENT** (verified: identical across p=200017/500113/1000033 at n=16).

**At the BINDING radius** (the `r` where `max_dir I` first crosses the prize budget `q·ε*`), the witness size
`s=n−k` gives `s−k` linear conditions on the single unknown γ. At the prize geometry `s−k ≥ 2` — the system is
**over-determined in γ**, so *generic* directions contribute incidence ≈0 (verified: random general directions
give 0 at the binding radius). Only **structured / over-determined** directions contribute, and their incidence
is the exact p-independent algebraic count.

## The evidence (n=16, k=4, ρ=1/4, binding radius r=10)

- Monomial max incidence = **89**, p-INDEPENDENT (89 at p=200017 and p=500113).
- A focused **198-direction structured search** (perturbations of the winning direction `x^{4}`+c·x^{j}, plus
  150 random 3-term structured directions) did **NOT beat 89** (`probe_407_binding_radius_structured.py`).
- ⟹ at accessible n, the binding incidence is monomial-dominated and p-independent, giving the computable
  `δ*(RS[μ_16,1/4]) = 9/16` (one rung beyond Johnson 1/2, inside the window interior (1−√ρ, 1−ρ−Θ)).

## Why this is interesting (the tension)

The per-frequency period `|η_b|` is **p-DEPENDENT** (Fermat vs non-Fermat primes differ — the whole BGK
difficulty). But this δ*-binding incidence is **p-INDEPENDENT**. If δ* is genuinely p-independent, it **cannot
equal the p-dependent BGK worst-case period** — meaning the campaign's long-assumed reduction "δ* = BGK max"
would be **lossy** (BGK is a sufficient sup-norm bound, but δ* itself is a *combinatorial* quantity, potentially
computable and EASIER). This is the first concrete evidence that δ* might decouple from the open analytic BGK
core.

## What stays open (do not overclaim)

1. **Is the monomial the true worst structured direction?** The 198-direction sample is NOT exhaustive; in-tree
   `ActionOrbitGeneralF.lean` argues the general-direction max "reduces to Q1/Q2/BGK" — so a wider/smarter search
   (or the right structured family) may still find a beater. Needs a complete characterization of the worst
   over-determined direction.
2. **Does p-independence survive to large n?** Prior audit flags a ">2^12 crossover" where concentration may
   re-introduce p-dependence. Must compute the binding incidence at n=32,64,… across multiple primes.
3. If both hold, δ* is a closed combinatorial quantity (count of over-determined witness configurations),
   computable, decoupled from BGK — a genuine closure path. If either fails, δ* re-reduces to the wall.

**Decisive next test:** compute the binding-radius structured-max incidence at n=32 (and n=64 if feasible)
across ≥2 primes; check (a) p-independence and (b) whether any structured direction beats the monomial. That
single experiment determines whether this is an escape or another face of the wall.
