# `B(μ_n)` IS the generalized-Paley-graph spectral gap — reframing + base case (2026-06-13)

From the user-supplied literature batch (42 papers), the genuinely useful finding: the prize's single
open input is *exactly* a **spectral-gap / almost-Ramanujan question for generalized Paley graphs**, a
studied object — with the **semiprimitive case proven Ramanujan** (a real sub-case) and the average
norm proven small, but the general 2-power case open.

## 1. The exact identity (Podestá–Videla, arXiv 2310.15378 / 1908.08097)
The generalized Paley graph `Γ = Cay(F_p, μ_n)` (connection set the multiplicative subgroup `μ_n`,
`n | p−1`) is `n`-regular, and its **eigenvalues are exactly the cyclotomic Gaussian periods**
`η_b = Σ_{x∈μ_n} e_p(bx)` (`b` over coset reps). Hence
> **`B(μ_n) = max_{b≠0}|η_b|` = the second-largest eigenvalue (in abs. value) of `Γ`.**
`Γ` is **Ramanujan ⟺ `|η_b| ≤ 2√(n−1)`** ∀ nontrivial `b`. The prize needs the weaker
**almost-Ramanujan** bound `|η_b| ≤ C√(n·log(p/n))` (= the **Alon–Roichman** second-eigenvalue for a
*random* `n`-element Cayley generating set). So:
> **Prize open core ⟺ the multiplicative subgroup `μ_n` is a spectrally-pseudorandom Cayley
> generating set of `F_p^+` (its Paley graph is almost-Ramanujan), for `n=2^μ ≪ √p`.**

## 2. PROVEN base case: the semiprimitive subgroups ARE Ramanujan
When `(p,n)` is **semiprimitive** (`−1 ∈ ⟨p⟩ mod n`), `Γ(k,p)` is **strongly regular** with two
explicit nontrivial eigenvalues of size `~√n` (Baumert–McEliece / the irreducible 2-weight cyclic
code spectrum; Podestá–Videla §5). So `B(μ_n) = O(√n)` — *genuinely Ramanujan, prize bound holds*.
This is a real proven sub-case of the open input; the general (non-semiprimitive 2-power) case is the
residual.

## 3. Average norm is small (Habegger 1611.07287; Cornelissen–Hokken–Ringeling 2507.09303)
The **average** `(1/(p−1))Σ_b log|η_b|` converges to a Mahler measure (`~n log log n` growth) — the
periods are small *on average*. Confirms there is no *generic* obstruction, but these are
average/fixed-small-`n` results; they do **not** bound the **max** for large `n` (the sup-norm vs
average gap is exactly the open point).

## 4. What the rest of the batch gives (and why it doesn't close it)
- **Probability (CCK Gaussian approximation 1212.6885; sub-Gaussian operator norm 1812.09618; Gaussian
  suprema 1012.0210):** the max-from-moments machinery — but the deterministic `L^{2r}` (Markov) method
  already does that step; these need *independence* of summands, which `μ_n` lacks (the Gauss sums
  `g(χ^j)` are correlated). They don't bypass the "no-conspiracy" core.
- **Superlacunary trig series (2110.01998):** max of lacunary `Σe(x n_j) ~ √(N log N)` — the right
  *shape*, but `{g^j mod p}` is lacunary multiplicatively, NOT additively (frequencies `g^j mod p` are
  equidistributed, not geometric), so Salem–Zygmund does not directly apply.
- **Automorphic sup-norm papers (batch 1):** methodological analogs (amplification / pre-trace), a
  different object; potentially transferable but a research program, not a ready bound.
- **Cyclic-code weight distributions / Davenport–Hasse / Waring (2105.14872, 2309.04068, …):** compute
  the *same* Gaussian periods in explicit (semiprimitive/2-weight) cases — same base case, not general.

## 5. Net (honest)
These papers **reframe** the open core as the **almost-Ramanujan property of generalized Paley graphs
of 2-power multiplicative subgroups**, supply the **proven semiprimitive base case** (`O(√n)`,
Ramanujan) and the **small-average-norm** results — but **none proves the general sup-norm / spectral
gap `≤ √(n log(p/n))` for `n=2^μ ≪ √p`**, which is the prize residual. New attack surfaces opened:
(a) extend the semiprimitive computation toward general `p` mod `2^μ`; (b) a trace-formula / amplification
bound for the Paley spectral gap; (c) the Alon–Roichman-style derandomization for the *specific*
subgroup generating set. No closure; the residual is now a named, studied spectral-graph problem.

## 6. CORRECTION: the semiprimitive base case is the WRONG regime for the prize
Checked: `μ_n ⊂ F_p` requires `n | p−1` (`p≡1 mod n`) — this IS the deployed NTT / prize setup.
But **semiprimitive** needs `−1 ∈ ⟨p⟩ mod n`; for `μ_n⊂F_p` (`p≡1 mod n`) we have `⟨p⟩ mod n = {1}`,
so `−1∉⟨p⟩` for `n>2` — **the prime-field prize case is NEVER semiprimitive.** The semiprimitive
GP-graphs live over **extension fields** `F_{p^m}`, `m≥2` (where `⟨p⟩ mod n` is nontrivial and can
contain `−1`); for 2-power `n` over the prime field this corresponds to the `n | p+1` setup where
`μ_n ⊄ F_p` (it sits in `F_{p^2}`) — the *easy* Frobenius case (`r(c)≤2`), NOT the prize.

So the proven-Ramanujan GP-graph results (semiprimitive, and the explicit `k≤4` i.e. `n≈p` cases) are
**all outside the prize regime** (prime field `F_p`, *small* 2-power subgroup `n=2^μ ≪ √p`,
`p≡1 mod n`). Verified empirically: for the deployed case `p≡1 mod n`, `B(μ_n)/√(n·log(p/n)) ≈ 0.9–1.0`
(almost-Ramanujan, NOT the tight `√n`). **The prize regime is precisely the open, non-semiprimitive,
prime-field, small-2-power-subgroup case that no GP-graph result covers.** The reframing stands; the
base case does not transfer. The residual is unchanged and genuinely open.

## 7. The proven unconditional baseline + why the gap is irreducible (deep read, 2026-06-13)
**Proven baseline (Weil / Gauss sum):** `B(μ_n) = max_{b≠0}|η_b| ≤ √p` unconditionally — via the
Gauss-sum decomposition `η_b=(1/f)Σ_ψ ψ̄(b)g(ψ)`, `|g(ψ)|=√p`; equivalently the eigenvalue↔code-weight
relation `λ_γ=n−(p/(p−1))w(c_γ)` + the Artin–Schreier point count `#C_{k,β}=2p+k(p−1)λ` bounded by
Weil (Podestá–Videla 1911.08549, eq. 1.9/6.1). This is the unconditional fallback for the scaffold.

**Why `√p` does NOT close the prize (precise):**
- The prize needs `B ≤ √(n·log(p/n))`, and `√p ≫ √(n log)` for `n≪p`. Via the moment identity
  `Σ_b η_b^{2r}=p·E_r`, the Weil bound gives only `E_r ≤ p^r` (since `|η|≤√p`), which is **useless**
  (the clean value is `(2r−1)!!n^r ≪ p^r`); so `√p` and the energy bound are genuinely separate.
- **`r≈log p` is genuinely required (no small-`r` shortcut):** `B ≤ (p·E_r)^{1/2r}`, and with
  `E_r=(2r−1)!!n^r≈(2rn/e)^r` this is `p^{1/2r}·√(2rn/e)`; `p^{1/2r}=O(1)` only at `r≈log p`, where it
  gives `√(n log p)`. Smaller `r` leaves a `p^{1/2r}≫1` factor. So the bound needs `E_r` clean (up to
  a `C^r` factor) all the way to `r≈log p` — exactly the open content.
- **Large `|F|` does NOT bypass it:** the field-size lever (`censusDomination_pin_largeField`) needs a
  `q`-INDEPENDENT list bound; the worst-case beyond-Johnson list is `q`-independent and open, so growing
  `q` enlarges the budget `ε*q` but not the (open) bound. `√p`-on-`B` does not bound the list.

**Exact residual (sharpest statement):** prove `E_r(μ_n) ≤ (C·r·n)^r` for `r ≤ log(p/n)`,
`n=2^μ ≪ √p`, `p≡1 mod n` (equivalently `B(μ_n) ≤ C√(n log(p/n))`, equivalently the Paley graph is
almost-Ramanujan). The proven `√p` is the unconditional baseline; this `√p → √(n log)` gap is the
entire open core. No acquired paper (incl. the 42 user-supplied) crosses it.
