
## Theme A (cont.) — the perfect-B_r rigidity of prime roots of unity

Probe: `scripts/probes/probe_conj_perfect_Br.py`. Verified p=3,5,7,11; r=2..6 (incl. r≥p).

- **A5 (perfect-B_r theorem — PROVED, strong survivor).** For every odd prime `p` and EVERY `r≥1`,
  `μ_p ⊂ ℂ` is a perfect `B_r` set: the only solutions to `a_1+…+a_r = b_1+…+b_r` (`a_i,b_i∈μ_p`)
  are permutations. Equivalently `E_r(μ_p) = Σ_{size-r multisets M}(orderings M)²` (the pure
  permutation count), a closed polynomial in `p`.
  **Proof (rigorous):** the lattice `{c∈ℤ^p : Σc_iζⁱ=0}` equals `ℤ·(1,…,1)` (Φ_p is the minimal
  polynomial of ζ, so the unique relation is the p-sum). An `E_r` relation has `c_i=mult_a(i)−mult_b(i)`
  ⟹ `c=m(1,…,1)`; `Σc_i = r−r = 0 = mp ⟹ m=0 ⟹` a,b the same multiset. ∎
  **Refutation checks passed:** (i) r<p AND r≥p both match (so it's "all r", not just r<p — my initial
  r<p hypothesis was itself too weak); (ii) `E_r(μ_p)` differs from a random Sidon set's at r=3
  (1645 vs 1663) — so this rigidity is SPECIAL to prime roots of unity, not generic to Sidon sets.
  **Significance:** prime-order roots of unity are simultaneously Sidon in ALL orders — maximal
  additive rigidity. Contrasts with composite `n` (relations from Φ_d, d|n) and 2-power `n` (antipodal
  B_2 failure, A1). This is the additive-rigidity root cause of why the prize's 2-power (NTT) domain is
  the hard case and odd-prime domains are generic. Count promoted: +1 (now 5 total).
