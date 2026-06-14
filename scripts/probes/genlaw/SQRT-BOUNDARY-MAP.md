# The √n-boundary map: four distinct quantities, one shared boundary shape — don't bridge them

2026-06-13. Consolidates three independently-verified guardrails. The δ* problem has several
quantities whose boundary sits near √n; they are genuinely DIFFERENT objects, and conflating
any two produces a false closure. Each pairwise check below was adversarially verified.

| quantity | what it is | boundary | side |
|---|---|---|---|
| **Ceiling band** (KKH26 sharp band `r²<2^μ`) | KKH26 bad-scalar family size | √n (true wall √(n·ln n)) | construction reach |
| **Energy transfer** (moon, `E(μ_n)=3n(n−1)`) | additive-energy char-0→F_p transfer | p ≳ n^2.3 (polynomial) | field transfer |
| **Packing demand** (`single_pencil_aclose_card_le`) | upper bound on #bad **scalars** γ | covers r ≤ √N, fails at n/2 | DEMAND (upper) |
| **My census supply** (`N_r(s)`, O136) | exact #balanced **configurations** | empty for r > √(s+1) | SUPPLY (exact) |

**The three verified non-identities (each a "same √ boundary, different quantity" trap):**
1. Ceiling band `r²<2^μ` vs census `r²≤s+1` — `SQRT-BOUNDARY-CROSSREF.md`. Same objects
   (λ_T=−e₁=ξ) but different theorems; walls √(n ln n) vs √s; no transfer.
2. Energy transfer (n^2.3, poly) vs codeword-supply (super-poly, exponent n/2) —
   `ENERGY-VS-SUPPLY-TRANSFER.md`. Energy exact ⇏ supply exact at production.
3. Packing demand vs census supply — this batch (`#389` comment). Dual sides of `#bad ≤ supply`;
   numeric non-identity decisive: at (16,5) census N_r=0 but N_fib=21 (nonzero). The bands
   genuinely overlap (not cosmetic), but `#bad ≤ #alignable` does NOT chain through N_r — wrong
   transport direction.

**The one transport that actually matters for the prize** (and that none of these supply):
an UPPER bound on #bad **scalars** in the deep band (√(n log n), n/2). The packing route is
too weak there (Catalan C(2m,m)/(m+1) > budget 2^m for m≥8, proven); my census bounds the
SUPPLY side, not the demand side; the energy/ceiling boundaries are different quantities. So
the open core stays exactly: bound the deep-band bad-**scalar** count. My census data
(N_r=0 throughout the band) is suggestive *evidence* about the supply side but is NOT a
demand-side bound and does NOT close it.

**Working rule:** do not cite any of these four boundaries as evidence for another. They
coincide near √n by the shared C(r,2)-pairwise / antipodal-balance substrate, not by any
theorem relating the quantities.
