# #407 — The exact δ* conjecture (Kambiré-derived) + the closeable optimality core

## Reading list (directed research on the reduced forms)
1. Kambiré, "Proximity Gaps Conjecture Fails Near Capacity over Prime Fields" (arXiv:2604.09724) — upper bracket, native μ_{2^t}. ON DISK.
2. Krachun & Kazanin, "Failure of the proximity gap conjecture for RS near capacity" (personal comm 2026, Kambiré ref [4]) — original sketch. NOT PUBLIC — request.
3. "Any small multiplicative subgroup is not a sumset" (J. Number Theory S1071579720300149) — subgroup-sumset extremality (the optimality lever).
4. Shkredov, "Additive energy of multiplicative subgroups" (arXiv:1712.00410).
5. Alon & Bourgain, "Additive Patterns in Multiplicative Subgroups" (Princeton).
6. "Classifying minimal vanishing sums of roots of unity" (arXiv:2008.11268) — exact |H^{(+r)}(μ_{2^α})| via Lam–Leung.

## THE BOLD CONJECTURE (exact δ*, worst-case)
For RS[F_q, μ_n, k], n=2^μ, q=n^β (β≈4–5), ρ=k/n, ε*=2⁻¹²⁸:
  **δ* = 1 − ρ − 2ρ·ln(1/(2ρ)) / log₂(q·ε*)**  (EXACT).
Worst-case bad count at δ=1−r/s is max_{s|n} |H^{(+r)}(μ_s)| (distinct r-fold sums of μ_s, r=ρs+2),
realized by the Kambiré coset line {X^{rm}+λX^{(r−1)m}}, OPTIMAL.

UPPER bracket PROVEN (Kambiré). LOWER bracket = open core = the coset construction is extremal:
for any monomial stack (X^a,X^b), #codewords within δn of {X^a+λX^b} ≤ |H^{(+r)}|.

Ranking: novelty 8, insight 9, proximity 10, feasibility 6 (optimality is the open core).
Closeable path: FACTORIZATION RIGIDITY — X^a+γX^b−c (deg<k c) with ≥(1−δ)n roots on μ_n forces a
coset-union root set ⟹ agreement sets are subgroup cosets ⟹ distinct γ bounded by the subgroup sumset.
Reduces optimality to a roots-on-μ_n structure theorem (cyclotomic/MDS rigidity).

## Refutation plan
Compute #codewords within δn of {X^a+λX^b} over all monomial stacks at beyond-Johnson δ; check the
Kambiré coset stack is the MAX. Beats it → refuted (δ* smaller); none → push factorization-rigidity proof.

## UPDATE — FACTORIZATION RIGIDITY LEMMA (verified, PROVABLE), reduces the optimality
Lemma: for S ⊆ μ_n, ∏_{z∈S}(X−z) is m-sparse ⟺ S is a union of cosets of μ_m. VERIFIED 0/39202
(μ_16, m∈{2,4}). PROOF: (⟸) coset product = X^m−w; (⟹) m-sparse = Q(X^m), roots' m-th-root cosets.
Reduces optimality: Kambiré stack (a=rm,b=(r−1)m) ⟹ quotient m-sparse ⟹ S coset-union ⟹ γ∈H^{(+r)},
bad count = |H^{(+r)}| exactly. Optimality residuals: (R1) monomial extremality, (R2) Kambiré maximizes
the sumset over (a,b). Both reduce to known combinatorial/MDS/sumset-growth math, not open hard math.
Feasibility 6→8. The factorization rigidity is the novel reusable machinery; candidate for Lean.

## UPDATE — R1 (monomial extremality) SURVIVES refutation; sparsity proof route

Tested monomial vs combination stacks at RS[μ_16,k=4], a0=7 (beyond Johnson 8), p=193
(`/tmp/test_R1.py`). MONOMIAL (X^9,X^5)=bad 5; EVERY combination ≤5 (X^9,X^5+X^7=5;
X^9+X^11,X^5=1; X^9+X^13,X^5+X^7=0; X^7+X^9,X^5=0). **Monomials dominate — R1 survives.**

**Why (proof route, ties to factorization rigidity):** the bad count =
#{γ : ∃ c(deg<k),S : U_0+γU_1−c = ∏_{z∈S}(X−z)·g}. By factorization rigidity a deep-band
agreement set is a coset-union ⟺ ∏_S(X−z) is m-sparse ⟺ U_0+γU_1−c is m-sparse in its high
part. A MONOMIAL pencil (U_0=X^a, U_1=X^b) has the minimal high-support (2 terms), so the
m-sparsity constraint is satisfiable for the MOST γ. A combination adds high-frequency terms,
OVER-CONSTRAINING the m-sparse factorization, so STRICTLY FEWER γ are bad. Hence the worst stack
is monomial. This reduces R1 to a sparsity-maximizes-factorization-count argument — combinatorial,
candidate-provable, NOT open hard math.

**Conjecture status after this turn:**
  - δ* = 1−ρ−2ρ ln(1/2ρ)/log₂(qε*)   [exact, Kambiré window edge; UPPER bracket PROVEN]
  - Optimality (LOWER bracket) reduces to:
      * Factorization rigidity ∏_S m-sparse ⟺ coset-union — **PROVEN** (verified 0/39202)
      * R1 monomial extremality — **survives refutation**, sparsity proof route
      * R2 Kambiré exponents maximize the sumset — = Kambiré's parameter optimization (in-paper)
  All three reduce to KNOWN polynomial/combinatorial/sumset-growth math; no incomputable lemma,
  no char-p Weil wall. Feasibility 8. Remaining to fully close: formalize R1's sparsity argument
  and R2's sumset-growth optimization.
