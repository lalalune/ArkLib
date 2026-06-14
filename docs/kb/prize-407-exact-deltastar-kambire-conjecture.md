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
