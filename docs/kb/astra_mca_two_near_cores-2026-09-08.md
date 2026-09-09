# Two cores of size t-1: a single polynomial-realization obstruction remains

2026-09-08. Written reduction and finite incidence census; no polynomial realization or new unsafe instance is asserted. Parameters n=4s, k=2s, t=3s-1, s>=136. Production has s=2^28 and the certified prime P=365375409332725729550921208179070755120141565953.

The [portable census](../../scripts/probes/astra_mca_two_near_cores_check.py)
reproduces the [exact receipt](../../scripts/probes/receipts/astra_firststep_next_20260908/final-pattern-census.json).
This extends the [near-source argument](astra_mca_near_source-2026-09-08.md).
The coordinator and an independent agent reviewed the deductions; the
[review](../../scripts/probes/receipts/astra_firststep_next_20260908/two-near-cores-review.md)
also checks the finite-field choice and conditional threshold implication.
The new degree-three normalization, case split, and realization reduction
are written proofs; they are not covered by the degree-one/two Lean list module.

## Reduction from two joint cores of size at least t-1

Choose two distinct joint sources with cores at least t-1. Factoring their difference as H(A,B), with coprime A,B, gives primitive carrier degree d<=3: their cores intersect at least 2(t-1)-n=k-4 times. Their union U misses h<=3-d points.

Normalize each chosen actual-MCA decoder by T_gamma=A+gamma B on U, and add the two base profiles. Each resulting rational profile has numerator degree at most k-1, denominator degree at most d, and agrees with the fixed scalar word on U at least t-h-d>=t-3 times. Distinct profiles have intersection at most k+2. Thus there are at most four profiles, since

    5(t-3)^2-n((t-3)+4(k+2))=s^2-136s+80>0.

For d>=1, a nonliftable profile occurs at at most one scalar, by coprimality of two distinct T_gamma and the fact that one has degree d. Liftable profiles are polynomials of degree at most k-1-d and define genuine joint sources. Their core sizes are at least t-3. This repeats the proved normalization argument with one additional degree of slack.

The following branches are safe:

* d=0: at most four normalized polynomial profiles, each charging at most h<=3 outside points, plus the possible scalar with T_gamma=0. Total at most 13.
* h=0: if every profile lifts, the received word is on the carrier everywhere and there is at most one scalar per coordinate. Otherwise at most three profiles lift; the two base cores and possible extra core give count at most 2(s+2)+(s+4)+2=3s+10<=n.
* d=2,h=1: call liftable profiles strong when their core is at least t-2. A weaker source needs at least three nonjoint points in an MCA witness, while T_gamma has at most two roots in U, so it must cancel at the sole outside point and accounts for at most one scalar. If at most three profiles are strong, the source budgets plus the exceptional profiles give at most 3s+9. If all four are strong, their core sum is at least 2(t-1)+2(t-2)=12s-10, with pair intersection cap k-3. If they all missed the outside point, on N=n-1 points the inequality binom(r,2)>=2r-3 would force at least 12s-17 pair incidences, exceeding the 6(k-3)=12s-18 budget. Thus all points are on the carrier and the n bound follows.
* d=1, h<=2, with at most three strong liftable profiles, where strong means core at least t-1: a weaker profile needs at least two nonjoint witness points and has at most one carrier root in U, so it must cancel at one of the at most two outside points. It accounts for at most two scalars. Nonliftable profiles account for one each. A loose total is 3(s+2)+4=3s+10<=n.

If d=1 has four strong profiles, they cannot all miss two points: their core sum is at least 4(t-1)=12s-8 and pair incidence cap is 6(k-2)=12s-12; on n-2 points, binom(r,2)>=2r-3 would give at least 12s-10 incidences. Thus at most one point remains outside all four cores. If no point remains, the global carrier count is safe.

The only unresolved configuration is therefore four distinct scalar polynomials f_0,...,f_3 of degree at most k-2, with joint cores at least t-1, all received values on their common linear carrier except at one remaining point o. Equivalently, on U=D\{o} there is a scalar word w such that every f_i agrees with w at least t-1 times and for every x in U there is an index i with f_i(x)=w(x).

## Exact three-pattern census

Let N_j count coordinates in U belonging to exactly j of the four agreement sets. Because they cover U, N_0=0. Their total membership R is at least 4(t-1)=12s-8 and their pair-incidence count is at most 6(k-2)=12s-12.

The inequality binom(r,2)>=2r-3 forces R<=12s-8, so every core has size exactly t-1 and R=12s-8. Moreover

    sum_x (binom(r_x,2)-2r_x+3)=N_1+N_4<=1,
    2N_1+N_2-N_4=3(n-1)-R=5.

Exactly three possibilities remain:

| Type | N1 | N2 | N3 | N4 | Pair-root slack |
|---|---:|---:|---:|---:|---:|
| A | 0 | 5 | 4s-6 | 0 | 1 |
| B | 1 | 3 | 4s-5 | 0 | 0 |
| C | 0 | 6 | 4s-8 | 1 | 0 |

At a double node record its two owners as an edge of K4. At a triple node label the omitted source. Enforcing all six individual pair-root bounds yields the following complete incidence census, up to relabeling:

* A: the five double edges are K4 minus one edge, each used once. If the missing edge joins sources 0,1, the omitted-source triple block sizes are (s-2,s-2,s-1,s-1). The only unsaturated pair-root budget is the opposite edge 2,3, with slack one.
* B: if source 0 owns the singleton, the three double edges are the triangle on sources 1,2,3. Triple block sizes are (s-2,s-1,s-1,s-1). Every pair-root budget is saturated.
* C: all six edges occur once. Every triple block has size s-2. Every pair-root budget is saturated.

The attached finite census enumerates all edge-count assignments and independently recovers six labeled A patterns, one B pattern for a fixed singleton owner, and one C pattern. These are incidence patterns, not polynomial realizations.

## Quadratic or linear reduced Pluecker identity

Set

    V_1=(f_0-f_1)(f_2-f_3),
    V_2=(f_0-f_2)(f_1-f_3),
    V_3=(f_0-f_3)(f_1-f_2).

They are nonzero polynomials of degree at most 2(k-2)=n-4 and satisfy V_1-V_2+V_3=0. Every triple node divides all three products once; every quadruple node divides all three at least twice. Thus their common gcd G has degree at least N_3+2N_4.

Consequently V_i/G have degree at most two in types A and C, and at most one in type B:

| Type | Guaranteed deg G | Reduced degree bound |
|---|---:|---:|
| A | n-6 | 2 |
| B | n-5 | 1 |
| C | n-6 | 2 |

These bounds use root multiplicity through polynomial factors and hold in every characteristic. They do not imply existence or nonexistence of the required f_i on the fixed subgroup.

## Every realization would yield an over-budget original-MCA family

This is a conditional construction: assume the required polynomials and word w on the actual D\{o} have been found. Use the carrier (A,B)=(X,1), so source pairs are

    z_i=(X f_i,f_i),

with degrees below k. On U set the received pair to (x w(x),w(x)). At o choose a received pair (a,b) off the line a=o b as specified below. The four source cores remain exactly t-1.

Every nonquadruple coordinate of U has a source nonowner. Its nonzero residual cancels at gamma=-x, giving n-1-N_4 distinct ordinary scalars. The support is that source's full core plus the coordinate, of size t. Since t-1>=k, any competing joint pair would be pinned by the core and fail at the added coordinate. These are actual same-support MCA witnesses.

Let r_o be the number of distinct values f_i(o). Types B and C saturate every pair-root budget on U, so no pair can also agree at o: r_o=4. Type A has only one unit of pair-root slack in total, so at most one pair can agree at o; hence r_o>=3.

For each distinct local value v=f_i(o), a fresh cancellation scalar is

    gamma_v=(o v-a)/(b-v).

Let Gamma be the ordinary scalar set. Avoid the following affine lines in F^2:

* a=o b, to stay off the carrier and make ratios for distinct v distinct;
* b=v, to make each ratio finite;
* a+gamma b=(o+gamma)v for each gamma in Gamma and each distinct v, to avoid all ordinary scalars.

There are at most 1+r_o+r_o|Gamma|<=4n+1 forbidden lines. Over the production field, each line has P points and P>4n+1, so their union has fewer than P^2 points. A permissible (a,b) therefore exists. Each fresh scalar has the same core-plus-hole original-MCA proof.

The resulting lower counts would be

    Type A: (n-1)+3 >= n+2,
    Type B: (n-1)+4 = n+3,
    Type C: (n-2)+4 = n+2.

Thus a stronger abstract charging argument cannot remove this final case: any polynomial realization already supplies the desired strict over-budget event. The missing ingredient is the polynomial realization itself.

## The conditional construction has no high-core joint source

All four selected sources have exact core t-1. A distinct source with core at least t would give five distinct joint pairs with cores at least t-1, whose pair intersections are at most k-1. This contradicts

    5(t-1)^2-n((t-1)+4(k-1))=s^2-36s+20>0.

One can also verify this through the requested carrier and scalar-profile route. For a hypothetical high-core source (p,q), the polynomial p-Xq has degree at most k and vanishes at at least t-1>k points of U. It is zero, so the source has the form (X f_*,f_*) with deg f_*<=k-2. The off-carrier hole cannot belong to its core, so f_* would be a fifth distinct scalar profile on U agreeing at least t-1 times. The sharper five-list gap on U is

    5(t-1)^2-(n-1)((t-1)+4(k-2))=s^2-9s+10>0.

Both arguments prove that the high-core joint list would be empty. Neither proves the requisite four-profile configuration exists.

## Status

The two-short-core extension reduces to the explicit degree-(k-2), four-profile realization problem above. Types A/B/C, the small Pluecker quotient, the conditional over-budget count, and the empty-high-core conclusion are established deductions. No production polynomials realizing any type were found in this batch. No universal two-short-core safety theorem or actual first-step disproof is claimed.

If a realization were found on the production subgroup, its bad count would
exceed `floor(P/2^128)=n` at radius `(s+1)/n`. Combined with the existing
supremum lower bound, this would give the exact first-prime, rate-one-half
threshold `deltaStar=268435457/2^30`. This conclusion is conditional on
the missing realization and concerns only that challenge instance.
