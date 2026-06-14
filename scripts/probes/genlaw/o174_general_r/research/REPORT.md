# E_{1,2} Literature Hunt — the demand-side prize wall (lalalune/ArkLib #389)

Research agent report. Date 2026-06-13. Worktree /home/nubs/Git/ArkLib-232.
Scope: find ANY published result upper-bounding the joint additive energy / simultaneous-second-moment
level-set of a thin 2-power multiplicative subgroup mu_n (n=2^k <= ~512) of F_q (q up to ~2^256), in the
prize regime (q-independent, deep band). Anti-fabrication: a result counts only if it gives an UPPER
bound, in the right DIRECTION, over a MULTIPLICATIVE SUBGROUP ground set, in the prize WINDOW.

---

## 0. THE OBJECT, RESTATED (source: scripts/probes/genlaw/o174_general_r/analytic/CONNECT.md)

- Joint level-set  N2(c1,c2) = #{ (r+1)-subsets S in mu_n : sum_{x in S} x = c1 AND sum x^2 = c2 }.
- Prize target = the e1-axis SUPPORT of N2 (count of DISTINCT bad scalars gamma = -sum x), cut by the
  line's e2 = phi(e1) relation:  #bad(r) <= K := 2^r * C(n/2, r).
- Collision-count handle [PROVEN in-tree, axiom-clean, Round7SecondMoment]:
  sum N2^2 = collisionCount(mu_n, r+1) = #{(S,S'): sum x = sum x' AND sum x^2 = sum x'^2}
  = the JOINT higher-order additive energy E_{1,r+1} of mu_n over the (sum, sum-of-squares) pair.
- Cauchy-Schwarz, in-tree choose_sq_le_support_mul_collisionCount:
  C(n,r+1)^2 <= #support * collisionCount  ==>  #support >= C(n,r+1)^2 / collisionCount.

DIRECTION FACT (the crux): an UPPER bound on the collision count (= the joint energy) gives a LOWER bound
on the support. The prize needs an UPPER bound on the support. Verified against the actual Lean lemma
signature. Decisive for every energy-type paper below.

Known floor (not re-derived): pair energy E_2 = #{(a,b,c,d) in mu_n^4 : a+b=c+d, a^2+b^2=c^2+d^2}
= 3n^2 - 3n (Duke-Garcia). The s=2 case of the object; the ONLY landed exact value.

---

## 1. RANKED RELEVANT PAPERS

### #1 Mansfield-Mudgal, "A Quadratic Vinogradov Mean Value Theorem in Finite Fields" [PARTIAL]
(closest existing UPPER bound on the EXACT object; fails the prize on direction + field, not on shape)
- arXiv:2310.02950 ; Q. J. Math. 75 (2024) no. 3, 1007-1029.
- What it bounds (verbatim setup): J_s(A) = #{ x_1..x_2s in A : sum(x_i - x_{i+s}) = 0 AND
  sum(x_i^2 - x_{i+s}^2) = 0 }. EXACTLY the joint additive energy / k=2 Vinogradov system -- the PTE-type
  system (sum x = sum y, sum x^2 = sum y^2) -- i.e. our collisionCount with s = r+1 (ordered tuples).
- Theorem 1.3: p prime, s>=3, A subset F_p, |A| << p^{1/2}  ==>  J_s(A) << |A|^{2s-2-1/9}
  (trivial bound |A|^{2s-2}; saves |A|^{1/9}). Constant absolute, q-independent.
- Theorem 1.4 (sparser, better exponent): s>=4, |A| <<_s p^{1/(13(s-1))} ==>
  J_s(A) <<_s |A|^{2s-2-1/7+eta_s}, eta_s = (4/11)^{s-3}*(2/63).
- GROUND SET = ARBITRARY A subset F_p. <-- the breakthrough vs LMRW/GPP: mu_n IS a valid instance of A.
  No ground-set mismatch in principle. (CONNECT.md predates this paper / treats only LMRW+GPP for MSS;
  this is the genuinely new hit my pass adds.)
- s>=3 covers our whole open range: r=3 -> (r+1)=4-subsets -> s=4; r general -> s=r+1 >= 4.
  (s=2 excluded precisely because the diagonal forces J_2 >= |A|^2 -- consistent with Duke-Garcia
  E_2 = 3n^2-3n; the theorem improves only the OFF-diagonal, which is why it starts at s>=3.)
- WHY IT STILL FAILS IN THE PRIZE REGIME (three independent reasons, all verified):
  1. WRONG DIRECTION (decisive, regime-independent). Upper-bounds the collision count / energy. Via the
     in-tree Cauchy-Schwarz (C(n,a)^2 <= #support*collisionCount) an energy UPPER bound yields a
     #support >= ... LOWER bound. The prize needs #bad = e1-support <= K, an UPPER bound. An energy bound
     never by itself caps the support; you need a per-fiber N2(c1,c2) <= small + a separate support arg.
  2. PRIME FIELD ONLY (regime). Stated for A subset F_p, p prime. Engine is incidence-geometric:
     Rudnev-Wheeler Mobius/hyperbola incidences in positive char [Lemma 2.1, needs |A|<<p^{1/2}] +
     Stevens-de Zeeuw point-line incidences "over arbitrary fields" [Lemma 2.2, needs |L|^13 << p^15 |P|^2].
     Stevens-de Zeeuw IS arbitrary-field, so the machinery is not hard-locked to F_p -- BUT over
     F_q=F_{p^m} every such incidence bound carries a no-large-subfield condition (degrades when A meets a
     proper subfield). The paper never states the F_q version; for faithful q=p (large prime) it transfers
     cleanly, for genuine extension fields it is an unproven transfer.
  3. WRONG FUNCTIONAL / OBJECT. Even granting field transfer, J_s is the FULL collision count (sum N2^2),
     not the e1-axis support (#bad). Different functionals of the same level-set.
- VERDICT for #1: the single most on-target published theorem -- same system (quadratic Vinogradov = PTE
  pair), arbitrary-set ground (subgroup allowed), q-independent constant, covers s>=3. A genuine UPPER
  bound on the JOINT higher-order energy of mu_n in the F_p case. Does NOT close the prize: bounds the
  energy not the support (wrong direction through Cauchy-Schwarz), and is the collision count not its
  e1-axis projection. [PARTIAL].

### #2 Mudgal, "Diameter-free estimates for the quadratic Vinogradov MVT" [FAILS-IN-REGIME]
(best exponent on the SAME system, but over R/Z, not a finite field)
- arXiv:2008.09247 ; Proc. LMS (3) 126 (2023) no. 1, 76-128.
- Bounds the SAME quadratic-Vinogradov/PTE system E_{s,2}(A) over A subset R, diameter-FREE:
  E_{s,2}(A) <<_s |A|^{2s-3+eta_s}, eta_3=1/2, eta_s=(1/4-1/7246)*2^{-s+4} (s>=4). Exponent -> floor 2s-3.
- WHY IT FAILS: ground set R/Z, not a finite field and not a subgroup. The finite-field analogue is #1
  (with weaker 2s-2-1/9 because finite-field incidences are weaker -- the paper says so). Still energy
  (wrong direction), not support. [FAILS-IN-REGIME] -- wrong field.

### #3 Murphy-Rudnev-Shkredov-Shteinikov, "On the few products, many sums problem" [FAILS-IN-REGIME]
- arXiv:1712.00410 (surfaced by "joint additive energy" search; actually a few-products-many-sums paper).
- Bounds E(A) <~_M |A|^{49/20} (FIRST-order additive energy #{a+b=c+d}) for small mult. doubling, and
  (M=1) for mult. subgroups Gamma <= F_p^x of order O(sqrt p).
- WHY IT FAILS: first-order energy (one constraint), not the JOINT two-constraint object; F_p, |Gamma|~sqrt p;
  energy = wrong direction. Right family, wrong moment order. [FAILS-IN-REGIME].

### #4 Shkredov, "On additive shifts of multiplicative subgroups" (1102.1172) + common-energy 2025 [FAILS-IN-REGIME]
- E^+(Gamma) (first-order) of Gamma <= F_p^x; best E(Gamma) << |Gamma|^{22/9}*polylog for |Gamma|<<p^{3/5}.
- WHY IT FAILS: first-order only; prime-field (Stepanov); documented F_q-transfer failure (in-tree O30);
  wrong direction. [FAILS-IN-REGIME].

### #5 Lai-Marino-Robinson-Wan (1910.05894) and Gottig-Perez-Privitelli (2401.06964) [FAILS-IN-REGIME]
- Moment-subset-sum (MSS). Bound the JOINT m-moment count N_m(k,b) but over D = F_q (full field) or
  D = g(F_q) (poly image) -- NOT a subgroup -- with q-dependent main term C(|D|,k)/q^m + q^{k/2} error,
  window k large / m small / k <= q^{0.24}.
- WHY IT FAILS: ground-set mismatch (full field/poly image vs thin subgroup); main term <<1 hence vacuous
  for thin G; needs k large (GPP needs k>=125 for m=2); q-dependent shape loses the /q the prize forbids.
  Full treatment in CONNECT.md sec 2,3(A); re-verified abstracts, no change. [FAILS-IN-REGIME] (4 axes).

### #6 Vanishing-sum classification: Christie-Dykema-Klep (2008.11268), Laba-Marshall (2202.07555),
###     Lam-Leung (math/9605216) [FAILS-IN-REGIME] (existence/support, not a count)
- Classify WHICH vanishing sums of roots of unity exist and the MINIMAL weight; n=2^a weight set = even
  numbers, built from antipodal {z,-z} weight-2 atoms. Govern which deep-band bad configs EXIST and the
  dyadic structure behind the r=3 antipodal reduction.
- WHY IT FAILS: bound the support/structure of the relation lattice and minimal weight; do NOT count the
  joint level-set or distinct-e1 count. Orthogonal (support, not count). [FAILS-IN-REGIME].

### #7 PTE-construction-from-roots-of-unity: "A New Proof of the PTE Problem" (1411.6168) +
###     cyclotomic-PTE line [FAILS-IN-REGIME] (construction/existence, never a count)
- CONSTRUCT PTE solutions (equal sum x, sum x^2, ...) USING roots of unity / cyclotomic identities, prove
  existence at each size. (Read 1411.6168: constructive existence proof; no enumeration.)
- WHY IT FAILS: wrong direction of use -- roots of unity are the TOOL to build integer PTE solutions; they
  never UPPER-BOUND the NUMBER of PTE pairs from a fixed subgroup. No counting, no upper bound, no
  subgroup-restricted enumeration in this line. [FAILS-IN-REGIME].

### #8 Hegyvari, "On the distribution of additive energy revisited" (2602.01781) [FAILS-IN-REGIME]
- Freshest (Feb 2026). Studies the DISTRIBUTION/spectrum of mult-energy VALUES (gaps between consecutive
  achievable energies) via Fourier + Kim-Vu, and k with A^k = F_p^*.
- WHY IT FAILS: about distribution of energy values, not an upper bound on a specific subgroup's joint
  higher-order energy; first-order; F_p. Confirmed via abstract+intro. [FAILS-IN-REGIME].

### #9 Hanson(-Petridis) (1905.09134 / PLMS 2021), "Refined estimates ... sumsets in roots of unity" [FAILS-IN-REGIME]
- Additive/sumset structure of QR/roots of unity in F_p; Paley clique <= sqrt(p/2)+1; co-Sidon decomps.
  First-order; F_p; nontrivial only for |mu_d| <~ sqrt p. [FAILS-IN-REGIME].

### Also screened, not relevant:
- "Additive energy of polynomial images" (2306.10677): poly images over Z_m, not subgroups. [FAILS]
- "Additive decompositions of large mult. subgroups" (2304.13801): A+A non-decomposability, not a count. [FAILS]
- "On multiplicative energy of subsets of varieties": multiplicative (ab=cd) energy, wrong operation. [FAILS]

---

## 2. THE PTE-CONNECTION ANALYSIS (the lead the task flagged hardest)

The connection is REAL and is the right framing -- but it has already been chased to its sharpest published
edge, and that edge is the wrong-direction energy bound.

1. The deep-band joint constraint (sum_{x in S} x = c1, sum x^2 = c2) for two subsets S,S' with
   (c1,c2)=(c1',c2') is LITERALLY a Prouhet-Tarry-Escott system of degree 2 (sum x = sum y, sum x^2 =
   sum y^2). The collision count sum N2^2 = the number of PTE-degree-2 solution PAIRS with both parts from
   mu_n. This is also exactly the k=2 Vinogradov mean value system (PTE-degree-k <=> Vinogradov-degree-k).
   So joint additive energy E_{1,r+1} = PTE-degree-2 count = quadratic Vinogradov J_{r+1} are the SAME
   object. This identification is the key clarifier of this pass.

2. The PTE literature splits cleanly and NEITHER half closes the prize:
   - Construction half (1411.6168, cyclotomic-PTE): builds PTE solutions out of roots of unity. Wrong
     direction of use -- roots of unity are the generator, not the constrained domain; never a count.
   - Counting half = the Vinogradov mean value literature. The finite-field instance is #1
     (Mansfield-Mudgal). The PTE count restricted to a set A subset F_p IS J_s(A) and the SOTA is
     J_s(A) << |A|^{2s-2-1/9}. So "the PTE solution count restricted to a multiplicative subgroup" -- the
     task's exact phrasing -- IS bounded in the literature (#1), for A subset F_p, subgroups included.
     The PTE lead therefore terminates at Mansfield-Mudgal.

3. Why even this sharpest PTE/Vinogradov bound does not pay the prize (the gap):
   (a) DIRECTION: bounds the PTE solution COUNT (= energy = collisionCount), which via Cauchy-Schwarz
       LOWER-bounds the support; the prize wants an UPPER bound on the e1-axis support.
   (b) FUNCTIONAL: collision count != e1-axis support (distinct-c1 projection). Need per-fiber
       N2(c1,c2) <= small + a support argument, which Vinogradov machinery does not provide.
   (c) FIELD: stated over F_p; F_q (extension) transfer is conditional (incidence/subfield).
   (d) The integer version reaching near-optimal 2s-3 (Mudgal 2008.09247) is over R/Z, no F_q transfer.

   So PTE => Vinogradov => Mansfield-Mudgal is the correct and complete chase, and it lands on [PARTIAL]:
   the joint energy of mu_n is genuinely UPPER-bounded in the literature (F_p case), but that is the wrong
   functional in the wrong direction for #bad <= K.

---

## 3. HONEST VERDICT

(iii) GENUINELY OPEN -- with one important refinement to the in-tree CONNECT.md verdict.

The prize quantity -- a q-independent poly(n) UPPER bound on the e1-axis SUPPORT of the (e1,e2) joint
level-set over the thin 2-power multiplicative subgroup mu_n (equivalently #bad <= 2^r*C(n/2,r)) -- is NOT
proven anywhere in the 2015-2026 literature. NOT (i) proven-somewhere.

Refinement my pass adds to CONNECT.md: the collision-count / joint-energy sibling of the object
(E_{1,r+1}(mu_n) = the PTE-degree-2 / quadratic-Vinogradov solution count) IS upper-bounded in the
published literature -- Mansfield-Mudgal Thm 1.3, J_s(A) << |A|^{2s-2-1/9} for arbitrary A subset F_p,
|A| << sqrt p, s>=3 -- which DOES include mu_n as a ground set. (CONNECT.md sec 3(C) called the joint
higher-order energy "itself OPEN; only the E_2 floor known"; that is too strong -- the GENERAL-s joint
energy has a nontrivial published upper bound over F_p via quadratic Vinogradov.) So:

- The JOINT higher-order energy E_{1,r+1}(mu_n) over F_p is a special case of a KNOWN framework (quadratic
  Vinogradov in finite fields, Mansfield-Mudgal) that IS instantiated for arbitrary sets and hence for
  mu_n -- [PARTIAL], the energy is bounded.
- The PRIZE object (e1-axis SUPPORT upper bound, q-independent incl. extension fields) is GENUINELY OPEN --
  three independent fatal gaps: (1) DIRECTION (energy upper bound -> support LOWER bound via the verified
  in-tree Cauchy-Schwarz; we need support UPPER bound); (2) FUNCTIONAL (collision count vs its e1-axis
  projection); (3) FIELD (F_p only; F_q/extension transfer conditional). Cleanest single obstruction is
  (1): no published result bounds the SUPPORT from above; every relevant result bounds an ENERGY/collision
  count, the wrong end of Cauchy-Schwarz.

This is a REDUCES-TO-OPEN finding, NOT a solution (consistent with the #232/#389 CLOSED honesty bar). r=3
stays the only PROVEN rung (#bad = n*C(n/4,2)+1, axiom-clean); r>=4 stays the named open analytic core
(ExcessCensusLaw), with all-n MEASURED margins 2.46x-20.1x and "production q = worst case" as the only
structural reductions in hand.

One concrete forward lead (honest, not a claim): the ONLY published machinery that bounds the exact system
over a finite field is the incidence-geometry route (Mobius/hyperbola incidences a la Rudnev-Wheeler +
Stevens-de Zeeuw point-line) inside Mansfield-Mudgal. If a per-fiber N2(c1,c2) bound (not just the summed
energy) can be extracted from those incidence counts -- bounding the LEVEL-SET fiber directly rather than
its second moment -- that would turn an energy bound into a support bound and is the most literature-
grounded attack on #bad <= K. No paper does this for mu_n today.

---

## 4. READING LIST (acquired PDFs / abstracts; tags)

[PARTIAL]  Mansfield-Mudgal, Quadratic Vinogradov MVT in finite fields, QJM 75 (2024)  arXiv:2310.02950
           UPPER-bounds the EXACT joint system J_s(A) << |A|^{2s-2-1/9} over arbitrary A in F_p (mu_n
           allowed); wrong direction+functional+field for the prize. PDF acquired & text-extracted
           (/tmp/mansfield_mudgal.txt).
[FAILS]    Mudgal, Diameter-free quadratic Vinogradov, PLMS 126 (2023)  arXiv:2008.09247
           Same system, near-optimal 2s-3 exponent, but over R/Z not finite fields.
[FAILS]    Murphy-Rudnev-Shkredov-Shteinikov, Few products many sums  arXiv:1712.00410
           First-order subgroup energy E(Gamma) <~ |Gamma|^{49/20}; wrong moment order. PDF acquired.
[FAILS]    Shkredov, Additive shifts of mult. subgroups  arXiv:1102.1172   First-order E^+, F_p, sqrt p.
[FAILS]    Lai-Marino-Robinson-Wan, Moment subset sums  arXiv:1910.05894   JOINT but poly-image/full-field.
[FAILS]    Gottig-Perez-Privitelli  arXiv:2401.06964     JOINT m-moment over F_q/poly-image; k>=125 for m=2.
[FAILS]    Christie-Dykema-Klep, Minimal vanishing sums  arXiv:2008.11268  Support/structure, not a count.
[FAILS]    Laba-Marshall  arXiv:2202.07555               Minimal weight of vanishing sums; not a count.
[FAILS]    Lam-Leung, Vanishing sums of m-th roots of unity  arXiv:math/9605216  Which weights vanish.
[FAILS]    A New Proof of the PTE Problem  arXiv:1411.6168  Constructs PTE from roots of unity; no count. PDF acquired.
[FAILS]    Hegyvari, Distribution of additive energy revisited  arXiv:2602.01781  Distribution of values. PDF acquired.
[FAILS]    Hanson(-Petridis), Sumsets in roots of unity  arXiv:1905.09134  First-order; F_p; |mu_d|<~sqrt p.

Key dependency inputs inside #1 (for the forward lead): Rudnev-Wheeler "Mobius hyperbolae in positive
characteristic" (Finite Fields Appl.); Stevens-de Zeeuw "improved point-line incidence over arbitrary
fields" (Bull. LMS); Shkredov-Shparlinski "Double character sums over intervals and arbitrary sets"
(Proc. Steklov) [Lemma 2.10].
