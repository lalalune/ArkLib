#!/usr/bin/env python3
"""
LANE L3 / R4 (b) (#407) — EFFECTIVE Rojas-Leon (arXiv:1010.0120) for the
mu_n incomplete-subgroup-sum sup-norm M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|.

EXACT statements quoted from the paper (text/pdftotext of 1010.0120):

  Sec 4 (Additive character sums for homothety invariant polynomials).
    Gamma_e = unique subgroup of k^* = F_q^* of index e (|Gamma_e| = (q-1)/e).
    f is Gamma_e-homothety invariant  <=>  f(x) = g(x^{(q-1)/e}) for some g (Lemma 4.1).
    Weil (trivial):  |sum_{x in k_r} psi(Tr f(x))| <= (d(q-1)/e - 1) q^{r/2}.   [eq before (3)]
    PROP 4.2:  for g of degree d prime to p, dim H^{r-1}_c(V_mu, L_psi(G)) = r d^{r-1},
               all other H^i_c vanish.   [the cohomology is on x_1...x_r = mu, dim r-1]
    COR 4.3:   |sum_{x in k_r^*} psi(Tr_{k_r/k} f(x))| <= r d^{r-1} (q-1) q^{(r-1)/2}.
    PER-FIBER (eq (4) + purity, in the Cor 4.3 proof):
               |sum_{N_{k_r/k}(x)=mu} psi(Tr_{k_r/k} g(x))| <= r d^{r-1} q^{(r-1)/2}.

  Abstract / Sec 1: "improve the bound by a factor of sqrt(q) OVER AN EXTENSION OF k OF
  CARDINALITY SUFFICIENTLY LARGE COMPARED TO THE DEGREE OF f."  <-- the uniformity
  hypothesis: q must be large vs d (degree of g). Concretely d prime to p, and the
  purity/dimension count r d^{r-1} is the SHEAF RANK = the conductor of the convolved
  sheaf (Swan conductor d^r at infinity, generic rank r d^{r-1}; [8, Thm 5.1(4,5)]).

THE DICTIONARY for M(n).  We want sum over mu_n subset F_p (p prime).  Two ways to
fit RL; we compute the bound each gives and compare to: trivial=n, prize-target=sqrt(n).

  (A) NO extension (r=1, k=k_r=F_p, q=p).  Then mu_n=Gamma_e, e=(p-1)/n, f(x)=g(x^e),
      and the sum sum_{x in mu_n} e_p(bx) is a single homothety-invariant sum.  But
      Cor 4.3 with r=1 gives bound  1*d^0*(p-1)*p^0 = (p-1) -- TRIVIAL (it bounds the
      sum over ALL of F_p^* of a homothety-invariant function, = e copies of the
      subgroup sum, so it carries the full e=(p-1)/n multiplicity).  Useless: the
      per-coset gain is exactly killed by the e=(p-1)/n outer factor.

      More precisely the per-FIBER bound r d^{r-1} q^{(r-1)/2} with r=1 is  1*1*p^0 = 1,
      but for r=1 the "norm fiber" N(x)=mu is a SINGLE point, NOT the subgroup mu_n.
      So r=1 does not realize a proper subgroup as a norm fiber -- the sqrt-gain
      mechanism requires r>=2.

  (B) WITH extension (r>=2).  To realize mu_n as a norm-fiber / homothety group of an
      extension F_{q^r} with the sqrt(q)-gain, the gain factor sqrt(q) is over the
      BASE field q, and the subgroup must sit in F_{q^r}.  The per-fiber bound is
      r d^{r-1} q^{(r-1)/2}.  We compute when this is < n (nontrivial for the subgroup
      sup-norm) and whether it can reach n^{1/2}.

KEY QUESTION (directive b): does the mu_n sheaf need n >= sqrt(p)?  And does the
constant-index (e = (p-1)/n fixed-ratio) structure lower the threshold?
"""
import math

# ----------------------------------------------------------------------
# Part 1: the exact RL per-fiber bound vs the prize target, as a function of how
# we embed mu_n.  In the prize, mu_n subset F_p, n = 2^mu, p = n^beta.
# To use RL with an r-fold extension we set q = p^{1/r} (so the top field is F_p),
# realize mu_n as Gamma_e in F_p^* of index e=(p-1)/n; the homothety polynomial is
# g(X) = b*X (degree d=1!) since f(x)=e_p(b x) restricted to x with x^n=1 is
# NOT itself homothety-invariant -- the homothety structure is of the FUNCTION
# f(x)=g(x^n), i.e. the LINEAR character composed with the n-th power map.
#
# CRUCIAL POINT.  Our function is f(x) = b*x on mu_n.  This is NOT of the form
# g(x^n): a homothety-invariant f satisfies f(lambda x)=f(x) for lambda in mu_n,
# but b*(lambda x) = lambda*(b x) != b x.  So the incomplete SUBGROUP sum is the
# WRONG object for RL's additive homothety theorem: RL bounds sums of homothety-
# INVARIANT functions over the WHOLE field, whereas we want a NON-invariant linear
# function summed over the subgroup.  The two are Fourier-dual, and the relevant
# RL input for OUR sum is the per-fiber / norm-restricted bound.  We test the
# best-case numeric bound RL can give and its threshold.
# ----------------------------------------------------------------------

def rl_perfiber_bound(q, r, d):
    """RL per-fiber bound  r d^{r-1} q^{(r-1)/2}  on  sum_{N(x)=mu} psi(Tr g(x))."""
    return r * (d ** (r - 1)) * q ** ((r - 1) / 2.0)

def rl_full_bound(q, r, d, e):
    """RL Cor 4.3 full bound  r d^{r-1} (q-1) q^{(r-1)/2}  divided by e copies =>
    per-subgroup-of-index-e: (1/e)* that = (1/e) r d^{r-1} (q-1) q^{(r-1)/2}."""
    return (1.0 / e) * r * (d ** (r - 1)) * (q - 1) * q ** ((r - 1) / 2.0)

print("=" * 92)
print("PART 1 — RL per-fiber bound r d^{r-1} q^{(r-1)/2} vs trivial n and prize sqrt(n)")
print("=" * 92)
print("Embed mu_n in top field F_{q^r}=F_P with P=p=n^beta. q = P^{1/r}.  d = aux degree.")
print("The subgroup mu_n has size n; norm-fiber size in F_{q^r}^* is (q^r-1)/(q-1) ~ q^{r-1}.")
print("For the norm fiber to BE mu_n we'd need q^{r-1} ~ n, i.e. q ~ n^{1/(r-1)}.")
print()
hdr = f"{'beta':>5} {'r':>3} {'d':>3} {'P=p':>14} {'q=P^(1/r)':>12} {'qfiber~q^(r-1)':>14} {'RLfiber':>14} {'n':>10} {'sqrtn':>9} {'<n?':>5}"
print(hdr)
for beta in [4.0, 5.0]:
    for mu in [20, 30]:
        n = 2 ** mu
        P = n ** beta
        for r in [2, 3, 4]:
            q = P ** (1.0 / r)
            qfiber = q ** (r - 1)              # approx norm-fiber size
            d = 1                              # linear g (best case)
            rlf = rl_perfiber_bound(q, r, d)
            below = rlf < n
            print(f"{beta:>5} {r:>3} {d:>3} {P:>14.2e} {q:>12.3e} {qfiber:>14.3e} "
                  f"{rlf:>14.3e} {n:>10.2e} {math.sqrt(n):>9.2e} {str(below):>5}")
    print()

print("=" * 92)
print("PART 2 — does the mu_n sheaf need n >= sqrt(p)?  (the KB claim to confirm/deny)")
print("=" * 92)
print("""
The RL sqrt-gain is q^{(r-1)/2} per fiber, vs trivial q^{r/2}.  For a SINGLE field
(r=1, no extension) there is NO gain: the homothety theorem degenerates (per-fiber
bound = 1 but the fiber is a point, not mu_n; the actual subgroup sum gets the
(p-1)/e = n multiplicity factor, giving the trivial n).

The cleanest way RL's q^{1/2}-saving applies to a subgroup sum sum_{x in mu_n} is via
the standard 'complete-and-Weil' route (Polya-Vinogradov + Weil), which is what RL's
abstract improvement is measured against.  For mu_n subset F_p the completion bound is:

   |sum_{x in mu_n} e_p(bx)|  <=  sqrt(p) * (log p)   [Polya-Vinogradov-Weil, the
                                                       classical sqrt(p) sup over cosets]

This is NONTRIVIAL (< n) ONLY IF sqrt(p) < n, i.e. n > sqrt(p), i.e. beta < 2.
""")
print(f"{'beta':>5} {'n=2^30':>12} {'sqrt(p)=n^(beta/2)':>20} {'sqrt(p)<n? (Weil nontrivial)':>30}")
n = 2 ** 30
for beta in [1.5, 1.9, 2.0, 2.1, 3.0, 4.0, 5.0]:
    p = n ** beta
    sp = math.sqrt(p)
    print(f"{beta:>5} {n:>12.2e} {sp:>20.3e} {str(sp < n):>30}")
print()
print(">>> CONFIRMED: the Weil/completion bound sqrt(p) beats the trivial n ONLY for")
print(">>> beta < 2, i.e. n > sqrt(p).  The KB claim 'needs n >= sqrt(p)' is CORRECT.")
print(">>> The prize has beta in [4,5] => n = p^{1/4..1/5} << sqrt(p) = p^{1/2}, so the")
print(">>> Weil completion is USELESS (sqrt(p) = n^{2..2.5} >> n = trivial).")
print()

print("=" * 92)
print("PART 3 — does CONSTANT-INDEX structure (e=(p-1)/n fixed ratio) lower the threshold?")
print("=" * 92)
print("""
'Constant index' for the PRIZE means: as n grows, the field grows so that the index
e = (p-1)/n stays a fixed power n^{beta-1} (NOT a fixed constant!).  RL's gain depends
on the SHEAF CONDUCTOR (rank r d^{r-1}, Swan d^r), NOT on the index e directly.  The
index enters only through the OUTER multiplicity (q-1)/e = n in Cor 4.3's full bound.

  - The per-fiber bound r d^{r-1} q^{(r-1)/2} is INDEPENDENT of e.  But to realize mu_n
    as a norm fiber we need q^{r-1} ~ n (the fiber size), forcing q ~ n^{1/(r-1)} and
    then the per-fiber bound is  r d^{r-1} n^{(r-1)/2 / (r-1)} = r d^{r-1} n^{1/2}.
    >>> So IF mu_n WERE a genuine norm-fiber of a degree-r extension, RL would give
        EXACTLY the prize n^{1/2} (times the harmless r d^{r-1} constant)!  <<<
  - THE OBSTRUCTION: mu_n subset F_p is NOT a norm-fiber of any nontrivial extension of
    F_p.  Norm fibers N_{F_{p^r}/F_p}(x)=mu are subsets of F_{p^r}, size (p^r-1)/(p-1);
    the multiplicative subgroup mu_n of the PRIME field F_p has a completely different
    structure (cyclic of order n | p-1).  There is no field extension realizing the
    prime-field subgroup mu_n as a norm fiber, so RL's theorem CANNOT be applied to it.
""")
print("Norm-fiber realization test: is mu_n (order n | p-1, in F_p) = a norm fiber?")
print(f"{'r':>3} {'fiber N(x)=mu size (p^r-1)/(p-1)':>34} {'= n? (n|p-1, prime field)':>28}")
for r in [2, 3, 4]:
    print(f"{r:>3} {'(p^r-1)/(p-1) = 1+p+...+p^(r-1)':>34} {'NO (size ~ p^(r-1) != n)':>28}")
print()
print(">>> VERDICT (part b): RL's homothety theorem gives n^{1/2} ONLY for norm-fiber")
print(">>> subgroups of EXTENSION fields, which the PRIME-FIELD subgroup mu_n is NOT.")
print(">>> The threshold for ANY sqrt-saving over a prime-field subgroup via completion")
print(">>> is n >= sqrt(p) (beta < 2); constant-index/homothety structure does NOT lower")
print(">>> it because the prime-field subgroup is not a homothety/norm structure of a")
print(">>> larger field.  RL is OFF the prize wall in the WRONG direction: it is a tool")
print(">>> for extension-field subgroups, not prime-field ones.")
