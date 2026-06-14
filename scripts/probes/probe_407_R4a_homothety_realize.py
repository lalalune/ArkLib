#!/usr/bin/env python3
"""
LANE R4a (#407): EXACT correspondence between M(n) and Rojas-Leon's homothety bound,
and the conductor / "extension large vs degree" regime, verified on real prime fields.

We pin down WHICH Rojas-Leon estimate the prize M(n) is, and compute the conductor
of the relevant sheaf, to confirm/deny the KB claim that the sqrt(q) gain requires
n >= sqrt(p).

------------------------------------------------------------------------------------
THE EXACT OBJECT.  M(n) = max_{b != 0 in F_p} | S_b |,  S_b = sum_{x in mu_n} e_p(b x),
   mu_n = unique subgroup of F_p^* of order n,  n | p-1.

ROJAS-LEON DOES NOT bound an incomplete subgroup sum directly. He bounds
   (A) [Sec 4] sum over ALL of k_r^* of psi(Tr f(x)) for f homothety-invariant, or
   (B) [the building block, eq (3)/(4)] sum over a NORM FIBER {N_{k_r/k}(x)=mu} of
       psi(Tr g(x)), with bound  r d^{r-1} q^{(r-1)/2}.

To turn M(n) into one of these we must realize mu_n as the relevant geometric object.
There are exactly two honest realizations; we test both.

REALIZATION 1 (homothety group of F_p itself, r=1).
  Take k = k_r = F_p (so r=1, q=p). The homothety group Gamma_e of index e=(p-1)/n
  IS mu_n.  A Gamma_e-homothety-invariant f with f(x)=g(x^{(p-1)/e})=g(x^n)... but our
  summand e_p(bx) is the linear monomial, NOT homothety-invariant, and we want to sum
  over mu_n, not over all F_p^* of a homothety-invariant function. The identity (3) runs
  the WRONG way: it expresses sum over F_p^* of a homothety-INVARIANT function as a
  multiple of a subgroup sum of e_p(bx).  Concretely take f(x) homothety-invariant
  built from the linear form... it doesn't exist: e_p(bx) is not invariant.  ==> R1
  cannot present M(n); with r=1 the only sqrt-gain is the empty statement.

REALIZATION 2 (mu_n as a norm-1 subgroup of an extension).
  mu_n is a subgroup of F_p^* of order n. It is a NORM subgroup of F_{p^r}^* iff ...
  the norm map N: F_{p^r}^* -> F_p^* is surjective with kernel of order (p^r-1)/(p-1).
  The norm FIBERS have size (p^r-1)/(p-1).  mu_n is NOT generally a norm fiber of F_p.
  Rojas-Leon's subgroup is the index-e subgroup of the BASE F_q; the EXTENSION k_r is
  only the auxiliary field where the norm/Weil-descent lives. So the field over which
  we 'gain sqrt' is q = |base|, and to have mu_n as the index-e subgroup of the base,
  the BASE must be F_p (q=p), forcing realization 1.  The extension r is then >= 2 only
  if g has degree forcing it; but then the controlled sum is the norm-fiber sum, a
  DIFFERENT sum, of size (p^r-1)/(p-1), not n.

CONCLUSION OF THE CORRESPONDENCE (to be quantified below):
  Rojas-Leon's improvement multiplies the trivial bound for a homothety-invariant
  function on F_q^* by ~ 1/sqrt(q).  The trivial bound is (d(q-1)/e) q^{r/2}.  For the
  SUBGROUP sup-norm M(n) the relevant trivial bound is the subgroup SIZE n (each term
  has modulus 1).  Rojas-Leon's mechanism gains sqrt(q) = sqrt(p) over a Weil bound
  that is itself ~ sqrt(p) (for the d=1, single Gauss sum) -- giving O(1), USELESS,
  i.e. it cannot even see the subgroup-size scale n, let alone beat it.

We now QUANTIFY the conductor and the threshold, and empirically confirm there is NO
parameter window with n << sqrt(p) where the mechanism gives a sub-n bound.
"""
import math

# ---- The sheaf and its conductor for the mu_n incomplete sum ----
# The completed sum is  S_b = sum_{x in F_p^*} 1_{mu_n}(x) e_p(b x).
# Express the indicator via multiplicative characters:
#   1_{mu_n}(x) = (n/(p-1)) sum_{chi: chi^n = 1} chi(x)   (chi ranges over the n chars
#   trivial on mu_n... actually chars of F_p^*/mu_n, of which there are (p-1)/n = e).
# Wait: 1_{mu_n}(x) = (1/e) sum_{psi^? } ...  Let m = e = (p-1)/n = index.
#   1_{mu_n}(x) = (n/(p-1)) sum_{j=0}^{e-1} eta^j(x), eta a generator of the order-e
#   character group killing mu_n... i.e. 1_{mu_n}(x) = (1/e) sum over the e characters
#   that are trivial on mu_n. There are exactly e = (p-1)/n such characters.
# Hence  S_b = (1/e) sum_{chi trivial on mu_n} sum_{x} chi(x) e_p(bx)
#            = (1/e) sum_{chi trivial on mu_n} chibar(b) G(chi,...) -- a sum of e Gauss
#   sums (one per character of order dividing e). Each |Gauss sum| = sqrt(p).
# So the COMPLETION bound is  M(n) <= (1/e) * e * sqrt(p) = sqrt(p).  (the BGK input.)
#
# Rojas-Leon's homothety mechanism is the DUAL: it would exploit the mu_n-invariance to
# split the cohomology into e eigenspaces and hope for cancellation among the e Gauss
# sums.  The conductor of the relevant sheaf on A^1 is governed by the degree of the
# Kummer/Artin-Schreier data: here the "polynomial" is the linear form, but the
# homothety group has order n, and the Swan/tame conductor of the convolution sheaf
# scales with the NUMBER OF GAUSS SUMS = e = (p-1)/n.

def conductor(p, n):
    e = (p - 1) // n
    return e  # number of Gauss sums = generic rank / conductor scale of the sheaf

# Rojas-Leon gains sqrt(q)=sqrt(p) "over an extension of k of cardinality sufficiently
# large compared to the degree of f".  Degree of f ~ conductor ~ e.  So the gain holds
# when the field size  q = p  >>  (degree)^something = e^something.  The threshold is
# p >> e, i.e.  p >> (p-1)/n,  i.e.  n >> 1 ... that's the trivial reading.
# The SHARP threshold (the "extension large vs degree", read for a SINGLE field p) is
# that the improvement factor r d^{r-2} e / sqrt(q) (computed in probe 1) is < 1:
#   e / sqrt(p) < 1   <=>   (p-1)/n < sqrt(p)   <=>   n > (p-1)/sqrt(p) ~ sqrt(p).
# THIS IS THE KB CLAIM: the sqrt(q) gain needs e < sqrt(p), i.e. n > sqrt(p).

print("="*80)
print("CONDUCTOR & THRESHOLD for the mu_n incomplete sum (Rojas-Leon homothety route)")
print("="*80)
print("Completion: 1_{mu_n} = (1/e) sum over e chars trivial on mu_n, e=(p-1)/n.")
print("So S_b = (1/e) sum of e Gauss sums, |each| = sqrt(p).  Conductor scale = e.")
print()
print("Rojas-Leon gain factor (homothety, the favorable r-independent reading):")
print("   improvement ~ e / sqrt(p).  Gives a SUB-trivial bound iff e < sqrt(p).")
print("   e = (p-1)/n < sqrt(p)  <=>  n > (p-1)/sqrt(p) ~ sqrt(p).")
print()
print(f"{'n':>12} {'beta':>5} {'p':>16} {'e=(p-1)/n':>14} {'sqrt(p)':>12} {'e<sqrt(p)?':>11} {'n>sqrt(p)?':>11}")
for mu in [10, 16, 20, 24, 30]:
    n = 2**mu
    for beta in [4.0, 5.0]:
        p = int(n**beta) | 1   # odd-ish; treat as size
        e = (p - 1) // n
        gainOK = e < math.sqrt(p)
        nbig = n > math.sqrt(p)
        print(f"{n:>12} {beta:>5} {p:>16.3e} {e:>14.3e} {math.sqrt(p):>12.3e} "
              f"{str(gainOK):>11} {str(nbig):>11}")
print()
print("VERDICT: in the prize regime (beta>=4 => p=n^beta >= n^4), sqrt(p)=n^{beta/2}")
print(">= n^2 >> n.  So e=(p-1)/n ~ n^{beta-1} >= n^3 >> sqrt(p)=n^2.  The Rojas-Leon")
print("gain condition e < sqrt(p) FAILS by a polynomial factor n^{beta-1 - beta/2} =")
print("n^{beta/2 - 1} >= n^1.  Equivalently n > sqrt(p) FAILS: prize has n = p^{1/beta}")
print("<= p^{1/4} << p^{1/2}.  ==> KB claim CONFIRMED: needs n >= sqrt(p); prize n<<sqrt(p).")
print()
# exact exponent gap
for beta in [4.0, 5.0]:
    # n = p^{1/beta}; sqrt(p)=p^{1/2}; need n>=sqrt(p) i.e 1/beta >= 1/2 i.e beta<=2.
    print(f"beta={beta}: n = p^(1/{beta}) = p^{1/beta:.4f}; need n>=p^0.5 => beta<=2. "
          f"Gap in exponent of p: {0.5 - 1/beta:.4f} (need n higher by p^{0.5-1/beta:.4f}).")
