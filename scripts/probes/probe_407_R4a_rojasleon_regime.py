#!/usr/bin/env python3
"""
LANE R4a (#407): Effective Rojas-Leon for the mu_n incomplete-subgroup-sum sup-norm.

Goal: map the prize target
   M(n) = max_{b != 0 mod p} | sum_{x in mu_n} e_p(b x) |
onto the Rojas-Leon (arXiv:1010.0120) homothety-invariant additive estimate, and
determine the EXACT regime where the sqrt(q)-gain applies.

=== Rojas-Leon Sec 4 (additive, homothety-invariant), exact statements ===

Setup (his notation): base field k = F_q, extension k_r = F_{q^r}.
  e | q-1, Gamma_e = unique subgroup of k^* = F_q^* of index e, |Gamma_e| = (q-1)/e.
  f in k_r[x] is Gamma_e-homothety invariant: f(lambda x) = f(x) for lambda in Gamma_e.
  Equivalently f(x) = g(x^{(q-1)/e}) for some g of degree d.
  psi: k -> C^* nontrivial additive character.

Weil (trivial) bound:   |sum_{x in k_r} psi(Tr(f(x)))| <= ( d(q-1)/e - 1 ) q^{r/2}.

His improved bound (Corollary 4.3, g degree d prime to p):
   |sum_{x in k_r^*} psi(Tr_{k_r/k}(f(x)))| <= r d^{r-1} (q-1) q^{(r-1)/2}.

=== The dictionary to M(n) ===

M(n) is a sum over a SINGLE field F_p (p prime), over the n-element subgroup mu_n.
   mu_n = Gamma_e for k=F_p, e = (p-1)/n,  so |mu_n| = (p-1)/e = n.
The "function" is f(x)=e_p(b x) restricted... but that's NOT homothety invariant.

Rojas-Leon's f is homothety invariant and summed over ALL of k_r^*. The subgroup
sum appears via the identity (his eq (3)) in the OTHER direction:
   sum_{x in k_r^*} psi(Tr f(x)) = (q-1)/e * sum_{mu^e=1} sum_{N(x)=mu} psi(Tr g(x)).
So his LHS packages e copies of subgroup-restricted sums. The clean single-subgroup
sum he controls is  sum_{N_{k_r/k}(x)=mu} psi(Tr g(x))  with bound r d^{r-1} q^{(r-1)/2}.

The natural identification for OUR M(n):
   We want sum over mu_n in F_p.  Take k = F_p as base?  Then there is no extension
   (r=1), g = the linear form b*x has degree d=1, and the bound r d^{r-1} q^{(r-1)/2}
   = 1 * 1 * p^0 = 1.  That is the trivially-best bound but it is NOT M(n): with r=1
   the subgroup mu_n = Gamma_e is the FULL norm-fiber only if e=1 (n=p-1). For a
   PROPER subgroup we need the norm map from an extension to cut out mu_n, i.e. mu_n
   must be realized as a norm-1 (or norm-fiber) subgroup of an EXTENSION.

Correct identification:  mu_n = { x in F_q^* : x^n = 1 }.  Realize F_p inside F_q with
   q = p (base) won't give a proper subgroup as a NORM fiber. Instead the genuine
   Rojas-Leon application sums  sum_{x in mu_n subset F_q} psi(Tr_{F_q/F_p}( b * g(x) ))
   where mu_n = Gamma_e (index e=(q-1)/n) of F_q^*, and r is the extension degree
   F_q / F_p.  Crucially the GAIN  q^{1/2}  is over a field of size q = |F_q|, and the
   degree-vs-extension hypothesis is  "extension r large compared to degree d".

We test which regime gives a NONTRIVIAL improvement for the subgroup sup-norm, and
whether it can ever reach n^{0.5}.
"""

import math

def weil_trivial(n, p):
    # |sum_{x in mu_n} e_p(bx)| <= ? The classical Weil/Polya-Vinogradov-type bound
    # via completing: mu_n is the zero set of x^n-1; the incomplete sum has the
    # trivial Weil bound ~ (number of "frequencies") sqrt(p). Standard completion:
    #   M(n) <= sqrt(p) * (something) ; but the SHARP classical input is
    #   M(n) <= sqrt(p)   (the single Gauss-sum-per-coset bound), and more refined
    #   M(n) <= n^{1-1/...} via BGK. We just track the two reference scales.
    return math.sqrt(p)

def prize_target(n, p):
    return math.sqrt(n * math.log(p / n))

# === The Rojas-Leon "extension large vs degree" regime ===
# In his setup the field over which we gain sqrt is q = |F_q|.  For a subgroup mu_n
# of F_q^* of index e=(q-1)/n, realized as a homothety group, the relevant 'degree'
# is d ~ deg of the auxiliary polynomial g, and r is the degree [F_q : F_p].
#
# KEY structural fact (from the proof, Prop 4.2 / Cor 4.3): the cohomology lives on
# the hypersurface x_1...x_r = mu in A^r, dimension r-1, and the bound is
#       r d^{r-1} q^{(r-1)/2}.
# Normalizing by the trivial bound ~ (d(q-1)/e) q^{r/2}, the GAIN FACTOR is
#       [ r d^{r-1} (q-1) q^{(r-1)/2} ] / [ (d(q-1)/e) q^{r/2} ]
#     = r d^{r-2} e / q^{1/2}.
# So the gain is sqrt(q) ONLY IF  r d^{r-2} e  is bounded, i.e. essentially when the
# EXTENSION DEGREE r and the index e are small relative to sqrt(q).  This is the
# "extension large compared to degree" being read the OTHER way: the improvement
# is by a factor sqrt(q) provided  r d^{r-1} e <<  (d(q-1)/e) q^{1/2}, i.e.
#       d^{r-2} r e^2 << q^{1/2} * (q-1)/...
# Let's just compute the actual bound r d^{r-1} (q-1) q^{(r-1)/2} and compare to the
# subgroup size n, to see when the bound is BELOW n (nontrivial for sup-norm).

def rl_bound_subgroup(n, q, r, d):
    # His per-fiber bound: r d^{r-1} q^{(r-1)/2}  (this controls sum over N(x)=mu).
    return r * d**(r-1) * q**((r-1)/2.0)

print("="*78)
print("REGIME ANALYSIS: Rojas-Leon homothety-invariant additive bound vs prize M(n)")
print("="*78)
print()
print("Prize regime: n = 2^mu, p = q = n^beta (beta in [4,5]). mu_n subset F_p^*.")
print("Target: M(n) <= C sqrt(n log(p/n)) ~ sqrt(n * (beta-1) log n).  (prize ~ n^0.5)")
print()
print(f"{'n':>10} {'beta':>5} {'p':>16} {'sqrt(p)':>12} {'prize~n^.5':>12} {'n (trivial)':>12}")
for mu in [10, 16, 20, 24, 30]:
    n = 2**mu
    for beta in [4.0, 5.0]:
        p = n**beta
        print(f"{n:>10} {beta:>5} {p:>16.3e} {math.sqrt(p):>12.3e} "
              f"{prize_target(n,p):>12.3e} {float(n):>12.3e}")
print()
print("Observation: sqrt(p) = n^{beta/2} = n^2 .. n^2.5  >> n.  So the *completion*")
print("Weil bound sqrt(p) is USELESS (>> n = trivial subgroup-size bound).")
print("The prize needs M(n) ~ n^0.5, FAR below even the trivial n.")
print()

# === The crux: in which regime does Rojas-Leon's sqrt(q) gain beat n? ===
# To use Rojas-Leon for a PROPER subgroup mu_n of F_q^*, we need mu_n to be the
# homothety group Gamma_e with e=(q-1)/n. His bound on the FULL homothety-invariant
# sum over F_q^* (Cor 4.3, base field is F_q itself with r=1? No: r is the extension
# in which the NORM lives). The cleanest reading: to gain sqrt over a subgroup of
# index e of F_q^*, the relevant extension degree is r = (log of subgroup structure)
# and the bound r d^{r-1} q^{(r-1)/2} must be << n.

print("="*78)
print("Does Rojas-Leon's per-fiber bound  r d^{r-1} q^{(r-1)/2}  ever beat n?")
print("="*78)
print("To realize mu_n (|mu_n|=n) as a homothety/norm structure of F_q with extension")
print("degree r and aux-degree d, the subgroup size relates as n ~ (q-1)/e and the")
print("fiber bound is r d^{r-1} q^{(r-1)/2}. We need this < n = sqrt-of-prize-target.")
print()
print(f"{'r':>3} {'d':>4} {'q':>14} {'rl_fiber':>14} {'sqrt(q)':>12} {'n=(q-1)/e?':>12}")
# The fiber bound is below sqrt(q) only when r=1: r d^{r-1} q^{(r-1)/2} = 1*1*1 = 1 (d arbitrary, r=1).
for r in [1, 2, 3, 4]:
    for d in [2, 4]:
        q = 10.0**12
        fib = rl_bound_subgroup(None, q, r, d)
        print(f"{r:>3} {d:>4} {q:>14.2e} {fib:>14.3e} {math.sqrt(q):>12.3e} {'-':>12}")
print()
print("For r=1 the fiber bound is r d^{r-1} q^{(r-1)/2} = 1 (q^0): a TRIVIAL extension,")
print("the norm fiber is all of F_q^*, NOT a proper subgroup. So r>=2 is forced to get")
print("a proper subgroup mu_n via norm, and then the bound carries q^{(r-1)/2} >= q^{1/2}.")
print("This is exactly the 'extension large vs degree' tension.")
