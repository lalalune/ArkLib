#!/usr/bin/env python3
"""
LANE R4a (#407): When does Rojas-Leon's homothety-invariant ADDITIVE bound (Cor 4.3)
actually IMPROVE on the trivial Weil bound? And is the improvement window EMPTY at a
fixed prime (the prize regime)?

Exact statements from arXiv:1010.0120, Section 4:

  f in k_r[x],  k=F_q,  k_r=F_{q^r},  e | q-1,  f Gamma_e-homothety invariant,
  f(x)=g(x^{(q-1)/e}),  deg g = d.

  TRIVIAL Weil bound:
     | sum_{x in k_r} psi(Tr f(x)) | <= ( d(q-1)/e - 1 ) * q^{r/2}.       (W)

  ROJAS-LEON (Cor 4.3, g degree d prime to p):
     | sum_{x in k_r^*} psi(Tr f(x)) | <= r * d^{r-1} * (q-1) * q^{(r-1)/2}.  (RL)

The "improvement by a factor sqrt(q)" the abstract claims: compare (RL)/(W).
  (RL)/(W) = [ r d^{r-1} (q-1) q^{(r-1)/2} ] / [ (d(q-1)/e) q^{r/2} ]
           = r d^{r-2} e / q^{1/2}.
So (RL) IS a sqrt(q) improvement over (W) IFF  r d^{r-2} e < q^{1/2}  (so the ratio<1).
The improvement is "by a factor sqrt(q)" PROVIDED r d^{r-2} e is bounded; the precise
hypothesis "extension k_r large vs degree d of f" means q^{1/2} >> r d^{r-2} e.

NOW MAP TO M(n).  We want mu_n subset F_p, |mu_n|=n.  The cleanest faithful encoding:
  base k = F_p (q := p),  e := index = (p-1)/n  (so Gamma_e = mu_n),  and the SUM we
  control is the full homothety-invariant sum over k_r^*.  But the prize sum M(n) is
  the bare subgroup sum of e_p(bx); via identity (3) it appears with d=1 (linear g),
  r=1.  With r=1, (RL) = 1 * d^0 * (q-1) * q^0 = (q-1) = p-1 -- the TRIVIAL bound
  (the whole subgroup of size p-1).  No gain at r=1 for the linear form.

To get a genuine subgroup sum of size n with a sqrt-gain we must take e=(p-1)/n>1 AND
have a nonlinear g OR an extension r>=2.  The structural obstruction: the gain factor
needs  r d^{r-2} e < sqrt(q) = sqrt(p).  With e=(p-1)/n this is
     r d^{r-2} (p-1)/n < sqrt(p)   =>   n > r d^{r-2} (p-1)/sqrt(p) ~ r d^{r-2} sqrt(p).
i.e.  n  must exceed (a constant times) sqrt(p).  EXACTLY the KB threshold n >= sqrt(p).

We tabulate the improvement window for several (r,d,e) and the implied n-threshold.
"""
import math

def W_trivial(q, r, e, d):
    return (d*(q-1)/e - 1) * q**(r/2.0)

def RL(q, r, e, d):
    return r * d**(r-1) * (q-1) * q**((r-1)/2.0)

print("="*82)
print("Improvement window  (RL)/(W) = r d^{r-2} e / sqrt(q)  < 1 ?")
print("="*82)
print(f"{'q':>12} {'r':>3} {'e':>10} {'d':>3} {'W':>12} {'RL':>12} {'RL/W':>10} {'<1?':>5}")
q = 10.0**12
for r in [1,2,3]:
    for e in [10, 1000, 10**6]:
        for d in [1,2,4]:
            if d % 1: continue
            w = W_trivial(q,r,e,d); rl = RL(q,r,e,d)
            ratio = rl/w
            print(f"{q:>12.1e} {r:>3} {e:>10} {d:>3} {w:>12.3e} {rl:>12.3e} {ratio:>10.3e} {str(ratio<1):>5}")
print()
print("The ratio r d^{r-2} e / sqrt(q) < 1 only when e < sqrt(q)/(r d^{r-2}).")
print("Translating e=(p-1)/n: improvement <=> n > r d^{r-2} (p-1)/sqrt(p) ~ sqrt(p).")
print()

# Now the SHARP question: even IN the improvement window, what bound on the SUBGROUP
# sum M(n) does RL give?  The controlled per-fiber sum (eq (3)) over {N(x)=mu} bounded
# by r d^{r-1} q^{(r-1)/2}.  Summed over the e fibers and divided appropriately, the
# net bound on the subgroup sum of size n is ~ r d^{r-1} q^{(r-1)/2}.  Compare to n.

print("="*82)
print("Even in-window, the RL bound on the SUBGROUP sum ~ r d^{r-1} q^{(r-1)/2}.")
print("Compare to the TRUTH (prize wants n^0.5) and the trivial subgroup size n.")
print("="*82)
print(f"{'mu':>3} {'n':>12} {'beta':>5} {'p':>14} {'RL_subgrp~q^.5':>14} {'n':>12} {'n^0.5':>10} {'RL<n?':>6}")
for mu in [10, 20, 30]:
    n = 2**mu
    for beta in [4.0, 5.0]:
        p = n**beta
        # best case r=2,d=1 (linear, smallest): RL_subgrp ~ 2*1*q^{1/2} = 2 sqrt(p)
        rl_sub = 2*1*p**0.5
        print(f"{mu:>3} {n:>12} {beta:>5} {p:>14.2e} {rl_sub:>14.3e} {float(n):>12.3e} "
              f"{n**0.5:>10.2e} {str(rl_sub<n):>6}")
print()
print("EVEN in the best case (r=2,d=1) the RL subgroup bound ~2 sqrt(p) = 2 n^{beta/2}")
print(">= 2 n^2 >> n. It cannot even reach the trivial subgroup size n, let alone n^0.5.")
print("The mechanism's natural scale is sqrt(p), which in the prize regime is n^{>=2}.")
