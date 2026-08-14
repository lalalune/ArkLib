#!/usr/bin/env python3
"""#407 Lane A — constant-index large-subgroup additive energy, STRUCTURAL shape.

THE LANE A CLAIM under test (the single un-refuted path to closure):

    For mu_n the smooth domain (n = 2^mu) a *proper* subgroup of F_p* with
    CONSTANT index m = (p-1)/n (the prize forces m ~ 2^128 fixed, n -> infty),
    the k-fold additive energy excess over the random main term satisfies, for
    ALL k asymptotically, the Poisson / factorial-Gaussian structural bound

        Exc_k(mu_n) := E_k(mu_n) - n^{2k}/p   <=   C^k * k! * n^k        (LANE A)

    equivalently the char-0 Lam-Leung shape  E_k <= (2k-1)!! n^k  transfers to
    char p with the *random main term* n^{2k}/p ADDED, UNCONDITIONALLY (i.e.
    WITHOUT the norm-bound side condition q > (2k)^{n/2} that the in-tree
    `GaussianEnergyBound` char-p transfer currently demands).

    E_k = #{ (x_1..x_k, y_1..y_k) in mu_n^{2k} : sum x_i = sum y_i in F_p }
        = sum_s r_k(s)^2,   r_k(s) = #{(x_1..x_k): sum x_i = s}.

WHY this is the right object (vs the refuted moment-hierarchy route): the
moment-method NoGo (_MomentMethodNoGo.lean) proves (p*E_k)^{1/2k} >= n ALWAYS, so
the *raw* energy can never beat n.  BUT the Gauss-period bound B <= sqrt(2 n ln q)
needs E_k only at k ~ ln q, and the n^{2k}/p main term is KILLED by the
b != 0 restriction in the moment identity sum_{b!=0} ||eta_b||^{2k} = q*Exc_k
(the b=0 term n^{2k} is exactly the s=0... no: the main term n^{2k}/p is the
b=0 contribution removed).  So the PRIZE-RELEVANT object is precisely Exc_k, and
the structural Lane A bound on Exc_k -- if unconditional in the prize regime --
feeds B <= (q * C^k k! n^k / ... )^{1/2k} minimized at k ~ ln q.

CHECKS (all EXACT integer / exact-FFT, never sampled):
  (1) Exc_k for constant index m, growing n: measure Exc_k / ((2k-1)!! n^k)
      and Exc_k / n^k.  Does it stay BOUNDED as n -> infty at FIXED m?  Find
      the worst constant C(m) := sup_n (Exc_k / n^k)^{1/k} over accessible n.
  (2) Index dependence: is C(m) genuinely bounded as m grows, or does it blow
      up?  (If C depends on m only and m is constant in the prize, Lane A is a
      real structural statement; if it blows up with the gcd-structure it is
      not.)
  (3) The DIAGONAL DECOMPOSITION: Exc_k = sum over non-principal-diagonal
      pairings.  Measure the leading non-diagonal term to see whether the
      char-0 (2k-1)!! matching count is the true asymptotic.
  (4) Plunnecke-Ruzsa feasibility: measure |mu_n + mu_n| (sumset size) and the
      doubling constant K = |mu_n+mu_n|/n.  Lane A via P-R needs K = O(1) on a
      LARGE subset (spread).  Is mu_n additively spread (K ~ n, NOT O(1))?  This
      is the structural test of the P-R transfer route.
"""

import sys
from math import comb
from collections import Counter
import numpy as np


def isprime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0:
            return False
        d += 2
    return True


def primroot(p):
    if p == 2:
        return 1
    fac = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for a in range(2, p):
        if all(pow(a, (p - 1) // q, p) != 1 for q in fac):
            return a


def domain(p, n):
    g = pow(primroot(p), (p - 1) // n, p)
    return [pow(g, i, p) for i in range(n)]


def double_fact_odd(k):
    """(2k-1)!! = product of odd numbers 1*3*5*...*(2k-1)."""
    r = 1
    for j in range(1, k + 1):
        r *= (2 * j - 1)
    return r


def rk_counts(p, dom, k):
    """r_k(s) = #{k-tuples from dom summing to s mod p}, as a length-p int array,
    via k-fold cyclic convolution (exact: integer FFT round-trip with check)."""
    r1 = np.zeros(p)
    for x in dom:
        r1[x] += 1.0
    F = np.fft.rfft(r1)
    rk_f = np.fft.irfft(F ** k, n=p)
    rk = np.rint(rk_f)
    if float(np.max(np.abs(rk_f - rk))) > 1e-1:
        return None  # FFT precision blew up
    rki = rk.astype(np.int64)
    if int(rki.sum()) != len(dom) ** k:
        return None
    return rki


def Ek(p, dom, k):
    rk = rk_counts(p, dom, k)
    if rk is None:
        return None
    return int(sum(int(v) * int(v) for v in rk.tolist()))


def find_prime_const_index(m, n_target):
    """smallest n that is a power of 2 (>= some scale) with m*n+1 prime, n ~ n_target.
    Here we relax 'power of 2' to 'even n' for data density but flag 2-power rows."""
    best = None
    for n in range(max(2, n_target - 200), n_target + 200):
        if n % 2:
            continue
        p = m * n + 1
        if isprime(p):
            if best is None or abs(n - n_target) < abs(best - n_target):
                best = n
    return best


def is_pow2(x):
    return x > 0 and (x & (x - 1)) == 0


print("=" * 78, flush=True)
print("LANE A: constant-index additive-energy excess Exc_k = E_k - n^{2k}/p", flush=True)
print("structural target:  Exc_k <= C^k k! n^k   (Poisson) ;  char-0:  E_k<=(2k-1)!! n^k", flush=True)
print("=" * 78, flush=True)

# -------------------------------------------------------------------------
# CHECK (1)+(2): Exc_k for constant index m, growing n; ratios to (2k-1)!! n^k.
# -------------------------------------------------------------------------
print("\n[1] FIXED index m, growing n  ->  Exc_k / ((2k-1)!! n^k)  and  (Exc_k/n^k)^{1/k}", flush=True)
print("    (bounded ratio as n->inf  <=>  Lane A structural shape holds at this m)\n", flush=True)

for m in [2, 4, 6, 8, 16]:
    for k in [2, 3, 4]:
        df = double_fact_odd(k)
        row = []
        for nt in [64, 128, 256, 512, 1024, 2048, 4096]:
            n = find_prime_const_index(m, nt)
            if n is None:
                continue
            p = m * n + 1
            if p > 8_000_000:  # FFT/runtime guard
                continue
            dom = domain(p, n)
            e = Ek(p, dom, k)
            if e is None:
                continue
            main = n ** (2 * k) / p
            exc = e - main
            ratio_df = exc / (df * n ** k) if df * n ** k > 0 else 0.0
            Cest = (abs(exc) / n ** k) ** (1.0 / k) if exc > 0 else 0.0
            pw = "*" if is_pow2(n) else " "
            row.append((n, ratio_df, Cest, pw))
        if row:
            s = "  ".join(f"n={n}{pw}:{rd:.3f}|C={C:.2f}" for n, rd, C, pw in row)
            print(f"  m={m:>2} k={k}: {s}", flush=True)
    print(flush=True)

# -------------------------------------------------------------------------
# CHECK (3): the diagonal decomposition leading term, k=2 and k=3.
#   E_2 random-like model: n^4/p (main) + 2n^2 - n (full-diagonal) is the
#   char-0 (2*2-1)!!=3 ... actually E_2 = 3n^2-3n char-0; main n^4/p.
# -------------------------------------------------------------------------
print("[3] diagonal structure: measured Exc_k vs char-0 closed forms", flush=True)
print("    char-0:  E_2=3n^2-3n  (Exc_2 ~ 3n^2),  E_3=15n^3-45n^2+40n  (Exc_3 ~ 15n^3)\n", flush=True)
for m in [4, 8]:
    for nt in [128, 512, 2048]:
        n = find_prime_const_index(m, nt)
        if n is None:
            continue
        p = m * n + 1
        if p > 8_000_000:
            continue
        dom = domain(p, n)
        e2 = Ek(p, dom, 2)
        e3 = Ek(p, dom, 3)
        if e2 is None or e3 is None:
            continue
        exc2 = e2 - n ** 4 / p
        exc3 = e3 - n ** 6 / p
        c0_2 = 3 * n ** 2 - 3 * n
        c0_3 = 15 * n ** 3 - 45 * n ** 2 + 40 * n
        print(f"  m={m} n={n} p={p}:  Exc2={exc2:.0f} (char0 {c0_2}, ratio {exc2/c0_2:.4f})  "
              f"Exc3={exc3:.0f} (char0 {c0_3}, ratio {exc3/c0_3:.4f})", flush=True)
    print(flush=True)

# -------------------------------------------------------------------------
# CHECK (4): Plunnecke-Ruzsa feasibility -- is mu_n additively SPREAD?
#   doubling K = |mu_n + mu_n| / n.  Lane A via P-R needs O(1) doubling on a
#   large piece; multiplicative subgroups are notoriously NON-spread additively.
# -------------------------------------------------------------------------
print("[4] additive spread / doubling K = |mu_n + mu_n| / n  (P-R transfer feasibility)", flush=True)
print("    K ~ n  =>  fully spread (good for sum bounds);  K = O(1)  =>  P-R applies\n", flush=True)
for m in [2, 4, 8, 16, 64]:
    row = []
    for nt in [64, 256, 1024]:
        n = find_prime_const_index(m, nt)
        if n is None:
            continue
        p = m * n + 1
        if p > 8_000_000:
            continue
        dom = set(domain(p, n))
        doml = list(dom)
        S = set()
        for a in doml:
            for b in doml:
                S.add((a + b) % p)
        K = len(S) / n
        # also triple sumset for spread confirmation
        row.append((n, K, len(S)))
    if row:
        s = "  ".join(f"n={n}:K={K:.2f}(|2A|={sz})" for n, K, sz in row)
        print(f"  m={m:>2}: {s}", flush=True)
print(flush=True)

print("=" * 78, flush=True)
print("READ:", flush=True)
print(" * [1] ratio Exc_k/((2k-1)!! n^k) BOUNDED & ->const as n->inf at fixed m  ==> Lane A shape", flush=True)
print(" * [1] C(m) := worst (Exc_k/n^k)^{1/k}; if grows with m, the constant is NOT index-free", flush=True)
print(" * [4] if K ~ n (spread), P-R doubling route is VACUOUS (no small doubling to exploit);", flush=True)
print("       Lane A must then come from the cyclotomic/diagonal structure, NOT Plunnecke-Ruzsa", flush=True)
print("=" * 78, flush=True)
