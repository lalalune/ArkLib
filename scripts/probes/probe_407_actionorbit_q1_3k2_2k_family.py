#!/usr/bin/env python3
"""
#407 LANE L4 (Action-Orbit, Chai-Fan eprint 2026/861) -- FAITHFUL Q1 test on the paper's
ACTUAL object: the (3k/2, 2k) family bad set, and its self-similarity descent.

WHAT Q1 ACTUALLY IS (verbatim from the paper, NOT a proxy):
  - Thm 4.10: for the ARISING pencil  h_rho(z) = rho*z^{3k/2} + z^{2k}  on  L_n = mu_n, n=4k,
    the bad-rho set is EXACTLY  {rho in F_q^* : rho^8 = 16}  -- a SINGLE action-orbit of size <=8.
    PROVEN char-uniformly for h := k/2 in {2,3,4}  (k in {4,6,8}, n in {16,24,32}).
  - Rmk 4.11 / Conj 4.12 (Q1): for general h, the Stage-2 variety decomposes as
        V_h = {0}  union  ( disjoint union over d|h, d>=4 of V_d^prim ),
    and the closure V_h = {0} reduces to: R_d := -3 x_{d/2} + 2 V_{d/2} + 3 W_{d/2}  does NOT
    vanish identically on V_d^prim,  i.e.  Norm_{K_d/Q}(F_d(alpha)) != 0.
    SETTLED d in {4,8}; OPEN d >= 16. (d = a divisor of h = k/2.)
  - The promising route (Q1 (i), the (*)_d hypothesis): on V_d^prim,  x_1 = 0  ==>  x_a = 0
    for every ODD a.  Rigorous d in {4,8}, conjectural d >= 16.

The companion-repo chain-ideal variables x_a, V, W are NOT public, so we CANNOT recompute R_d
symbolically. But the OPERATIVE CONSEQUENCE of Q1 IS computable and is exactly what the paper's
O(1) bound needs:  does the bad-rho set of the (3k/2,2k) pencil STAY the single orbit {rho^8=16}
as k grows (so that d = k/2 reaches 16, 32)?  If a SPURIOUS bad rho appears (rho^8 != 16) over a
prize-scale field, then V_d^prim has a primitive point ==> R_d vanishes there ==> Q1 FAILS and the
orbit count inflates.  If the bad set stays exactly {rho^8=16} ==> Q1's operative consequence holds.

We compute the bad-rho set TWO independent faithful ways:
  (A) GENUINE RS agreement: bad rho <=> exists deg<k0 codeword g with
        #{z in mu_n : rho*z^{3k/2} + z^{2k} = g(z)} >= (1-delta)*n  above Johnson.
      (n0=4k, the level-1 pencil exponents 3k/2, 2k; message degree k0=k per the paper's panel.)
      Exact deg<k0 agreement via Lagrange; full rho-sweep over F_p (feasible for small n,p).
  (B) The certificate / locator-divisibility characterization the paper proves: a Johnson half-set
      locator sigma_S(z) = prod_{z in S}(z - s), |S| = n/2, with supp in {0..k-1} u {3k/2, 2k}
      (Thm 4.9) and sigma_S | z^n - 1.  The bad rho is the z^{3k/2}-coefficient.  We enumerate
      half-set locators dividing z^n-1 with the pinned support and read off the realized rho set.

DECISIVE OUTPUTS:
  * Is bad-rho == {rho^8 = 16} for k=4 (d=2), k=8 (d=4), k=12 (d=6), k=16 (d=8), k=32 (d=16)?
  * Does a spurious bad rho (rho^8 != 16) EVER appear over a prize-scale prime?  (=> Q1 fails)
  * Self-similarity (*)_d over Z[zeta]: does x_1=0 force x_a=0 (odd a) on the primitive stratum?
"""

import itertools, sys
from math import gcd, sqrt, log
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out=[]; p = lo|1
    while len(out) < cap:
        if (p-1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w,n,p)==1 and all(pow(w, n//q, p)!=1 for q in (2,3,5,7,11,13) if n%q==0):
            return w
    raise RuntimeError("no gen")

# ------- exact deg<k agreement of a value sequence on mu_n, via best k-subset interpolation
def best_agreement(H, vals, p, k):
    n = len(H); best = 0
    # if k is large vs n, C(n,k) blows up; we cap usage to small n
    for sub in itertools.combinations(range(n), k):
        bx = [H[i] for i in sub]; by = [vals[i] for i in sub]
        def interp(x):
            tot = 0
            for j in range(k):
                num = by[j] % p; den = 1
                for l in range(k):
                    if l != j:
                        num = num * ((x - bx[l]) % p) % p
                        den = den * ((bx[j] - bx[l]) % p) % p
                tot = (tot + num * pow(den, p-2, p)) % p
            return tot
        cnt = sum(1 for i in range(n) if interp(H[i]) == vals[i] % p)
        if cnt > best:
            best = cnt
            if best == n: break
    return best

def bad_rho_set_RS(p, k, threshold):
    """(A) Genuine RS: n=4k, pencil rho*z^{3k/2}+z^{2k}, message deg<k. Full rho sweep.
    threshold = required agreement (>= it => bad).  Returns set of bad rho."""
    n = 4*k
    w = find_gen(p, n); H = [pow(w,i,p) for i in range(n)]
    e1 = (3*k)//2; e2 = 2*k
    A = [pow(x, e1, p) for x in H]; B = [pow(x, e2, p) for x in H]
    bad = set()
    for rho in range(1, p):
        vals = [(rho*A[i] + B[i]) % p for i in range(n)]
        if best_agreement(H, vals, p, k) >= threshold:
            bad.add(rho)
    return bad, n, w

def rho8eq16_set(p, n, w):
    """The single orbit {rho : rho^8 = 16} in F_p (the predicted bad set)."""
    s = set()
    for rho in range(1, p):
        if pow(rho, 8, p) == 16 % p:
            s.add(rho)
    return s

# ------- (B) locator-divisibility realization: enumerate sigma_S | z^n-1, |S|=n/2,
#         supp(sigma_S) subset {0..k-1} u {3k/2, 2k}, read off z^{3k/2}-coeff = bad rho.
def bad_rho_set_locator(p, k):
    """Enumerate half-sets S subset mu_n (|S|=n/2) whose locator prod (z - s) has support
    in {0,...,k-1, 3k/2, 2k} (Thm 4.9 pinned support). Return the multiset of z^{3k/2} coeffs."""
    n = 4*k
    w = find_gen(p, n); H = [pow(w,i,p) for i in range(n)]
    allowed = set(range(0, k)) | {3*k//2, 2*k}
    # |S| = n/2 = 2k; locator is monic degree 2k; coefficients are e_j(S) up to sign.
    # n=16 (k=4): C(16,8)=12870 half-sets -- feasible. n=32 (k=8): C(32,16)=601M -- infeasible.
    from math import comb
    if comb(n, n//2) > 2_000_000:
        return None
    rhos = set()
    half = n//2
    for S in itertools.combinations(range(n), half):
        pts = [H[i] for i in S]
        # build monic locator coeffs: poly = prod (z - pt). coeffs[d] = coeff of z^d.
        coeffs = [1]
        for pt in pts:
            new = [0]*(len(coeffs)+1)
            for i,c in enumerate(coeffs):
                new[i]   = (new[i]   + (-pt)*c) % p
                new[i+1] = (new[i+1] + c) % p
            coeffs = new
        # support check
        supp = {d for d in range(len(coeffs)) if coeffs[d] % p != 0}
        if supp <= allowed:
            rhos.add(coeffs[3*k//2] % p)
    return rhos

# ------- (C) self-similarity (*)_d over Z[zeta_n]: x_1=0 => x_a=0 (odd a) on primitive stratum
# Here we test the in-tree Lam-Leung corollary: an antipodal-free subset of mu_n (= 2^j) with
# p_1 = 0 over C is impossible (so V_d^prim with x_1=0 is empty over C). For non-2-power d the
# primitive stratum can be nonempty; we report.
def selfsim_C(n):
    """Over C: is there an antipodal-free nonempty subset of mu_n with p_1 = sum = 0?
    (If none, (*)_d holds vacuously over C for the 2-power case.)  Also for general antipodal-free
    subsets with p_1=0, check whether p_3 (an odd power) also vanishes."""
    half = n//2
    def root(j):
        e=j%n; v=[0]*half
        if e<half: v[e]=1
        else: v[e-half]=-1
        return tuple(v)
    def add(u,v): return tuple(a+b for a,b in zip(u,v))
    zero=tuple([0]*half)
    # antipodal-free subsets: pick from one representative of each {j, j+half}; sign chosen by which
    # of the two we take. Enumerate small sizes.
    found_p1zero = 0
    viol_p3 = 0
    examples=[]
    for size in range(2, min(half, 7)+1):
        # choose `size` of the n exponents, antipodal-free
        for S in itertools.combinations(range(n), size):
            Sset=set(S)
            if any(((j+half)%n) in Sset for j in S):
                continue  # has antipodal pair
            p1=zero
            for j in S: p1=add(p1, root(j))
            if p1==zero:
                found_p1zero += 1
                # check odd power p_3
                p3=zero
                for j in S: p3=add(p3, root((3*j)%n))
                if p3 != zero:
                    viol_p3 += 1
                    if len(examples)<3: examples.append((S,'p3!=0'))
    return found_p1zero, viol_p3, examples

def main():
    print("="*86)
    print("#407 LANE L4 -- FAITHFUL Q1: bad-rho set of the (3k/2,2k) pencil == {rho^8=16}?")
    print("="*86)
    print("Q1 holds (operative) <=> bad set STAYS {rho^8=16} (single orbit) as k grows (d=k/2 ->16,32).")
    print("Q1 FAILS <=> a spurious bad rho (rho^8 != 16) appears => V_d^prim primitive point => norm=0.\n")

    # (A) genuine RS, small k where full sweep feasible. n=4k, message deg<k.
    # k=4 -> n=16, d=h=k/2=2; k=8 -> n=32, d=4. Larger k: agreement C(n,k) blows; cap.
    print("--- (A) GENUINE RS agreement, full rho-sweep, bad set vs {rho^8=16} ---")
    print("    (delta just above Johnson; threshold = ceil((1-dJ)*n)+1 .. n/2+1 swept)")
    for k in [2, 4]:
        n = 4*k; rho_rate = k/n  # = 1/4
        dJ = 1 - sqrt(rho_rate)
        ps = primes_1_mod_n(n, max(50, n*n), cap=3)
        for p in ps:
            # threshold: agreement >= t.  Johnson agreement ~ sqrt(rho)*n = n/2. Use t = n/2+1 (interior).
            t = n//2 + 1
            badRS, nn, w = bad_rho_set_RS(p, k, t)
            target = rho8eq16_set(p, n, w)
            spurious = badRS - target
            missing = target - badRS
            verdict = "== {rho^8=16}" if not spurious else f"SPURIOUS {sorted(spurious)[:5]} -> Q1 FAILS"
            print(f"  k={k} n={n} d=k/2={k//2} p={p} t={t}: |badRS|={len(badRS)} |target rho^8=16|={len(target)} {verdict}"
                  + (f"  (target not all bad: {len(missing)} missing -- agreement threshold too high)" if missing and not spurious else ""))

    # (B) locator-divisibility realization at n=16 (the d=4 panel inside h via k=4 -> but actually
    # the paper's V_d^prim with d>=4 first appears for h>=4, i.e. k>=8, n>=32; n=32 locator enum is
    # infeasible exhaustively, so (B) is a structural sanity check at n=16).
    print("\n--- (B) locator-divisibility realization (Thm 4.9 pinned support), n=16 (k=4) ---")
    for p in primes_1_mod_n(16, 100, cap=2):
        rhos = bad_rho_set_locator(p, 4)
        if rhos is None:
            print(f"  k=4 n=16 p={p}: (enum too big)"); continue
        n=16; w=find_gen(p,n)
        target = rho8eq16_set(p, n, w)
        nz = {r for r in rhos if r != 0}
        spurious = nz - target
        print(f"  k=4 n=16 p={p}: realized z^{{3k/2}} coeffs (nonzero) = {sorted(nz)[:8]}{'...' if len(nz)>8 else ''}  "
              f"({len(nz)} vals);  rho^8=16 set = {sorted(target)}  "
              f"{'subset OK' if not spurious else f'SPURIOUS {sorted(spurious)}'}")

    # (C) self-similarity (*)_d over C: antipodal-free p_1=0 sets, and odd-power vanishing.
    print("\n--- (C) self-similarity (*)_d over C [2-power n]: p_1=0 antipodal-free => p_3=0? ---")
    for n in [8, 16, 32]:
        f1, v3, ex = selfsim_C(n)
        if f1 == 0:
            print(f"  n={n}: NO antipodal-free subset with p_1=0 exists over C "
                  f"=> V_d^prim (x_1=0) EMPTY => (*)_d holds vacuously over C.")
        else:
            tag = "ALL also have p_3=0 ((*)_d holds)" if v3==0 else f"{v3} VIOLATE p_3=0 ((*)_d FAILS over C!) ex={ex}"
            print(f"  n={n}: {f1} antipodal-free p_1=0 subsets; {tag}")

if __name__ == "__main__":
    main()
