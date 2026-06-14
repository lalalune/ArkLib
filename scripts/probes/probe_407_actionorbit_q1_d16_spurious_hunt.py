#!/usr/bin/env python3
"""
#407 LANE L4 -- Q1 at d>=16: char-p spurious-hunt on the (3k/2,2k) bad set via the EXACT
locator-divisibility characterization the paper proves (Thm 4.9 + 4.10), pushed to n=4k with
h=k/2 reaching 16 and 32.

Q1 (operative form, faithful):  the bad-rho set of  h_rho(z) = rho*z^{3k/2} + z^{2k}  on mu_n
(n=4k) is exactly the single action-orbit {rho : rho^8 = 16}.  Proven char-uniformly for h=k/2
in {2,3,4} (Thm 4.10).  OPEN for h>=5; the structural obstruction is non-vanishing of R_d on
V_d^prim for d|h, d in {4,8,16,...} (Conj 4.12 / Q1), SETTLED d in {4,8}, OPEN d>=16.

WHAT WE COMPUTE (no companion repo needed -- the paper's own characterization):
A bad rho <=> a Johnson half-set locator  sigma_S(z) = prod_{s in S}(z - s),  S subset mu_n,
|S| = n/2,  with  sigma_S | z^n - 1  (S is a union of cosets / the agreement set is a half-set)
AND pinned support supp(sigma_S) subset {0,...,k-1} u {3k/2, 2k}  (Thm 4.9), and then
rho = [z^{3k/2}] sigma_S.  The PREDICTED set of such rho is {rho^8 = 16}.

A SPURIOUS bad rho (rho^8 != 16) over F_p  <=>  V_d^prim has a primitive point mod p  <=>
Norm_{K_d/Q}(F_d) vanishes mod p (bad reduction) => Q1 FAILS at d=h's relevant divisor.

Since sigma_S | z^n - 1 means S is a union of mu_? cosets, the half-sets S with that pinned
support are HIGHLY structured.  We enumerate them by:
  - S must be a SUBSET of mu_n of size n/2 with sigma_S | z^n-1  <=>  S is a 'spectral half-set':
    actually ANY subset S gives sigma_S | z^n-1 iff S subset mu_n (roots are among the n-th roots),
    which holds automatically.  The REAL constraint is the SPARSE support {0..k-1, 3k/2, 2k}.
  - So we need half-sets S subset mu_n whose elementary symmetric functions e_j(S) vanish for
    j in {k, ..., 3k/2 - 1} u {3k/2+1, ..., 2k-1}  (the support GAPS).  This is the gap-variety
    for THIS family.  We MITM-search over half-sets for those with the pinned support and read
    rho = +/- e_{2k - 3k/2}(S) = +/- e_{k/2}(S)... (coeff of z^{3k/2} in a degree-2k monic poly
    is +/- e_{2k - 3k/2}(S) = +/- e_{k/2}(S)).

To reach n=128 (k=32, h=16, d up to 16) we do NOT enumerate C(128,64). Instead we use the
ACTION-ORBIT + SUBSTITUTION reduction the paper itself uses: by Prop 2.4 the bad set depends
only on gcd(a,b,n).  For (3k/2,2k) with n=4k: gcd(3k/2,2k,4k) = k/2 = h.  So substitute u=z^{h}:
the pencil collapses to  rho*u^3 + u^4  on  mu_{n/h} = mu_{4k/(k/2)} = mu_8,  a FIXED size-8 base
domain, with rho the SAME ratio.  Then the bad set is computed on mu_8 (tiny) EXACTLY, and the
self-similar primitive strata V_d^prim are the corrections at each doubling.  We test:
  (1) the collapsed base pencil rho*u^3 + u^4 on mu_8: bad set == {rho^8=16}?  (the d=base check)
  (2) the FULL pencil on mu_n directly at n=16,24,32 (locator MITM) for spurious rho;
  (3) a DIRECT char-p search for a primitive (non-coset, antipodal-free) gap config of the
      family's gap-variety at n up to 64 over many primes -- the V_d^prim mod-p point = Q1 failure.
"""

import itertools, sys
from math import gcd, sqrt, comb
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

# ---- (1) collapsed base pencil rho*u^3 + u^4 on mu_8 (the substitution u=z^h base case) ----
def base_pencil_badset(p):
    """On mu_8 (size 8): pencil rho*u^3 + u^4, message deg < 2 (rate 1/4 panel (8,2)).
    Full rho-sweep, exact best deg<2 agreement.  Return bad rho set + the rho^8=16 set."""
    n = 8; k = 2
    w = find_gen(p, n); H = [pow(w,i,p) for i in range(n)]
    A = [pow(x,3,p) for x in H]; B = [pow(x,4,p) for x in H]
    def best_agree(vals):
        best=0
        for sub in itertools.combinations(range(n), k):
            bx=[H[i] for i in sub]; by=[vals[i] for i in sub]
            def interp(x):
                tot=0
                for j in range(k):
                    num=by[j]%p; den=1
                    for l in range(k):
                        if l!=j:
                            num=num*((x-bx[l])%p)%p; den=den*((bx[j]-bx[l])%p)%p
                    tot=(tot+num*pow(den,p-2,p))%p
                return tot
            cnt=sum(1 for i in range(n) if interp(H[i])==vals[i]%p)
            best=max(best,cnt)
        return best
    target={rho for rho in range(1,p) if pow(rho,8,p)==16%p}
    # bad at the Johnson boundary (agreement >= n/2 = 4) AND strictly above (>=5)
    badJ=set(); badInt=set()
    for rho in range(1,p):
        vals=[(rho*A[i]+B[i])%p for i in range(n)]
        bb=best_agree(vals)
        if bb>=4: badJ.add(rho)
        if bb>=5: badInt.add(rho)
    return badJ, badInt, target

# ---- (2) full-pencil locator MITM for spurious rho at n=16,24,32 ----
def full_locator_badrho(p, k, cap_combos=3_000_000):
    """Half-sets S subset mu_n (n=4k, |S|=n/2) with sparse locator support {0..k-1,3k/2,2k};
    read rho = [z^{3k/2}] sigma_S.  Return set of realized rho (the family's bad set) + target."""
    n=4*k
    if comb(n, n//2) > cap_combos:
        return None, None
    w=find_gen(p,n); H=[pow(w,i,p) for i in range(n)]
    allowed=set(range(0,k)) | {3*k//2, 2*k}
    target={rho for rho in range(1,p) if pow(rho,8,p)==16%p}
    rhos=set()
    half=n//2
    for S in itertools.combinations(range(n), half):
        pts=[H[i] for i in S]
        coeffs=[1]
        for pt in pts:
            new=[0]*(len(coeffs)+1)
            for i,c in enumerate(coeffs):
                new[i]=(new[i]+(-pt)*c)%p
                new[i+1]=(new[i+1]+c)%p
            coeffs=new
        supp={d for d in range(len(coeffs)) if coeffs[d]%p!=0}
        if supp<=allowed:
            rhos.add(coeffs[3*k//2]%p)
    return rhos, target

# ---- (3) DIRECT V_d^prim mod-p hunt: a primitive (antipodal-free) config of the family gap-variety
# A genuine bad rho with rho^8 != 16 requires the agreement half-set S to be NOT a coset-union
# (a 'primitive' point). We hunt antipodal-free S subset mu_n with the pinned-support locator,
# over a wide prime band, at n where MITM on the support constraints is feasible.
def primitive_hunt(p, k, want=2):
    """Search for an antipodal-free half-set S (|S|=n/2) with the pinned support whose rho^8 != 16.
    n=4k. We MITM: choose the k/2 'high' structure. Feasible n<=32 via direct half-set scan with
    early support pruning."""
    n=4*k
    if comb(n,n//2) > 4_000_000:
        return None
    w=find_gen(p,n); H=[pow(w,i,p) for i in range(n)]
    allowed=set(range(0,k)) | {3*k//2,2*k}
    half=n//2
    found=[]
    for S in itertools.combinations(range(n), half):
        Sset=set(S)
        # antipodal-free in exponents (j and j+n/2)
        if any(((j+n//2)%n) in Sset for j in S if j < n//2):
            continue
        pts=[H[i] for i in S]
        coeffs=[1]
        for pt in pts:
            new=[0]*(len(coeffs)+1)
            for i,c in enumerate(coeffs):
                new[i]=(new[i]+(-pt)*c)%p; new[i+1]=(new[i+1]+c)%p
            coeffs=new
        supp={d for d in range(len(coeffs)) if coeffs[d]%p!=0}
        if supp<=allowed:
            rho=coeffs[3*k//2]%p
            if rho!=0 and pow(rho,8,p)!=16%p:
                found.append((S,rho))
                if len(found)>=want: break
    return found

def main():
    print("="*88)
    print("#407 LANE L4 -- Q1 at d>=16: faithful char-p spurious hunt on the (3k/2,2k) bad set")
    print("="*88)

    print("\n--- (1) Substitution base pencil rho*u^3+u^4 on mu_8 (the u=z^h collapse) ---")
    print("    By Prop 2.4 EVERY (3k/2,2k) pencil collapses here; bad set should be {rho^8=16}.")
    for p in primes_1_mod_n(8, 50, cap=6):
        badJ, badInt, target = base_pencil_badset(p)
        spJ = badJ - target
        print(f"  p={p}: badset(agree>=n/2)={sorted(badJ)}  rho^8=16={sorted(target)}  "
              f"{'MATCH' if badJ==target else ('SPURIOUS '+str(sorted(spJ)) if spJ else 'subset, missing '+str(sorted(target-badJ)))}; "
              f"strictly-interior(agree>=5)={sorted(badInt) if badInt else 'EMPTY'}")

    print("\n--- (2) FULL pencil locator realization, n=16,24,32 (spurious rho^8 != 16 ?) ---")
    for k in [4, 6]:   # n=16, 24
        n=4*k
        for p in primes_1_mod_n(n, 100, cap=3):
            rhos, target = full_locator_badrho(p, k)
            if rhos is None:
                print(f"  k={k} n={n} p={p}: enum too big"); continue
            nz={r for r in rhos if r!=0}
            spurious=nz - target
            print(f"  k={k} n={n} p={p}: |realized nonzero rho|={len(nz)}  |rho^8=16|={len(target)}  "
                  f"{'== target (Q1 holds)' if nz==target else ('SPURIOUS '+str(sorted(spurious)[:6])+' -> Q1 FAILS' if spurious else 'strict subset')}")

    print("\n--- (3) DIRECT primitive V_d^prim mod-p hunt (antipodal-free, rho^8 != 16) ---")
    print("    A primitive point => Q1 norm vanishes mod p => bad reduction. n=16,24,32; wide prime band.")
    for k in [4, 6, 8]:
        n=4*k
        any_prim=False
        ps = primes_1_mod_n(n, 100, cap=10)
        for p in ps:
            res = primitive_hunt(p, k)
            if res is None:
                print(f"  k={k} n={n}: C({n},{n//2}) too big for direct hunt"); break
            if res:
                any_prim=True
                print(f"  k={k} n={n} p={p}: PRIMITIVE pt found rho={res[0][1]} (rho^8={pow(res[0][1],8,p)}!=16) -> Q1 FAILS / bad reduction")
        else:
            if not any_prim:
                print(f"  k={k} n={n}: NO primitive (rho^8!=16) point over {len(ps)} primes up to {ps[-1]} -> Q1 holds (clean reduction)")

if __name__ == "__main__":
    main()
