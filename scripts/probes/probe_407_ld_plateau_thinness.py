#!/usr/bin/env python3
"""
probe_407_ld_plateau_thinness.py  (#444 LD-radius lane)

GOAL (rule-3 thinness gate on the list-decoding reframing):
The board reframed delta* = 1 - s*/n where
  s*(D,k) = max over far monomial lines  L = x^a + gamma*x^b  of
            (max agreement of L with RS[D,k]  over scalars gamma, with #gamma <= budget=n).
Per-direction I_dir(a,b;s) = #{gamma in F_p : x^a+gamma x^b agrees with some deg<k poly on >= s of the s-subsets}
is asserted to be a clean step function whose PLATEAU value = exactly n (one cyclic orbit, n | #bad),
the "divisibility quantization" claimed to come from mu_n being a SUBGROUP.

OPEN, UNCONTESTED QUESTION this probe answers:
  Is the n-plateau quantization (and the resulting s*) THINNESS-ESSENTIAL?
  i.e. does it require D = mu_n (2-power smooth subgroup), or does a RANDOM domain D of the same size
  give the SAME plateau / same s*?  If random gives the SAME s*, the LD-radius object is thickness/
  domain-INVARIANT => any proof of CORE through it would be NON-thinness-essential => WRONG (rule 3).
  If random gives a DIFFERENT (larger s*, i.e. worse) s*, then mu_n's smoothness genuinely SUPPRESSES
  the LD radius -> a live thinness-essential lever.

METHOD (exact, prize regime, PROPER subgroup, never n=q-1):
  - n = 2^a, prime p in prize band p ~ n^beta, p == 1 mod n, index m=(p-1)/n >= 2 (proper subgroup).
  - mu_n = <h>, h = g^m a primitive n-th root.  Verified |mu_n| = n, h^{n/2} != 1.
  - RANDOM control domain D_rand = random n distinct nonzero elements of F_p (NOT a subgroup), same p.
  - For each domain, exact per-direction incidence I_dir(a,b;s) over ALL directions (a in [0,n), b in [k,n))
    and find s* = min s with max_dir I_dir(a,b;s) <= budget=n  (engine's exact definition).
  - Report s*, the plateau structure, Johnson s_J = k + sqrt(k*n), floor k+Theta(n/log n).
  - Compare smooth vs random at the SAME prime (q-fixed, isolates domain structure = thinness).

Honesty: exact integer arithmetic mod p; no float thresholds in the count.  Python-only => axiom-clean
trivially (no Lean produced).  Validates ONLY on proper subgroups; random control is a non-subgroup
domain of equal size, which is exactly the rule-3 contrast object (NOT n=q-1).
"""
import sys, random
from itertools import combinations

def is_prime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % q == 0: return x == q
    d = x-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        y = pow(a,d,x)
        if y==1 or y==x-1: continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True

def factor(x):
    f=[]; d=2
    while d*d<=x:
        if x%d==0:
            f.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: f.append(x)
    return f

def proot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 0

def big_prime(n, beta=4):
    # smallest prime p == 1 mod n with p ~ n^beta (proper subgroup, index>=2)
    base = n**beta
    p = base - (base % n) + 1
    if p <= n: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def divdiff_k(vals, nodes, k, p):
    # k-th divided difference of vals over nodes[0..k], all distinct
    vs = list(vals[:k+1])
    nd = nodes[:k+1]
    for j in range(1,k+1):
        for i in range(k, j-1, -1):
            denom = (nd[i]-nd[i-j]) % p
            vs[i] = (vs[i]-vs[i-1]) * pow(denom, p-2, p) % p
    return vs[k]

def in_rs(vals, nodes, k, p):
    s=len(nodes)
    if s<=k: return True
    for st in range(s-k):
        if divdiff_k(vals[st:st+k+1], nodes[st:st+k+1], k, p) != 0:
            return False
    return True

def incidence_dir(a, b, dom, k, p, s):
    """exact engine incidence: #distinct gamma s.t. x^a+gamma x^b agrees with deg<k poly on the s-subset,
    summed/union over all s-subsets. Returns None if any subset is 'heavy' (saturated)."""
    n=len(dom)
    mua=[pow(d,a,p) for d in dom]
    mub=[pow(d,b,p) for d in dom]
    local=set()
    for comb in combinations(range(n), s):
        nodes=[dom[i] for i in comb]
        u0=[mua[i] for i in comb]
        u1=[mub[i] for i in comb]
        if in_rs(u1, nodes, k, p):
            if in_rs(u0, nodes, k, p):
                return None  # heavy
            continue
        a0=divdiff_k(u0, nodes, k, p) if len(nodes)>k else 0
        a1=divdiff_k(u1, nodes, k, p) if len(nodes)>k else 0
        # need the FULL agreement check across all consecutive windows, not just one divdiff,
        # so solve gamma from the FIRST nonvanishing window then verify entire subset:
        # find a window where a1-component nonzero
        gm=None
        for st in range(len(nodes)-k):
            uu0=u0[st:st+k+1]; uu1=u1[st:st+k+1]; nn=nodes[st:st+k+1]
            d0=divdiff_k(uu0, nn, k, p); d1=divdiff_k(uu1, nn, k, p)
            if d1 != 0:
                gm = (-d0) * pow(d1, p-2, p) % p
                break
        if gm is None:
            continue
        full=[(u0[i]+gm*u1[i])%p for i in range(len(nodes))]
        if in_rs(full, nodes, k, p):
            local.add(gm)
    return local

def s_star(dom, k, p, budget):
    """min s with max over far dirs (b>=k, b!=a) of |incidence| <= budget. returns (s*, peak_profile)."""
    n=len(dom)
    # far monomial lines: a in [0,n), b in [k,n), b != a (x^b is "far" = not in RS[k])
    dirs=[(a,b) for a in range(n) for b in range(k,n) if b!=a]
    # find s* by scanning s upward; s* = min s where max_dir incidence(s) <= budget
    prof={}
    for s in range(k+1, n+1):
        mx=0; heavy=False
        for (a,b) in dirs:
            c=incidence_dir(a,b,dom,k,p,s)
            if c is None:
                heavy=True; break
            mx=max(mx, len(c))
        prof[s]=('HEAVY' if heavy else mx)
        if not heavy and mx<=budget:
            return s, prof  # first s with everything <= budget => s* is the LD radius boundary
    return n, prof

def main():
    print("="*78)
    print("LD-radius PLATEAU thinness gate (#444) — smooth mu_n vs random domain, exact, prize band")
    print("="*78)
    random.seed(20260615)
    import math
    # feasible exhaustive cases: n small (combinatorics C(n,s) blows up). n=8,k=2 and n=8,k=3.
    for (n,k,beta) in [(8,2,4),(8,3,4)]:
        p=big_prime(n,beta)
        g=proot(p); m=(p-1)//n; h=pow(g,m,p)
        assert pow(h,n,p)==1 and pow(h,n//2,p)!=1, "h not primitive n-th root"
        mu=[pow(h,i,p) for i in range(n)]
        assert len(set(mu))==n
        budget=n
        sJ = k + math.sqrt(k*n)
        # smooth
        s_smooth, prof_s = s_star(mu, k, p, budget)
        # random control: n distinct nonzero, NOT a subgroup (verify it's not closed: check a*b not in set typically)
        while True:
            dom_r=random.sample(range(1,p), n)
            # ensure not accidentally a coset/subgroup: check closure fails
            sset=set(dom_r)
            if not all((x*y%p) in sset for x in dom_r[:3] for y in dom_r[:3]):
                break
        s_rand, prof_r = s_star(dom_r, k, p, budget)
        print(f"\n--- n={n} k={k} p={p} (index m={m}, prize-band beta~{beta}) budget={budget} ---")
        print(f"    Johnson s_J = k+sqrt(kn) = {sJ:.3f}  (delta*_J = {1-sJ/n:.3f})")
        print(f"    SMOOTH mu_n : s* = {s_smooth}  delta* = {1-s_smooth/n:.4f}   profile(s->maxI): {prof_s}")
        print(f"    RANDOM dom  : s* = {s_rand}  delta* = {1-s_rand/n:.4f}   profile(s->maxI): {prof_r}")
        verdict = ("THICKNESS-INVARIANT (s* equal) => LD-radius NOT thinness-essential (rule-3 FAIL for this object)"
                   if s_smooth==s_rand else
                   f"THINNESS-SENSITIVE: smooth s*={s_smooth} vs random s*={s_rand} "
                   + ("(smooth SMALLER => mu_n suppresses LD radius: LIVE lever)" if s_smooth<s_rand
                      else "(smooth LARGER => mu_n HELPS adversary: anti-helpful)"))
        print(f"    VERDICT: {verdict}")

if __name__=="__main__":
    main()
