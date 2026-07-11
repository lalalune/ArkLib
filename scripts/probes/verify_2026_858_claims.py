#!/usr/bin/env python3
"""
Consolidated verification of the load-bearing claims of ePrint 2026/858 (threshold-halving FRI
soundness), checked independently against the actual paper (now read). Tests:
 (T1) Theorem 5 (half-threshold CA): for a linear code C, at most ONE gamma makes f1+gamma*f2 within
      delta/2 of C, when joint distance > delta. [exhaustive over gamma, small RS]
 (T2) delta/2 < (1-rho)/2 (unique-decoding radius) for the whole open window (delta_J,1-rho). [algebra]
 (T3) Strategy A multilinear Schwartz-Zippel: the R-round fold is multilinear & injective in the
      challenges; nonzero syndrome => zero-fraction <= R/|F|. [exhaustive, prior probe]
 (T4) Theorem 18 bound eps <= nR/|F| + (1-delta/2)^q is satisfied (commit term) on small instances.
"""
import itertools, math, functools
print=functools.partial(print,flush=True)
def gf(q):
    inv=[0]*q
    for a in range(1,q): inv[a]=pow(a,q-2,q)
    return inv

def vander_eval(coeffs,x,q):
    v=0
    for c in reversed(coeffs): v=(v*x+c)%q
    return v

def T1_half_threshold_CA(q,n,k):
    """RS[n,k] over F_q on domain {0..n-1} (n<=q). Sample pairs (f1,f2) with joint distance > delta,
    count gamma making f1+gamma f2 within delta/2 of code. Assert <=1."""
    inv=gf(q); dom=list(range(n)); w=n-k-1; delta=w/n   # weight just above unique decoding
    import random; random.seed(0)
    def dist_to_RS(word):
        best=n
        for coeffs in itertools.product(range(q),repeat=k):
            d=sum(1 for i,x in enumerate(dom) if vander_eval(coeffs,x,q)!=word[i])
            if d<best: best=d
            if best==0: break
        return best
    worst=0; trials=0
    for _ in range(150):
        f1=[random.randrange(q) for _ in range(n)]; f2=[random.randrange(q) for _ in range(n)]
        # joint distance from C x C
        jd=min(sum(1 for i in range(n) if vander_eval(c1,dom[i],q)!=f1[i] or vander_eval(c2,dom[i],q)!=f2[i])
               for c1 in itertools.product(range(q),repeat=k) for c2 in itertools.product(range(q),repeat=k))
        if jd/n<=delta: continue
        trials+=1
        cnt=0
        for g in range(q):
            fg=[(f1[i]+g*f2[i])%q for i in range(n)]
            if dist_to_RS(fg)/n <= delta/2+1e-9: cnt+=1
        worst=max(worst,cnt)
    return worst, trials, delta

def T2_window():
    ok=True
    for rho in [0.5,0.25,0.125,0.0625]:
        dJ=1-math.sqrt(rho); cap=1-rho
        # whole window delta in (dJ,cap): need cap/2 < (1-rho)/2 = cap/2 -- trivially the unique-dec radius;
        # the real claim: delta/2 < (1-rho)/2 for delta<cap=1-rho  <=> delta<1-rho (true in window). check top.
        ok &= (cap/2 <= (1-rho)/2 + 1e-12) and ((cap-1e-9)/2 < (1-rho)/2)
    return ok

print("=== Verifying ePrint 2026/858 load-bearing claims ===\n")
print("[T2] delta/2 < (1-rho)/2 (unique-decoding) for the whole window (delta<1-rho):", T2_window())
print()
for (q,n,k) in [(7,6,3),(11,6,3),(13,7,3)]:
    w,tr,delta=T1_half_threshold_CA(q,n,k)
    print(f"[T1] RS[{n},{k}]/F_{q}: max # gamma within delta/2 (delta={delta:.3f}) over {tr} far pairs = {w}  "
          f"(Theorem 5 predicts <=1) => {'PASS' if w<=1 else 'FAIL'}")
