#!/usr/bin/env python3
"""
FAST decisive #444 test on the B-vs-p ANTI-CORRELATED prime pairs (numpy, exact mcaEvent
over the MONOMIAL stack family -- the structurally extremal directions, a PROVEN lower bound
on epsMCA, matching the discipline of probe_epsmca_field_drift / probe_farline_incidence_exact).

mu_8: B = max_{b!=0}||eta_b|| is non-monotone in p:
   p=97  -> B=5.461  (LARGER B)     p=113 -> B=5.114  (SMALLER B, LARGER p)
   p=241 -> B=6.339  (LARGER B)     p=257 -> B=6.101  (SMALLER B, LARGER p)
So in each pair the SMALLER prime has the LARGER B.  We compute the exact worst-case mcaEvent
bad-gamma COUNT over monomial-syndrome stacks (s0=syn(x^a), s1=syn(x^b)), exactly as the in-tree
mcaEvent: bad at S  <=>  line=s0+g*s1 extends to a codeword on S  AND NOT (s0 extends AND s1
extends) on S, |S|>=m.  Worst-case over (a,b) monomial pairs and all gamma.

OUTCOMES per witness threshold m:
  count IDENTICAL across the pair             => B-blind AND p-blind (combinatorial invariant)
  count LARGER at smaller-p (=larger-B)       => RE-COUPLES to B (the wall)
  count LARGER at larger-p (=smaller-B)       => FIELD-SIZE driven (B irrelevant)

This is a PROVEN LOWER bound on epsMCA (monomial subfamily); a B-blind lower bound that still
captures the binding rung is strong evidence for B-blindness of the true epsMCA, and a B-tracking
lower bound is decisive evidence for re-coupling.
"""
import math, cmath, itertools
import numpy as np

def is_prime(m):
    if m<2: return False
    for d in range(2,int(m**0.5)+1):
        if m%d==0: return False
    return True

def smooth_domain(p,n):
    assert (p-1)%n==0
    for cand in range(2,p):
        g=pow(cand,(p-1)//n,p)
        if pow(g,n,p)==1 and all(pow(g,d,p)!=1 for d in range(1,n)):
            return [pow(g,i,p) for i in range(n)]
    raise ValueError("no gen")

def sup_B(mu,p):
    w=2j*math.pi/p; B=0.0
    for b in range(1,p):
        s=sum(cmath.exp(w*((b*x)%p)) for x in mu)
        if abs(s)>B: B=abs(s)
    return B

def left_null_rows(V,p):
    """left null space basis of (size x k) matrix V over F_p (rows P with P V = 0)."""
    m=len(V); kk=len(V[0]) if m else 0
    aug=[V[i][:]+[1 if j==i else 0 for j in range(m)] for i in range(m)]
    # rref
    pr=0
    for c in range(kk):
        sel=next((r for r in range(pr,m) if aug[r][c]%p),None)
        if sel is None: continue
        aug[pr],aug[sel]=aug[sel],aug[pr]
        inv=pow(aug[pr][c],p-2,p); aug[pr]=[(x*inv)%p for x in aug[pr]]
        for r in range(m):
            if r!=pr and aug[r][c]%p:
                f=aug[r][c]; aug[r]=[(aug[r][j]-f*aug[pr][j])%p for j in range(kk+m)]
        pr+=1
        if pr==m: break
    return [[row[kk+j]%p for j in range(m)] for row in aug
            if all(x%p==0 for x in row[:kk]) and any(x%p for x in row[kk:])]

def mca_count_monomial(p,n,k,a,b,m):
    """exact #{gamma : mcaEvent at line syn(x^a)+gamma*syn(x^b)} restricted to witness sets
    of size >= m.  mcaEvent: exists S, |S|>=m, line extends to codeword on S, AND NOT
    (x^a extends on S AND x^b extends on S).  Computed via per-S left-null affine-in-gamma."""
    xs=smooth_domain.__wrapped__ if False else None
    # precompute per-position monomial values
    X=[smooth_dom[i] for i in range(n)]
    va=[pow(X[i],a,p) for i in range(n)]
    vb=[pow(X[i],b,p) for i in range(n)]
    bad_gammas=set()
    heavy=False
    for size in range(m,n+1):
        for R in itertools.combinations(range(n),size):
            V=[[pow(X[i],j,p) for j in range(k)] for i in R]
            P=left_null_rows(V,p)
            if not P:   # |R|<=k or full rank => everything extends, R cannot witness non-agreement
                continue
            # x^a extends on R  <=>  P (va|R) = 0 ; same for x^b
            paR=[sum(P[t][ii]*va[R[ii]] for ii in range(size))%p for t in range(len(P))]
            pbR=[sum(P[t][ii]*vb[R[ii]] for ii in range(size))%p for t in range(len(P))]
            a_ext = not any(paR)
            b_ext = not any(pbR)
            if a_ext and b_ext:
                continue   # pairJointAgreesOn on R (both extend) => R not a witness for non-agree
            # line = va + g vb extends on R  <=>  P(va|R) + g P(vb|R) = 0
            if not any(pbR):
                if not any(paR):
                    heavy=True   # all gamma make line extend AND not both extend => p bad gammas
                    return p
                continue
            i=next(j for j in range(len(pbR)) if pbR[j])
            g=(-paR[i]*pow(pbR[i],p-2,p))%p
            if all((paR[t]+g*pbR[t])%p==0 for t in range(len(pbR))):
                bad_gammas.add(g)
    return len(bad_gammas)

def worst_mca_count(p,n,k,m):
    global smooth_dom
    smooth_dom=smooth_domain(p,n)
    best=0; arg=None
    for a in range(n):
        for b in range(n):
            if a==b: continue
            c=mca_count_monomial(p,n,k,a,b,m)
            if c>best: best=c; arg=(a,b)
            if best==p: return best,arg
    return best,arg

def main():
    n=8
    PAIRS=[(97,113),(241,257)]
    for k in [6,5,4]:
        rho=k/n
        print(f"\n{'='*84}")
        print(f"RS[mu_{n}, k={k}]  rho={rho:.3f}  Johnson={1-math.sqrt(rho):.3f}  capacity={1-rho:.3f}"
              f"   exact mcaEvent over MONOMIAL stacks (proven lower bound)")
        print(f"{'='*84}")
        ms=list(range(k+1,n+1))   # witness sizes that can refuse a pair
        for (pa,pb) in PAIRS:
            muA=smooth_domain(pa,n); muB=smooth_domain(pb,n)
            Ba=sup_B(muA,pa); Bb=sup_B(muB,pb)
            print(f"\n  PAIR ({pa},{pb}): B({pa})={Ba:.4f} > B({pb})={Bb:.4f}  "
                  f"(smaller prime has LARGER B; B anti-correlated with p)")
            print(f"     {'m':>3} {'delta':>7} | {'cnt@'+str(pa):>9} | {'cnt@'+str(pb):>9} | verdict")
            for m in sorted(ms,reverse=True):
                cA,argA=worst_mca_count(pa,n,k,m)
                cB,argB=worst_mca_count(pb,n,k,m)
                delta=1-m/n
                if cA==0 and cB==0: v="(both 0)"
                elif cA==cB: v=f"IDENTICAL ({cA}) => B-BLIND & p-blind"
                elif cA>cB: v=f"LARGER at smaller-p/larger-B => RE-COUPLES to B"
                else: v=f"larger at larger-p => FIELD-SIZE driven"
                print(f"     {m:>3} {delta:>7.3f} | {cA:>9} | {cB:>9} | {v}   "
                      f"args {argA}/{argB}",flush=True)

if __name__=="__main__":
    main()
