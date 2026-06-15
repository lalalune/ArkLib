#!/usr/bin/env python3
"""
A9 EXPLICIT COSET+TAIL WITNESS -> closed-form upper bound on delta*  (issue #407).

CONSTRUCTION (Mann antipodal block + tail; the extremal bad-witness family):
  For n=2^a, the largest antipodal-paired ("consistent") block is a Phi_2-coset
  B = { mu[i] : i odd } of size n/2 (roots of x^{n/2}+1). We build witness agreement
  subsets  S = B' union T,  where B' subset B is a sub-block and T is a short tail of
  free index points, with |S| = w. For a fixed far direction (a,b), each such S forces
  (generically) a UNIQUE bad gamma; the witness incidence  Iw(a,b;w) = #distinct forced
  gammas over the explicit family. delta* <= 1 - w/n for the DEEPEST w with
      max_dir Iw(a,b; w) > budget = n.

This is a CONSTRUCTIVE LOWER bound on the true I (the family is a subset of all
consistent subsets), hence a PROVEN UPPER bound on delta*. We:
  (1) Compute Iw exactly (big prime q>>n^4, proper mu_n; p-independence re-checked).
  (2) Report the deepest exceeding band -> explicit delta* upper bound g(n,rho).
  (3) Fit closed forms and the orbit decomposition; cross-check vs ground truth.

Fast: family size is small (choose tail from n-|B'| points + choose sub-block), no full
C(n,w) blow-up. Flushes every line.
"""
import itertools, sys
from math import gcd, comb, log2

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=m-1; s=0
    while d%2==0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x in (1,m-1): continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True; break
        if not ok: return False
    return True
def factor(x):
    f={}; d=2
    while d*d<=x:
        while x%d==0: f[d]=f.get(d,0)+1; x//=d
        d+=1
    if x>1: f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(factor(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
def setup(n, plo, skip=0):
    p = plo + (1-plo)%n
    if p<plo: p+=n
    found=0
    while True:
        if isprime(p):
            v=p-1; v2=0
            while v%2==0: v//=2; v2+=1
            if v2 <= int(log2(n))+4:
                if found==skip:
                    g=proot(p); h=pow(g,(p-1)//n,p)
                    mu=[pow(h,i,p) for i in range(n)]
                    return p, mu
                found+=1
        p+=n

def make_member(p, mu, k):
    inv=lambda z: pow(z,p-2,p)
    invc={}
    def ddk(vals, idx):
        vs=list(vals)
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                key=(idx[i],idx[i-j]); d=invc.get(key)
                if d is None:
                    d=inv((mu[idx[i]]-mu[idx[i-j]])%p); invc[key]=d
                vs[i]=(vs[i]-vs[i-1])*d%p
        return vs[k]
    def in_RS(vals, idx):
        w=len(idx)
        if w<=k: return True
        for st in range(w-k):
            if ddk(vals[st:st+k+1], idx[st:st+k+1])!=0: return False
        return True
    return ddk, in_RS

def gamma_of_subset(R, MUa, MUb, mu, k, p, member):
    ddk, in_RS = member
    idx=sorted(R)
    u1=[MUb[i] for i in idx]
    if in_RS(u1, idx):
        u0=[MUa[i] for i in idx]
        return 'SAT' if in_RS(u0, idx) else None
    u0=[MUa[i] for i in idx]
    inv=lambda z: pow(z,p-2,p)
    gm=None; w=len(idx)
    for st in range(w-k):
        a1=ddk(u1[st:st+k+1], idx[st:st+k+1])
        if a1%p:
            a0=ddk(u0[st:st+k+1], idx[st:st+k+1])
            gm=(-a0*inv(a1))%p; break
    if gm is None: return None
    if in_RS([(u0[i]+gm*u1[i])%p for i in range(w)], idx): return gm
    return None

def witness_incidence_at_w(a, b, n, mu, k, p, w, member, blockmode="odd"):
    """Witness family for direction (a,b) at agreement size w:
       S = (sub-block B' of the antipodal coset) union (tail T from complement),
       sized to w. We enumerate all such S with |B'| as large as possible down to 0
       (i.e. all S that are 'block-heavy'): for each split |B'|=j (0..min(w,|B|)),
       choose B' subset B (size j), tail subset complement (size w-j). To keep it a
       genuine *structured witness* (not full enum) we restrict B' to be a PREFIX-coset
       (consecutive in the coset) OR full B, and tail to single points / small runs.
       Returns set of distinct forced gammas."""
    MUa=[pow(x,a,p) for x in mu]; MUb=[pow(x,b,p) for x in mu]
    B=[i for i in range(n) if i%2==1] if blockmode=="odd" else [i for i in range(n) if i%2==0]
    comp=[i for i in range(n) if i not in set(B)]
    gam=set()
    Bsz=len(B)
    # structured witness: full antipodal block B (size n/2) + tail of size w-n/2 from comp,
    # AND all dilates of this pattern by odd units (index dilation preserves coset structure).
    units=[s for s in range(1,n) if gcd(s,n)==1]
    seen=set()
    for s in units:
        Bd=sorted((s*i)%n for i in B)            # dilated block (still an antipodal coset)
        compd=sorted(set(range(n))-set(Bd))
        if w<=len(Bd):
            # sub-block only: take consecutive-in-coset windows of size w
            for start in range(len(Bd)):
                Bp=tuple(sorted(Bd[(start+j)%len(Bd)] for j in range(w)))
                if Bp in seen: continue
                seen.add(Bp)
                g=gamma_of_subset(Bp, MUa, MUb, mu, k, p, member)
                if g not in (None,'SAT'): gam.add(g)
        else:
            tail_need=w-len(Bd)
            if tail_need>len(compd): continue
            for T in itertools.combinations(compd, tail_need):
                S=tuple(sorted(list(Bd)+list(T)))
                if S in seen: continue
                seen.add(S)
                g=gamma_of_subset(S, MUa, MUb, mu, k, p, member)
                if g not in (None,'SAT'): gam.add(g)
    return gam

def main():
    print("="*84, flush=True)
    print("A9 COSET+TAIL WITNESS upper bound on delta*  (exact char-0, big prime, proper mu_n)", flush=True)
    print("="*84, flush=True)
    cases=[(8,2),(8,4),(16,4),(16,8),(32,8),(32,16)]
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    rows=[]
    for (n,k) in cases:
        rho=k/n
        plo=max(200003, 4*n*n*n*n+7)
        p, mu = setup(n, plo); p2, mu2 = setup(n, plo, skip=3)
        member=make_member(p,mu,k); member2=make_member(p2,mu2,k)
        budget=n
        print(f"\n{'='*72}", flush=True)
        print(f"n={n} k={k} rho={rho}  q={p} (pindep q2={p2})  budget=n={n}", flush=True)
        # far directions; for speed restrict to a representative spread incl maximal-orbit
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
        w_constr=None; w_constr_dir=None
        for w in range(k+1, n):
            wbest=0; wbdir=None; wbest2=0
            for (a,b) in dirs:
                wg=witness_incidence_at_w(a,b,n,mu,k,p,w,member)
                if len(wg)>wbest: wbest=len(wg); wbdir=(a,b)
            # p-independence check at the worst dir found
            if wbdir is not None:
                wbest2=len(witness_incidence_at_w(*wbdir, n,mu2,k,p2,w,member2))
            pin = "PINDEP-OK" if wbest==wbest2 else f"PINDEP-FAIL({wbest}vs{wbest2})"
            cross = "OVER" if wbest>budget else "ok"
            if wbest>budget:
                w_constr=w; w_constr_dir=wbdir
            mk = " <-- deepest exceeding (so far)" if wbest>budget else ""
            print(f"   w={w:2d} delta={1-w/n:.4f}: witnessWorstI={wbest:5d}[{cross}] dir={wbdir} {pin}{mk}", flush=True)
        ds_upper = 1-(w_constr+1)/n if w_constr is not None else None
        # delta* <= 1 - (w_constr+1)/n : at w_constr witness EXCEEDS budget, so delta=1-w_constr/n
        # is NOT admissible; the upper bound on admissible delta is 1-(w_constr+1)/n.
        ds_upper_strict = 1-(w_constr)/n if w_constr is not None else None
        print(f"  RESULT: deepest band with witness-I > n: w_constr={w_constr} (dir {w_constr_dir})", flush=True)
        print(f"          => delta* <= 1-(w_constr+1)/n = {ds_upper}  "
              f"[witness rules out delta >= 1-w_constr/n = {ds_upper_strict}]", flush=True)
        g=gt.get((n,k))
        if g is not None:
            print(f"          issue ground-truth delta* = {g}  "
                  f"(upper bound {'VALID' if ds_upper is None or ds_upper>=g-1e-12 else 'VIOLATED'})", flush=True)
        rows.append((n,k,rho,w_constr,ds_upper,g))
    print("\n"+"="*84, flush=True)
    print("CLOSED-FORM TABLE: witness upper bound vs ground truth", flush=True)
    print(f"{'n':>4}{'k':>4}{'rho':>7}{'w_constr':>9}{'dsUpper':>9}{'gt':>8}"
          f"{'1-rho':>7}{'1-rho-1/n':>11}{'gap*log2n':>11}", flush=True)
    for (n,k,rho,wc,du,g) in rows:
        gl = (((1-rho)-du)*log2(n)) if du is not None else 0
        print(f"{n:>4}{k:>4}{rho:>7.3f}{str(wc):>9}{str(round(du,4) if du else du):>9}"
              f"{str(g):>8}{1-rho:>7.3f}{1-rho-1/n:>11.4f}{gl:>11.4f}", flush=True)

if __name__=="__main__":
    main()
