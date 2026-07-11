#!/usr/bin/env python3
"""
wf407 / T389-02-hill  (v2, unbuffered, faster)

Settle the worst-case far-line incidence extremizer:
 (1) Is the extremal binding DIRECTION a monomial? low-exp, high-exp, or neither?
 (2) Does hill-climb over arbitrary words beat the best monomial direction?
 (3) Reproduce the deep-band monomial-PAIR maximizers (x^9,x^11)=104 etc. -> high exponents.

Object:  C = RS[F_p, mu_n, k].  far-line incidence at agreement threshold w:
   I(u0,u1) = #{ gamma in F_p :  max-agreement(u0 + gamma*u1) >= w }
where max-agreement(t) = max over deg-<k polys P of #{i : P(dom_i)=t_i}.

We compute max-agreement EXACTLY via k-subset interpolation (cached denominators).
"""
import sys, itertools, random

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    fs = set(); m = p-1; d = 2
    while d*d <= m:
        while m % d == 0: fs.add(d); m//=d
        d += 1
    if m>1: fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError

def mu_n(p,n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    dom=[pow(h,i,p) for i in range(n)]
    assert len(set(dom))==n
    return dom

class Engine:
    """Exact max-agreement engine with cached Lagrange basis denominators."""
    def __init__(self, dom, k, p):
        self.dom=dom; self.k=k; self.p=p; self.n=len(dom)
        self.subs=list(itertools.combinations(range(self.n),k))
        # precompute, per subset, the Lagrange-evaluated basis: for subset sub and each x in dom,
        # coefficient c[sub][x_index][j] s.t. P(x) = sum_j t[sub[j]]*c[...][j]
        self.basis={}
        inv=[0]*p
        for a in range(1,p): inv[a]=pow(a,p-2,p)
        self.inv=inv
        for sub in self.subs:
            xs=[dom[j] for j in sub]
            # denom_j = prod_{m!=j}(xs[j]-xs[m])
            denoms=[]
            for j in range(k):
                d=1
                for m in range(k):
                    if m!=j: d=(d*(xs[j]-xs[m]))%p
                denoms.append(inv[d%p])
            # for each target x in dom, numerator_j(x)=prod_{m!=j}(x-xs[m])
            rows=[]
            for x in dom:
                coeffs=[]
                for j in range(k):
                    num=1
                    for m in range(k):
                        if m!=j: num=(num*(x-xs[m]))%p
                    coeffs.append((num*denoms[j])%p)
                rows.append(coeffs)
            self.basis[sub]=rows

    def max_agreement(self, t):
        p=self.p; n=self.n; best=self.k
        for sub in self.subs:
            rows=self.basis[sub]
            tj=[t[j] for j in sub]
            cnt=0
            for i in range(n):
                v=0; r=rows[i]
                for jj in range(self.k):
                    v+=tj[jj]*r[jj]
                if v%p==t[i]: cnt+=1
            if cnt>best:
                best=cnt
                if best==n: return n
        return best

    def incidence(self, u0, u1, w, gammas=None):
        p=self.p; n=self.n; cnt=0; bad=[]
        rng = range(p) if gammas is None else gammas
        for gamma in rng:
            t=[(u0[i]+gamma*u1[i])%p for i in range(n)]
            if self.max_agreement(t)>=w:
                cnt+=1; bad.append(gamma)
        return cnt,bad

def powword(dom,a,p): return [pow(x,a,p) for x in dom]

def run_instance(n,k,p,w,label, hc_restarts=20, seed=7, do_hc=True):
    print(f"\n########## {label}: n={n} k={k} p={p} w={w} (rho={k}/{n}={k/n:.3f}) ##########",flush=True)
    dom=mu_n(p,n)
    E=Engine(dom,k,p)
    mon=[powword(dom,a,p) for a in range(n)]

    # (1) monomial directions u1=x^a, u0=0  (a in [k,n-1], so x^a not a codeword)
    print(" -- monomial directions u1=x^a (u0=0) --",flush=True)
    mono=[]
    for a in range(k,n):
        u1=mon[a]
        if E.max_agreement(u1)>=w:   # u1 itself explainable -> not 'far'; skip
            print(f"   a={a:2d}  (skip: u1 not far)",flush=True); continue
        c,_=E.incidence([0]*n,u1,w)
        mono.append((a,c)); print(f"   a={a:2d}  I={c}",flush=True)
    bm=max(mono,key=lambda t:t[1]) if mono else (None,-1)
    print(f"   => best monomial (u0=0): a={bm[0]} I={bm[1]}",flush=True)

    # (2) monomial PAIRS u1=x^a, u0=x^b  -- the (X^a,X^b) family
    print(" -- monomial PAIRS u1=x^a, u0=x^b --",flush=True)
    pb=(None,None,-1); rows=[]
    for a in range(k,n):
        u1=mon[a]
        if E.max_agreement(u1)>=w: continue
        for b in range(0,a):
            c,_=E.incidence(mon[b],u1,w)
            rows.append((a,b,c))
            if c>pb[2]: pb=(a,b,c)
    rows.sort(key=lambda r:-r[2])
    for (a,b,c) in rows[:6]: print(f"   (X^{a},X^{b}) I={c}",flush=True)
    print(f"   => best pair: (X^{pb[0]},X^{pb[1]}) I={pb[2]}",flush=True)

    # (3) hill-climb over arbitrary direction words (u0=0)
    hcb=-1; hcw=None
    if do_hc:
        print(f" -- hill-climb arbitrary u1 (u0=0), {hc_restarts} restarts --",flush=True)
        rng=random.Random(seed)
        def sc(u1):
            if E.max_agreement(u1)>=w: return -1
            return E.incidence([0]*n,u1,w)[0]
        for r in range(hc_restarts):
            cur = list(mon[k + (r % (n-k))]) if r < 2*(n-k) else [rng.randrange(p) for _ in range(n)]
            cs=sc(cur); imp=True
            while imp:
                imp=False
                for i in range(n):
                    old=cur[i]; bv,bs=old,cs
                    cand=set(rng.randrange(p) for _ in range(20)) | set(mon[a][i] for a in range(n))
                    for v in cand:
                        if v==old: continue
                        cur[i]=v; s=sc(cur)
                        if s>bs: bs,bv=s,v
                    cur[i]=bv
                    if bs>cs: cs=bs; imp=True
            if cs>hcb: hcb=cs; hcw=list(cur)
        print(f"   => hill-climb best I={hcb}",flush=True)
        # classify
        isMon=False
        for a in range(n):
            m=mon[a]; ratios=set(); ok=True
            for i in range(n):
                if m[i]==0:
                    if hcw[i]!=0: ok=False;break
                    continue
                ratios.add((hcw[i]*pow(m[i],p-2,p))%p)
            if ok and len(ratios)==1:
                print(f"   converged word = {ratios}*x^{a}  (IS scaled monomial)",flush=True); isMon=True; break
        if not isMon:
            print(f"   converged word NOT a scaled monomial (genuine non-monomial extremizer)",flush=True)

    print(f" SUMMARY {label}: monomial={bm[1]}  pair={pb[2]}@(X^{pb[0]},X^{pb[1]})  "
          f"hillclimb={hcb if do_hc else 'n/a'}",flush=True)
    return dict(mono=bm,pair=pb,hc=hcb)

if __name__=="__main__":
    # Instance A: (12,6) delta=1/4 -> floor(12/4)=3 -> w=9   [O138 / corrected extremality]
    run_instance(12,6,13, 9, "A (12,6) d=1/4", hc_restarts=24)
    # Instance B: (16,8) agree>=9 (radius 7/16, past Johnson) -> w=9  [O12/O163 instance]
    run_instance(16,8,17, 9, "B (16,8) w=9 past-Johnson", hc_restarts=16)
