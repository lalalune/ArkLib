#!/usr/bin/env python3
"""
probe_ncore_empty_listgrowth_prize v4 (#389/#407 — THE prize-deciding cyclic-sieving experiment)

EXACT in-tree object (AbacusNCore.lean, n beads; HOMDSSmoothObstruction; RootsOfUnityVandermonde):
  beta_j = lam_j + (n-1-j), j=0..n-1, lam a partition with <= n parts.
  nCoreEmpty(lam) <=> {beta_j mod n} pairwise distinct (one bead per runner)
                  <=> det(zeta^{beta_j i}) != 0 on mu_n  <=>  s_lam(mu_n) != 0  (RSW hook-content).

DERIVED EXACT COUNT (this probe proves it & cross-checks brute, ALL n):
  n-core-EMPTY configs (n beads) <-> tuples (c_0,...,c_{n-1}) in N^n, beta = desc-sort{r+n*c_r},
  and  |lam| = n * sum_r c_r.  Hence
       #{ n-core-EMPTY lam of size n*S }  =  #{ c in N^n : sum c = S }  =  C(S+n-1, n-1).
  (NOT the n-quotient n-tuple-of-partitions count -- that is a different statistic; we use the
   correct c-parametrization, validated below against brute force for n in {4,6,8}.)

PRIZE QUESTION: at prize params (smooth mu_{2^mu}, rate k=n/2, agreement a~Johnson sqrt(kn)),
the LIST-certificate gap shapes fit a (<=k rows) x (<=excess=a-k cols) box.  We count the
n-core-EMPTY shapes in that box (the certificate count) AND the EXACT distinct pinned F_p
codewords (the genuine list), multi-n {16..256}, and fit poly vs super-poly.
"""
import math, itertools, sys
def out(*a): print(*a); sys.stdout.flush()

# ---- number theory (NO sympy) ----
def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True
def prime_for(n, mult=8):
    c = mult*n + 1
    while not (c > n and is_prime(c)): c += n
    return c
def smooth_subgroup(p, n):
    assert (p-1) % n == 0 and n < p-1
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        if pow(h, n, p) == 1 and all(pow(h, j, p) != 1 for j in range(1, n)):
            return [pow(h, t, p) for t in range(n)]
    raise RuntimeError

# ---- abacus n-core (AbacusNCore.lean) ----
def beta_of(lam, n):
    lam = list(lam) + [0]*(n-len(lam)); return [lam[j]+(n-1-j) for j in range(n)]
def ncore_empty(lam, n):
    return len(lam) <= n and len(set(x%n for x in beta_of(lam, n))) == n

# ---- hook-content (RSW) ----
def cells_content_hook(lam):
    lam = [x for x in lam if x > 0]
    if not lam: return []
    conj = [sum(1 for r in lam if r > c) for c in range(lam[0])]
    return [(j-i, (lam[i]-1-j)+(conj[j]-1-i)+1) for i in range(len(lam)) for j in range(lam[i])]
def schur_vanishes_at_d(lam, d):
    nc = sum(1 for ct,_ in cells_content_hook(lam) if ct%d==0)
    nh = sum(1 for _,h in cells_content_hook(lam) if h%d==0)
    return nc > nh

# ---- brute enumeration (small-n validation) ----
def parts_in_box(maxparts, maxpart):
    seen=set()
    def rec(slots,prev):
        if slots==0: yield (); return
        for v in range(prev,0,-1):
            for rest in rec(slots-1,v): yield (v,)+rest
        yield ()
    for t in rec(maxparts, maxpart):
        if t not in seen: seen.add(t); yield t

# ---- EXACT closed form: c-parametrization, UNBOUNDED (<=n parts) ----
def ncore_empty_count_size_le(n, Nmax):
    """#{n-core-EMPTY lam (<=n parts) of size <= Nmax} = sum_{S: nS<=Nmax} C(S+n-1,n-1)."""
    Smax = Nmax // n
    return sum(math.comb(S+n-1, n-1) for S in range(Smax+1))

# ---- box-constrained n-core-EMPTY count via abacus DP ----
def ncore_empty_count_in_box(n, krows, excess):
    """#{ n-core-EMPTY lam : <= krows parts, each part <= excess }.
    Uses c-param: lam <-> c in N^n via beta=desc-sort{r+n c_r}. The box (krows x excess) is a
    constraint on lam directly; we count by DIRECT brute over c only when feasible, else by the
    SIZE-bounded closed form as an UPPER bound (every box shape has size <= krows*excess).
    For decisive growth law we report BOTH: exact-box (small n via brute c) and size-cap closed form."""
    # exact box count via brute over partitions (feasible only small)
    cnt = 0
    for lam in parts_in_box(min(krows,n), excess):
        if lam and ncore_empty(lam, n): cnt += 1
    return cnt

# ---- exact F_p codeword list (optimized) ----
def interp(xs, ys, k, p):
    co=[0]*k
    for i in range(k):
        num=[1]; den=1
        for j in range(k):
            if j==i: continue
            nw=[0]*(len(num)+1); mj=(-xs[j])%p
            for t,cc in enumerate(num):
                nw[t]=(nw[t]+cc*mj)%p; nw[t+1]=(nw[t+1]+cc)%p
            num=nw; den=den*(xs[i]-xs[j])%p
        yi=ys[i]*pow(den,p-2,p)%p
        for t in range(len(num)): co[t]=(co[t]+yi*num[t])%p
    return tuple(co)
def exact_list_multi(D, w, p, k, thresholds):
    n=len(D); powmat=[[pow(x,t,p) for t in range(k)] for x in D]; polys={}
    for idx in itertools.combinations(range(n), k):
        c=interp([D[i] for i in idx],[w[i] for i in idx],k,p)
        if c in polys: continue
        ag=0
        for i in range(n):
            v=0; pm=powmat[i]
            for t in range(k): v+=c[t]*pm[t]
            if v%p==w[i]: ag+=1
        polys[c]=ag
    return {a: sum(1 for ag in polys.values() if ag>=a) for a in thresholds}, polys
def worst_word(D, p, k):
    """Best over cyclic-sieving coset-glued words AND random words (maximize list)."""
    import random; rng=random.Random(7); n=len(D); best=None; bestL=-1
    cands=[]
    for nb in [d for d in (2,4,8) if n%d==0]:
        bc=[tuple(((b*37+t*101+5)%(p-1))+1 for t in range(k)) for b in range(nb)]
        cands.append([sum(bc[t%nb][s]*pow(D[t],s,p) for s in range(k))%p for t in range(n)])
    for _ in range(20):
        cands.append([rng.randrange(p) for _ in range(n)])
    # pick the one with largest list at a=k+1 (cheap proxy) -- but just return all candidates' max later
    return cands

# ---- growth law fit ----
def fit(ns, vals):
    pts=[(n,v) for n,v in zip(ns,vals) if v>0]
    if len(pts)<2: return None,None
    ln=[math.log(n) for n,_ in pts]; lv=[math.log(v) for _,v in pts]; nn=[float(n) for n,_ in pts]
    def slope(xs,ys):
        m=len(xs); mx=sum(xs)/m; my=sum(ys)/m
        return sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
    return slope(ln,lv), slope(nn,lv)


def main():
    out("="*94)
    out("n-CORE-EMPTY LIST GROWTH at PRIZE PARAMETERS (cyclic-sieving prize-decider, v4 EXACT)")
    out("  smooth mu_{2^mu}, a=Johnson sqrt(kn), k=rho*n, multi-n {16..256}, multi-prime")
    out("="*94)

    NS=[16,32,64,128,256]

    out("\n[0] CROSS-VAL hook-content(d=n) == abacus n-core (in-tree theorem; 0 mismatch req'd):")
    for n in [8,12,16]:
        tot=mism=0
        for lam in parts_in_box(min(6,n),6):
            tot+=1
            if (not ncore_empty(lam,n))!=schur_vanishes_at_d(lam,n): mism+=1
        out(f"    n={n:>3}: shapes={tot}, mismatches={mism}  {'OK' if mism==0 else '*** BAD ***'}")

    out("\n[0b] VALIDATE closed form C(S+n-1,n-1) vs brute #{n-core-EMPTY, <=n parts, size<=N}:")
    for n in [4,6,8,10]:
        N=4*n
        brute=0
        # brute over partitions of size<=N with <=n parts
        for m in range(N+1):
            def parts_of(mm,maxp):
                r=[]
                def rec(rem,prev,cur):
                    if rem==0: r.append(tuple(cur)); return
                    if len(cur)>=maxp: return
                    for v in range(min(prev,rem),0,-1):
                        cur.append(v); rec(rem-v,v,cur); cur.pop()
                rec(mm,mm,[]); return r
            for lam in parts_of(m,n):
                if ncore_empty(lam,n): brute+=1
        cf=ncore_empty_count_size_le(n,N)
        out(f"    n={n:>3} (size<={N}): brute={brute:>6}  closed=C-sum={cf:>6}  {'OK' if brute==cf else '*** DIFF ***'}")

    out("\n[1] PRIZE PARAMS (rho=1/2; Johnson agreement a=ceil(sqrt(kn))):")
    out(f"    {'n':>4} {'k':>5} {'a':>5} {'excess':>7} {'box k*excess':>13} {'p':>12}")
    params={}
    for n in NS:
        k=n//2; a=math.ceil(math.sqrt(k*n)); excess=a-k; p=prime_for(n,8)
        params[n]=(k,a,excess,p)
        out(f"    {n:>4} {k:>5} {a:>5} {excess:>7} {k*excess:>13} {p:>12}")

    out("\n[2] n-core-EMPTY CERTIFICATE COUNT, two measures, at Johnson agreement:")
    out("    (A) UNBOUNDED size<=k*excess closed form C-sum;  (B) EXACT box(<=k rows,<=excess cols)")
    out(f"    {'n':>4} {'excess':>7} | {'(A) size-cap closed':>20} {'(B) exact box (brute)':>22}")
    certA=[]; certB=[]
    for n in NS:
        k,a,excess,p=params[n]
        A=ncore_empty_count_size_le(n, k*excess)
        # exact box brute feasible only if partition count in box is small
        B = None
        if excess <= 4 and min(k,n)*excess <= 64:
            B = ncore_empty_count_in_box(n,k,excess)
        certA.append(A); certB.append(B)
        bs = f"{B}" if B is not None else "(box brute infeasible)"
        out(f"    {n:>4} {excess:>7} | {A:>20} {bs:>22}")

    out("\n[3] EXACT F_p CODEWORD LIST (worst over coset-glued + random words), full C(n,k):")
    out(f"    {'n':>4} {'k':>5} {'a(John)':>8} {'p':>7} | {'list@Johnson':>12} {'list@k+1(boundary)':>18} {'C(n,k)':>10}")
    cw_ns=[]; cw_johnson=[]; cw_boundary=[]
    for n in NS:
        k,a,excess,p=params[n]
        if math.comb(n,k) > 60_000:
            out(f"    {n:>4} {k:>5} {a:>8} {p:>7} | {'(C(n,k) huge: C='+str(math.comb(n,k))+')':>40}")
            continue
        D=smooth_subgroup(p,n); cands=worst_word(D,p,k)
        thr=[k+1,a]; bestJ=0; bestB=0
        for w in cands:
            res,_=exact_list_multi(D,w,p,k,thr)
            bestJ=max(bestJ,res[a]); bestB=max(bestB,res[k+1])
        cw_ns.append(n); cw_johnson.append(bestJ); cw_boundary.append(bestB)
        out(f"    {n:>4} {k:>5} {a:>8} {p:>7} | {bestJ:>12} {bestB:>18} {math.comb(n,k):>10}")

    out("\n[4] AGREEMENT SWEEP n=16: cert count (size-cap) vs EXACT worst codeword list:")
    out(f"    {'a':>3} {'a-k':>4} | {'cert(size-cap)':>14} {'exact list':>11}")
    n=16; k,_,_,p=params[n]; D=smooth_subgroup(p,n); cands=worst_word(D,p,k)
    sweep=list(range(k+1, math.ceil(math.sqrt(k*n))+3))
    listres={a:0 for a in sweep}
    for w in cands:
        res,_=exact_list_multi(D,w,p,k,sweep)
        for a in sweep: listres[a]=max(listres[a],res[a])
    for a in sweep:
        excess=a-k; cert=ncore_empty_count_size_le(n, k*excess)
        out(f"    {a:>3} {a-k:>4} | {cert:>14} {listres[a]:>11}")

    out("\n[5] GROWTH LAW (decisive):")
    pa,ea=fit(NS,certA)
    out(f"    n-core-EMPTY CERT (size-cap closed): poly-deg(loglog)={pa:.3f}  exp-rate(linlog)={ea:.5f}")
    if len(cw_johnson)>=2:
        pj,ej=fit(cw_ns,cw_johnson); pb,eb=fit(cw_ns,cw_boundary)
        out(f"    EXACT list @ Johnson:                poly-deg(loglog)={pj:.3f}  exp-rate(linlog)={ej:.5f}")
        out(f"    EXACT list @ k+1 boundary:           poly-deg(loglog)={pb:.3f}  exp-rate(linlog)={eb:.5f}")
    out("\n    VERDICT:")
    out(f"      CERT count: {'SUPER-POLY' if ea>0.05 else 'POLY'} (exp-rate {ea:.3f}, poly-deg {pa:.2f})")
    if len(cw_johnson)>=2:
        out(f"      EXACT LIST @ Johnson: {'SUPER-POLY => FLOOR REFUTED' if ej>0.05 else 'POLY (deg %.2f) => list face closes'%pj}")
    out("="*94)


if __name__ == "__main__":
    main()
