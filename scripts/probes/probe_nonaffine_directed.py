#!/usr/bin/env python3
"""Directed adversarial search for NONAFFINE bad families at UDR-edge band radii.

Slope collapse conjecture: on the band n in [2w+k+1, 2w+2k), every bad family's
explainer map gamma -> p_gamma admits an affine selection (deg <= 1). Affine families
are capped at #bad <= w+1 (live-column count). A nonaffine family BEATING w+1 would
refute the conjectured #bad <= n-shape on the band; ANY nonaffine family >= 3 refutes
slope collapse as stated.

Construction strategy (from the pencil analysis): a degree-t family needs
  u0(i) + g*eps(i) - P(g)(i) = -psi_i * prod_{r in roots_i} (g - r)   per column i,
with P's coefficients m_2..m_t CODEWORDS. Writing the column poly's coefficients:
  top: m_t(i) = psi_i (codeword), and for 2 <= j < t: m_j(i) = psi_i * (+-e_{t-j}(roots_i))
must ALSO be codewords -- "rational rigidity". For t = 2 (quadratic pencils):
  column i with root pair {r1_i, r2_i}: m_2(i) = psi_i, and the linear/constant parts
  fold into eps and u0 which are FREE. So t=2 needs NO rigidity beyond m_2 a codeword!
  Columns: u0(i) + g*eps(i) - q(i) - g*m1(i) - g^2*m2(i) = -m2(i)*(g-r1_i)*(g-r2_i)
  expand: matching coefficients in g:
    g^2: -m2(i) = -m2(i)                                   [free, m2 = any codeword]
    g^1: eps(i) - m1(i) = m2(i)*(r1_i + r2_i)              [defines eps given m1 free... m1 codeword]
    g^0: u0(i) - q(i) = -m2(i)*r1_i*r2_i                   [defines u0 given q codeword]
  ALL FREE: eps(i) := m1(i) + m2(i)*(r1_i+r2_i), u0(i) := q(i) - m2(i)*r1_i*r2_i.
  Columns where m2(i) = 0 (<= k-1 of them): column poly = (eps(i)-m1(i))*g + (u0-q)(i):
  choose eps(i)=m1(i), u0(i)=q(i): IDENTICALLY-ZERO columns (joint-risk: they explain
  (q,m1) jointly on <= k-1 < a points -- safe).
  Then gamma in Gamma is bad iff #{i : gamma in roots_i} + z_id >= a.
  Coverage: sum_i |roots_i ∩ Gamma| <= 2 * #live. Per-gamma need a - z_id.
  So N <= 2*live/(a - z_id) <= 2(n-k+1)/(a-k+1).
  At band a ~ n/2: N <= ~4. COMPARE affine cap w+1 ~ n/2: t=2 directed is WORSE.
  CONCLUSION TO VERIFY: t=2 construction exists (refuting literal slope collapse!)
  but cannot beat affine. Then the conjecture must be RESTATED:
  "pencil count: #bad <= max over t of t*(n - z_t)/(a - z_t) with z_t <= a-1 (t=1),
   z_t <= k-1 (t>=2)" => #bad <= max(w+1, t*(n-k+1)/(a-k+1)) -- need t-control for t>=3.

This probe BUILDS the t=2 stacks explicitly and measures actual #bad and affineness:
  1. verify the constructed stacks have the predicted bad gammas (sanity of the design),
  2. check whether bad sets ARE nonaffine (>=3 gammas, no affine selection),
  3. measure max nonaffine #bad achievable vs the affine cap w+1,
  4. ALSO try t=3 with rigidity hack: all root-triples sharing fixed pair structure.

If (2) finds nonaffine families: slope collapse AS STATED is refuted (witness logged),
and the surviving statement is the two-regime pencil cap. That is the honest outcome
to report either way.
"""
import itertools, random

def make_inv(p):
    return [0]+[pow(x,p-2,p) for x in range(1,p)]

def poly_mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]=(r[i+j]+ai*bj)%p
    return r

def poly_eval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r

def interp(xs,ys,p,inv):
    k=len(xs); co=[0]*k
    for i in range(k):
        num=[1];den=1
        for j in range(k):
            if j==i:continue
            num=poly_mul(num,[(-xs[j])%p,1],p); den=den*((xs[i]-xs[j])%p)%p
        s=ys[i]*inv[den]%p
        for d_ in range(len(num)): co[d_]=(co[d_]+s*num[d_])%p
    return co

def cw_through(idx,vals,pts,k,p,inv):
    return tuple(poly_eval(interp([pts[i] for i in idx],list(vals),p,inv),x,p) for x in pts)

def explainers(word,pts,k,a,p,inv):
    n=len(word); seen={}
    for sub in itertools.combinations(range(n),k):
        cw=cw_through(sub,[word[i] for i in sub],pts,k,p,inv)
        agr=sum(1 for i in range(n) if cw[i]==word[i])
        if agr>=a: seen[cw]=agr
    return seen

def joint(u0,u1,pts,k,a,p,inv):
    n=len(u0)
    e0=explainers(u0,pts,k,a,p,inv); e1=explainers(u1,pts,k,a,p,inv)
    for c0 in e0:
        for c1 in e1:
            if sum(1 for i in range(n) if c0[i]==u0[i] and c1[i]==u1[i])>=a: return True
    return False

def bad_gammas(u0,u1,pts,k,a,p,inv):
    n=len(u0)
    if joint(u0,u1,pts,k,a,p,inv): return None  # dead stack
    out={}
    for g_ in range(p):
        w_=tuple((u0[i]+g_*u1[i])%p for i in range(n))
        ex=explainers(w_,pts,k,a,p,inv)
        if ex: out[g_]=ex
    return out

def affine_selectable(bad,p,inv,n):
    gs=sorted(bad); N=len(gs)
    if N<=2: return True
    g0,g1=gs[0],gs[1]
    for p0 in bad[g0]:
        for p1 in bad[g1]:
            dg=(g1-g0)%p
            c=tuple((p1[i]-p0[i])*inv[dg]%p for i in range(n))
            q=tuple((p0[i]-g0*c[i])%p for i in range(n))
            if all(tuple((q[i]+g_*c[i])%p for i in range(n)) in bad[g_] for g_ in gs[2:]):
                return True
    return False

def t2_construct(p,g,n,k,w,rng,assign_mode):
    """Build the explicit t=2 stack: q, m1, m2 codewords; root pairs per live column."""
    inv=make_inv(p); pts=[pow(g,i,p) for i in range(n)]; a=n-w
    # codewords from random k-point interpolation
    def rand_cw():
        sub=rng.sample(range(n),k)
        return cw_through(sub,[rng.randrange(p) for _ in range(k)],pts,k,p,inv)
    q=rand_cw(); m1=rand_cw()
    # m2: nonzero codeword, prefer some zeros in-domain (max k-1)
    sub=rng.sample(range(n),k)
    vals=[0]*(k-1)+[rng.randrange(1,p)]
    m2=cw_through(sub,vals,pts,k,p,inv)
    live=[i for i in range(n) if m2[i]!=0]
    zid=[i for i in range(n) if m2[i]==0]
    # target family Gamma and root assignment
    z=len(zid); need=a-z  # live zeros needed per gamma
    if need<=0: return None
    Nmax=max(2, (2*len(live))//need)
    Gamma=rng.sample(range(p),min(p, Nmax))
    roots={}
    if assign_mode=='greedy':
        # round-robin pairs to equalize coverage
        cover={g_:0 for g_ in Gamma}
        for i in live:
            picks=sorted(Gamma,key=lambda g_:cover[g_])[:2]
            roots[i]=(picks[0],picks[1])
            for g_ in picks: cover[g_]+=1
    else:
        for i in live:
            roots[i]=tuple(rng.sample(Gamma,2))
    # build the stack
    u1=[0]*n; u0=[0]*n
    for i in range(n):
        if i in roots:
            r1,r2=roots[i]
            u1[i]=(m1[i]+m2[i]*(r1+r2))%p
            u0[i]=(q[i]-m2[i]*r1*r2)%p
        else:
            u1[i]=m1[i]; u0[i]=q[i]
    return tuple(u0),tuple(u1),pts,a,inv,Gamma,roots,zid

def run(p,g,n,k,w,trials,label):
    rng=random.Random(2026)
    best_nonaffine=0; best_total=0; refuted=False
    for t in range(trials):
        mode='greedy' if t%2==0 else 'random'
        c=t2_construct(p,g,n,k,w,rng,mode)
        if c is None: continue
        u0,u1,pts,a,inv,Gamma,roots,zid=c
        bad=bad_gammas(u0,u1,pts,k,a,p,inv)
        if bad is None or not bad: continue
        N=len(bad)
        best_total=max(best_total,N)
        if N>=3 and not affine_selectable(bad,p,inv,n):
            refuted=True
            best_nonaffine=max(best_nonaffine,N)
            if best_nonaffine==N:
                print(f"  NONAFFINE WITNESS #bad={N}: u0={u0} u1={u1} bad={sorted(bad)}")
    print(f"[{label}] p={p} n={n} k={k} w={w} a={n-w} trials={trials}: "
          f"max#bad={best_total}, nonaffine_found={refuted}, max_nonaffine={best_nonaffine}, affine_cap(w+1)={w+1}")

if __name__=='__main__':
    # band instances
    run(19,4,9,2,3,150,'t2-edge-n9k2')
    run(17,2,8,3,2,150,'t2-edge-n8k3')
    run(17,3,16,3,6,60,'t2-edge-n16k3')
    # larger p for more gamma-room at same band geometry
    run(73,16,9,2,3,80,'t2-edge-n9k2-p73')   # ord(16) mod 73 = 9? 16^3=4096=4096-56*73=8, 16^9=8^3=512=512-7*73=1 yes
