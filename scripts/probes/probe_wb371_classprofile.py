#!/usr/bin/env python3
"""
Class-size profile of real bad sets (p=12289): is small-class multiplicity
a real gap, or does size-6 dominate?

For each bad scalar gamma in a stack, its class = the quadratic q with
R1 = q on the agreement part of gamma's witness. Measure, over the
record-22 stack + adversarial constructions: the number of DISTINCT
classes (quadratics carrying >=2 bad scalars) and their size distribution.
If many small (size 3-5) classes appear, the assembly needs a small-class
count bound (attachment-gated); if size-6 dominates and few classes total,
three_class_collapse + sharp caps nearly suffice.
"""
import itertools, random
from collections import Counter
src = open("scripts/probes/probe_wb371_blockladder2.py").read()
ns = {}
exec(src[:src.index("best_per_ns")], ns)
p, n, D, peval = ns['p'], ns['n'], ns['D'], ns['peval']
solve_linear, pencil_row, MATS = ns['solve_linear'], ns['pencil_row'], ns['MATS']
s = 7

def census_full(u0, u1):
    """return dict gamma -> list of witness subsets (size 7)."""
    bad = {}
    for S, M in MATS:
        v0 = [u0[i] for i in S]; v1 = [u1[i] for i in S]
        tb = [sum(M[r][j]*v1[j] for j in range(s))%p for r in range(4)]
        if not any(tb): continue
        ta = [sum(M[r][j]*v0[j] for j in range(s))%p for r in range(4)]
        j = next(t for t in range(4) if tb[t])
        gam = (-ta[j])*pow(tb[j],p-2,p)%p
        if all((ta[t]+gam*tb[t])%p==0 for t in range(4)):
            bad.setdefault(gam, []).append(set(S))
    return bad

def interp_quad_agreement(u1):
    """for each quadratic through >=3 graph pts, its agreement size."""
    # reuse: quadratics through triples
    def quad(i,j,k):
        xs=[D[i],D[j],D[k]]
        if len(set(xs))<3: return None
        ys=[u1[i],u1[j],u1[k]]; c=[0,0,0]
        for a in range(3):
            num=[1]; den=1
            for b in range(3):
                if b==a: continue
                num=[(-xs[b]*(num[t] if t<len(num) else 0)+(num[t-1] if t-1>=0 else 0))%p
                     for t in range(len(num)+1)]
                den=den*((xs[a]-xs[b])%p)%p
            f=ys[a]*pow(den,p-2,p)%p
            for t in range(3): c[t]=(c[t]+f*(num[t] if t<len(num) else 0))%p
        return tuple(c)
    sizes={}
    for (i,j,k) in itertools.combinations(range(n),3):
        c=quad(i,j,k)
        if c is None: continue
        if c not in sizes:
            cnt=sum(1 for t in range(n) if (c[0]+c[1]*D[t]+c[2]*D[t]*D[t])%p==u1[t])
            sizes[c]=cnt
    return sizes

# record-22 stack
rng=random.Random(7000+2)
gams=rng.sample(range(2,p),2)
b1=rng.sample(range(0,6),4); b2=rng.sample(range(6,12),4)
rows=[]
for jj,gg in enumerate(gams):
    for i in b1[2*jj:2*jj+2]: rows.append(pencil_row(0,6,D[i],gg))
    for i in b2[2*jj:2*jj+2]: rows.append(pencil_row(3,9,D[i],gg))
sol=solve_linear(rows,18,rng)
q1,q2,r1,r2,q3,r3=sol[0:3],sol[3:6],sol[6:9],sol[9:12],sol[12:15],sol[15:18]
u1=[0]*n; u0=[0]*n
for i in range(6): u1[i]=peval(q1,D[i]); u0[i]=peval(r1,D[i])
for i in range(6,12): u1[i]=peval(q2,D[i]); u0[i]=peval(r2,D[i])
for i in (12,13,14): u1[i]=peval(q3,D[i]); u0[i]=peval(r3,D[i])
ga,gb=rng.randrange(1,p),rng.randrange(1,p); x=D[15]
rh1=(peval(r1,x)+ga*peval(q1,x))%p; rh2=(peval(r2,x)+gb*peval(q2,x))%p
u1[15]=(rh1-rh2)*pow((ga-gb)%p,p-2,p)%p; u0[15]=(rh1-ga*u1[15])%p
bad=census_full(u0,u1)
# assign each bad gamma a class via its witness agreement structure: the
# quadratic R1 agrees with on the witness's largest low-deg-agreement part
qsizes=interp_quad_agreement(u1)
big_quads=Counter(v for v in qsizes.values() if v>=4)
print(f"record-22: #bad={len(bad)}; R1 quadratic agreement-size dist "
      f"(>=4 only): {sorted(big_quads.items(), reverse=True)}; "
      f"#quadratics with a_q>=6: {sum(1 for v in qsizes.values() if v>=6)}, "
      f"a_q=5: {sum(1 for v in qsizes.values() if v==5)}, "
      f"a_q=4: {sum(1 for v in qsizes.values() if v==4)}")
print("(small-class concern = many a_q in 3-5 each carrying >=2 attached "
      "bad scalars; check vs #bad)")
