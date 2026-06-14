# Coset family at j=1 with the PROPORTIONALITY fix: rep1 || rep0.
# RESULT (37,12,5,3) j=1: bad = 4 = n/w EXACTLY (gammas [7,17,34,35]); the j=1 coset
# family fires once the two tuned residues are made PROPORTIONAL (the shared h links
# the two CRT sides: one extra linear condition). Theta(n/w) extends to j=1; the
# packing cap (n/(w-1))^2 is loose there.
import random
from itertools import combinations
exec(open('scripts/probes/probe_aboveudr_cost_law.py').read().split("def run(")[0])
random.seed(11)
q,n,k,w = 37,12,5,3
g = find_gen(q,n); dom=[pow(g,i,q) for i in range(n)]
munw = {pow(x,w,q) for x in dom}
es=[e for e in range(2,q) if e not in munw][:2]; e0,e1=es
l0=[(-e0)%q,0,0,1]; l1=[(-e1)%q,0,0,1]
def pdivmod2(num,den):
    num=num[:]; out=[0]*max(1,len(num)-len(den)+1)
    inv=pow(den[-1],q-2,q)
    while True:
        while num and num[-1]%q==0: num.pop()
        if len(num)<len(den): break
        f=num[-1]*inv%q; off=len(num)-len(den); out[off]=f
        for i2 in range(len(den)): num[off+i2]=(num[off+i2]-f*den[i2])%q
        num.pop()
    return out,(num or [0])
# R0: tune coeff X^2 of (l1*R0 mod l0) to 0 -> rep0 deg <= 1, nonzero
def coeff_rows(lme, lother, cidx):
    return [pmod(pmul([0]*d+[1],lother,q),lme,q)[cidx] for d in range(w+k)]
rows0 = coeff_rows(l0,l1,2)
# kernel vector for R0
piv = next(d for d in range(w+k) if rows0[d]%q)
d2 = next(d for d in range(w+k) if d != piv)
R0=[0]*(w+k); R0[d2]=1; R0[piv]=(-rows0[d2])*pow(rows0[piv],q-2,q)%q
rep0 = pmod(pmul(l1,R0,q),l0,q)  # deg <= 1
assert rep0[2]%q==0 and any(rep0)
# R1: conditions: coeff X^2 of (l0*R1 mod l1) = 0 AND rep1 || rep0:
# rep1[0]*rep0[1] - rep1[1]*rep0[0] = 0  (both linear in R1)
rows1a = coeff_rows(l1,l0,2)
r1c0 = coeff_rows(l1,l0,0); r1c1 = coeff_rows(l1,l0,1)
rows1b = [(r1c0[d]*rep0[1]-r1c1[d]*rep0[0])%q for d in range(w+k)]
# solve 2 homogeneous conditions on R1 (8 unknowns): find kernel vector, genuine
A=[rows1a,rows1b]
basis=[]
# simple: random kernel sampling via solving pinned systems
found=None
for _ in range(4000):
    R1=[random.randrange(q) for _ in range(w+k)]
    # project out: adjust two coordinates to satisfy both conditions (solve 2x2)
    # pick two pivot coords
    import itertools
    ok=False
    for (a,b) in itertools.combinations(range(w+k),2):
        det=(rows1a[a]*rows1b[b]-rows1a[b]*rows1b[a])%q
        if det:
            s1=sum(rows1a[d]*R1[d] for d in range(w+k) if d not in (a,b))%q
            s2=sum(rows1b[d]*R1[d] for d in range(w+k) if d not in (a,b))%q
            inv=pow(det,q-2,q)
            R1[a]=(-(s1*rows1b[b]-s2*rows1a[b])*inv)%q
            R1[b]=(-(rows1a[a]*s2-rows1b[a]*s1)*inv)%q
            ok=True; break
    if not ok: continue
    assert sum(rows1a[d]*R1[d] for d in range(w+k))%q==0
    assert sum(rows1b[d]*R1[d] for d in range(w+k))%q==0
    _,r1m=pdivmod2(R1,l1)
    if any(v%q for v in r1m) and any(R1):
        found=R1; break
R1=found
print("R0,R1 tuned:", R0 is not None, R1 is not None)
u0=tuple(evalp(R0,x,q)*pow(evalp(l0,x,q),q-2,q)%q for x in dom)
u1=tuple(evalp(R1,x,q)*pow(evalp(l1,x,q),q-2,q)%q for x in dom)
# exact bad count
pw=[[pow(x,j,q) for j in range(k)] for x in dom]
def cons(S,vals):
    rows=[pw[i][:]+[vals[i]%q] for i in S]
    m_,r=len(rows),0
    for c in range(k):
        p=next((i for i in range(r,m_) if rows[i][c]%q),None)
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]
        inv=pow(rows[r][c],q-2,q); rows[r]=[(v*inv)%q for v in rows[r]]
        for i in range(m_):
            if i!=r and rows[i][c]%q:
                f=rows[i][c]; rows[i]=[(a-f*b)%q for a,b in zip(rows[i],rows[r])]
        r+=1
    return not any(rows[i][k]%q for i in range(r,m_))
subs=list(combinations(range(n),n-w))
bad=[]
for gam in range(q):
    line=[(u0[i]+gam*u1[i])%q for i in range(n)]
    for S in subs:
        S=list(S)
        if not cons(S,line): continue
        if cons(S,list(u0)) and cons(S,list(u1)): continue
        bad.append(gam); break
print("j=1 PROPORTIONAL coset: bad =", len(bad), " predicted m = n/w =", n//w, " gammas:", bad)
