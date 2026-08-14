# THE n/w-LAW STRESS TEST at (37,12,2,4): j=1, h-freedom dim 2 = consistency cost w-2.
# VERDICT (37,12,2,4), j=1, h-dim 2 = consistency cost: tuned involution-union
# stacks max at bad = 1 (not C(6,2)=15, not even n/w=3): the shared-h consistency
# PRUNES 3-dim net fibers to pencils. The n/w-law survives its sharpest test.
# Fiber dichotomy: double-class fibers = D-split members of span<Z_T0, l0, l1>;
# pencils cap at n/w (five-line disjointness); nets are pruned by h-consistency.
# Pre-registered fork: (a) multi-pair unions fire -> ~C(6,2)=15 bad >> n/w=3: LAW FALSE;
# (b) consistency persists -> bad ~ 3: law survives sharpest test.
import random
from itertools import combinations
exec(open('scripts/probes/probe_aboveudr_cost_law.py').read().split("def run(")[0])
random.seed(44)
q,n,k,w = 37,12,2,4
j = 3*w+k-1-n
print("j =", j, "(expect 1); UDR ok:", 2*w+k+1 <= n)
g = find_gen(q,n); dom=[pow(g,i,q) for i in range(n)]
domset=set(dom)
# involution quadratic products: c=1: pairs {x, 1/x}
c=1
used=set()
def next_root(avoid):
    for x in range(2,q):
        cx = pow(x,q-2,q)
        if x in domset or cx in domset or cx==x or x in avoid or cx in avoid: continue
        return x,cx
quads=[]
for _ in range(4):
    r=next_root(used); used|=set(r); quads.append(r)
def quadprod(qs):
    co=[1]
    for (a,b) in qs:
        co2=[a*b%q,(-(a+b))%q,1]
        res=[0]*(len(co)+2)
        for i,ai in enumerate(co):
            for jj,bj in enumerate(co2): res[i+jj]=(res[i+jj]+ai*bj)%q
        co=res
    return co
l0=quadprod(quads[:2]); l1=quadprod(quads[2:4])
m01=pmul(l0,l1,q)
Xn1=[(-1)%q]+[0]*(n-1)+[1]
# involution pairs in dom: {x, 1/x}
pairs=[]; seen=set()
for x in dom:
    b=pow(x,q-2,q)
    if x in seen or b in seen or b==x: continue
    seen|=set((x,b)); pairs.append((x,b))
print("invol pairs:", len(pairs))
# target: ONE union-of-2-pairs T0; tune (R0,R1) for alignment with h free (deg<=1):
# conditions: rep((l1*R0+gamma*l0*R1)*ZS^{-1}) deg <= j=1: 2w-(j+1) = 6 conditions
# minus gamma -> on (R0,R1): 6 rows; genuine budget 2w = 8: kernel-genuine dim >= 2.
T0 = pairs[0]+pairs[1]
ZT=[1]
for x in T0: ZT=pmul(ZT,[(-x)%q,1],q)
ZSinv=pinv(pmod(pmul(Xn1,pinv(ZT,m01,q),q),m01,q),m01,q)
gam0 = 5
A_rows=[]
for cidx in range(j+1,2*w):
    row=[]
    for which,lpoly,scale in ((0,l1,1),(1,l0,gam0)):
        for d in range(w+k):
            base=pmod(pmul(pmul([0]*d+[1],lpoly,q),ZSinv,q),m01,q)
            row.append(base[cidx]*scale%q)
    A_rows.append(row)
def nullspace(A,nvar):
    M=[r[:] for r in A]; mm=len(M); r=0; piv=[]
    for cc in range(nvar):
        p=next((i for i in range(r,mm) if M[i][cc]%q),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        inv=pow(M[r][cc],q-2,q); M[r]=[(v*inv)%q for v in M[r]]
        for i in range(mm):
            if i!=r and M[i][cc]%q:
                f=M[i][cc]; M[i]=[(a-f*b)%q for a,b in zip(M[i],M[r])]
        piv.append(cc); r+=1
    free=[cc for cc in range(nvar) if cc not in piv]
    basis=[]
    for fc in free:
        v=[0]*nvar; v[fc]=1
        for ri,pc in enumerate(piv): v[pc]=(-M[ri][fc])%q
        basis.append(v)
    return basis
basis=nullspace(A_rows,2*(w+k))
print("kernel dim:", len(basis), " degenerate dim 2k =", 2*k)
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
best=0; bestinfo=None
for _ in range(400):
    co=[random.randrange(q) for _ in basis]
    v=[0]*(2*(w+k))
    for ci,b in zip(co,basis):
        if ci:
            for i2 in range(len(v)): v[i2]=(v[i2]+ci*b[i2])%q
    R0,R1=v[:w+k],v[w+k:]
    if not any(R0) or not any(R1): continue
    _,r0m=pdivmod2(R0,l0); _,r1m=pdivmod2(R1,l1)
    if not any(x%q for x in r0m) or not any(x%q for x in r1m): continue
    u0=tuple(evalp(R0,x,q)*pow(evalp(l0,x,q),q-2,q)%q for x in dom)
    u1=tuple(evalp(R1,x,q)*pow(evalp(l1,x,q),q-2,q)%q for x in dom)
    pw=[[pow(x,jj,q) for jj in range(k)] for x in dom]
    def cons(S,vals):
        rows=[pw[i][:]+[vals[i]%q] for i in S]
        m_,r=len(rows),0
        for cc in range(k):
            p=next((i for i in range(r,m_) if rows[i][cc]%q),None)
            if p is None: continue
            rows[r],rows[p]=rows[p],rows[r]
            inv=pow(rows[r][cc],q-2,q); rows[r]=[(vv*inv)%q for vv in rows[r]]
            for i in range(m_):
                if i!=r and rows[i][cc]%q:
                    f=rows[i][cc]; rows[i]=[(a-f*b)%q for a,b in zip(rows[i],rows[r])]
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
    if len(bad)>best: best=len(bad); bestinfo=bad
print("BEST bad over tuned involution stacks =", best, " vs n/w =", n//w,
      " vs C(6,2) =", 15, " gammas:", bestinfo)
