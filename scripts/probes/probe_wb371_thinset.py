#!/usr/bin/env python3
"""
Decisive test of the size-6 kernel's exceptional set (p=12289).

The gluing forces <=2 size-6 classes in 98.9% of configs (independent
overlap-monics). The 1.1% with DEPENDENT overlap-monics allow 3 distinct
size-6 quadratics. This probe: find such dependent configs, build R1 = 3
distinct quadratics on them (consistent on overlaps), steer R0 (via the
candidate-map / pencil to plant attached scalars per class), census, and
sweep hard. If any realizes > 31: OBLIGATION REFUTED. If capped ~22:
the attachment gate finishes the bound even on the exceptional set.
"""
import itertools, random
src = open("scripts/probes/probe_wb371_refute31.py").read()
ns = {}
exec(src[:src.index("# class-set patterns")], ns)
p, n, D, peval, census = ns['p'], ns['n'], ns['D'], ns['peval'], ns['census']

def monic2(pp):
    a,b=D[pp[0]],D[pp[1]]; return [(a*b)%p,(-(a+b))%p,1]
def det3(v1,v2,v3):
    M=[v1,v2,v3]
    return ((M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
            -M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            +M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))%p)

# find dependent configs
rng=random.Random(7)
configs=[]
for _ in range(400000):
    pts=list(range(n)); rng.shuffle(pts)
    O12=tuple(sorted(pts[0:2])); O23=tuple(sorted(pts[2:4])); O31=tuple(sorted(pts[4:6]))
    if len(set(O12)|set(O23)|set(O31))!=6: continue
    rest=pts[6:]; u1,u2,u3=rest[0:2],rest[2:4],rest[4:6]
    A1=set(O12)|set(O31)|set(u1); A2=set(O12)|set(O23)|set(u2); A3=set(O23)|set(O31)|set(u3)
    if not(len(A1)==6 and len(A2)==6 and len(A3)==6): continue
    if len(A1&A2)!=2 or len(A2&A3)!=2 or len(A1&A3)!=2: continue
    if det3(monic2(O12),monic2(O23),monic2(O31))==0:
        configs.append((sorted(A1),sorted(A2),sorted(A3),O12,O23,O31))
        if len(configs)>=12: break

print(f"found {len(configs)} dependent (3-size-6-feasible) configs")

def solve_q(A1,A2,A3,O12,O23,O31,rng):
    # q1=q2 on O12, q2=q3 on O23, q3=q1 on O31; 9 vars, 6 constraints
    rows=[]
    for (a,b,O) in ((0,3,O12),(3,6,O23),(6,0,O31)):
        for pt in O:
            row=[0]*9
            for t in range(3):
                xt=pow(D[pt],t,p); row[a+t]=(row[a+t]+xt)%p; row[b+t]=(row[b+t]-xt)%p
            rows.append(row)
    m=len(rows); Aug=[r[:] for r in rows]; piv=[]; rr=0
    for c in range(9):
        pr=next((r for r in range(rr,m) if Aug[r][c]),None)
        if pr is None: continue
        Aug[rr],Aug[pr]=Aug[pr],Aug[rr]; inv=pow(Aug[rr][c],p-2,p); Aug[rr]=[v*inv%p for v in Aug[rr]]
        for r2 in range(m):
            if r2!=rr and Aug[r2][c]:
                f=Aug[r2][c]; Aug[r2]=[(Aug[r2][t]-f*Aug[rr][t])%p for t in range(9)]
        piv.append(c); rr+=1
    frees=[c for c in range(9) if c not in piv]; sol=[0]*9
    for c in frees: sol[c]=rng.randrange(p)
    for idx in range(len(piv)-1,-1,-1):
        c=piv[idx]; v=0
        for c2 in range(c+1,9): v=(v+Aug[idx][c2]*sol[c2])%p
        sol[c]=(-v)%p
    return [sol[0:3],sol[3:6],sol[6:9]]

best=0
for (A1,A2,A3,O12,O23,O31) in configs:
    covered=sorted(set(A1)|set(A2)|set(A3)); free=[i for i in range(n) if i not in covered]
    rng2=random.Random(hash(O12)%9999)
    for trial in range(150):
        qs=solve_q(A1,A2,A3,O12,O23,O31,rng2)
        if len({tuple(qs[0]),tuple(qs[1]),tuple(qs[2])})<3: continue
        rs=solve_q(A1,A2,A3,O12,O23,O31,rng2)
        u1=[None]*n; u0=[None]*n
        for ci,b in enumerate((A1,A2,A3)):
            for i in b:
                if u1[i] is None: u1[i]=peval(qs[ci],D[i]); u0[i]=peval(rs[ci],D[i])
        # steer free pts to plant scalars (pencil between class pairs)
        for i in free:
            ga,gb=rng2.randrange(1,p),rng2.randrange(1,p)
            if ga==gb: gb=(gb+1)%p or 1
            c1,c2=rng2.randrange(3),rng2.randrange(3)
            x=D[i]; rh1=(peval(rs[c1],x)+ga*peval(qs[c1],x))%p; rh2=(peval(rs[c2],x)+gb*peval(qs[c2],x))%p
            det=(ga-gb)%p
            if det==0: u1[i]=rng2.randrange(p); u0[i]=rng2.randrange(p); continue
            R1x=(rh1-rh2)*pow(det,p-2,p)%p; u1[i]=R1x; u0[i]=(rh1-ga*R1x)%p
        if any(v is None for v in u1): continue
        c=census(u0,u1)
        if c>best:
            best=c
            if c>31: print(f"  *** BEAT 31: {c} OBLIGATION REFUTED ***")
print(f"THIN-SET RESULT: max census over dependent 3-size-6 configs = {best}; "
      f"obligation 31; {'REFUTED' if best>31 else 'holds even on exceptional set'}")
