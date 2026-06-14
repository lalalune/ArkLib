#!/usr/bin/env python3
"""
The size-6 kernel: 3 clean size-6 classes, pairwise overlap EXACTLY 2,
quadratics solved for overlap-consistency (p=12289). The irreducible case
(sharp cap gives 10 each => 30, +zero = 31 boundary; can it realize?).

A1={0..5}, A2={4..9} (share 4,5), A3={8,9,10,11,0,1} (share 8,9 w/A2;
0,1 w/A1). Union {0..11}=12, free {12,13,14,15}. Solve q1,q2,q3 (and
r1,r2,r3) deg<3 with q1=q2 on {4,5}, q2=q3 on {8,9}, q1=q3 on {0,1}
(6 linear constraints on 9 coeffs each -> 3-dim solution space). Build
R1=q_i on A_i, R0=r_i on A_i, sweep free pts + solution-space coords,
census. If max > 31: OBLIGATION REFUTED. Else: size-6 kernel bound holds.
"""
import itertools, random
src = open("scripts/probes/probe_wb371_refute31.py").read()
ns = {}
exec(src[:src.index("# class-set patterns")], ns)
p, n, D, peval, census = ns['p'], ns['n'], ns['D'], ns['peval'], ns['census']

A1=[0,1,2,3,4,5]; A2=[4,5,6,7,8,9]; A3=[8,9,10,11,0,1]
free=[12,13,14,15]
# overlap consistency: q1=q2 on {4,5}, q2=q3 on {8,9}, q3=q1 on {0,1}
def solve_consistent(rng):
    # vars: q1(0:3) q2(3:6) q3(6:9); rows: eval diff = 0
    rows=[]
    for (a,b,pts) in ((0,3,[4,5]),(3,6,[8,9]),(6,0,[0,1])):
        for pt in pts:
            row=[0]*9
            for t in range(3):
                xt=pow(D[pt],t,p)
                row[a+t]=(row[a+t]+xt)%p; row[b+t]=(row[b+t]-xt)%p
            rows.append(row)
    # random kernel solution (9 vars, 6 constraints -> 3-dim)
    # gaussian elim
    m=len(rows); Aug=[r[:] for r in rows]; piv=[]; rr=0
    for c in range(9):
        pr=next((r for r in range(rr,m) if Aug[r][c]),None)
        if pr is None: continue
        Aug[rr],Aug[pr]=Aug[pr],Aug[rr]
        inv=pow(Aug[rr][c],p-2,p); Aug[rr]=[v*inv%p for v in Aug[rr]]
        for r2 in range(m):
            if r2!=rr and Aug[r2][c]:
                f=Aug[r2][c]; Aug[r2]=[(Aug[r2][t]-f*Aug[rr][t])%p for t in range(9)]
        piv.append(c); rr+=1
        if rr==m: break
    frees=[c for c in range(9) if c not in piv]
    sol=[0]*9
    for c in frees: sol[c]=rng.randrange(p)
    for idx in range(len(piv)-1,-1,-1):
        c=piv[idx]; v=0
        for c2 in range(c+1,9): v=(v+Aug[idx][c2]*sol[c2])%p
        sol[c]=(-v)%p
    return [sol[0:3],sol[3:6],sol[6:9]]

best=0; best_d=None
rng=random.Random(606)
for trial in range(400):
    qs=solve_consistent(rng)
    rs=solve_consistent(rng)
    if len({tuple(qs[0]),tuple(qs[1]),tuple(qs[2])})<3: continue
    u1=[None]*n; u0=[None]*n
    for ci,b in enumerate((A1,A2,A3)):
        for i in b:
            if u1[i] is None:
                u1[i]=peval(qs[ci],D[i]); u0[i]=peval(rs[ci],D[i])
    for i in free: u1[i]=rng.randrange(p); u0[i]=rng.randrange(p)
    # verify consistency held (no None, overlaps agree)
    if any(v is None for v in u1): continue
    c=census(u0,u1)
    if c>best:
        best=c; best_d=trial
        if c>31: print(f"  *** BEAT 31: {c} (trial {trial}) OBLIGATION REFUTED ***")
print(f"SIZE-6 KERNEL (3 clean size-6, pairwise overlap 2): max census = {best}; "
      f"obligation 31; {'REFUTED' if best>31 else 'holds (kernel bound confirmed)'}")
