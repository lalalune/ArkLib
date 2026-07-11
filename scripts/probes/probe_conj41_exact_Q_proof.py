#!/usr/bin/env python3
"""
RIGOROUS exact-Q construction upgrading the Conj 41 (w+1)-clique candidate to a proof.
For the fixed RATIONAL clique S={0,1,...,w} (distinct points), construct a syndrome line (s1,s2) in Q^D
and w+1 decodings EXACTLY over Q, and verify ALL defining equations as exact rational identities:
  for each support E_i = S\{a_i}: gamma_i in Q, error v_i in Q^w with V_{E_i} v_i = s1 + gamma_i s2,
  all v_i entries != 0, and the gamma_i pairwise distinct.
If all hold over Q, the same construction reduces mod every prime p not dividing the (finitely many)
denominators => M_true(s1,s2) >= w+1 > floor((2D-1)/c) at all large p => Conj 41's WORST-CASE form is
false (one exact-Q counterexample suffices). Uses exact Fraction arithmetic (no floating point, no mod-p).
"""
from fractions import Fraction as F
import itertools, functools
print=functools.partial(print,flush=True)

def vander(E, L, D):   # D x w over Q
    return [[F(L[e])**j for e in E] for j in range(D)]
def lam_coeffs(E, L):  # coeffs (low->high) of prod_{e in E}(x - L[e])
    c=[F(1)]
    for e in E:
        nc=[F(0)]*(len(c)+1)
        for i,a in enumerate(c):
            nc[i]-=F(L[e])*a; nc[i+1]+=a
        c=nc
    return c
def normals(E, L, D, c):   # c x D : coeffs of Lambda_E * x^r, r=0..c-1, padded to length D
    lam=lam_coeffs(E,L); rows=[]
    for r in range(c):
        row=[F(0)]*D
        for i,a in enumerate(lam):
            if i+r<D: row[i+r]=a
        rows.append(row)
    return rows
def rref(M):   # exact RREF over Q; returns (matrix, pivot cols)
    M=[row[:] for row in M]; R=len(M); C=len(M[0]); piv=[]; r=0
    for col in range(C):
        pr=next((i for i in range(r,R) if M[i][col]!=0),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; d=M[r][col]; M[r]=[x/d for x in M[r]]
        for i in range(R):
            if i!=r and M[i][col]!=0:
                f=M[i][col]; M[i]=[M[i][j]-f*M[r][j] for j in range(C)]
        piv.append(col); r+=1
        if r==R: break
    return M, piv
def null_space(M):   # basis of right null space over Q
    R=len(M); C=len(M[0]); Mr,piv=rref(M); free=[c for c in range(C) if c not in piv]; B=[]
    for fc in free:
        v=[F(0)]*C; v[fc]=F(1)
        for ri,pc in enumerate(piv): v[pc]=-Mr[ri][fc]
        B.append(v)
    return B
def solve_overdet(V, s):   # solve V v = s exactly over Q (V is D x w, expect unique); None if inconsistent
    D=len(V); w=len(V[0]); A=[V[i][:]+[s[i]] for i in range(D)]; Mr,piv=rref(A)
    if (w) in piv: return None       # rhs column is pivot => inconsistent
    # read solution
    v=[F(0)]*w
    # find each pivot row
    for ri,pc in enumerate(piv):
        if pc<w: v[pc]=Mr[ri][w]
    # verify
    for i in range(D):
        if sum(V[i][j]*v[j] for j in range(w))!=s[i]: return None
    return v

def build_A(Es, gammas, L, D, c):
    A=[]
    for E,g in zip(Es,gammas):
        for row in normals(E,L,D,c): A.append(row[:] + [g*x for x in row])   # [N | g N], width 2D
    return A

def prove(n,k,c):
    D=n-k; w=D-c; L=list(range(n)); S=list(range(w+1)); Es=[tuple(sorted(set(S)-{a})) for a in S]; m=len(Es)
    bound=(2*D-1)//c
    # choose rational distinct gammas; search a few simple choices for one giving a nonzero Q-kernel
    for gs in [ [F(i+1) for i in range(m)], [F(i+2) for i in range(m)], [F(2*i+1) for i in range(m)],
                [F(i+1,1) for i in range(m)], [F(3*i+1) for i in range(m)] ]:
        if len(set(gs))<m: continue
        A=build_A(Es,gs,L,D,c)
        ker=null_space(A)
        for kv in ker:
            s1=kv[:D]; s2=kv[D:]
            if all(x==0 for x in s1) and all(x==0 for x in s2): continue
            # verify each support decodes to nonzero error at its OWN isolated gamma (recompute, not gs)
            recs=[]; ok=True; gset=set()
            for E in Es:
                N=normals(E,L,D,c); a=[sum(N[i][j]*s1[j] for j in range(D)) for i in range(c)]
                b=[sum(N[i][j]*s2[j] for j in range(D)) for i in range(c)]
                ge=None; good=True
                for i in range(c):
                    if b[i]==0:
                        if a[i]!=0: good=False; break
                    else:
                        gi=-a[i]/b[i]
                        if ge is None: ge=gi
                        elif ge!=gi: good=False; break
                if not good or ge is None: ok=False; break
                s=[s1[j]+ge*s2[j] for j in range(D)]; v=solve_overdet(vander(E,L,D),s)
                if v is None or any(x==0 for x in v): ok=False; break
                recs.append((E,ge,v)); gset.add(ge)
            if ok and len(gset)==m:
                return dict(ok=True, m=m, distinct=len(gset), bound=bound, D=D, w=w, gammas=[str(r[1]) for r in recs],
                            denoms_ok=True)
    return dict(ok=False, bound=bound, D=D, w=w, m=m)

print("=== EXACT-Q proof: (w+1)-clique on S={0..w} gives M_true=w+1 > bound over Q (=> all large p) ===")
for (n,k,c) in [(20,10,5),(24,12,5),(18,9,3),(28,14,6)]:
    r=prove(n,k,c)
    if r['ok']:
        print(f"  n={n} k={k} c={c} w={r['w']} D={r['D']}: PROVED over Q — {r['distinct']} distinct-gamma genuine "
              f"decodings (= w+1 = {r['m']}) > bound {r['bound']}.  gammas={r['gammas']}")
    else:
        print(f"  n={n} k={k} c={c}: no simple-gamma Q-kernel found in tried set (bound {r['bound']}, m={r['m']}) — needs other gammas")
