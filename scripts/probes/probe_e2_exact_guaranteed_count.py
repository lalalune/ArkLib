#!/usr/bin/env python3
"""
PROBE 7: confirm the EXACT count card(T1uT2uT3)=3n^2-3n via inclusion-exclusion structure:
 - |F1|=|F2|=|F3|=n^2
 - each pairwise overlap EXACTLY n
 - TRIPLE intersection F1nF2nF3 = empty (under odd char / no 2-torsion)
Then 3n^2 - 3n + 0 = 3n^2-3n exactly. Also identify each pairwise overlap set explicitly so
the Lean lemma can give an exact bijection (overlap = a constant/antipodal-diagonal family of size n).
F1={(a,b,a,b)}, F2={(a,b,b,a)}, F3={(a,-a,c,-c)}.
"""
import sympy

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

for p,nlist in [(769,[4,8,16]),(7681,[8,16,32]),(40961,[16,32,64])]:
    for n in nlist:
        if (p-1)%n: continue
        S = subgroup(p,n)
        neg = lambda x: (p-x)%p
        F1 = set((a,b,a,b) for a in S for b in S)
        F2 = set((a,b,b,a) for a in S for b in S)
        F3 = set((a,neg(a),c,neg(c)) for a in S for c in S)
        i12 = F1&F2; i13 = F1&F3; i23 = F2&F3
        triple = F1&F2&F3
        U = F1|F2|F3
        # describe i12 (should be (a,a,a,a)), i13 (should be (a,-a,a,-a)), i23 (a,-a,-a,a)
        ok12 = all(q[0]==q[1] for q in i12)
        ok13 = all(q[1]==neg(q[0]) and q[2]==q[0] for q in i13)
        ok23 = all(q[1]==neg(q[0]) and q[2]==q[1] for q in i23)
        print(f"p={p} n={n}: |U|={len(U)} 3n^2-3n={3*n*n-3*n} eq={len(U)==3*n*n-3*n} "
              f"|i12|={len(i12)} |i13|={len(i13)} |i23|={len(i23)} |triple|={len(triple)} "
              f"i12diag={ok12} i13={ok13} i23={ok23}")
print()
print("Expect: |triple|=0, each |iXY|=n, eq=True, and the overlap-shape flags True.")
