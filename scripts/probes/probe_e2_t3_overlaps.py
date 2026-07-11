#!/usr/bin/env python3
"""
PROBE 6: confirm the three pairwise overlaps F1nF2, F1nF3, F2nF3 are each <= n (size of S),
so inclusion-exclusion gives |F1uF2uF3| >= 3n^2 - 3n for negation-closed S.
F1 = {(a,b,a,b)}, F2 = {(a,b,b,a)}, F3 = {(a,-a,c,-c)}.
"""
import sympy

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def fams(S, p):
    F1 = set((a,b,a,b) for a in S for b in S)
    F2 = set((a,b,b,a) for a in S for b in S)
    F3 = set((a,(p-a)%p,c,(p-c)%p) for a in S for c in S)
    return F1,F2,F3

print(f"{'p':>6} {'n':>4} {'|F1|':>5} {'|F2|':>5} {'|F3|':>5} {'F1nF2':>6} {'F1nF3':>6} {'F2nF3':>6} {'|U|':>7} {'3n^2-3n':>8} {'U>=fl':>6}")
for p,nlist in [(769,[4,8,16,32]),(7681,[8,16,32]),(40961,[16,32,64]),(12289,[16,32,64,128])]:
    for n in nlist:
        if (p-1)%n: continue
        S = subgroup(p,n)
        F1,F2,F3 = fams(S,p)
        U = F1|F2|F3
        i12=len(F1&F2); i13=len(F1&F3); i23=len(F2&F3)
        fl=3*n*n-3*n
        print(f"{p:>6} {n:>4} {len(F1):>5} {len(F2):>5} {len(F3):>5} {i12:>6} {i13:>6} {i23:>6} {len(U):>7} {fl:>8} {str(len(U)>=fl):>6}")
print()
print("If all pairwise overlaps <= n and |U| >= 3n^2-3n: inclusion-exclusion lower bound confirmed.")
print("(Note F3 may have |F3|<n^2 if a=-a possible, but for odd p a!=-a always, so |F3|=n^2.)")
