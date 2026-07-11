#!/usr/bin/env python3
"""
PROBE 8: does a multiplicative GenuineQuadruple (1+B=C+D, {1,B}!={C,D}, B,C,D in S) always give
an ADDITIVE energy quad (1,B,C,D) OUTSIDE the guaranteed families T1/T2/T3?
T1 = {(a,b,a,b)}: (1,B,C,D) in T1 <=> C=1 and D=B.
T2 = {(a,b,b,a)}: (1,B,C,D) in T2 <=> C=B and D=1.
T3 = {(a,-a,c,-c)}: (1,B,C,D) in T3 <=> B=-1 and D=-C.
We need: {1,B}!={C,D} EXCLUDES T1 and T2 (since those are exactly {1,B}={C,D} as multisets).
BUT T3 membership (B=-1, D=-C) is a SEPARATE condition NOT excluded by {1,B}!={C,D}.
So the bridge GenuineQuadruple -> genuineQuads.Nonempty needs an EXTRA exclusion: the witness
must avoid the antipodal shape too. Test whether deep-regime genuine quads can be FORCED off T3,
i.e. whether there's ALWAYS a non-antipodal genuine quad when E_2 excess>0.
"""
import sympy

def subgroup(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S, x = set(), 1
    for _ in range(n):
        S.add(x); x = (x*h) % p
    return sorted(S)

def analyze(p, n):
    S = subgroup(p, n); Sset=set(S); neg=lambda x:(p-x)%p
    # all additive energy quads
    guaranteed = set()
    for a in S:
        for b in S:
            guaranteed.add((a,b,a,b)); guaranteed.add((a,b,b,a)); guaranteed.add((a,neg(a),b,neg(b)))
    genuine = []
    for a in S:
        for b in S:
            for c in S:
                d = (a+b-c)%p
                if d in Sset and (a,b,c,d) not in guaranteed:
                    genuine.append((a,b,c,d))
    # how many genuine quads have the distinguished '1' form normalizable? just report counts.
    return len(genuine)

for p,nlist in [(40961,[32,64,256,512]),(12289,[128,256])]:
    for n in nlist:
        if (p-1)%n: continue
        g = analyze(p,n)
        print(f"p={p} n={n}: #genuineQuads(ordered, outside T1uT2uT3) = {g}  (=E2-(3n^2-3n))")
print()
print("If >0 in deep regime: confirms genuineQuads nonempty there (char-dependent existence = open core).")
