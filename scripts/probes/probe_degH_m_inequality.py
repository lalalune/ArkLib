#!/usr/bin/env python3
"""Pin the exact statement of the swarm's char-p-crux inequality  deg H + m >= k-1.
Setup (from unlock-workflow-synthesis): S a 2k-subset of mu_{4k}; sigma_S(z)=prod_{s in S}(z-s)
= G(z^2)+z H(z^2); m = #antipodal pairs {s,-s} subset S = deg gcd(G,H). Check deg H + m vs k-1
over ALL S (exact, via roots of unity as exp). Also stratify by the odd-power-sum vanishing
(e_1=e_3=...=0) to see the interaction. Goal: confirm/refute the inequality and its exact hypotheses."""
import itertools, cmath, math

def sigma_coeffs(S, roots):
    # poly prod (z - roots[s]) for s in S, return complex coeff list low->high, deg=|S|
    poly=[1.0+0j]
    for s in S:
        r=roots[s]
        new=[0j]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]+= c*(-r)   # (z - r): multiply
            new[i+1]+= c
        poly=new
    return poly

def split_even_odd(poly):
    # poly in z (low->high). G = even-index coeffs (as poly in w), H = odd-index coeffs (as poly in w)
    G=[poly[i] for i in range(0,len(poly),2)]   # z^{2j} -> w^j
    H=[poly[i] for i in range(1,len(poly),2)]   # z^{2j+1} -> w^j
    return G,H

def deg(p, tol=1e-7):
    d=-1
    for i,c in enumerate(p):
        if abs(c)>tol: d=i
    return d

def analyze(k):
    n=4*k
    roots=[cmath.exp(2j*math.pi*t/n) for t in range(n)]   # mu_{4k}
    half=n//2
    viol=0; tot=0; minmargin=999
    # also count: antipodal-free with vanishing e_1
    examples=[]
    for S in itertools.combinations(range(n), 2*k):
        Sset=set(S)
        m=sum(1 for s in S if s<half and (s+half) in Sset)   # antipodal pairs (s, s+2k)
        poly=sigma_coeffs(S, roots)
        G,H=split_even_odd(poly)
        dH=deg(H)
        tot+=1
        lhs=dH+m
        margin=lhs-(k-1)
        if margin<minmargin: minmargin=margin
        if lhs < k-1:
            viol+=1
            if len(examples)<5:
                # e_1 = sum of roots
                e1=sum(roots[s] for s in S)
                examples.append((sorted(S), m, dH, abs(e1)))
    print(f" k={k} (mu_{n}, |S|={2*k}): #subsets={tot}, violations(degH+m<k-1)={viol}, min(degH+m-(k-1))={minmargin}",flush=True)
    for ex in examples:
        print(f"     VIOLATION S={ex[0]} m={ex[1]} degH={ex[2]} |e1|={ex[3]:.3f}",flush=True)

for k in (2,3,4):
    analyze(k)
