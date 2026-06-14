import itertools, cmath
# n = 12 (p=3, q=2... use q=2,p=3): test: S subset of mu_12, full window [1,t];
# decompose into prime packets (all decompositions); check spectrum R (q=2-packets' squares)
# window: Sum_R r^e = 0 for q*e <= t?
n = 12; 
import math
roots=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
def packets():
    p2=[frozenset([k,(k+6)%12]) for k in range(6)]            # mu_2 packets (antipodal)
    p3=[frozenset([k,(k+4)%12,(k+8)%12]) for k in range(4)]    # mu_3 packets
    return p2,p3
P2,P3=packets()
def all_decomps(s, acc, out):
    if not s: out.append(acc); return
    k=min(s)
    for P in P2+P3:
        if k in P and P<=s:
            all_decomps(s-P, acc+[P], out)
def win(S,t):
    return all(abs(sum(roots[k]**j for k in S))<1e-9 for j in range(1,t+1))
viol=0; tested=0
for r in range(2,13):
    for E in itertools.combinations(range(12),r):
        Es=frozenset(E)
        for t in (4,5,6):
            if not win(Es,t): continue
            outs=[]; all_decomps(Es,[],outs)
            for D in outs[:20]:
                # R = squares of q=2-packet reps; T = cubes of p=3-packet reps
                R=[roots[min(P)]**2 for P in D if len(P)==2]
                T=[roots[min(P)]**3 for P in D if len(P)==3]
                # R-window: e with 2e <= t ; T-window: e with 3e <= t
                for e in range(1, t//2+1):
                    tested+=1
                    if abs(sum(x**e for x in R))>1e-9:
                        viol+=1
                        if viol<=4: print(f"R-VIOL S={sorted(Es)} t={t} e={e} decomp_sizes={[len(P) for P in D]}")
                for e in range(1, t//3+1):
                    tested+=1
                    if abs(sum(x**e for x in T))>1e-9:
                        viol+=1
                        if viol<=4: print(f"T-VIOL S={sorted(Es)} t={t} e={e}")
print(f"tested {tested} window-claims, violations: {viol}")
