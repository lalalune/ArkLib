# Find explicit primitive U (antipodal-free, sum u = sum u^3 = 0) and dissect e_2(U) in Sigma_k.
# Goal: see the CONSTRUCTION that puts e_2(U) into the sumset, to find a general proof.
from itertools import combinations
import sympy as sp

def analyze(n,p,t):
    e=(p-1)//n; g=None
    for a in range(2,p):
        gg=pow(a,e,p)
        if pow(gg,n,p)==1 and pow(gg,n//2,p)==p-1: g=gg;break
    mun=[pow(g,j,p) for j in range(n)]          # exponent j -> g^j
    munhalf=[pow(g,2*j,p) for j in range(n//2)]  # mu_{n/2}, exponent in g^2
    expn={mun[j]:j for j in range(n)}
    exph={munhalf[j]:j for j in range(n//2)}
    i2=pow(2,p-2,p)
    k=t//2
    examples=[]
    for Uidx in combinations(range(n),t):
        # antipodal-free
        if any(((j+n//2)%n) in set(Uidx) for j in Uidx): continue
        U=[mun[j] for j in Uidx]
        if sum(U)%p!=0: continue
        if sum(pow(u,3,p) for u in U)%p!=0: continue
        e2=(-i2*sum(pow(u,2,p) for u in U))%p
        # find 2-subset(s) of mu_{n/2} summing to e2
        reps=[]
        for W in combinations(range(n//2),k):
            if sum(munhalf[j] for j in W)%p==e2:
                reps.append(tuple(W))
        sqr=[ (2*j)%n for j in Uidx ]   # exponents of u^2 in mu_n = even; in mu_{n/2} index = j mod n/2
        sqr_h=sorted(j% (n//2) for j in Uidx)
        examples.append((sorted(Uidx), e2, sqr_h, reps[:4]))
        if len(examples)>=6: break
    print(f"n={n} p={p} |U|={t}: {len(examples)} primitive U (showing up to 6)")
    print(f"   [U exponents mod {n}], e2, [U^2 exponents mod {n//2}], [mu_{n//2}-2-subsets (exp) summing to e2]")
    for ex in examples:
        print("   ", ex)

analyze(16,17,4)
analyze(16,17,6)
