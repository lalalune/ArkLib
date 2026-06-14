# REFUTATION ATTEMPT for the Half-Sum Lemma (the distilled m=2 optimality residual):
#   U subset mu_n, U cap -U = empty, sum u = sum u^3 = 0  (over F_p, p=1 mod n)
#   ==> -1/2 sum u^2  is a sum of |U|/2 distinct mu_{n/2} elements (in Sigma).
# If ANY such U violates it -> exact delta* REFUTED (char-p inflation of #bad).
from itertools import combinations
import sympy as sp

def search(n, sizes, primes):
    inv2={}
    found=[]
    total_U=0
    for p in primes:
        e=(p-1)//n; g=None
        for a in range(2,p):
            gg=pow(a,e,p)
            if pow(gg,n,p)==1 and pow(gg,n//2,p)==p-1: g=gg;break
        if g is None: continue
        i2=pow(2,p-2,p)
        mun=[pow(g,j,p) for j in range(n)]
        munhalf=[pow(g,2*j,p) for j in range(n//2)]
        neg={mun[j]: mun[(j+n//2)%n] for j in range(n)}
        for t in sizes:                 # |U| = t (even)
            k=t//2
            # Sigma_k mod p (sums of k distinct mu_{n/2})
            if sp.binomial(n//2,k) > 3_000_000:
                Sig=None
            else:
                Sig=set(sum(W)%p for W in combinations(munhalf,k))
            cnt=0
            for Uidx in combinations(range(n), t):
                U=[mun[j] for j in Uidx]
                Uset=set(U)
                if any(neg[u] in Uset for u in U):  # antipodal pair -> skip
                    continue
                if sum(U)%p!=0: continue
                if sum(pow(u,3,p) for u in U)%p!=0: continue
                cnt+=1; total_U+=1
                val=(-i2*sum(pow(u,2,p) for u in U))%p
                if Sig is not None and val not in Sig:
                    found.append((p,t,sorted(Uidx),val))
            # report per (p,t)
        # only first prime per n to keep it fast unless we want more
    print(f"n={n}: U-configs satisfying constraints found={total_U}; "
          + (f"COUNTEREXAMPLES={len(found)} e.g. {found[:2]}  <<< REFUTES exact delta*" if found
             else "NO counterexample -> Half-Sum Lemma holds (supports exact delta*)"))
    return found

# n=32: |U|=4,6 ; primes 1 mod 32
p32=[p for p in sp.primerange(33, 400) if p%32==1][:4]
search(32, [4,6], p32)
# n=64: |U|=4 ; primes 1 mod 64
p64=[p for p in sp.primerange(65, 900) if p%64==1][:3]
search(64, [4], p64)
