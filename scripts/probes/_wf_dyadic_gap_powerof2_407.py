"""
#407 dyadic-uncertainty: CONFIRM the two-part rigidity discovered:
  (1) gap t (=largest t with e_1..e_{t-1}=0) is ALWAYS a power of 2 for S subset mu_{2^mu}
  (2) S with gap t is EXACTLY a union of mu_t-cosets (closed under +N/t), AND max-coset s = t.
Test on N=32 bounded weight + look for ANY counterexample (gap not power of 2, or gap != s).
Also report: for fixed t, the COUNT of S with gap exactly t = number of mu_t-coset-unions of
 the right total weight. This gives the char-0 count directly.
"""
import itertools, cmath, math
from collections import defaultdict

def poly_coeffs(idx_set,N,zeta):
    coeffs=[1.0+0j]
    for i in idx_set:
        p=zeta[i]; new=[0j]*(len(coeffs)+1)
        for k,c in enumerate(coeffs):
            new[k]+=c; new[k+1]+=-p*c
        coeffs=new
    return coeffs

def gap_below_lead(idx_set,N,zeta):
    c=poly_coeffs(idx_set,N,zeta); a=len(idx_set); t=1
    while t<a and abs(c[t])<1e-7: t+=1
    return t

def max_s_coset(idx_set,N):
    S=set(idx_set); best=1
    for s in range(1,N+1):
        if N%s: continue
        if all((x+N//s)%N in S for x in S): best=max(best,s)
    return best

# Confirm on N=32 (bounded weight) and report any anomaly
N=32
zeta=[cmath.exp(2j*math.pi*i/N) for i in range(N)]
anomaly_nonpow2=0; anomaly_s_ne_t=0; total=0
table=defaultdict(lambda: defaultdict(int))
def ispow2(x): return x&(x-1)==0
for a in range(2,13):
    for idx in itertools.combinations(range(N),a):
        t=gap_below_lead(idx,N,zeta)
        if t<2: continue
        total+=1
        s=max_s_coset(idx,N)
        table[t][s]+=1
        if not ispow2(t): anomaly_nonpow2+=1
        if s!=t: anomaly_s_ne_t+=1
print(f"N={N} weight<=12: total vanishing(gap>=2)={total}")
print(f"  gap-not-power-of-2 anomalies: {anomaly_nonpow2}")
print(f"  max-coset-s != gap-t anomalies: {anomaly_s_ne_t}")
for t in sorted(table):
    print(f"  gap t={t:2d}: max-coset-s dist = {dict(table[t])}")
