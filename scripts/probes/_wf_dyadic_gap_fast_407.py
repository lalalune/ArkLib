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
def ispow2(x): return x&(x-1)==0
N=32; zeta=[cmath.exp(2j*math.pi*i/N) for i in range(N)]
anomaly_nonpow2=0; anomaly_s_ne_t=0; total=0; table=defaultdict(lambda: defaultdict(int))
for a in range(2,9):  # weight up to 8 -- fast, decisive for the structure
    for idx in itertools.combinations(range(N),a):
        t=gap_below_lead(idx,N,zeta)
        if t<2: continue
        total+=1; s=max_s_coset(idx,N); table[t][s]+=1
        if not ispow2(t): anomaly_nonpow2+=1
        if s!=t: anomaly_s_ne_t+=1
print(f"N=32 weight<=8: total(gap>=2)={total}, nonpow2={anomaly_nonpow2}, s!=t={anomaly_s_ne_t}")
for t in sorted(table): print(f"  gap t={t:2d}: dist={dict(table[t])}")
