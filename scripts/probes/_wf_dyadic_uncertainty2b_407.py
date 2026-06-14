import itertools, cmath, math
from collections import defaultdict

def poly_coeffs(idx_set, N, zeta):
    coeffs=[1.0+0j]
    for i in idx_set:
        p=zeta[i]; new=[0j]*(len(coeffs)+1)
        for k,c in enumerate(coeffs):
            new[k]+=c; new[k+1]+=-p*c
        coeffs=new
    return coeffs

def gap_below_lead(idx_set,N,zeta):
    c=poly_coeffs(idx_set,N,zeta); a=len(idx_set)
    t=1
    while t<a and abs(c[t])<1e-7: t+=1
    return t

def max_s_coset(idx_set,N):
    S=set(idx_set); best=1
    for s in range(1,N+1):
        if N%s: continue
        step=N//s
        if all((x+step)%N in S for x in S): best=max(best,s)
    return best

for N in [8,16]:
    zeta=[cmath.exp(2j*math.pi*i/N) for i in range(N)]
    print(f"\n=== N={N} ===")
    table=defaultdict(lambda: defaultdict(int))
    for a in range(2,N+1):
        for idx in itertools.combinations(range(N),a):
            t=gap_below_lead(idx,N,zeta)
            if t<2: continue
            table[t][max_s_coset(idx,N)]+=1
    for t in sorted(table):
        print(f"  gap t={t:2d}: max-coset-s dist = {dict(table[t])}")

# N=32: bounded weight only (a up to 12)
N=32
zeta=[cmath.exp(2j*math.pi*i/N) for i in range(N)]
print(f"\n=== N={N} (weight a<=12) ===")
table=defaultdict(lambda: defaultdict(int))
for a in range(2,13):
    for idx in itertools.combinations(range(N),a):
        t=gap_below_lead(idx,N,zeta)
        if t<2: continue
        table[t][max_s_coset(idx,N)]+=1
for t in sorted(table):
    print(f"  gap t={t:2d}: max-coset-s dist = {dict(table[t])}")
