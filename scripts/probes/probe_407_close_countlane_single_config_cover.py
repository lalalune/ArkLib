# Test: is there a SINGLE config U* whose resultant N_{U*}=Res(e2Fold_{U*},Phi_n) is
# divisible by ALL the count-lane candidate primes?  (If so, D=N_{U*} is a single integer
# of height <=(n^2+n)^{n/2}=2^{O(n log n)} bounding the prime COUNT by log2(N_{U*}).)
# Test n=16: candidate primes = {17,97,113,193,241,337,353,401,433,577,881}.
# For each candidate prime p, it divides gcd(N(sum u),N(sum u^3)) for SOME config; check
# whether a single config's gcd is divisible by MANY of them, or each prime needs its own config.
import sympy as sp
from itertools import combinations, product
n=16; HALF=8
z=sp.symbols('z'); Phi=sp.Poly(sp.cyclotomic_poly(n,z),z)
def vec(exps):
    v=[0]*HALF
    for e in exps:
        e%=n
        if e<HALF: v[e]+=1
        else: v[e-HALF]-=1
    return v
def poly(v): return sp.Poly(sum(int(c)*z**l for l,c in enumerate(v)),z)
def Nrm(v): return abs(int(sp.resultant(Phi.as_expr(), poly(v).as_expr(), z)))
cand={17,97,113,193,241,337,353,401,433,577,881}
# count how many candidate primes each config's gcd hits, and the MAX
best=(0,None,set()); per_config_prime_sets=[]
for size in range(2,HALF+1):
    for pr in combinations(range(HALF),size):
        for signs in product([0,1],repeat=size):
            exps=[pr[i]+(HALF if signs[i] else 0) for i in range(size)]
            a=vec(exps); b=vec([3*e for e in exps])
            if all(c==0 for c in a) or all(c==0 for c in b): continue
            g=sp.gcd(Nrm(a),Nrm(b))
            if g<=1: continue
            ps={int(q) for q,_ in sp.factorint(g).items() if q%2==1 and q%n==1}
            if ps:
                per_config_prime_sets.append(ps)
                if len(ps)>best[0]: best=(len(ps),exps,ps)
print(f"max candidate primes hit by a SINGLE config gcd: {best[0]}  primes={sorted(best[2])}")
# is the union covered by few configs? greedy
union=set().union(*per_config_prime_sets) if per_config_prime_sets else set()
print(f"total distinct candidate primes in union: {len(union)} = {sorted(union)}")
# minimal #configs to cover all primes (greedy upper bound)
remaining=set(union); chosen=0
sets=sorted(per_config_prime_sets,key=len,reverse=True)
while remaining:
    bestset=max(sets,key=lambda S:len(S&remaining))
    if not (bestset&remaining): break
    remaining-=bestset; chosen+=1
print(f"greedy #configs to cover all candidate primes: {chosen}")
print("=> if a single config hits all, D=one resultant works; if not, D is a union (no single small-height integer).")
