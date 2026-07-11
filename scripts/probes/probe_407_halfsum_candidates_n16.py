# EXHAUSTIVE n=16 (prize-relevant primes p===1 mod 16): is there an ODD bad prime?
# Every odd bad prime p must have a primitive U (antipodal-free, 𝔭|sum u & 𝔭|sum u^3) with e_2(U) NOT in Sigma.
# Such p divides N(sum u). Enumerate ALL antipodal-free U (sizes 4,6,8), factor N(alpha), test each odd p===1 mod16.
import sympy as sp
from itertools import combinations, product
z=sp.symbols('z')
n=16; HALF=8
Phi=sp.Poly(sp.cyclotomic_poly(n,z),z)
pairs=[(j,j+HALF) for j in range(HALF)]   # antipodal pairs in mu_16

def vec_of(exps):   # element sum of zeta^e, reduced via zeta^8=-1, as length-8 int vector
    v=[0]*HALF
    for e in exps:
        e%=n
        if e<HALF: v[e]+=1
        else: v[e-HALF]-=1
    return v
def poly_of(v): return sp.Poly(sum(int(c)*z**l for l,c in enumerate(v)),z)
def fnorm(v): return abs(int(sp.resultant(Phi.as_expr(), poly_of(v).as_expr(), z)))

# Sigma generators: for r matching |U|/2, Sigma_k = sums of k distinct mu_8 elements (exps even: 2*l)
def sigma_set_modp(k,h,p):
    munhalf=[pow(h,2*l,p) for l in range(HALF)]
    return set(sum(W)%p for W in combinations(munhalf,k))

def primitive_configs(size):
    k=size//2
    chosen_pairs=combinations(range(HALF),size//2 if False else size)  # we pick 'size' pairs? no
    # antipodal-free size = choose 'size' pairs out of 8, one elt each
    out=[]
    for pr in combinations(range(HALF), size):
        for signs in product([0,1],repeat=size):
            exps=[ (j if s==0 else j+HALF) for j,s in zip(pr,signs)]
            out.append(exps)
    return out

cand_primes=set()
configs_by_size={}
for size in [4,6,8]:
    cfgs=primitive_configs(size)
    configs_by_size[size]=cfgs
    for exps in cfgs:
        a=vec_of(exps)
        b=vec_of([3*e for e in exps])
        # alpha=0 in Z[z]? then char-0 relation (not primitive) -> skip
        if all(c==0 for c in a): continue
        Na=fnorm(a); Nb=fnorm(b)
        g=sp.gcd(Na,Nb)
        for pr,mult in sp.factorint(g).items():
            if pr%2==1 and pr%n==1:
                cand_primes.add(int(pr))
print(f"n=16: candidate ODD primes ===1 mod 16 dividing gcd(N(a),N(b)) over all antipodal-free configs (sizes 4,6,8): {sorted(cand_primes)}")

# Now test each candidate prime: is there a primitive U with e_2(U) NOT in Sigma?
def h_of(p):
    e=(p-1)//n
    for a in range(2,p):
        hh=pow(a,e,p)
        if pow(hh,n,p)==1 and pow(hh,HALF,p)==p-1: return hh
bad=[]
for p in sorted(cand_primes):
    h=h_of(p); i2=pow(2,p-2,p)
    for size in [4,6,8]:
        k=size//2
        Sig=sigma_set_modp(k,h,p)
        for exps in configs_by_size[size]:
            us=[pow(h,e,p) for e in exps]
            if sum(us)%p!=0: continue
            if sum(pow(u,3,p) for u in us)%p!=0: continue
            e2=(-i2*sum(pow(u,2,p) for u in us))%p
            if e2 not in Sig:
                bad.append((p,size,exps,e2)); break
        if bad and bad[-1][0]==p: break
print("ODD BAD PRIMES (===1 mod 16) for n=16:", bad if bad else "NONE")
print("=> NONE means: NO odd prime ===1 mod 16 inflates #bad => Half-Sum Lemma PROVEN for n=16 at every prize-relevant prime (D's odd part = 1).")
