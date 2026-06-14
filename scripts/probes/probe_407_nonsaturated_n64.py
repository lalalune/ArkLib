# Is the n=64 counterexample a SATURATION artifact (small p) or a REAL prize-regime refutation?
# Prize regime = NON-saturated: p >> |Sigma_3|. Test large p ===1 mod 64.
from itertools import combinations
from sympy import primerange
import random
n=64; HALF=32
# char-0 count of distinct 3-subset sums of mu_32 (exact via Z[zeta_64] vectors)
def sigma0_count():
    # represent mu_32 = {zeta_64^{2l}} ; sum of 3 distinct, count distinct as Z[zeta_64] vectors (len 32, zeta^32=-1)
    vecs=set()
    for W in combinations(range(HALF),3):
        v=[0]*HALF
        for l in W:
            e=(2*l)%n
            if e<HALF: v[e]+=1
            else: v[e-HALF]-=1
        vecs.add(tuple(v))
    return len(vecs)
N0=sigma0_count()
print(f"char-0 |Sigma_3| (distinct 3-subset sums of mu_32) = {N0}")
print(f"=> non-saturated requires p >> {N0}\n")

def hunt(lo,hi,sample_per_prime=200000):
    cex=[]; tested_primes=0; prim_found=0
    for p in primerange(lo,hi):
        if p%n!=1: continue
        e=(p-1)//n; g=None
        for a in range(2,p):
            gg=pow(a,e,p)
            if pow(gg,n,p)==1 and pow(gg,HALF,p)==p-1: g=gg;break
        if g is None: continue
        tested_primes+=1
        i2=pow(2,p-2,p)
        mu=[pow(g,j,p) for j in range(n)]
        mu32=[pow(g,2*l,p) for l in range(HALF)]
        Sig=set(sum(W)%p for W in combinations(mu32,3))   # exact full Sigma_3 mod p
        satur = len(Sig)/p
        # sample antipodal-free size-6 configs
        cnt=0; local_cex=0
        # smarter: iterate combos but cap
        for Uidx in combinations(range(n),6):
            if any(((j+HALF)%n) in set(Uidx) for j in Uidx): continue
            us=[mu[j] for j in Uidx]
            if sum(us)%p!=0: continue
            if sum(pow(u,3,p) for u in us)%p!=0: continue
            prim_found+=1
            e2=(-i2*sum(pow(u,2,p) for u in us))%p
            if e2 not in Sig:
                local_cex+=1; cex.append((p,Uidx,e2,round(satur,3)))
            cnt+=1
            if cnt>sample_per_prime: break
        print(f"  p={p}: |Sigma_3|={len(Sig)} (sat={satur:.2f}), primitive sampled, e2-not-in-Sigma count={local_cex}",flush=True)
        if tested_primes>=6: break
    print("\nNON-saturated counterexamples:", [c for c in cex if c[3]<0.5][:3] if cex else "checking...")
    real=[c for c in cex if c[3]<0.5]
    print("REAL (non-saturated, sat<0.5) refutations:", real[:3] if real else "NONE -> p=2113 was a saturation artifact")

# saturation boundary ~ N0; test p from ~5*N0 upward (non-saturated)
hunt(10000, 60000)
