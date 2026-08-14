#!/usr/bin/env python3
"""
PROBE v2 (#444 C71 residual, 3-term strata): STRESS-TEST the (GCDSUM) candidate
  #{x in mu_n : x^i - c1 x^j - c2 x^k = 0} <= gcd(i-j,n) + gcd(j-k,n)
against ALL c1,c2 in F_p^* (not just mu_n), and the (DEG) bound i-k, to decide which is a
real universal law vs a small-sample coincidence. Larger n, more primes.
NEVER n=q-1. PROPER thin mu_n=2^a.
"""
import itertools, math

def subgroup_gen(p, n):
    def order(g):
        x=1
        for e in range(1,p):
            x=(x*g)%p
            if x==1: return e
        return p-1
    for cand in range(2,p):
        if order(cand)==p-1:
            return pow(cand,(p-1)//n,p)

def main():
    cases = [(97,8),(193,16),(257,16),(521,8),(4129,16),(12289,16),(7681,16),(40961,16)]
    deg_ok=gcdsum_ok=True
    deg_tight=0; gcdsum_tight=0; total_nonzero=0
    gcdsum_fail_ex=None
    for (p,n) in cases:
        if (p-1)%n or (p-1)//n<2: continue
        g=subgroup_gen(p,n); mun=[pow(g,t,p) for t in range(n)]
        munset=set(mun)
        maxr=0; ex=None
        # genuine trinomials, c1,c2 over ALL F_p^* (full adversary)
        for i,j,k in itertools.combinations(range(n),3):
            i,j,k=max(i,j,k),sorted([i,j,k])[1],min(i,j,k)
            deg=i-k; gsum=math.gcd(i-j,n)+math.gcd(j-k,n)
            # sample c1,c2 across F_p^* (step to keep it tractable for big p)
            step=max(1,(p-1)//40)
            for c1 in range(1,p,step):
                for c2 in range(1,p,step):
                    r=sum(1 for x in mun if (pow(x,i,p)-c1*pow(x,j,p)-c2*pow(x,k,p))%p==0)
                    if r>0: total_nonzero+=1
                    if r>deg: deg_ok=False
                    if r==deg and r>0: deg_tight+=1
                    if r>gsum:
                        gcdsum_ok=False
                        if gcdsum_fail_ex is None:
                            gcdsum_fail_ex=(p,n,i,j,k,c1,c2,r,gsum)
                    if r==gsum and r>0: gcdsum_tight+=1
                    if r>maxr: maxr=r; ex=(i,j,k,c1,c2,deg,gsum)
        print(f"p={p:6d} n={n:3d}: maxr={maxr} ex={ex}")
    print()
    print(f"(DEG)    #roots <= i-k                 : {'HOLDS' if deg_ok else 'FAILS'}  (tight hits {deg_tight})")
    print(f"(GCDSUM) #roots <= g(i-j,n)+g(j-k,n)   : {'HOLDS' if gcdsum_ok else 'FAILS'}  (tight hits {gcdsum_tight})")
    if gcdsum_fail_ex: print("  GCDSUM FAIL:", gcdsum_fail_ex)
    print(f"  nonzero-root configs sampled: {total_nonzero}")

if __name__=="__main__":
    main()
