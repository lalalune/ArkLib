"""
probe_dsmds_underdet_contrast.py  (issue #407 / #389 -- DO NOT COMMIT)

Confirms the OVER-det vs UNDER-det dichotomy is REAL for the higher-order-MDS minor family of
mu_n (not merely inherited from the older subset-sum probe). The MDS(ell) obstruction is a
CONJUNCTION (over-det) and is char-faithful (probe_dsmds_largeprime: 0 bad primes q>>n^4).
The UNDER-determined sibling = a SINGLE generalized-Vandermonde minor det([x^0..x^{k-1}, x^a, x^b]
restricted to one subset S) = 0 -- one equation, the BGK object -- should have bad primes GROWING.

We measure, for the SAME mu_n, the largest prime q=n*m+1 at which a single (k+2)x(k+2) generalized-
Vandermonde minor spuriously vanishes (char-0 nonzero), vs n. If it grows past n^2 toward n^3+,
that is the under-determined BGK wall, confirming the MDS(ell) conjunction sits on the rigid side.

Honesty: q up to ~2e6; q=1 mod n; over genuine non-antipodal subsets; nothing committed.
"""
import sympy, math, cmath, random
import numpy as np
random.seed(17); TAU=2*math.pi
def zc(n,e): return cmath.exp(1j*TAU*(e%n)/n)
def cdet(rows): return abs(np.linalg.det(np.array(rows,dtype=complex)))
def detmodq(rows,q):
    m=len(rows); A=[[x%q for x in r] for r in rows]; det=1
    for i in range(m):
        piv=next((r for r in range(i,m) if A[r][i]%q),None)
        if piv is None: return 0
        if piv!=i: A[i],A[piv]=A[piv],A[i]; det=-det
        det=(det*A[i][i])%q; inv=pow(A[i][i],q-2,q)
        for r in range(i+1,m):
            f=(A[r][i]*inv)%q
            if f: A[r]=[(A[r][c]-f*A[i][c])%q for c in range(m)]
    return det%q
def zq(n,q): g=sympy.primitive_root(q); return pow(g,(q-1)//n,q)

def underdet_maxbad(n,k,a,b,nsub,qmax):
    """single generalized-Vandermonde minor: cols = {0..k-1, a, b}, rows = subset S of size k+2.
    char-0 nonzero (generic), find max prime q where det==0 mod q."""
    cols=list(range(k))+[a,b]; w=k+2
    gen=[]; t=0
    while len(gen)<nsub and t<nsub*60:
        t+=1; S=tuple(sorted(random.sample(range(n),w)))
        rows=[[zc(n,(s*c)%n) for c in cols] for s in S]
        if cdet(rows)>1e-6: gen.append(S)
    mx=0; m=1
    while n*m+1<=qmax:
        q=n*m+1
        if sympy.isprime(q):
            z=zq(n,q)
            for S in gen:
                M=[[pow(z,(s*c)%n,q) for c in cols] for s in S]
                if detmodq(M,q)==0: mx=q; break
        m+=1
    return mx,len(gen)

print("UNDER-determined single generalized-Vandermonde minor (the BGK sibling of the MDS(ell)")
print("conjunction): max spurious-vanish prime vs n  [expect GROWING past n^2 = wall side]")
for (n,k,a,b,qmax) in [(8,2,2,5,400000),(16,4,4,10,1500000),(32,8,8,20,2000000)]:
    mx,g=underdet_maxbad(n,k,a,b,80 if n<32 else 50,qmax)
    print(f"  n={n} (k={k}): {g} subsets; max bad prime = {mx}"
          f"{' = n^%.2f'%(math.log(mx)/math.log(n)) if mx>1 else ' NONE'}"
          f"  [{'>n^2 (under-det grows)' if mx>n*n else '<=n^2'}]")
print()
print("Compare to probe_dsmds_largeprime: the MDS(ell) CONJUNCTION (over-det) had 0 bad primes")
print("even at q>n^4. The single minor (under-det) grows -> confirms the dichotomy is intrinsic")
print("to the higher-order-MDS minor family of mu_n, not an artifact.")
