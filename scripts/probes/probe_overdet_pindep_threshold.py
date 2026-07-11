import sympy, random, cmath, math
random.seed(7); TAU=2*math.pi
def char0_nonzero(n,cols,S):
    import numpy as np
    rows=[[cmath.exp(1j*TAU*((s*c)%n)/n) for c in cols] for s in S]
    return abs(np.linalg.det(np.array(rows,dtype=complex)))>1e-6
def detmodq(n,cols,S,q,zeta):
    M=[[pow(zeta,(s*c)%n,q) for c in cols] for s in S]; m=len(M); det=1; A=[r[:] for r in M]
    for i in range(m):
        piv=next((r for r in range(i,m) if A[r][i]%q),None)
        if piv is None: return 0
        if piv!=i: A[i],A[piv]=A[piv],A[i]; det=-det
        det=(det*A[i][i])%q; inv=pow(A[i][i],q-2,q)
        for r in range(i+1,m):
            f=(A[r][i]*inv)%q
            if f: A[r]=[(A[r][c]-f*A[i][c])%q for c in range(m)]
    return det%q
def maxbad(n,k,a,b,nsub,qmax):
    cols=list(range(k))+[a,b]; w=k+2   # square (k+2)x(k+2)
    gen=[]; t=0
    while len(gen)<nsub and t<nsub*50:
        S=tuple(sorted(random.sample(range(n),w))); t+=1
        if char0_nonzero(n,cols,S): gen.append(S)
    mx=0; m=1
    while n*m+1<=qmax:
        q=n*m+1
        if sympy.isprime(q):
            g=sympy.primitive_root(q); zeta=pow(g,(q-1)//n,q)
            if any(detmodq(n,cols,S,q,zeta)==0 for S in gen): mx=q
        m+=1
    return mx,len(gen)
print("Over-det (s-k=2, square det) MAX bad prime vs n  [decoupling: threshold ~ n^2, NOT growing like under-det n^4+]:")
for (n,k,a,b,qmax) in [(16,4,4,10,200000),(32,8,8,20,300000),(64,16,16,40,300000)]:
    mx,g=maxbad(n,k,a,b, 150 if n<64 else 90, qmax)
    print(f"  n={n}: max over-det bad prime={mx} (n^2={n*n}); {'= n^%.2f'%(math.log(mx)/math.log(n)) if mx>1 else 'NONE'}  [{'<n^2 DECOUPLED' if 0<mx<=n*n else ('>n^2' if mx>n*n else 'none')}]")
print("contrast UNDER-det (single Schur h_{b-k}) bad primes from probe_excess_prime_growth: n16->8161(n^3.25), n32->877313(n^3.95), n64->n^5.99 (GROWING = BGK)")

# RESULT (2026-06-14): CORROBORATES the B5 decoupling claim (δ* decouples from BGK).
# Over-determined band (s-k=2, det(M)=0 = generalized-Vandermonde consistency for SOME gamma):
#   max bad prime (q=1 mod n, spurious det=0): n16->17 (n^1.02), n32->2113 (n^2.21), n64->2753 (n^1.90)
#   => threshold ~ n^2, STABLE exponent ~2 (NOT growing). p-INDEPENDENT for prize primes q>>n^2.
# Under-determined band (s-k=1, single Schur h_{b-k}=0, = the bad-SCALAR/subset-sum/Vieta object):
#   max bad prime GROWS n^3.25 -> 3.95 -> 5.99 (probe_excess_prime_growth) = reaches prize scale = BGK.
# Since delta* binds at the OVER-det band (R4: I(w=k+2)=88>budget, I(w=k+3)=8<budget at n=16; under-det
# w=k+1 is DEEPER, above delta*), delta* is governed by the p-INDEPENDENT over-det incidence
# => delta* DECOUPLES from the analytic BGK char-sum; it is a char-0 COMBINATORIAL (decidable-per-n)
# quantity. Corrects the "delta* gates the subset-sum = BGK" framing (that under-det band is above delta*).
# RESIDUAL (not closure): (a) prize-RATE binding band s-k scaling (tested s-k=2); (b) bounding the
# char-0 over-det incidence asymptotically (= the #400/#389 Theta(n) orbit count, feasibility ~5).
