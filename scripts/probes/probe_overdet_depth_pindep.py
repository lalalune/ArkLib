import sympy, random, cmath, math
random.seed(11); TAU=2*math.pi
def rank_modq(M,q):
    A=[row[:] for row in M]; rows=len(A); cols=len(A[0]); r=0
    for c in range(cols):
        piv=next((i for i in range(r,rows) if A[i][c]%q),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],q-2,q)
        A[r]=[(x*inv)%q for x in A[r]]
        for i in range(rows):
            if i!=r and A[i][c]%q:
                f=A[i][c]; A[i]=[(A[i][cc]-f*A[r][cc])%q for cc in range(cols)]
        r+=1
        if r==rows: break
    return r
def rank_C(M):
    import numpy as np
    return np.linalg.matrix_rank(np.array(M,dtype=complex),tol=1e-7)
def maxbad_for_sk(n,k,a,b,sk,nsub,qmax):
    cols=list(range(k))+[a,b]; w=k+sk; full=k+2
    gen=[]; t=0
    while len(gen)<nsub and t<nsub*60:
        S=tuple(sorted(random.sample(range(n),w))); t+=1
        Mc=[[cmath.exp(1j*TAU*((s*c)%n)/n) for c in cols] for s in S]
        if rank_C(Mc)==full: gen.append(S)   # char-0 rank full (=k+2): NOT char-0-consistent
    mx=0; m=1
    while n*m+1<=qmax:
        q=n*m+1
        if sympy.isprime(q):
            g=sympy.primitive_root(q); z=pow(g,(q-1)//n,q)
            for S in gen:
                Mq=[[pow(z,(s*c)%n,q) for c in cols] for s in S]
                if rank_modq(Mq,q)<full: mx=q; break  # spurious rank drop = bad prime
        m+=1
    return mx,len(gen),w
print("Over-det bad-prime threshold vs over-determination depth s-k (n fixed): does it stay ~n^2 as s-k grows?")
for (n,k,a,b) in [(32,8,8,20),(64,16,16,40)]:
    for sk in ([2,3,4,6] if n==32 else [2,4]):
        mx,g,w=maxbad_for_sk(n,k,a,b,sk, 100 if n<64 else 60, 120000)
        e=math.log(mx)/math.log(n) if mx>1 else 0
        print(f"  n={n} k={k} s-k={sk} (w={w}): max bad prime={mx} (n^2={n*n}); {'n^%.2f'%e if mx>1 else 'NONE'} [{'<=n^2 decoupled' if 0<mx<=n*n else ('NONE' if mx==0 else '>n^2')}]")
