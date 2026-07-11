# Pure-python exact cyclotomic norm: N(F) = Res(Phi_n, F) = det(mult-by-F matrix) in Z[X]/(X^{n/2}+1).
# For n=2^mu, Phi_n = X^{n/2}+1. Reduce F mod X^{n/2}+1 -> a(X) deg<m, m=n/2. Norm = det of mult matrix.
import random
from math import log2
from fractions import Fraction

def reduce_mod(coeffs, m):
    # reduce a polynomial (dict exp->coeff or list) mod X^m + 1: X^m = -1
    a=[0]*m
    for e,c in coeffs:
        e%= (2*m)            # X^{2m}=1 since (X^m)^2=1
        if e<m: a[e]+=c
        else:   a[e-m]-=c
    return a

def mult_matrix(a, m):
    # column k = coeffs of a(X)*X^k mod X^m+1
    M=[[0]*m for _ in range(m)]
    for k in range(m):
        # a*X^k: shift
        for i in range(m):
            if a[i]==0: continue
            e=i+k
            if e<m: M[e][k]+=a[i]
            else:   M[e-m][k]-=a[i]
    return M

def det_int(M):
    n=len(M); A=[[Fraction(x) for x in row] for row in M]; det=Fraction(1)
    for col in range(n):
        piv=None
        for r in range(col,n):
            if A[r][col]!=0: piv=r;break
        if piv is None: return 0
        if piv!=col: A[col],A[piv]=A[piv],A[col]; det=-det
        det*=A[col][col]
        inv=A[col][col]
        for r in range(col+1,n):
            f=A[r][col]/inv
            if f!=0:
                for c in range(col,n): A[r][c]-=f*A[col][c]
    assert det.denominator==1
    return int(det)

def Nres(n, exps, signs):
    m=n//2
    a=reduce_mod(list(zip(exps,signs)), m)
    return det_int(mult_matrix(a,m))

def factor_small(x, lim=10**7):
    x=abs(x); fs={}; d=2
    while d*d<=x and d<lim:
        while x%d==0: fs[d]=fs.get(d,0)+1; x//=d
        d+=1
    if x>1: fs[x]=fs.get(x,0)+1
    return fs  # last factor may be composite if > lim^2; flag

print("EXACT |N(F)|=|Res(Phi_n,F)| for short ±1-relations of 2^mu-th roots (pure-python determinant)")
print("="*74)
for n in (16,32,64):
    m=n//2; rng=random.Random(0)
    for r in (2,3,4):
        rels=[]; seen=set()
        for _ in range(250):
            ks=tuple(sorted(rng.sample(range(n),2*r)))
            if ks in seen: continue
            seen.add(ks)
            sg=[1]*r+[-1]*r; rng.shuffle(sg)
            N=Nres(n,ks,sg)
            if N!=0: rels.append((ks,sg,abs(N)))
        if not rels: print(f"n={n} r={r}: no nonzero rel"); continue
        hs=[h for _,_,h in rels]; mx=max(hs)
        maxbad=1
        for h in hs:
            for q in factor_small(h):
                if q>2: maxbad=max(maxbad,q)
        crude=(2*r)**m
        print(f"n={n:3d} r={r}: {len(rels)} rels; max|N|=2^{log2(mx):.1f} (crude (2r)^{m}=2^{log2(crude):.0f}); "
              f"max ODD prime div=2^{log2(maxbad):.1f}; n^4=2^{log2(n**4):.0f}  "
              f"{'-> bad odd prime CAN exceed n^4 (WALL)' if maxbad>=n**4 else '-> bad odd primes < n^4 (Linnik-favorable?)'}")
