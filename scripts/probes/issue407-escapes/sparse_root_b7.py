import numpy as np
from itertools import combinations, product
from math import comb, sqrt, gcd, log, pi
from sympy import isprime

# THE PRIZE QUANTITY directly: bad-SCALAR count of the monomial line (u0, X^k) for RS[k].
# Via MonomialLineListBridge: bad gamma <=> exists q in RS[k+1], coeff_k(q)=-gamma, q agrees
# with u0 on >= (1-delta)n points. #bad = #distinct leading coeffs in the radius-delta list.
#
# We compute EXACTLY for u0 = a far monomial x^b (the binding low-exponent direction, comment 125):
#   bad gamma <=> exists deg-<k poly P and witness S, |S|>=(1-delta)n, with
#                x^b agrees with P + gamma x^k  on S  (i.e. line x^b vs codeword, scalar on x^k)
# Actually the line is (u0=x^b, u1=x^k): point x in S iff x^b + gamma x^k = P(x), deg P<k.
# bad gamma <=> the (k+2)-sparse poly x^b + gamma x^k - P has >= (1-delta)n roots in mu_n.
#
# We count #{distinct bad gamma} EXACTLY (char-p) and compare to the Kambire budget n.
# THIS is what R-thin must bound; if it stays small (<= k+const), off-BGK; if ~ n, = BGK.

def primitive_root_mod_p(p):
    if p==2:return 1
    phi=p-1;mm=phi;d=2;fac=[]
    while d*d<=mm:
        if mm%d==0:
            fac.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fac.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):return g
def find_thin_prime(n,lo):
    t=(lo-1)//n+1
    while True:
        p=1+n*t
        if isprime(p):return p
        t+=1
def rank_modp(M,p):
    M=[[x%p for x in r] for r in M];rows=len(M);cols=len(M[0]) if rows else 0;r=0
    for col in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i][col]%p!=0:piv=i;break
        if piv is None:continue
        M[r],M[piv]=M[piv],M[r];inv=pow(M[r][col],p-2,p);M[r]=[(x*inv)%p for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][col]%p!=0:
                f=M[i][col];M[i]=[(M[i][j]-f*M[r][j])%p for j in range(cols)]
        r+=1
        if r==rows:break
    return r

def solve_gamma_for_subset(p,n,k,b,sub,powers):
    """For a fixed witness subset S=sub, is there (gamma, P deg<k) with x^b + gamma x^k = P(x) on S?
    Unknowns: gamma, c_0..c_{k-1}. Eqn at x_j: c_0+...+c_{k-1}x_j^{k-1} - gamma x_j^k = x_j^b.
    Return the UNIQUE gamma if the system is consistent and gamma is determined; else None or 'free'."""
    # Build augmented system; unknowns ordered [c_0..c_{k-1}, gamma]; rhs x_j^b
    rows=[];rhs=[]
    for j in sub:
        xj=powers[j]
        row=[pow(xj,t,p) for t in range(k)]+[(-pow(xj,k,p))%p]
        rows.append(row);rhs.append(pow(xj,b,p)%p)
    # solve via gaussian elim, get gamma (last var) if determined
    M=[rows[i][:]+[rhs[i]] for i in range(len(rows))]
    rows_n=len(M);cols=k+1
    # reduce
    Mr=[[x%p for x in r] for r in M];r=0;pivcol=[]
    for col in range(cols):
        piv=None
        for i in range(r,rows_n):
            if Mr[i][col]%p!=0:piv=i;break
        if piv is None: continue
        Mr[r],Mr[piv]=Mr[piv],Mr[r];inv=pow(Mr[r][col],p-2,p);Mr[r]=[(x*inv)%p for x in Mr[r]]
        for i in range(rows_n):
            if i!=r and Mr[i][col]%p!=0:
                f=Mr[i][col];Mr[i]=[(Mr[i][jj]-f*Mr[r][jj])%p for jj in range(cols+1)]
        pivcol.append(col);r+=1
        if r==rows_n:break
    # check consistency
    for i in range(r,rows_n):
        if Mr[i][cols]%p!=0: return ('incons',None)
    # gamma is variable index k (last). Is it a pivot (determined) or free?
    if k in pivcol:
        # find the row with pivot at col k
        ri=pivcol.index(k)
        # value = rhs (since reduced, pivot=1, other pivots eliminated; but free vars may appear)
        # gamma determined only if no free var appears in its row
        rowk=Mr[ri]
        free=[c for c in range(cols) if c not in pivcol]
        if any(rowk[c]%p!=0 for c in free):
            return ('free',None)
        return ('det', rowk[cols]%p)
    else:
        return ('free',None)  # gamma free

def count_bad_scalars(p,n,k,b,g,w_witness):
    """Count distinct bad gamma: gamma is bad iff some witness S of size>=w has the line agree.
    We enumerate witness subsets of size exactly w (the minimal far witness) and collect determined gammas.
    (A bad gamma needs a size>=w agreement; we take w=w_witness=(1-delta)n.)"""
    e_exp=(p-1)//n;base=pow(g,e_exp,p);powers=[pow(base,j,p) for j in range(n)]
    bad=set(); free_seen=False
    w=w_witness
    if comb(n,w)>1_500_000:
        return None
    for sub in combinations(range(n),w):
        kind,val=solve_gamma_for_subset(p,n,k,b,sub,powers)
        if kind=='det': bad.add(val)
        elif kind=='free': free_seen=True  # gamma free => all of F_p bad (saturation)
    return len(bad), free_seen

print("=== EXACT bad-SCALAR count of monomial line (binding low-exp dir), char-p ===")
print("Witness w=(1-delta)n at the crossing. #bad vs Kambire budget n and k+2.")
print(" n  k  b   delta   w   #badScalars  free?  budget=n  k+2")
for n in [8,12,16]:
    p=find_thin_prime(n,2000);g=primitive_root_mod_p(p)
    k=max(2,n//4)
    b=k+2  # low-exponent far direction (b mod n = b, far)
    # crossing delta ~ Johnson-ish: w just above b so that x^b is far (w> b => far by FarThreshold)
    for w in [b+1, b+2]:
        if w>=n: continue
        res=count_bad_scalars(p,n,k,b,g,w)
        if res is None: 
            print(f"{n} {k} {b}  -- w={w} too big"); continue
        nb,free=res
        delta=1-w/n
        print(f"{n:2d} {k:2d} {b:2d}  {delta:.3f}  {w:2d}    {nb:4d}      {free}    {n}      {k+2}")
