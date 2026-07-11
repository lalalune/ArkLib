"""
GENUINELY NOVEL: analyze the wraparound SEQUENCE W_r structure (no prior analysis of this object).
W_r = E_r(F_p) - E_r(char0). Compute W_r to high r, look for:
 (1) a linear recurrence (=> rational generating function => W_r ~ lambda^r, lambda computable).
 (2) growth rate W_{r+1}/W_r and W_r/E_r^0 and W_r/Wick.
 (3) Is W_r/E_r^0 itself a nice sequence? (the relative wraparound)
 (4) Q>=0 provability: is the wraparound sub-Gaussian-monotone for STRUCTURAL reasons?
"""
from collections import Counter
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def energies(p,n,R):
    S=subgroup(p,n); c=Counter({0:1}); E={}
    for r in range(1,R+1):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc
        E[r]=sum(m*m for m in c.values())
    return E
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
def fit_linrec(seq, order):
    """try to fit seq to a linear recurrence of given order with CONSTANT coeffs (exact rational via solve)."""
    # seq[k] = sum_{j=1..order} c_j seq[k-j]. Set up linear system, solve over Q.
    import fractions
    F=fractions.Fraction
    n=len(seq)
    if n < 2*order+1: return None
    # use first `order` equations to solve for c_j
    import itertools
    rows=[]; rhs=[]
    for k in range(order, 2*order):
        rows.append([F(seq[k-j]) for j in range(1,order+1)]); rhs.append(F(seq[k]))
    # gaussian elim
    A=[row[:]+[rhs[i]] for i,row in enumerate(rows)]
    m=order
    for col in range(m):
        piv=next((r for r in range(col,m) if A[r][col]!=0),None)
        if piv is None: return None
        A[col],A[piv]=A[piv],A[col]
        inv=F(1)/A[col][col]
        A[col]=[x*inv for x in A[col]]
        for r in range(m):
            if r!=col and A[r][col]!=0:
                f=A[r][col]; A[r]=[A[r][i]-f*A[col][i] for i in range(m+1)]
    coeffs=[A[i][m] for i in range(m)]
    # verify on remaining
    for k in range(2*order, n):
        pred=sum(coeffs[j-1]*seq[k-j] for j in range(1,order+1))
        if pred!=F(seq[k]): return None
    return coeffs

n=16; R=14
q=10**9
while not(q%n==1 and isprime(q)): q+=1
E0=energies(q,n,R)
p=65537
Ep=energies(p,n,R)
W=[Ep[r]-E0[r] for r in range(1,R+1)]  # W[0]=W_1, etc.
print(f"n={n}, prize prime p={p}. Wraparound W_r (r=1..{R}):")
for r in range(2,R+1):
    w=W[r-1]; e0=E0[r]; wick=dfac(r)*n**r
    ratio_e0 = w/e0 if e0 else 0
    ratio_wick = w/wick
    rr = (W[r-1]/W[r-2]) if r>2 and W[r-2] else 0
    print(f"  r={r:>2}: W_r={w:.4e}  W_r/E_r^0={ratio_e0:.5f}  W_r/Wick={ratio_wick:.5f}  W_r/W_{{r-1}}={rr:.3f}")
print()
print("(1) Linear recurrence fit for W_r (constant coeffs):")
Wseq=[W[r-1] for r in range(4,R+1)]  # start where W>0
for order in (1,2,3,4):
    c=fit_linrec(Wseq, order)
    if c: print(f"   order {order}: W_r = " + " + ".join(f"({ci})*W_{{r-{j+1}}}" for j,ci in enumerate(c))); break
else:
    print("   no constant-coeff linear recurrence up to order 4 (W_r is NOT C-finite => no rational gen func)")
print()
print("(2) growth: W_{r+1}/W_r vs (2r+1)n (Wick step rate):")
for r in range(5,R):
    print(f"   r={r}: W_{{r+1}}/W_r={W[r]/W[r-1]:.2f}  (2r+1)n={(2*r+1)*n}")
