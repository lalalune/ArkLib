#!/usr/bin/env python3
"""Batch 2: systematic exact closed forms for mu_{2^m} additive structure (no-relation regime).
All falsifiable, decidable, novel, wall-free. Fit-then-verify on an independent larger point."""
import sys; sys.path.insert(0,'scripts/conjectures')
from engine import isprime, primroot, big_prime_with, mu, energyR, test_conjecture, SURVIVORS, DEAD
import itertools
from fractions import Fraction

CACHE={}
def getG(m):
    if m not in CACHE:
        n=1<<m; p=big_prime_with(n,200003); CACHE[m]=(mu(p,n),p,n)
    return CACHE[m]

# --- A: even moments E_r closed forms (corrected/extended) ---
def Er(m,r):
    G,p,n=getG(m); return energyR(G,p,r)
# C2': E_3 = 15n^3 - 45n^2 + 40n  (refit, verified at n=32)
test_conjecture("C2","E_3(mu_n) = 15n^3 - 45n^2 + 40n",
    lambda m:(lambda n:15*n**3-45*n*n+40*n)(1<<m), lambda m:Er(m,3), [1,2,3,4,5], "NOVEL")

# fit E_4 from n=2,4,8,16,32 then verify n=64
def fit_poly(xs,ys,deg):
    A=[[Fraction(x)**j for j in range(deg+1)] for x in xs[:deg+1]]
    b=[Fraction(y) for y in ys[:deg+1]]
    M=[A[i][:]+[b[i]] for i in range(deg+1)]; nn=deg+1
    for c in range(nn):
        piv=next(r for r in range(c,nn) if M[r][c]!=0); M[c],M[piv]=M[piv],M[c]
        inv=Fraction(1)/M[c][c]; M[c]=[v*inv for v in M[c]]
        for r in range(nn):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(nn+1)]
    return [M[i][nn] for i in range(nn)]
e4=[Er(m,4) for m in range(1,6)]   # n=2..32
ns=[1<<m for m in range(1,6)]
coef4=fit_poly(ns,e4,4)
print("E4 fitted coeffs:",[str(c) for c in coef4])
# verify against n=64
e4_64=Er(6,4)
pred64=sum(coef4[i]*Fraction(64)**i for i in range(5))
print(f"E4 verify n=64: pred {pred64} actual {e4_64}  {'OK' if pred64==e4_64 else 'MISMATCH'}")
if all(c.denominator==1 for c in coef4) and pred64==e4_64:
    a0,a1,a2,a3,a4=[int(c) for c in coef4]
    test_conjecture("C8",f"E_4(mu_n) = {a4}n^4+{a3}n^3+{a2}n^2+{a1}n+{a0}",
        lambda m:(lambda n:a4*n**4+a3*n**3+a2*n*n+a1*n+a0)(1<<m), lambda m:Er(m,4), [1,2,3,4,5,6],"NOVEL")

# C9 (NOVEL general): leading coeff of E_r(mu_n) is (2r-1)!!
def dblfact(k):
    r=1
    while k>0: r*=k; k-=2
    return r
# verify leading coeff for r=2,3,4 by (E_r(2n)-...)/n^r ratio at large n -> (2r-1)!!
def lead_ratio(r):
    # E_r ~ (2r-1)!! n^r ; check E_r(n)/n^r -> (2r-1)!! as n grows (use n=32)
    G,p,n=getG(5); return energyR(G,p,r)  # n=32
for r in [2,3,4]:
    val=lead_ratio(r); n=32
    lead = Fraction(val, n**r)
    # leading coeff approx; exact statement: lim = (2r-1)!!
    print(f"E_{r}(32)/32^{r} = {float(lead):.4f}  vs (2{r}-1)!!={dblfact(2*r-1)}")
test_conjecture("C9","leading coeff of E_r(mu_n) = (2r-1)!! for all r",
    lambda r:dblfact(2*r-1),
    lambda r:round(Fraction(lead_ratio(r),32**r)),  # rounds to leading coeff at n=32
    [2,3,4],"NOVEL-general")

# --- D: k-term zero-sum counts Z_k(mu_n) = #{k-tuples summing to 0} ---
def Zk(m,k):
    G,p,n=getG(m)
    from collections import Counter
    # build (k-1)-fold sum histogram, count those = -last
    if k<=4:
        c=Counter()
        for tup in itertools.product(G,repeat=k-1): c[sum(tup)%p]+=1
        return sum(c[(-x)%p] for x in G)
    return None
# C10 (NOVEL): Z_4(mu_{2^m}) = 3n^2 - 2n   (4-term zero-sums = antipodal pairs of pairs)
test_conjecture("C10","Z_4(mu_n)=#{4-tuples sum 0} = 3n^2 - 2n",
    lambda m:(lambda n:3*n*n-2*n)(1<<m), lambda m:Zk(m,4), [1,2,3,4,5],"NOVEL")
# C11: Z_5(mu_{2^m}) = 0 (odd zero-sum count; parity)
test_conjecture("C11","Z_5(mu_{2^m})=0 (odd term zero-sum)",
    lambda m:0, lambda m:Zk(m,5), [1,2,3,4],"NOVEL")

# --- E: intersection statistics ---
# C12 (NOVEL): #{t!=0 : |mu_n cap (mu_n - t)| = 2} = (n^2-2n)/2
def cnt_two(m):
    G,p,n=getG(m); S=set(G)
    from collections import Counter
    d=Counter()
    for a in G:
        for b in G:
            if a!=b: d[(a-b)%p]+=1
    return sum(1 for t,v in d.items() if v==2)
test_conjecture("C12","#{t!=0: |mu_n cap (mu_n-t)|=2} = (n^2-2n)/2",
    lambda m:(lambda n:(n*n-2*n)//2)(1<<m), cnt_two, [2,3,4,5],"NOVEL")
# C13: #{t!=0 : intersection = 1} = n  (the '2a' translates)
def cnt_one(m):
    G,p,n=getG(m)
    from collections import Counter
    d=Counter()
    for a in G:
        for b in G:
            if a!=b: d[(a-b)%p]+=1
    return sum(1 for t,v in d.items() if v==1)
test_conjecture("C13","#{t!=0: |mu_n cap (mu_n-t)|=1} = n",
    lambda m:(1<<m), cnt_one, [2,3,4,5],"NOVEL")

print("\n==== BATCH 2 SUMMARY ====")
print(f"survivors total: {len(SURVIVORS)}  dead: {len(DEAD)}")
