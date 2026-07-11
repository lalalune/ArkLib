"""
Attack the monotonicity R(r+1)<=R(r)  <=>  (2r+1) E_r E_{r+2} <= (2r+3) E_{r+1}^2  (bounded log-convexity).
For Gaussian E_r=(2r-1)!!n^r this is EQUALITY. The prize: periods are LESS log-convex than Gaussian.
Test: (a) does it hold in char-p at prize primes? (b) the char-0 version -- is it a clean polynomial in n
(provable from closed forms)? (c) the gap (2r+3)E_{r+1}^2 - (2r+1)E_r E_{r+2} >= 0 -- structure?
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
print("=== (a) char-p: (2r+1)E_r E_{r+2} <= (2r+3)E_{r+1}^2 at prize primes? (ratio<1 => monotone holds) ===")
for n in (8,16):
    p=n**4+1
    while not(p%n==1 and isprime(p)): p+=1
    E=energies(p,n,12)
    print(f" n={n} p={p}:")
    for r in range(2,9):
        lhs=(2*r+1)*E[r]*E[r+2]; rhs=(2*r+3)*E[r+1]**2
        print(f"   r={r}: ratio LHS/RHS={lhs/rhs:.5f}  ({'HOLDS' if lhs<=rhs else 'FAILS'})")
print()
print("=== (b) char-0 version: clean polynomial in n? (compute E_r char-0 closed forms, check the inequality) ===")
# char-0 E_r via big prime
n=16; q=10**9
while not(q%n==1 and isprime(q)): q+=1
E0=energies(q,n,12)
print(f" char-0 (n={n}): E_2..E_8 = "+", ".join(str(E0[r]) for r in range(2,9)))
print(" char-0 monotonicity gap G(r)=(2r+3)E_{r+1}^2-(2r+1)E_r E_{r+2} (>=0 needed):")
for r in range(2,8):
    G=(2*r+3)*E0[r+1]**2-(2*r+1)*E0[r]*E0[r+2]
    print(f"   r={r}: G={G}  ratio={(2*r+1)*E0[r]*E0[r+2]/((2*r+3)*E0[r+1]**2):.5f}  {'OK' if G>=0 else 'NEG'}")
print()
print("=> if char-0 G(r)>0 for all r, the char-0 monotonicity is a polynomial inequality (provable from")
print("   the E_r closed forms). The char-p version adds the wraparound; preservation is the remaining step.")
