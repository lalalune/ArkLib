"""
Machine tests for the most concrete NEW attack vectors (#444).
(V1) T_3 = E_3(mu_n) = O(n^3)? -- the di Benedetto SOTA-beat input (No-Excess r=3). Verify closed form
     E_3 = 15n^3-45n^2+40n EXACTLY for char-0, AND test char-p stability at prize-scale primes (W_3=0?).
(V2) Dyadic-tower exponent: does M(mu_{2n})/M(mu_n) use the index-2 sublattice structure to beat generic?
     Test M(n)^2 vs 2*M(n/2)^2 + cross -- the EXACT recursion, looking for a provable contraction.
(V3) Is there a fold where the WORST direction's list has a closed form (the rigidity sub-goal, exact)?
"""
import itertools, math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
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
def primes1modn(n,lo,cnt):
    out=[];p=lo+(n-lo%n)+1
    while len(out)<cnt:
        if p%n==1 and isprime(p):out.append(p)
        p+=n
    return out
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def E_r(p,n,r):
    """additive energy level r: #{(x_1..x_r,y_1..y_r) in mu_n^{2r}: sum x = sum y mod p}."""
    from collections import Counter
    S=subgroup(p,n)
    sums=Counter()
    for combo in itertools.product(S,repeat=r):
        sums[sum(combo)%p]+=1
    return sum(v*v for v in sums.values())

print("=== (V1) T_3 = E_3(mu_n): is it O(n^3), and does the closed form 15n^3-45n^2+40n hold? ===")
print(f"{'n':>4} {'E_3 (char-0 large p)':>20} {'15n^3-45n^2+40n':>16} {'match?':>7} {'E_3/n^3':>8}")
for n in (4,8,16,32):
    p=primes1modn(n,50*n**4,1)[0]
    e3=E_r(p,n,3)
    cf=15*n**3-45*n**2+40*n
    print(f"{n:>4} {e3:>20} {cf:>16} {str(e3==cf):>7} {e3/n**3:>8.3f}")
print("  => if E_3 = 15n^3-45n^2+40n EXACTLY = O(n^3), the di Benedetto T_3-conditional beat is UNCONDITIONAL")
print("     (the open part is a CHAR-0 PROOF of this closed form for all n -- a concrete, tractable sub-goal).")
print()
print("=== (V1b) char-p stability: W_3 = E_3(F_p) - E_3(char0) at prize-scale primes (is it 0?) ===")
for n in (8,16):
    cf=15*n**3-45*n**2+40*n
    print(f"  n={n}, char-0 E_3={cf}:")
    for p in primes1modn(n,50*n**4,3):
        e3=E_r(p,n,3)
        print(f"    p={p}: E_3(F_p)={e3}, W_3={e3-cf}")
print()
print("=== (V2) dyadic-tower exact recursion M(n)^2 vs 2 M(n/2)^2 (is there a provable contraction?) ===")
def M_of(p,n,S):
    g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n; best=0.0; step=max(1,m//3000)
    for j in range(0,m,step):
        b=pow(g,j,p); e=sum(math.cos(2*math.pi*(b*x%p)/p) for x in S)
        if abs(e)>best: best=abs(e)
    return best
for n in (8,16,32):
    p=primes1modn(n,50*n**4,1)[0]
    S=subgroup(p,n); Sh=S[::2] if len(set(S[::2]))==n//2 else None
    Mn=M_of(p,n,S)
    # mu_{n/2} = squares of mu_n
    Sh=list({pow(x,2,p) for x in S})
    Mh=M_of(p,n//2,Sh)
    print(f"  n={n}: M(n)={Mn:.3f}, M(n/2)={Mh:.3f}, M(n)^2/M(n/2)^2={Mn**2/Mh**2:.3f}  (=2 means no gain; <2 = sub-additive)")
