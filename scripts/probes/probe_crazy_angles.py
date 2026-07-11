"""
CRAZIER angles (#444), data-driven:
(1) NEGATIVE-RESOLUTION: could C(n)=M/sqrt(n log(q/n)) provably DIVERGE? If yes, prize resolves NEGATIVELY
    (delta*=Johnson, DETERMINED). Compute the WORST-prime C over many primes at fixed n -- does the max grow?
(2) STRUCTURED-PRIME HUNT: M across many primes -- is M anomalous for special p (split type, p mod small)?
    An anomalous prime with PROVABLE M would be a wedge.
(3) EXACT C trajectory (full coset enum) n<=32 -- sharpen bounded-vs-diverging.
"""
import math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
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
def M_exact(p,n):
    S=subgroup(p,n)
    g=2
    while pow(g,(p-1)//2,p)==1: g+=1
    m=(p-1)//n
    best=0.0
    for j in range(m):
        b=pow(g,j,p)
        e=sum(math.cos(2*math.pi*(b*x%p)/p) for x in S)
        a=abs(e)
        if a>best: best=a
    return best

print("=== (1)+(3): EXACT M and C over MANY primes at fixed n -- does worst-case C grow? ===")
for n in (8,16):
    ps=primes1modn(n,50*n**4, 25)
    Cs=[]
    for p in ps:
        M=M_exact(p,n); C=M/math.sqrt(n*math.log(p/n)); Cs.append((C,M,p))
    Cs.sort()
    cvals=[c for c,_,_ in Cs]
    print(f" n={n}: over {len(ps)} primes: C in [{min(cvals):.4f}, {max(cvals):.4f}], mean {sum(cvals)/len(cvals):.4f}")
    print(f"        WORST (max C): C={Cs[-1][0]:.4f} M={Cs[-1][1]:.3f} p={Cs[-1][2]}; BEST: C={Cs[0][0]:.4f} p={Cs[0][2]}")
    # is the worst-case C anomalous for a special prime?
    cmax,Mmax,pmax=Cs[-1]
    v2=0;t=pmax-1
    while t%2==0:v2+=1;t//=2
    print(f"        worst prime pmax={pmax}: v2(p-1)={v2}, p mod 16={pmax%16}, p mod 5={pmax%5}, p mod 3={pmax%3}")
print()
print("=== worst-case C across n (the divergence test): does max_p C(n) trend up? ===")
print(f"{'n':>4} {'#primes':>8} {'min C':>8} {'max C':>8} {'mean C':>8}")
for n in (8,16,32):
    cnt = 25 if n<=16 else 8
    ps=primes1modn(n,50*n**4, cnt)
    cvals=[M_exact(p,n)/math.sqrt(n*math.log(p/n)) for p in ps]
    print(f"{n:>4} {len(ps):>8} {min(cvals):>8.4f} {max(cvals):>8.4f} {sum(cvals)/len(cvals):>8.4f}")
print()
print("INTERPRETATION: if max_p C(n) is FLAT/bounded across n -> mildly supports prize TRUE (delta* interior).")
print("If it TRENDS UP -> evidence for divergence (prize FALSE, delta*=Johnson, which would DETERMINE delta*).")
print("Either way, a PROOF of the trend (not just data) is needed = the BGK/Paley wall.")
