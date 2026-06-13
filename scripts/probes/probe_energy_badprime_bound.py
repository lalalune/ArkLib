from collections import Counter
def is_prime(x):
    if x<2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x%w==0: return x==w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(w,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True
def subgroup(p,n):
    for g in range(2,200):
        h=pow(g,(p-1)//n,p); s,x=set(),1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    raise RuntimeError
def energy(p,n):
    H=subgroup(p,n); c=Counter()
    for a in H:
        for b in H: c[(a+b)%p]+=1
    return sum(v*v for v in c.values())
n=32; target=3*n*(n-1)
print(f"n=32, target 3n(n-1)={target}, n^2={n*n}, Cn^2 bound check (HBK worst ~n^2.5={int(n**2.5)})")
for p in (21523361, 156353, 65537, 4129, 50177):  # bad primes incl. the max
    assert is_prime(p) and (p-1)%n==0, (p, is_prime(p), (p-1)%n)
    E=energy(p,n)
    print(f"  p={p:>9} (bad): E={E:>6}  surplus +{E-target:<5}  E/n^2={E/n**2:.3f}  "
          f"{'BOUND HOLDS (E<4n^2)' if E<4*n*n else 'BOUND STRESSED'}")
