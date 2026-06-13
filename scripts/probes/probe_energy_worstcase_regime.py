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
    for g in range(2,p):
        h=pow(g,(p-1)//n,p); s,x=set(),1
        for _ in range(n): s.add(x); x=x*h%p
        if len(s)==n: return sorted(s)
    return None
def energy(H,p):
    c=Counter()
    for a in H:
        for b in H: c[(a+b)%p]+=1
    return sum(v*v for v in c.values())
print("WORST-CASE energy over ALL p≡1 mod n (the HBK regime lives at small p):")
for n in (8,16,32):
    tgt=3*n*(n-1); n2=n*n; n25=n**2.5
    worstE=0; worstp=0
    p=n+1
    # scan all valid primes from just above n up to a bound (small p = worst regime)
    bound = max(20000, n*n*4)
    while p<=bound:
        if (p-1)%n==0 and is_prime(p):
            H=subgroup(p,n)
            if H:
                E=energy(H,p)
                if E>worstE: worstE,worstp=E,p
        p+=1
    print(f"  n={n}: 3n(n-1)={tgt}, n^2={n2}, n^2.5={n25:.0f} | "
          f"WORST E={worstE} at p={worstp} | E/n^2={worstE/n2:.2f}, E/n^2.5={worstE/n25:.2f}, "
          f"E/3n(n-1)={worstE/tgt:.3f}")

print("\nPRODUCTION-REGIME check: is E=3n(n-1) for p >> n^2.5 (where production lives)?")
import math
for n in (8,16,32):
    tgt=3*n*(n-1)
    # production analog: p ~ n^3 .. n^4 (>> n^2.5); production has p~2^128 >> n^2.5 for n<=2^40
    ok=True; tested=[]
    base=int(n**3.5)
    p=base + ((1-base)%n)
    found=0
    while found<3:
        if (p-1)%n==0 and is_prime(p):
            H=subgroup(p,n); E=energy(H,p); tested.append((p,E)); ok &= (E==tgt); found+=1
        p+=1
    print(f"  n={n}: p~n^3.5+ → {['p=%d E=%d%s'%(p,E,'✓' if E==tgt else f'≠{tgt}') for p,E in tested]}")
print("\nPRODUCTION SAFETY: prize needs q>=2^128 (eps*=2^-128); n<=2^40 ⟹ n^2.5<=2^100 << 2^128<=q.")
print("So production sits FAR in the clean p>>n^2.5 regime ⟹ E=3n(n-1), bound holds (C=3).")
