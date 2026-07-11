"""
DECISIVE TEST of Idea A (Frobenius orbit principle): find a BAD prime (W_r>0), enumerate the wraparound
solutions, compute their orbits under Frobenius sigma_p: x->x^p, and check:
 (1) is W_r EVEN? [proven claim]
 (2) do the orbits have FULL size f=ord(p mod n)? [Conjecture A -> would give f|W_r -> W_r=0 if W_r<f]
 (3) are there FIXED points (orbit size 1)? [obstruction to Conjecture A]
"""
import itertools
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
def primes1modn(n,lo,hi):
    return [p for p in range(lo,hi) if p%n==1 and isprime(p)]
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def E_r_modp(p,n,S,r):
    from collections import Counter
    cc=Counter()
    for combo in itertools.product(S,repeat=r):
        cc[sum(combo)%p]+=1
    return sum(v*v for v in cc.values())
def order_mod(p,n):
    x=p%n;k=1
    while x!=1: x=x*p%n;k+=1
    return k

# work with n=8 (small), enumerate. char-0 E_r via a huge prime.
n=8
bigp=primes1modn(n,10**7,10**7+10000)[0]
Sbig=subgroup(bigp,n)
E2_char0=E_r_modp(bigp,n,Sbig,2)
E3_char0=E_r_modp(bigp,n,Sbig,3)
print(f"n={n}: E_2(char0)={E2_char0}, E_3(char0)={E3_char0} (via p={bigp})")
print()
print("Scanning small primes p=1 mod 8 for wraparound W_r=E_r(F_p)-E_r(char0)>0:")
for p in primes1modn(n,9,2000):
    S=subgroup(p,n)
    if S is None: continue
    f=order_mod(p,n)
    for r,E0 in [(2,E2_char0),(3,E3_char0)]:
        Ep=E_r_modp(p,n,S,r)
        W=Ep-E0
        if W>0:
            # enumerate the wraparound solutions and their Frobenius orbits
            from collections import Counter
            # solutions mod p:
            sols_modp=set()
            for combo in itertools.product(range(n),repeat=2*r):  # indices into S
                xs=[S[i] for i in combo[:r]]; ys=[S[i] for i in combo[r:]]
                if sum(xs)%p==sum(ys)%p:
                    sols_modp.add(combo)
            # char-0 solutions (same but mod bigp)
            sols_c0=set()
            for combo in itertools.product(range(n),repeat=2*r):
                xs=[Sbig[i] for i in combo[:r]]; ys=[Sbig[i] for i in combo[r:]]
                if sum(xs)%bigp==sum(ys)%bigp:
                    sols_c0.add(combo)
            extra=sols_modp-sols_c0  # the wraparound tuples (by index pattern)
            # Frobenius sigma_p on indices: S[i]^p = S[(i*?)]. h^p = h^(p mod n) since h has order n.
            pm=p%n
            def frob(combo): return tuple((i*pm)%n for i in combo)
            # orbit sizes
            seen=set(); orbit_sizes=[]
            for c in extra:
                if c in seen: continue
                orb=set(); cur=c
                while cur not in orb:
                    orb.add(cur); cur=frob(cur)
                seen|=orb
                orbit_sizes.append(len(orb & extra))  # orbit within extra
            from collections import Counter as Ct
            print(f"  p={p} f=ord(p mod {n})={f}, r={r}: W_r={W}, #extra_tuples={len(extra)}, "
                  f"orbit_sizes={dict(Ct(orbit_sizes))}, W even? {W%2==0}, any fixed(size1)? {1 in orbit_sizes}")
