import itertools
def isprime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def pfac(n):
    s=set();d=2
    while d*d<=n:
        while n%d==0:s.add(d);n//=d
        d+=1
    if n>1:s.add(n)
    return s
def subgroup(p,n):
    e=(p-1)//n;pf=pfac(n)
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)!=1:continue
        if any(pow(h,n//q,p)==1 for q in pf):continue
        S=set();x=1
        for _ in range(n):x=x*h%p;S.add(x)
        if len(S)==n:return sorted(S)
    return None
def esym(S,p):
    # elementary symmetric e_1..e_k of multiset S mod p, via poly prod (z - x)
    coeffs=[1]  # coeff of z^k down; build prod (z-x): coeffs of monic poly
    for x in S:
        # multiply current poly by (z - x)
        new=[0]*(len(coeffs)+1)
        for i,c in enumerate(coeffs):
            new[i]=(new[i]+c)%p            # z * c
            new[i+1]=(new[i+1]-c*x)%p      # -x * c
        coeffs=new
    # coeffs[i] = coeff of z^{k-i} = (-1)^i e_i  ; so e_i = (-1)^i coeffs[i]
    k=len(S)
    return [ ((-1)**i)*coeffs[i] % p for i in range(k+1) ]  # e_0..e_k
def antipodal(S,p):
    Sset=set(S)
    return all((p-x)%p in Sset for x in S)
print("VERIFY: e_i(S)=0 for ALL odd i<=k  <=>  S antipodal (S=-S),  over mu_n, char-free across primes")
print("(k=|S|; only even k can be antipodal since 0 not in S)\n")
for (n,k) in [(8,4),(16,4),(16,8),(32,4)]:
    for p in [97,113,193,241,257]:
        if (p-1)%n: continue
        S0=subgroup(p,n)
        if S0 is None: continue
        n_eodd0=0; n_anti=0; mismatch=0
        n_eodd0_anti=0
        for S in itertools.combinations(S0,k):
            e=esym(S,p)
            eodd0 = all(e[i]%p==0 for i in range(1,k+1,2))
            anti = antipodal(S,p)
            if eodd0: n_eodd0+=1
            if anti: n_anti+=1
            if eodd0 and anti: n_eodd0_anti+=1
            if eodd0 != anti: mismatch+=1
        status = "EQUIV ✓" if mismatch==0 else f"MISMATCH {mismatch} !!"
        print(f"  n={n:2d} k={k} p={p:3d}: #{{e_odd=0}}={n_eodd0:5d}  #antipodal={n_anti:5d}  both={n_eodd0_anti:5d}  => {status}")
        break  # one prime per (n,k) for speed; remove to sweep all
print("\nIf EQUIV holds for ALL rows (char-free), the crux 'e_odd=0 => antipodal' is PROVEN by the")
print("polynomial-parity argument: e_odd=0 => sigma_S has only exponents ≡ k mod 2 => sigma_S(-z)=(-1)^k sigma_S(z)")
print("=> sigma_{-S}=sigma_S => S=-S.  CHAR-FREE (any char != 2).")
