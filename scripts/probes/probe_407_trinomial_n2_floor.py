# Verify the CLEAN trinomial: g(X) = (X^{n/4} - 1)(X^{n/4} - i) = X^{n/2} - (1+i) X^{n/4} + i
# where i = zeta^{n/4} is a primitive 4th root. Support {0, n/4, n/2} (3 terms). Roots in mu_n:
# X^{n/4} in {1, i}. #roots = #{j<n : (zeta^j)^{n/4} in {1,i}}.
# (zeta^j)^{n/4} = (zeta^{n/4})^j = i^j (order 4) => i^j in {1,i} iff j ≡ 0 or 1 mod 4 => n/2 of them.
from sympy import isprime, primitive_root

def primes_for(n, count=3, beta=4):
    target=n**beta; p=((target//n)+1)*n+1; out=[]
    while len(out)<count:
        if isprime(p) and (p-1)//n>=2: out.append(p)
        p+=n
    return out

for mu in [3,4,5,6]:
    n=2**mu
    for p in primes_for(n,2):
        gen=primitive_root(p);m=(p-1)//n
        zeta=pow(gen,m,p)  # primitive n-th root
        i=pow(zeta,n//4,p) # primitive 4th root
        # g(X)=X^{n/2} - (1+i)X^{n/4} + i, evaluate over mu_n
        cnt=0; res=[]
        for j in range(n):
            x=pow(zeta,j,p)
            val=(pow(x,n//2,p) - ((1+i)%p)*pow(x,n//4,p) + i) % p
            if val==0:
                cnt+=1; res.append(j)
        # also confirm i^j in {1,i} <=> j%4 in {0,1}
        predicted=[j for j in range(n) if j%4 in (0,1)]
        print(f"n={n} p={p}: #roots of (X^(n/4)-1)(X^(n/4)-i) in mu_n = {cnt} (n/2={n//2}), roots==(j%4 in 0,1)? {res==predicted}")
