import itertools, cmath, math
def Nmax(n, k):
    h=n//2
    roots=[cmath.exp(2j*math.pi*e/n) for e in range(n)]
    odd=[j for j in range(1,n) if math.gcd(j,n)==1]
    best=0; bestw=None
    # reduced w in Z^h, sum|w|<=k, parity k, w!=0
    def gen(pos, rem, cur):
        if pos==h:
            if rem>=0 and (k-rem)%2==0 and any(cur):
                yield tuple(cur)
            return
        for val in range(-rem, rem+1):
            cur.append(val)
            yield from gen(pos+1, rem-abs(val), cur)
            cur.pop()
    for w in gen(0,k,[]):
        pr=1.0
        for j in odd:
            s=sum(w[a]*roots[(a*j)%n] for a in range(h))
            pr*=abs(s)
        nm=round(pr)
        if nm>best: best=nm; bestw=w
    return best,bestw
print("N_max(k) = max |Norm| of nonzero sum of k signed 2^mu-th roots (deterministic; G_r=0 iff p>N_max(2r))",flush=True)
for n in [8,16]:
    row=[]
    kmax = 12 if n==8 else 10
    for k in range(2,kmax+1,2):
        b,w=Nmax(n,k); row.append((k,b))
    print(f"n={n}: {row}",flush=True)
