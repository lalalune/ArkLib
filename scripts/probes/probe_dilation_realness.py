import cmath, math
# Structural probe: is eta_b(mu_{2^i}) REAL for i>=1 (antipodal symmetry -1 in mu_{2^i})?
# And what does that buy in the recursion f_{i+1}=f_i(b)+f_i(zeta b)?
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if (q-1)%n==0 and all(q%p for p in range(2,int(q**.5)+1)):
            for g in range(2,q):
                if pow(g,q-1,q)==1 and all(pow(g,(q-1)//pp,q)!=1 for pp in set(f for f in range(2,q) if (q-1)%f==0)):
                    return q,g
        q+=1
def eta(b,G,p):
    return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in G)
print("check: imag(eta_b) == 0 for mu_{2^i}, i>=1, over many b", flush=True)
for n in [16,32,64]:
    p,g=primfind(n,5000)
    z=pow(g,(p-1)//n,p)
    a=int(math.log2(n))
    worst_imag=0.0
    for i in range(1,a+1):
        m=2**i
        zz=pow(z,n//m,p)
        G=[pow(zz,j,p) for j in range(m)]
        # check -1 in G
        neg1=(p-1)
        has_neg1 = neg1 in G
        for b in range(1,min(p,200)):
            val=eta(b,G,p)
            worst_imag=max(worst_imag,abs(val.imag))
    print(f"n={n} p={p}: max|imag eta_b| over i>=1,b<200 = {worst_imag:.2e}  (-1 in every mu_2^i for i>=1: forces real)", flush=True)
# Now: real-valuedness => cos in recursion is +-1 only? No: f_i(b),f_i(zeta b) both real,
# so their "alignment" is literally a SIGN. Check sign pattern along worst descent.
print("\nSIGN structure: f_i(b) real => recursion is REAL ADDITIVE f_{i+1}=f_i(b)+f_i(zeta b), signs s_i in {+,-}", flush=True)
for n in [16,32,64]:
    p,g=primfind(n,5000)
    z=pow(g,(p-1)//n,p)
    Gtop=[pow(z,i,p) for i in range(n)]
    M=0;bs=1
    for b in range(1,p):
        v=abs(eta(b,Gtop,p))
        if v>M:M=v;bs=b
    a=int(math.log2(n))
    signs=[]
    for i in range(a):
        m=2**i
        zz=pow(z,n//m,p)
        Gi=[pow(zz,j,p) for j in range(m)]
        zeta=pow(z,n//(2*m),p)
        fb=eta(bs,Gi,p).real
        fzb=eta((bs*zeta)%p,Gi,p).real
        s = '+' if fb*fzb>=0 else '-'
        signs.append(s)
    print(f"n={n} M={M:.2f} worst-path level signs (fb*fzb): {''.join(signs)}  (all + would be full alignment=2^a=n; any - is cancellation)", flush=True)
