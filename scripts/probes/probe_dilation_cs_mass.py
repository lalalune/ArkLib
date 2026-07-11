import cmath, math
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if (q-1)%n==0 and all(q%p for p in range(2,int(q**.5)+1)):
            for g in range(2,q):
                if pow(g,q-1,q)==1 and all(pow(g,(q-1)//pp,q)!=1 for pp in set(f for f in range(2,q) if (q-1)%f==0)):
                    return q,g
        q+=1
def eta(b,G,p): return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in G)
# verify  sum_b |f_b f_zb| <= q|G|  (CS, since sum f_b^2 = sum f_zb^2 = q|G|)
print("verify sum_b |f_b f_zb| <= q|G| (CS bound on total doubling mass = 2T)", flush=True)
for n in [16,32]:
    p,g=primfind(n,3000); z=pow(g,(p-1)//n,p); a=int(math.log2(n))
    for i in range(1,a):
        m=2**i; zz=pow(z,n//m,p); Gi=[pow(zz,j,p) for j in range(m)]; zeta=pow(z,n//(2*m),p)
        S=sum(abs(eta(b,Gi,p).real*eta((b*zeta)%p,Gi,p).real) for b in range(p))
        l2b=sum(eta(b,Gi,p).real**2 for b in range(p))
        print(f"n={n} i={i}->{i+1}: sum|f_b f_zb|={S:.1f}  q|G|={p*m}  sum f_b^2={l2b:.1f}  CS ok: {S<=p*m+1}", flush=True)
