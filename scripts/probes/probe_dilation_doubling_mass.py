import cmath, math
# Probe: does sign_balance + L2 bound the L-infinity mass on the DOUBLING (+) set?
# Balance: sum_+ f_b f_zb = sum_- |f_b f_zb|  =: T (the "doubling mass").
# L2 at level i: sum_b f_b^2 = q*|G_i| (proven). Also sum_b (f_b f_zb) = 0.
# By Cauchy-Schwarz: |sum_b f_b f_zb over +| <= sqrt(sum f_b^2)*sqrt(sum f_zb^2) = q|G_i|.
# Question: is the WORST-CASE doubling child |f_{i+1}(b*)| controlled by T or just by max?
# Really test: at the worst freq b*, how often is its WHOLE descent +? and what's the
# realized L-inf vs the sqrt(2) floor along the way?
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if (q-1)%n==0 and all(q%p for p in range(2,int(q**.5)+1)):
            for g in range(2,q):
                if pow(g,q-1,q)==1 and all(pow(g,(q-1)//pp,q)!=1 for pp in set(f for f in range(2,q) if (q-1)%f==0)):
                    return q,g
        q+=1
def eta(b,G,p): return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in G)
print("per level i->i+1: T=doubling mass, q|G_i| (L2 total), #all-+ descent freqs so far", flush=True)
for n in [16,32,64]:
    p,g=primfind(n,3000)
    z=pow(g,(p-1)//n,p)
    a=int(math.log2(n))
    allplus=set(range(1,p))  # freqs whose descent has been + at every level so far
    for i in range(1,a):
        m=2**i; zz=pow(z,n//m,p)
        Gi=[pow(zz,j,p) for j in range(m)]
        zeta=pow(z,n//(2*m),p)
        T=0.0
        newplus=set()
        for b in range(1,p):
            prod=eta(b,Gi,p).real*eta((b*zeta)%p,Gi,p).real
            if prod>1e-9:
                T+=prod
                if b in allplus: newplus.add(b)
        allplus=newplus
        print(f"n={n} i={i}->{i+1}: T={T:.1f} q|G_i|={p*m} ratio={T/(p*m):.3f} #all+_sofar={len(allplus)} (/{p-1})", flush=True)
    print(f"   -> n={n}: freqs with FULLY-+ descent to top: {len(allplus)} of {p-1}", flush=True)
