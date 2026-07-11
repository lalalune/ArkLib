# Gaussian-period decorrelation test: compute all m=(p-1)/n periods of mu_n in F_p,
# check distribution (Gaussian variance n?), max vs sqrt(n log m), correlations.
import cmath, math
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if all(q%p for p in range(2,int(q**.5)+1)) and (q-1)%n==0:
            for g in range(2,q):
                if all(pow(g,d,q)!=1 for d in range(1,q-1)) and pow(g,q-1,q)==1:
                    return q,g
        q+=1
def periods(n,p,g):
    z=pow(g,(p-1)//n,p); G=[pow(z,i,p) for i in range(n)]
    m=(p-1)//n
    # eta_i = S_{g^i}(mu_n), i=0..m-1
    out=[]
    b=1
    for i in range(m):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G)
        out.append(s.real)   # real (negation symmetry)
        b=b*g%p
    return out,m
for (n,lo) in [(8,4000),(16,4000),(32,16000)]:
    p,g=primfind(n,lo)
    eta,m=periods(n,p,g)
    import statistics as st
    mx=max(abs(e) for e in eta)
    var=sum(e*e for e in eta)/m
    pred_max=math.sqrt(2*n*math.log(m))  # sub-Gaussian max of m vars, variance n
    # fraction within tails (Gaussianity rough): kurtosis
    mu=sum(eta)/m
    m2=sum((e-mu)**2 for e in eta)/m
    m4=sum((e-mu)**4 for e in eta)/m
    kurt=m4/(m2*m2)  # Gaussian=3
    print(f"n={n} p={p} m={m}: var={var:.1f}(~n={n}?) max={mx:.2f} sqrt(2n log m)={pred_max:.2f} max/pred={mx/pred_max:.2f} kurtosis={kurt:.2f}(G=3)",flush=True)
