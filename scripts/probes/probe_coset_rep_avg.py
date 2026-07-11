import cmath, math
def primroot(p):
    for c in range(2,p):
        order=1;x=c%p
        while x!=1:
            x=(x*c)%p;order+=1
            if order>p:break
        if order==p-1:return c
def mu_n(p,n):
    g=primroot(p);h=pow(g,(p-1)//n,p)
    return sorted({pow(h,k,p) for k in range(n)})
def eta(p,n,b,G):
    return sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G)
# EXACT claim: sum_{b!=0}|eta_b|^2 = q*E_1 - n^2, E_1=n => = n(q-n).
# per-orbit n-fold: sum_reps|eta_rep|^2 = (q-n). avg over m reps = (q-n)/m.
for (p,n) in [(257,4),(257,8),(241,8),(337,16),(1297,16),(7681,16),(65537,16),(7681,32)]:
    if (p-1)%n: continue
    G=mu_n(p,n)
    if len(G)!=n: continue
    seen=set();reps=[]
    for b in range(1,p):
        if b in seen:continue
        reps.append(b);seen|={(u*b)%p for u in G}
    m=(p-1)//n
    sumsq_reps=sum(abs(eta(p,n,b,G))**2 for b in reps)
    avg=sumsq_reps/m
    M=max(abs(eta(p,n,b,G)) for b in range(1,p))
    pred=p-n
    print(f"p={p} n={n} m={m} | sum_reps|eta|^2={sumsq_reps:.2f} pred(q-n)={pred} match={abs(sumsq_reps-pred)<1e-6} | avg|eta_rep|^2={avg:.3f} sqrt={math.sqrt(avg):.3f} | M={M:.3f} M^2={M*M:.2f} | M^2/avg={M*M/avg:.3f}")
