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
def addEnergy(G,p):
    Gs=set(G); E=0
    for a in G:
        for ap in G:
            for c in G:
                d=(a+ap-c)%p
                if d in Gs: E+=1
    return E
# fourth moment: sum_b |eta|^4 = q*E. erase 0: q*E - n^4. partition: = n * sum_reps|eta|^4.
# => sum_reps|eta|^4 = (q*E - n^4)/n. Check exact + see how E scales (thinness-sensitive).
for (p,n) in [(257,4),(257,8),(241,8),(337,16),(1297,16),(7681,16),(65537,16)]:
    if (p-1)%n: continue
    G=mu_n(p,n)
    if len(G)!=n: continue
    seen=set();reps=[]
    for b in range(1,p):
        if b in seen:continue
        reps.append(b);seen|={(u*b)%p for u in G}
    m=(p-1)//n
    E=addEnergy(G,p)
    sum4_reps=sum(abs(eta(p,n,b,G))**4 for b in reps)
    pred=(p*E - n**4)/n
    M=max(abs(eta(p,n,b,G)) for b in range(1,p))
    avg4=sum4_reps/m
    # E for a Sidon set (thin) ~ n^2 (only trivial a+a'=c+c' solutions, ~2n^2-n). thick: E larger.
    print(f"p={p} n={n} m={m} | E={E} E/n^2={E/n**2:.3f} | sum_reps|eta|^4={sum4_reps:.1f} pred={pred:.1f} match={abs(sum4_reps-pred)<1e-3} | avg|eta|^4={avg4:.2f} | M^4={M**4:.1f} M^4/avg4={M**4/avg4:.3f}")
