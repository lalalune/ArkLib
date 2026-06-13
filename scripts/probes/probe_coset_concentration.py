# Validate repCount_sq_card_le_energy: n*r(c)^2 <= E(G) for c != 0, and the sqrt(n) saving.
# G = mu_n in F_p (n | p-1). r(c) = #{y in G : c-y in G}. E(G) = sum_t r(t)^2.
def primes():
    for p in range(5,4000):
        if all(p%d for d in range(2,int(p**0.5)+1)): yield p
def test(n):
    for p in primes():
        if (p-1)%n: continue
        # generator of mu_n
        g=None
        for a in range(2,p):
            if pow(a,n,p)==1 and all(pow(a,n//q,p)!=1 for q in set(f for f in range(2,n+1) if n%f==0 and all(f%d for d in range(2,int(f**0.5)+1)))):
                g=a; break
        if g is None: continue
        G=set(pow(g,i,p) for i in range(n))
        if len(G)!=n: continue
        # rep count over all field elements
        from collections import Counter
        rep=Counter()
        for a in G:
            for b in G:
                rep[(a+b)%p]+=1
        E=sum(v*v for v in rep.values())
        # check n*r(c)^2 <= E for all c != 0; and max r(c), sqrt(E/n)
        maxr=0; ok=True
        for c in range(1,p):
            r=rep.get(c,0)
            if n*r*r > E: ok=False
            maxr=max(maxr,r)
        import math
        return p,n,E,maxr,round(math.sqrt(E/n),2),round(math.sqrt(E),2),ok
    return None
print(f"{'p':>5}{'n':>4}{'E':>8}{'maxr':>6}{'sqrt(E/n)':>11}{'sqrt(E)':>9}  bound_holds  saving")
for n in [4,6,8,10,12,16]:
    r=test(n)
    if r:
        p,n,E,maxr,sen,se,ok=r
        print(f"{p:>5}{n:>4}{E:>8}{maxr:>6}{sen:>11}{se:>9}   {ok!s:>5}      x{round(se/sen,2)}")
