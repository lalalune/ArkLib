import numpy as np, cmath, math
# Probe: (1) orbit-partition identity exactness, (2) coset-reduced r=1 bound vs actual M, thinness-essential check
def mu_n(p, n):
    # n-th roots of unity in F_p^* : need n | p-1
    g = None
    for cand in range(2,p):
        # find element of order p-1 (primitive root) - brute
        order=1; x=cand%p
        while x!=1:
            x=(x*cand)%p; order+=1
            if order>p: break
        if order==p-1:
            g=cand; break
    assert g is not None
    h=pow(g,(p-1)//n,p)  # order n
    return sorted({pow(h,k,p) for k in range(n)})

def eta(p,n,b,G):
    return sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in G)

def rEnergy(G,p,r):
    # E_r = #{(a_1..a_r,a'_1..a'_r) in G^2r : sum a = sum a'} ... use r=1: E_1=#{(a,a'):a=a'}=n? 
    # Actually rEnergy in tree: additive energy. For r=1: #{(a,b,c,d)? } - use moment def: sum_b |eta_b|^2 = q*E_1
    # E_1 = (1/q) sum_b |eta_b|^2. Compute directly.
    tot=0.0
    for b in range(p):
        tot+=abs(eta(p,n,b,G))**(2*r)
    return tot/p

for (p,n,beta) in [(257,4,4.0),(257,8,2.67),(241,8,2.6),(337,16,2.1),(1297,16,2.6),(7681,16,3.25)]:
    if (p-1)%n!=0: 
        print(f"skip p={p} n={n}: n∤p-1"); continue
    G=mu_n(p,n)
    if len(G)!=n: print(f"skip p={p}: |G|={len(G)}"); continue
    Gset=set(G)
    # orbit partition: for b!=0, orbit = {u*b mod p : u in G}. Check eta constant on orbit, orbits partition F^*.
    seen=set(); reps=[]; ok_const=True
    for b in range(1,p):
        if b in seen: continue
        orbit={ (u*b)%p for u in G }
        reps.append(b); seen|=orbit
        vals=[abs(eta(p,n,bb,G)) for bb in orbit]
        if max(vals)-min(vals)>1e-9: ok_const=False
    m=(p-1)//n
    # M = max over b!=0
    M=max(abs(eta(p,n,b,G)) for b in range(1,p))
    # r=1 coset bound: |eta|^2 <= (q*E_1 - n^2)/n
    E1=rEnergy(G,p,1); q=p
    bound2=(q*E1 - n**2)/n
    johnson=math.sqrt(n)  # Johnson ~ sqrt(n)
    prize=math.sqrt(n*math.log(p/n)) if p>n else math.sqrt(n)
    print(f"p={p} n={n} m={m} | orbit-const={ok_const} #reps={len(reps)}(=m?{len(reps)==m}) | M={M:.3f} M/sqrtn={M/math.sqrt(n):.3f} | r=1 cosetbound sqrt={math.sqrt(max(bound2,0)):.3f} | sqrt(n log p/n)={prize:.3f}")
