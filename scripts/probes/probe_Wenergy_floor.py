# Door-IV Lane-3 PROBE: additive-energy structure of the worst-b set W.
# Claim to test: beyond the FORCED antipodal coincidences (from -1 in mu_n => W = -W),
# does W carry extra additive structure, or is E(W) pinned at the negation floor?
# E(W) = #{(a,b,c,d) in W^4 : a+b = c+d}.
# Negation-symmetry forces: for every (a,b), (-a,-b) also pairs to -(a+b); and the
# zero-sum class {(a,-a)} has size |W| -> contributes >= |W|^2 trivially? Let's MEASURE
# E(W), the zero-sum-class size Z=#{(a,b):a+b=0}=|W| (since W=-W, each a pairs with -a),
# and compare E(W) to a RANDOM negation-symmetric set of same size in Z_p.
import random
def subgroup(n,p,g):
    s=set();x=1
    for _ in range(n): s.add(x); x=x*g%p
    return s
def primitive_root(p):
    # small p only
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None
def energy(W):
    from collections import Counter
    c=Counter()
    Wl=list(W)
    for a in Wl:
        for b in Wl:
            c[(a+b)]+=1
    return sum(v*v for v in c.values())
def find_worstb_W(n,p,g,tau=0.05):
    import cmath,math
    mu=subgroup(n,p,g)
    # b ranges over coset reps g^j, j=0..(p-1)/n-1 ; eta_b const on mu-cosets
    m=(p-1)//n
    best=-1;vals={}
    for j in range(m):
        b=pow(g,j,p)
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in mu)
        vals[j]=abs(s)
        if abs(s)>best: best=abs(s)
    thr=(1-tau)*best
    Wj=[j for j in vals if vals[j]>=thr]
    # expand each rep j to its full mu-coset, plus negation already inside? include all b with that |eta|
    W=set()
    for j in Wj:
        b=pow(g,j,p)
        for x in mu: W.add(b*x%p)
    return W,best
for (n,p) in [(8,4153),(8,11593),(16,65617)]:
    g=primitive_root(p)
    W,best=find_worstb_W(n,p,g,0.05)
    W=list(W)
    E=energy(W)
    sz=len(W)
    # zero-sum class size (a+b=0): since W=-W, = |W|
    from collections import Counter
    zc=Counter()
    for a in W:
        for b in W: zc[(a+b)%p]+=1
    Z0=zc[0]
    # negation floor model: forced energy from antipodal pairs.
    # Random negation-symmetric baseline of same size:
    def rand_negsym(sz,p):
        S=set()
        while len(S)<sz:
            r=random.randrange(1,p)
            S.add(r); S.add((p-r)%p)
        return list(S)[:sz]
    Es=[]
    for _ in range(8):
        R=rand_negsym(sz,p); Es.append(energy(R))
    Er=sum(Es)/len(Es)
    print(f"n={n} p={p}: |W|={sz}  E(W)={E}  Z0(zero-sum class)={Z0}  E(rand negsym)={Er:.0f}  E(W)/E_rand={E/Er:.3f}  E(W)/|W|^2={E/sz**2:.3f}  trivial_min~{2*sz**2-sz}")
