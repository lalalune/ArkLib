import itertools
from collections import Counter

def subgroup_mu_n(p, n):
    assert (p-1) % n == 0
    for cand in range(2, p):
        x=1; order=0
        for _ in range(p):
            x=(x*cand)%p; order+=1
            if x==1: break
        if order==p-1:
            g=cand; break
    h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n):
        S.add(x); x=(x*h)%p
    return sorted(S)

def rEnergy(p,G,r):
    sums=Counter()
    for tup in itertools.product(G,repeat=r):
        sums[sum(tup)%p]+=1
    return sum(c*c for c in sums.values())

def autocorr(p,G,r,d):
    # C_r(d) = #{(v,w) in G^r x G^r : sum v - sum w = d mod p}
    sums=Counter()
    for tup in itertools.product(G,repeat=r):
        sums[sum(tup)%p]+=1
    # count pairs with sv - sw = d
    c=0
    for sv,cv in sums.items():
        sw=(sv-d)%p
        c += cv*sums.get(sw,0)
    return c

for (p,n) in [(7,3),(13,4),(13,6),(17,8),(31,5)]:
    G=subgroup_mu_n(p,n)
    for r in range(0,4):
        Er1=rEnergy(p,G,r+1)
        Er=rEnergy(p,G,r)
        # cross_r = sum_{s != t in G} C_r(t-s)
        cross=0
        for s in G:
            for t in G:
                if s!=t:
                    cross += autocorr(p,G,r,(t-s)%p)
        rhs = n*Er + cross
        ok = (Er1==rhs)
        print(f"p={p} n={n} r={r}: E_{{r+1}}={Er1} n*E_r+cross={rhs} (n*E_r={n*Er}, cross={cross}) {'OK' if ok else 'MISMATCH'}")

print("\n=== autocorrelation diagonal bound C_r(d) <= C_r(0) = E_r ===")
for (p,n) in [(7,3),(13,4),(17,8)]:
    G=subgroup_mu_n(p,n)
    for r in range(1,4):
        C0=autocorr(p,G,r,0)
        Er=rEnergy(p,G,r)
        maxd=max(autocorr(p,G,r,d) for d in range(p))
        print(f"p={p} n={n} r={r}: C_r(0)={C0} E_r={Er} max_d C_r(d)={maxd}  C0==E_r:{C0==Er} maxd<=C0:{maxd<=C0}")
