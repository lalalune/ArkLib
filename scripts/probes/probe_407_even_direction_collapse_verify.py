# Adversarially verify ONE extra scalar at p=97, n=16: confirm it is genuinely
# full-domain even-bad (agreement >=6 with deg<4 on mu_16) but NOT half-domain bad
# (agreement <3 with deg<2 on mu_8). Rule out interpolation/counter bug.
import sympy
from itertools import combinations
p=97; n=16; nh=8; k=2
g=sympy.primitive_root(p)
omn=pow(g,(p-1)//n,p); omh=pow(omn,2,p)
dom_n=[pow(omn,i,p) for i in range(n)]
dom_h=[pow(omh,i,p) for i in range(nh)]
assert pow(omn,n,p)==1 and all(pow(omn,d,p)!=1 for d in range(1,n))
assert pow(omh,nh,p)==1 and all(pow(omh,d,p)!=1 for d in range(1,nh))

cprime=k; aprime=k+1
# full even line on mu_16
u0f=[pow(x,2*cprime,p) for x in dom_n]; u1f=[pow(x,2*aprime,p) for x in dom_n]
# half line on mu_8
u0h=[pow(x,cprime,p) for x in dom_h]; u1h=[pow(x,aprime,p) for x in dom_h]

def max_agreement(domain, K, target):
    D=len(domain); best=0
    for sub in combinations(range(D),K):
        xs=[domain[i] for i in sub]; ys=[target[i] for i in sub]
        if len(set(xs))<K: continue
        ag=0
        for i in range(D):
            x=domain[i]; val=0
            for j in range(K):
                num=1;den=1
                for l in range(K):
                    if l==j:continue
                    num=num*((x-xs[l])%p)%p; den=den*((xs[j]-xs[l])%p)%p
                val=(val+ys[j]*num*pow(den,p-2,p))%p
            if val==target[i]%p: ag+=1
        best=max(best,ag)
    return best

gamma=14  # first reported extra scalar
tf=[(u0f[i]+gamma*u1f[i])%p for i in range(n)]
th=[(u0h[i]+gamma*u1h[i])%p for i in range(nh)]
agf=max_agreement(dom_n,2*k,tf)
agh=max_agreement(dom_h,k,th)
print(f"gamma={gamma}, p={p}, n={n}")
print(f"  full-domain even line vs RS[mu_16,4]: max agreement = {agf} (threshold s_full=6 => bad iff >=6: {agf>=6})")
print(f"  half-domain line   vs RS[mu_8,2]:     max agreement = {agh} (threshold s_half=3 => bad iff >=3: {agh>=3})")
print(f"  => REVERSE COLLAPSE {'FAILS (full-bad but half-NOT-bad) CONFIRMED' if agf>=6 and agh<3 else 'does not fail here'}")
# also confirm a couple more
for gamma in [17,21,23]:
    tf=[(u0f[i]+gamma*u1f[i])%p for i in range(n)]
    th=[(u0h[i]+gamma*u1h[i])%p for i in range(nh)]
    agf=max_agreement(dom_n,2*k,tf); agh=max_agreement(dom_h,k,th)
    print(f"  gamma={gamma}: agf={agf}(bad>={6}:{agf>=6}) agh={agh}(bad>={3}:{agh>=3}) "
          f"=> reverse-fails:{agf>=6 and agh<3}")
