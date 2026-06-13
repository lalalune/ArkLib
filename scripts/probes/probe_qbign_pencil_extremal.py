#!/usr/bin/env python3
"""
probe_qbign_pencil_extremal.py  (issue #389)

GENUINE q>>n prize-regime test (no S_w enumeration -> reaches q>>n): for RS[mu_n,k] over F_q with
q>>n, compute #bad directly per pencil (u0,u1) = #{gamma : maxagreement(u0+gamma*u1, RS[k]) >= a},
comparing the worst MONOMIAL pencil (x^b,x^c) against sampled NON-monomial pencils.

RESULT at RS[mu_8,k=4]/F_257 (q/n=32, incidence/q small = prize-like):
  w=3 ABOVE Johnson (delta=0.375>J=0.293): I_mono=40 (x^4,x^5), non-mono=55, ALL 47 samples beat
      -> monomials NOT extremal above Johnson, by a CONSTANT factor (~1.4x), even at q>>n.
  w=2 below Johnson: I_mono=4, non-mono=2, monomials extremal.
Consistent pattern (both q~n and q>>n): mono extremal BELOW Johnson, non-mono win ABOVE Johnson.
=> NubsCarson's worst-over-monomials closed form n*C(n/4,2)+1 is the right ORDER (~n^3/32) but is
beaten by non-monomials by O(1); whether that O(1) is sub-exponential in n (=> same delta* to leading
order) is the open trend question.
"""
import itertools, random
# q >> n prize-like test: monomial vs non-monomial pencils, #bad computed DIRECTLY (no S_w enum).
def inv(a,q): return pow(a,q-2,q)
def rou(q,n):
    for g in range(2,q):
        x=1;s=set()
        for _ in range(q-1): x=x*g%q;s.add(x)
        if len(s)==q-1: o=pow(g,(q-1)//n,q);return [pow(o,i,q) for i in range(n)]
def interp_fit(pts_idx, mu, vals, q, k):
    # Lagrange interpolate deg<k poly through k points (pts_idx), return poly-values at all mu, or None
    xs=[mu[i] for i in pts_idx]; ys=[vals[i] for i in pts_idx]
    # build coeffs via Lagrange eval at each domain point
    res=[0]*len(mu)
    for t in range(len(mu)):
        xt=mu[t]; acc=0
        for j in range(k):
            num=1;den=1
            for l in range(k):
                if l!=j:
                    num=num*(xt-xs[l])%q; den=den*(xs[j]-xs[l])%q
            acc=(acc+ys[j]*num*inv(den,q))%q
        res[t]=acc
    return res
def maxagree(mu,vals,q,k,n):
    best=0
    for sub in itertools.combinations(range(n),k):
        f=interp_fit(sub,mu,vals,q,k)
        c=sum(1 for i in range(n) if f[i]==vals[i])
        if c>best: best=c
    return best
def nbad(mu,u0,u1,q,k,n,a):
    # #{gamma : maxagree(u0+gamma u1) >= a}.  But iterating all q gammas is too many for q=257? 257 ok.
    c=0
    for g in range(q):
        v=[(u0[i]+g*u1[i])%q for i in range(n)]
        if maxagree(mu,v,q,k,n)>=a: c+=1
    return c
def isfar(mu,u1,q,k,n,a):
    return maxagree(mu,u1,q,k,n) < a   # u1 itself not within radius (coset far-ish)
def run(q,n,k,w,nsamp=60):
    mu=rou(q,n); a=n-w; J=1-(k/n)**0.5; d=w/n
    # monomial pencils (x^b, x^c)
    monwords=[[pow(mu[i],e,q) for i in range(n)] for e in range(n)]
    Imono=0; marg=None
    for b in range(n):
        for c in range(n):
            if b==c: continue
            u1=monwords[c]
            if not isfar(mu,u1,q,k,n,a): continue
            nb=nbad(mu,monwords[b],u1,q,k,n,a)
            if nb>Imono: Imono,marg=nb,(b,c)
    # non-monomial pencils (random)
    rng=random.Random(3); Isamp=0; beats=0; tried=0; sarg=None
    for _ in range(nsamp):
        u0=[rng.randrange(q) for _ in range(n)]; u1=[rng.randrange(q) for _ in range(n)]
        if not isfar(mu,u1,q,k,n,a): continue
        tried+=1; nb=nbad(mu,u0,u1,q,k,n,a)
        if nb>Isamp: Isamp,sarg=nb,(u0,u1)
        if nb>Imono: beats+=1
    print(f"n={n} q={q} k={k} (rho={k/n:.2f} q/n={q/n:.0f}) w={w} d={d:.3f} {'ABOVE-J' if d>J else 'below-J'} J={J:.3f} a={a}")
    print(f"   I_mono = {Imono}  (pencil x^{marg[0]},x^{marg[1]})   incidence/q = {Imono/q:.3f}")
    print(f"   I_nonmono(sampled {tried}) = {Isamp}   #beating mono = {beats}")
    print(f"   -> {'NON-MONO BEATS (mono not extremal)' if beats>0 else 'monomials extremal over samples'}\n")
print("q>>n prize-like test (incidence/q small = prize-like):\n")
run(257,8,4,3)   # q/n=32, above Johnson
run(257,8,4,2)   # control smaller radius
print("done")
