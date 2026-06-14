#!/usr/bin/env python3
"""
Tight load-bearing test of TowerSupplySubAverage claim D/E (#389):
  "the GENUINE worst super-code MINIMIZES distance; above Sidon (n-k)-d+ = O(1) gives
   O(1) list advantage."  We test whether a low-coset-weight (min-distance) far direction
   u1 actually beats the monomial/tower direction x^k, and by how much, in the window
   interior at q>>n.   Single case n=8 q=257 k=4 (rho=.5, window (.293,.5)), w=3 -> d=.375.
"""
import itertools, random
def rou(q,n):
    for g in range(2,q):
        x=1;s=set()
        for _ in range(q-1): x=x*g%q;s.add(x)
        if len(s)==q-1: o=pow(g,(q-1)//n,q);return [pow(o,i,q) for i in range(n)]
def maxagree(mu,vals,q,k,n,inv):
    best=0
    for sub in itertools.combinations(range(n),k):
        c=0
        for t in range(n):
            xt=mu[t];acc=0
            for j in range(k):
                num=1;den=1
                for l in range(k):
                    if l!=j: num=num*(xt-mu[sub[l]])%q; den=den*(mu[sub[j]]-mu[sub[l]])%q
                acc=(acc+vals[sub[j]]*num*inv[den%q])%q
            if acc==vals[t]: c+=1
        if c>best: best=c
    return best
def nbad(mu,u0,u1,q,k,n,a,inv):
    c=0
    for g in range(q):
        v=[(u0[i]+g*u1[i])%q for i in range(n)]
        if maxagree(mu,v,q,k,n,inv)>=a: c+=1
    return c

q,n,k,w=257,8,4,3
inv=[0]*q
for x in range(1,q): inv[x]=pow(x,q-2,q)
mu=rou(q,n); a=n-w; J=1-(k/n)**0.5; rho=k/n
mon=[[pow(mu[i],e,q) for i in range(n)] for e in range(n)]
rng=random.Random(7)

# MONOMIAL direction x^k = mon[k] (super-code RS[k+1], MDS). dist = n - maxagree(x^k, RS[k]).
u1mono=mon[k]
dist_mono=n-maxagree(mu,u1mono,q,k,n,inv)
Imono=0
for _ in range(40):
    u0=[rng.randrange(q) for _ in range(n)]
    Imono=max(Imono,nbad(mu,u0,u1mono,q,k,n,a,inv))
for b in range(n):
    Imono=max(Imono,nbad(mu,mon[b],u1mono,q,k,n,a,inv))

# MIN-DISTANCE far directions: enumerate codeword + low-weight error patterns.
# u1 = c + e where c in RS[k], e supported on small set -> coset-min-weight = wt(e) (if < d/2).
# These are the NON-MDS low-distance super-code directions (claim: the real worst).
results=[]
# weight-2,3,4 error directions added to zero codeword (=just the error word itself, far from code)
for wt in [1,2,3]:
    for supp in itertools.combinations(range(n), wt):
        if len(results)>200: break
        e=[0]*n
        for idx,p in enumerate(supp): e[p]=(1+idx)%q or 1
        # ensure e is a genuine far direction (not in code) and far enough: agreement < a
        ag=maxagree(mu,e,q,k,n,inv)
        if ag>=a: continue
        cw=n-ag  # coset min weight of direction e
        results.append((cw,e))
# pick the SMALLEST coset-weight direction (the claimed worst = min distance)
results.sort(key=lambda t:t[0])
# measure incidence of the few smallest-distance directions
print(f"n={n} q={q} k={k} rho={rho:.3f} q/n={q//n} w={w} d={w/n:.3f} (J={J:.3f}, ABOVE-J) a={a}")
print(f"MONOMIAL x^k: coset-dist={dist_mono}  I_mono={Imono}  inc/q={Imono/q:.4f}")
print(f"min-coset-weight far directions (claimed worst):")
seen=set()
tested=0
for cw,e in results:
    key=cw
    if tested>=6: break
    I=0
    for _ in range(40):
        u0=[rng.randrange(q) for _ in range(n)]
        I=max(I,nbad(mu,u0,e,q,k,n,a,inv))
    for b in range(n):
        I=max(I,nbad(mu,mon[b],e,q,k,n,a,inv))
    print(f"   coset-wt={cw}: I={I} inc/q={I/q:.4f}  ratio I/I_mono={I/max(Imono,1):.3f}")
    tested+=1
print("done")
