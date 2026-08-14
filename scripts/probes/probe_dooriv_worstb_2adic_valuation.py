#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — is the WORST-b 2-adic structured? (dyadic refinement of the walled
mod-e argmax question, bdb0405d6)

Prior brick (bdb0405d6): the worst-b argmax coset class c* = dlog(worst-b) mod e is
RANDOM in [0,e) at generic primes (no mod-e selection rule). UNMINED refinement: since
the prize regime is DEFINED by n=2^a (a dyadic tower), the natural structure to look for
is 2-ADIC. Define for the worst b:
   k* = dlog_g(worst-b) mod n   (position of worst-b's coset within mu_n's index group Z_n)
and ask whether v_2(k*) (the 2-adic valuation, i.e. which dyadic SUBTOWER level worst-b
sits in) is structured across many primes, or uniform.

If worst-b consistently lands at a fixed 2-adic level (e.g. always v_2(k*) = a-1, the
"halfway" subtower), that is EXPLOITABLE dyadic structure a non-sum-product method could
grip (it would pin the adversarial coset to one tower rung). If v_2(k*) is uniform over
{0,...,a} with the Haar 2-adic weights (P(v_2=j) ~ 2^-(j+1)), the dyadic-selection hope
is ALSO walled, jointly with the mod-e one.

PROBE-FIRST, EXACT, prize regime: PROPER mu_n (n=2^a, a in [4,7]), p = k*n+1 PRIME with
p >> n^3, MANY primes per n (sample the distribution), incl Fermat-type. NEVER n=q-1.
"""
import math, random
from collections import Counter

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def primes_with_subgroup(n, beta, count):
    """yield up to `count` primes p ~ n^beta, n | p-1, p prime, p >> n^3."""
    target=int(round(n**beta)); k0=max(2,target//n); out=[]
    dk=0
    while len(out)<count and dk<2000000:
        for k in (k0+dk, k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n*n*n and is_prime(p):
                out.append(p)
                if len(out)>=count: break
        dk+=1
    return out

def fac(m):
    f={};d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1;m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def gen(p,F):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in F): return g

def v2(x):
    if x==0: return None  # convention: k*=0 means worst-b in mu_n itself
    v=0
    while x%2==0: x//=2; v+=1
    return v

def worstb_k(p, n):
    """find worst b (max |eta_b|), return k* = dlog_g(b) mod n (its index in Z_n)."""
    F=fac(p-1); g=gen(p,F)
    h=pow(g,(p-1)//n,p)  # generator of mu_n
    mu=[]; x=1
    for _ in range(n): mu.append(x); x=x*h%p
    # |eta_b| is constant on mu_n-cosets => depends only on k=dlog(b) mod n.
    # compute |eta| for one rep per coset: b = g^k, k=0..n-1
    best=-1; bk=None
    for k in range(n):
        b=pow(g,k,p)
        re=im=0.0
        for y in mu:
            ang=2*math.pi*((b*y)%p)/p
            re+=math.cos(ang); im+=math.sin(ang)
        mag=math.hypot(re,im)
        if mag>best: best=mag; bk=k
    return bk, best, g

if __name__=="__main__":
    random.seed(444)
    print("=== Door-(iv) Lane-1: is worst-b 2-ADICALLY structured? ===")
    print("k* = dlog(worst-b) mod n;  v_2(k*) = dyadic subtower level.")
    print("Haar-uniform null: P(v_2=j)=2^-(j+1) for j<a, P(v_2>=a incl 0)=2^-a.\n")
    for a in (4,5,6,7):
        n=2**a
        primes=primes_with_subgroup(n, 4.0, 24)
        vals=[]; ks=[]
        for p in primes:
            k,_,_=worstb_k(p,n)
            ks.append(k); vals.append(v2(k) if k!=0 else 'in_mu')
        cnt=Counter(vals)
        print(f"n={n:3d} (a={a})  {len(primes)} primes  k* values: {sorted(set(ks))[:12]}{'...' if len(set(ks))>12 else ''}")
        # null expectation
        null={}
        for j in range(a):
            null[j]=len(primes)*2**-(j+1)
        null_inmu=len(primes)*2**-a
        print(f"     observed v_2(k*) dist: {dict(cnt)}")
        exp_str=", ".join(f"{j}:{null[j]:.1f}" for j in range(a))
        print(f"     Haar-null expected:    {{{exp_str}, in_mu/top:{null_inmu:.2f}}}")
        # is there a spike at a fixed level beyond null?
        spike=None
        for j in range(a):
            obs=cnt.get(j,0)
            if obs > 2.5*null[j] and obs>=max(3,0.4*len(primes)):
                spike=j
        print(f"     => structured 2-adic spike at a fixed level? {'YES at v_2='+str(spike) if spike is not None else 'NO (consistent with Haar-uniform)'}\n")
    print("=== VERDICT: interpret spike flags. NO spike => dyadic-selection ALSO walled. ===")
