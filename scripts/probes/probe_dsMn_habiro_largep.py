#!/usr/bin/env python3
"""
probe_dsMn_habiro_largep.py  (NOT committed; scratch)

Follow-up to probe_dsMn_habiro_coherence.py at LARGER primes, in/near the prize regime
n ~ p^{1/4}, to test ROBUSTNESS of the "worst frequency is incoherent up the 2-power tower"
finding -- i.e. whether Habiro coherence can give a sub-BGK sup-norm bound.

Decisive measurement (the Habiro hypothesis crux):
  Let C_inf := max_b min_k |eta_b^{(k)}| / sqrt(n_k)      (best COHERENT-worst growth const)
  Let C_top := |eta_{btop}^{(top)}| / sqrt(n_top)         (actual top sup-norm const)
  If Habiro coherence helped, the worst frequency would be a coherent family and
  C_inf ~ C_top.  If C_inf << (growth of M), the constraint "be worst at every level
  simultaneously" is STRICTLY HARDER than being worst at the top => coherence does NOT
  bound M from above; the actual worst freq exploits a single level it doesn't share.

We also fit M(n)/sqrt(n) vs log p across several primes: BGK predicts ~ sqrt(log p).
"""
import cmath, math

def is_prime(p):
    if p<2: return False
    if p%2==0: return p==2
    d=3
    while d*d<=p:
        if p%d==0: return False
        d+=2
    return True

def find_prime_1modn(approx, n):
    p = approx - (approx % n) + 1
    while p < approx: p += n
    while True:
        if is_prime(p): return p
        p += n

def prim_root(p):
    # factor p-1
    m=p-1; fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fs): return g
    raise RuntimeError

def make_tower(p, mu_top):
    n_top=2**mu_top
    g=prim_root(p)
    h_top=pow(g,(p-1)//n_top,p)
    towers={}
    for k in range(1,mu_top+1):
        nk=2**k
        step=pow(h_top,(n_top//nk),p)
        S=set(); x=1
        for _ in range(nk): S.add(x); x=(x*step)%p
        towers[k]=sorted(S)
        assert len(towers[k])==nk
    return towers

def eta_abs(b,S,p):
    z=0j
    for y in S: z+=cmath.exp(2j*math.pi*((b*y)%p)/p)
    return abs(z)

def analyze(p, mu_top, label):
    towers=make_tower(p,mu_top)
    n_top=2**mu_top
    # per-level M and argmax, plus per-b profile (vectorized-ish but p brute force)
    Mk={}; etas={}  # etas[k] = list indexed by b (1..p-1)
    for k in range(1,mu_top+1):
        vals=[0.0]*(p)
        for b in range(1,p):
            vals[b]=eta_abs(b,towers[k],p)
        etas[k]=vals
        Mk[k]=max(vals[1:])
    n=n_top
    M=Mk[mu_top]
    # C_top
    btop=max(range(1,p), key=lambda b: etas[mu_top][b])
    C_top = etas[mu_top][btop]/math.sqrt(n)
    # C_inf: best over b of min_k |eta_b^(k)|/sqrt(nk)
    best_b=None; best=-1
    for b in range(1,p):
        mq=min(etas[k][b]/math.sqrt(2**k) for k in range(1,mu_top+1))
        if mq>best: best=mq; best_b=b
    C_inf=best
    # coherence of top-worst: its min-level normalized quality
    top_minq=min(etas[k][btop]/Mk[k] for k in range(1,mu_top+1))
    # argmax overlap across last two levels
    eps=1e-6
    arg_top=set(b for b in range(1,p) if abs(etas[mu_top][b]-Mk[mu_top])<eps)
    arg_below=set(b for b in range(1,p) if abs(etas[mu_top-1][b]-Mk[mu_top-1])<eps)
    # push arg_below up via butterfly: b and b*om belong to level up; check if argmaxes relate
    overlap=len(arg_top & arg_below)
    print(f"[{label}] p={p} n={n} (p^(1/4)={p**0.25:.1f})")
    print(f"   M(n)={M:.3f}  M/sqrt(n)={C_top:.4f}  M/sqrt(2n ln p)={M/math.sqrt(2*n*math.log(p)):.4f}")
    print(f"   C_top (actual worst, top only) = {C_top:.4f}")
    print(f"   C_inf (best COHERENT-worst, min over all levels /sqrt(nk)) = {C_inf:.4f}  at b={best_b}")
    print(f"   ratio C_inf/C_top = {C_inf/C_top:.4f}   (1 => coherence reaches the worst; <1 => incoherent)")
    print(f"   top-worst b={btop}: its WEAKEST-level quality min_k |eta|/M_k = {top_minq:.4f}")
    print(f"   |argmax overlap top vs below| = {overlap}  (of {len(arg_top)} top, {len(arg_below)} below)")
    return (math.log(p), C_top)

def main():
    pts=[]
    # several primes, mu_top scaled so n is meaningful vs p
    configs=[
        (find_prime_1modn(1100,32), 5, "p~1k n32"),
        (find_prime_1modn(4200,64), 6, "p~4k n64"),
        (find_prime_1modn(17000,64), 6, "p~17k n64"),
        (find_prime_1modn(70000,64), 6, "p~70k n64"),
    ]
    for p,mu,lab in configs:
        pts.append(analyze(p,mu,lab))
        print()
    print("M/sqrt(n) vs log p (BGK predicts growth ~ sqrt(log p)):")
    for lp,c in pts:
        print(f"   log p = {lp:.3f}  M/sqrt(n) = {c:.4f}   C/sqrt(log p) = {c/math.sqrt(lp):.4f}")

if __name__=="__main__":
    main()
