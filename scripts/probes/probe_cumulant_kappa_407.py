#!/usr/bin/env python3
"""
#407 — INDEPENDENT verification of the CUMULANT moment claim (lalalune 03:14):
does κ_r = (Σ_i|η_i|^{2r}/m)/((2r−1)!!·n^r) stay ≤ 1 at the optimal depth r*≈ln p, so that the
period sup-norm floor M ≤ √(2n·ln m) follows from M^{2r} ≤ n·Σ_i|η_i|^{2r} = the CUMULANT (the
raw moment's b=0 term n^{2r}/p is M-irrelevant and cancels)?

η_b = Σ_{x∈μ_n} e_p(b·x); constant on cosets ⟹ m=(p-1)/n distinct periods η_i.
GATE (exact): Σ_i|η_i|² must equal p−n. Reports κ_r at r=1..r*, the sup-norm ratio C=M/√(2n ln m),
across generic, FFT-friendly (high 2-adic), and adversarial primes, n=32,64.
"""
import cmath, math

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s

def order_n_gen(p,n):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return pow(h,(p-1)//n,p)
    return None

def v2(m):  # 2-adic valuation of m
    v=0
    while m%2==0: m//=2; v+=1
    return v

def periods(p,n,g):
    """All m=(p-1)/n distinct Gauss periods η_i (one per coset of μ_n in F_p*)."""
    mu=[pow(g,i,p) for i in range(n)]
    # transversal of F_p* / μ_n: take b running, skip those in already-seen cosets
    m=(p-1)//n
    seen=set(); reps=[]
    b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    # compute η for each rep
    etas=[]
    for b in reps:
        s=0j
        for x in mu:
            s+=cmath.exp(2j*cmath.pi*(b*x%p)/p)
        etas.append(abs(s))
    return etas

def find_primes(n, beta, count, fft=False):
    out=[]; lo=int(n**beta); p=lo+(1-lo)%n
    while len(out)<count and p<int(n**(beta+0.5)):
        if is_prime(p):
            if fft and v2(p-1)<int(0.6*math.log2(p)): p+=n; continue
            if (not fft) and v2(p-1)>6: p+=n; continue
            out.append(p)
        p+=n
    return out

def dfac2(r):  # (2r-1)!!
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

print("="*90)
print("CUMULANT κ_r verification: κ_r=(Σ|η_i|^{2r}/m)/((2r-1)!!·n^r) at optimal r*≈ln p")
print("  floor M≤√(2n ln m) holds iff κ_r ≤ ~1 to depth r*.  (gate: Σ|η_i|²=p−n exact)")
print("="*90)
print(f"{'n':>4} {'p':>10} {'β':>5} {'type':>8} {'v2(p-1)':>7} {'m':>8} | {'gate ok':>7} "
      f"{'r*':>3} {'κ@r*':>8} {'κ@r*/2':>8} {'C=M/√(2n ln m)':>14}")
for n in (32,64):
    rows=[]
    for fft,tag in ((False,"generic"),(True,"fft")):
        for p in find_primes(n,4.0,2,fft=fft):
            g=order_n_gen(p,n)
            if g is None: continue
            etas=periods(p,n,g)
            m=len(etas)
            gate=abs(sum(e*e for e in etas)-(p-n))<1e-3*p
            rstar=max(2,int(round(math.log(p))))
            def kap(r): return (sum(e**(2*r) for e in etas)/m)/(dfac2(r)*n**r)
            kr=kap(rstar); kh=kap(max(1,rstar//2))
            M=max(etas); C=M/math.sqrt(2*n*math.log(m))
            rows.append((n,p,math.log(p)/math.log(n),tag,v2(p-1),m,gate,rstar,kr,kh,C))
    # also one adversarial (highest 2-adic / Fermat-like) if available
    for (n_,p,beta,tag,vv,m,gate,rstar,kr,kh,C) in rows:
        print(f"{n_:>4} {p:>10} {beta:>5.2f} {tag:>8} {vv:>7} {m:>8} | {str(gate):>7} "
              f"{rstar:>3} {kr:>8.3f} {kh:>8.3f} {C:>14.3f}")
    print()
print("VERDICT: if κ@r* ≤ ~1 across generic AND fft primes (and decreasing in n), the cumulant")
print("moment route gives the floor M≤√(2n ln m) — the open core is then the ASYMPTOTIC κ_r≤1")
print("(period sub-Gaussianity to depth ln p), measured-supported but not proven. If κ@r*≫1 for")
print("some prime, the route is refuted there.")
