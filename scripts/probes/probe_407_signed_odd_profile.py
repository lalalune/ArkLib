#!/usr/bin/env python3
"""
probe_407_signed_odd_profile.py  (#407/#444 surviving-lane: SIGNED odd moment beyond the Sidon depth)

CONTEXT: the even energy profile E_{2r} is collectively INFLATED in thin (probe_407_even_census, push
6feb11b53) -- wrong sign. The surviving thin advantage is in the ODD/SIGNED object (r_min, d_odd deeper).
Since mu_n is negation-closed (-1 in mu_n for n=2^a>=2), eta_b is REAL, so ODD moments A_r=sum_{b!=0}eta_b^r
are real + sign-sensitive -- the natural place for genuine signed cancellation.

The odd_moment entry (DISPROOF_LOG) established: BELOW the Sidon depth (r < d_odd, zero-sum census W_r=0),
A_r = -n^r RIGID + p-independent (NO info about M). UNPROBED: BEYOND d_odd (W_r>0), A_r is non-rigid --
does the SIGNED cancellation compound FAVORABLY across r (thin |A_r| SMALLER than random => collective
signed suppression, the bootstrap mechanism), or not?

RULE-3 FIX: a random n-subset is NOT negation-closed, so its eta_b is complex + odd moments aren't real.
For a FAIR control I use a NEGATION-CLOSED random control: a random union of n/2 antipodal pairs {+/-x}.
This matches mu_n's negation-closure (the structural feature that makes odd moments real) while randomizing
the rest -- isolating the 2-POWER-subgroup structure from mere negation-closure (rule-3, the right control).

OBJECT measured per odd r:
  A_r(thin) = sum_{b!=0} eta_b^r  (real, mu_n)
  A_r(rand) = median over negation-closed random controls
  Compare |A_r|(thin) vs |A_r|(rand) and the normalized |A_r|/(p * M^r)? NO -- that's the refuted artifact.
  Correct normalization: |A_r| / E_r^{1/2}... actually compare |A_r(thin)|/|A_r(rand)| DIRECTLY (same
  structure control) and |A_r|/sqrt(E_{2r}) (a signed-cancellation efficiency: 1 = no cancellation, 0 = full).
  Signed SUPPRESSION = thin has SMALLER |A_r|/sqrt(E_2r) than the neg-closed random (more cancellation).
"""
import cmath, math, random
from sympy import isprime

def prime_for(n, beta, seed=0, nf=False):
    base=int(round(n**beta)); t=max(2,base//n); tr=0
    while True:
        p=1+n*t
        if isprime(p) and (p-1)//n>1:
            if not nf or ((p-1)//n)%2==1 or (((p-1)//n)&((p-1)//n-1))!=0: return p
        t+=1; tr+=1
        if tr>500000: raise RuntimeError("no prime")

def primroot(p):
    order=p-1; x=order; fac=set(); d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    g=2
    while any(pow(g,order//q,p)==1 for q in fac): g+=1
    return g

def mu_n(p,n):
    m=(p-1)//n; h=pow(primroot(p),m,p); S=[]; cur=1
    for _ in range(n): S.append(cur); cur=cur*h%p
    assert len(set(S))==n and n!=p-1
    # verify negation-closed
    Sset=set(S)
    assert all((p-x) in Sset for x in S), "mu_n not negation-closed?!"
    return S

def neg_closed_random(p,n,rnd):
    # random union of n/2 antipodal pairs {x, p-x}, x in 1..(p-1)/2
    half=[]
    seen=set()
    while len(half) < n//2:
        x=rnd.randrange(1,(p-1)//2+1)
        if x not in seen and (p-x) not in seen:
            seen.add(x); half.append(x)
    S=[]
    for x in half: S.append(x); S.append(p-x)
    assert len(set(S))==n
    return S

def periods_real(S,p):
    # eta_b = sum cos(2pi b x/p) (real, since S negation-closed). b=1..p-1.
    n=len(S); tp=2*math.pi/p; out=[0.0]*p
    for b in range(1,p):
        s=0.0
        for x in S: s+=math.cos(tp*((b*x)%p))
        out[b]=s
    return out

def moments(eta,p):
    # returns dict r-> A_r (signed) for r up to RMAX, and E_{2r}
    pass

def analyze(n,beta,seed,nf=False,RMAX=9,n_rand=5):
    p=prime_for(n,beta,seed,nf)
    eta_thin=periods_real(mu_n(p,n),p)
    rnd=random.Random(seed*977+3)
    rand_etas=[periods_real(neg_closed_random(p,n,rnd),p) for _ in range(n_rand)]
    print(f"\nn={n} beta={beta} p={p} m={(p-1)//n} {'[nf]' if nf else ''}  (neg-closed random control, rule-3)")
    print(f"  {'r':>2} {'|A_r|thin':>14} {'|A_r|rand(med)':>16} {'|At|/|Ar|':>10} {'eff_thin':>9} {'eff_rand':>9}  note")
    # find d_odd for thin (first odd r with A_r != -n^r within tol)
    for r in range(1,RMAX+1):
        At=sum(e**r for e in eta_thin[1:])
        Ars=sorted(sum(e**r for e in re[1:]) for re in rand_etas)
        Ar=Ars[len(Ars)//2]
        E2r_thin=sum(e**(2*r) for e in eta_thin[1:])
        E2r_rand_list=sorted(sum(e**(2*r) for e in re[1:]) for re in rand_etas)
        E2r_rand=E2r_rand_list[len(E2r_rand_list)//2]
        eff_thin=abs(At)/math.sqrt(E2r_thin) if E2r_thin>0 else float('inf')
        eff_rand=abs(Ar)/math.sqrt(E2r_rand) if E2r_rand>0 else float('inf')
        ratio=abs(At)/abs(Ar) if abs(Ar)>1e-9 else float('inf')
        # rigid check: A_r == -n^r ?  (only meaningful odd r below d_odd)
        rigid = (r%2==1 and abs(At-(-(n**r)))/max(1,n**r) < 1e-6)
        note=""
        if r%2==1:
            note = "RIGID A_r=-n^r (below d_odd)" if rigid else "non-rigid (>=d_odd)"
        else:
            note = "even (=energy, inflated -- see 6feb11b53)"
        print(f"  {r:>2} {At:14.2f} {Ar:16.2f} {ratio:10.4f} {eff_thin:9.4f} {eff_rand:9.4f}  {note}")
    print("  [signed SUPPRESSION = thin eff < rand eff at ODD r>=d_odd: thin cancels MORE => helps bootstrap]")

def main():
    print("="*86)
    print("SIGNED ODD moment profile beyond the Sidon depth: thin mu_n vs NEGATION-CLOSED random (rule-3)")
    print("eff = |A_r|/sqrt(E_2r) (signed-cancellation efficiency; smaller=more cancellation). ODD r only is signed.")
    print("="*86)
    for (n,beta,seed,nf) in [(16,4.0,1,False),(16,4.5,2,True),(32,4.0,3,False)]:
        analyze(n,beta,seed,nf)

if __name__=="__main__":
    main()
