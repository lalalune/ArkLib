#!/usr/bin/env python3
"""
Door-(iv) Lane 1 sweep 6 — the SIGNED 4-point connected cumulant of the period field: does the
non-Gaussian part carry PHASE-coherent off-diagonal mass (door-iv crack) or is it the dead E2 again?

My sweep-5 pointer: a surviving door-iv lever must be a 4-point object that does NOT reduce to the
additive energy E2 = the modulus 4th moment. The candidate is the SIGNED connected 4th cumulant of
eta on the multiplicative quotient.

For a complex field z_j (j on the cyclic quotient Z_N, z_j = eta_{g^j}), the 4th moment splits as
  E[z_a z_b zbar_c zbar_d]  (a,b,c,d quotient indices)
The GAUSSIAN (Wick) part is supported on the "diagonal" pairings {a,b}={c,d}; the CONNECTED 4th
CUMULANT is the rest. Specifically the L4 norm of the field minus its Gaussian prediction:
  C4 = E|z|^4  -  2 (E|z|^2)^2        (the one-point connected 4th cumulant; =0 for complex Gaussian)
We already know C4 ~ (K4-2)(E|z|^2)^2 > 0 and = E2-excess (dead). The NEW object is the TRANSLATION-
STRUCTURED connected piece: the lag-correlated 4th cumulant
  T4(k) = E_j[ |z_j|^2 |z_{j+k}|^2 ] - (E|z|^2)^2 - |E_j[z_j zbar_{j+k}]|^2 - |E_j[z_j z_{j+k}]|^2
which for a GAUSSIAN field is identically 0 (Wick: the 2-2 moment is fully determined by the
covariance). A nonzero T4(k) at some lag k, NOT explained by the (already ~0, white) 2-point
covariance, is genuine non-Gaussian PHASE structure = the door-iv candidate.

Measure on the cyclic quotient (proper mu_n, p>>n^3, never n=q-1):
  - the energy-energy lag correlation EE(k) = corr(|z_j|^2, |z_{j+k}|^2)  for small k
  - its Wick prediction (from the 2-pt covariance, which my white-field sweep found ~0)
  - the RESIDUAL T4(k) = EE(k) - Wick(k); is it bounded away from 0 as N grows? (=> phase structure)
EXACT complex arithmetic.
"""
import cmath, math, statistics

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n,beta):
    t=int(round(n**beta)); k0=max(2,t//n)
    for dk in range(0,400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n and is_prime(p): return p
    return None

def subgroup(p,n):
    pm1=p-1; f={}; m=pm1; d=2
    while d*d<=m:
        while m%d==0: f[d]=1; m//=d
        d+=1
    if m>1: f[m]=1
    def isg(g): return all(pow(g,pm1//q,p)!=1 for q in f)
    g=2
    while not isg(g): g+=1
    h=pow(g,pm1//n,p); mu=[]; c=1
    for _ in range(n): mu.append(c); c=c*h%p
    return mu,g

def eta_c(b,mu,p):
    return sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in mu)

def main():
    print("=== signed 4-point connected cumulant (energy-energy lag, Wick-subtracted) ===")
    print(f"{'n':>4} {'p':>10} {'N':>7} {'lag':>4} {'EE(k)':>9} {'cov2_re':>9} {'cov2_an':>9} "
          f"{'T4resid':>9}")
    for n,beta in [(16,4.0),(32,4.0),(64,4.0),(16,4.5)]:
        p=find_prime(n,beta)
        if p is None: continue
        mu,g=subgroup(p,n)
        N=(p-1)//n; cap=min(N,30000)
        z=[]; cur=1
        for j in range(cap):
            z.append(eta_c(cur,mu,p)); cur=cur*g%p
        E2=sum(abs(v)**2 for v in z)/cap   # E|z|^2 (~ n)
        Esq=E2*E2
        for k in (1,2,3):
            # energy-energy: E[|z_j|^2 |z_{j+k}|^2]
            ee=sum((abs(z[j])**2)*(abs(z[(j+k)%cap])**2) for j in range(cap))/cap
            EEcorr=ee - Esq  # connected energy-energy (=0 if energies independent)
            # 2-pt covariances (Wick contributions): "normal" cov <z_j zbar_{j+k}> and "anomalous" <z_j z_{j+k}>
            m=sum(z)/cap
            cov_n=sum((z[j]-m)*((z[(j+k)%cap]-m).conjugate()) for j in range(cap))/cap
            cov_a=sum((z[j]-m)*(z[(j+k)%cap]-m) for j in range(cap))/cap
            wick=abs(cov_n)**2 + abs(cov_a)**2  # Wick prediction for connected EE
            T4=EEcorr - wick
            # normalize by Esq for scale
            print(f"{n:>4} {p:>10} {N:>7} {k:>4} {ee/Esq:>9.4f} {abs(cov_n)/E2:>9.4f} "
                  f"{abs(cov_a)/E2:>9.4f} {T4/Esq:>9.4f}")
    print("\n(Gaussian/Wick field: EE(k)/Esq=1 for k!=0, cov2~0, T4resid~0. |T4resid| bounded away from 0")
    print(" as N grows => genuine non-Gaussian PHASE structure = door-iv candidate.)")

if __name__=="__main__":
    main()
