#!/usr/bin/env python3
# Fast refutation of WeilIndex-MultiplierWeightedFixedPoint (#444 25-novel doc).
# Exact-identity CLAIM: eta_b = gamma_p(b)*sqrt(2)*eta'_{phi(b)},  gamma_p in mu_8.
# Necessary magnitude consequence (|gamma_p|=1): for EVERY far b there EXISTS b' with
#   |eta_b| = sqrt(2)*|eta'_{b'}|.  An exact identity must satisfy this at all n.
# We compute the FULL spectra |eta_b| (b in F_p^x) and |eta'_{b'}| and test membership.
import numpy as np

def isprime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True
def find_p(n, lo):
    p=lo+((1-lo)%n)
    while not (p%n==1 and isprime(p)): p+=n
    return p
def primroot(p):
    m=p-1; fs=set(); d=2
    while d*d<=m:
        if m%d==0:
            fs.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return 0

def spectrum(S, p):
    # |sum_{x in S} exp(2 pi i b x / p)| for all b in 0..p-1
    b = np.arange(p, dtype=np.float64)
    acc = np.zeros(p, dtype=np.complex128)
    for x in S:
        acc += np.exp(2j*np.pi*(x % p)*b/p)
    return np.abs(acc)

def main():
    sqrt2 = np.sqrt(2.0)
    print("# Refute WeilIndex fiber identity: does every |eta_b| have a sqrt(2)*|eta'| partner?")
    for mu in (3,4):                       # n=8,16  (decisive: exact identity must hold at every n)
        n=2**mu
        p=find_p(n, n**4)
        g=primroot(p); h=pow(g,(p-1)//n,p)
        mun=[pow(h,i,p) for i in range(n)]
        muh=[pow(h,2*i,p) for i in range(n//2)]
        Eb  = spectrum(mun,p)[1:]          # far b in 1..p-1
        Ep  = spectrum(muh,p)[1:]
        # set of |eta'| magnitudes (rounded), and the matching target |eta_b|/sqrt2
        tol=1e-6
        ep_sorted=np.sort(Ep)
        targets=Eb/sqrt2
        # nearest |eta'| to each target via searchsorted
        idx=np.searchsorted(ep_sorted, targets)
        idx=np.clip(idx,1,len(ep_sorted)-1)
        nearest=np.minimum(np.abs(ep_sorted[idx]-targets), np.abs(ep_sorted[idx-1]-targets))
        relgap=nearest/(targets+1e-30)
        misses=int(np.sum(relgap>tol))
        beta=np.log(p)/np.log(n)
        print(f"n={n:3d} p={p:8d} beta={beta:.2f}  max|eta_b|={Eb.max():.4f}  "
              f"sqrt2*max|eta'|={sqrt2*Ep.max():.4f}  "
              f"far-b with NO sqrt(2)-partner: {misses}/{len(Eb)}  "
              f"(worst rel gap {relgap.max():.3g})")
        if Eb.max() > sqrt2*Ep.max()*(1+tol):
            print(f"      -> REFUTED: max|eta_b|={Eb.max():.4f} EXCEEDS sqrt(2)*max|eta'|="
                  f"{sqrt2*Ep.max():.4f}; the worst frequency has no fiber partner. "
                  f"Exact identity eta_b=gamma*sqrt2*eta' is FALSE.")
        elif misses>0:
            print(f"      -> REFUTED: {misses} far frequencies lack any sqrt(2)-magnitude partner.")
        else:
            print(f"      -> magnitude-consistent at n={n}; would need phase (mu_8) check.")

if __name__=='__main__':
    main()
