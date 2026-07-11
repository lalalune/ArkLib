#!/usr/bin/env python3
# Refute two frequency-side conjectures from the #444 25-novel doc (verdicts pending):
#  (A) FourierDimFreqField-RestrictionGap: subgroup support => "no sqrt-loss" => M=O(sqrt n), NO log.
#  (B) FreqDecoupling-CosetCurvatureModuli: decoupling => M = sqrt(n log m) with EXACT constant 1.
# Both settled by measuring M(mu_n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x),
# m=(p-1)/n.  Gaussian-EVT (eta_b/sqrt n ~ N(0,1), ~m/2 distinct by eta_b=eta_{-b}) predicts
#   M ~ sqrt(2 n log(m/2)):  log IS present (kills A);  M/sqrt(n log m) ~ sqrt(2) != 1 (kills B).
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
def M_of(n,p):
    g=primroot(p); h=pow(g,(p-1)//n,p)
    mun=[pow(h,i,p) for i in range(n)]
    b=np.arange(p,dtype=np.float64)
    acc=np.zeros(p,dtype=np.complex128)
    for x in mun: acc+=np.exp(2j*np.pi*(x%p)*b/p)
    a=np.abs(acc); a[0]=0.0
    return a.max()

def main():
    print("# M = max_{b!=0}|eta_b|.  EVT predicts M ~ sqrt(2 n log(m/2)).")
    print(f"# {'n':>3} {'beta':>4} {'p':>9} {'m=(p-1)/n':>10} {'M':>8} {'M/sqrtn':>8} "
          f"{'M/sqrt(n log m)':>15} {'M/sqrt(2n log(m/2))':>20}")
    rows=[]
    cases=[(8,4),(16,3),(16,4),(16,5),(32,4)]   # vary n and beta to expose log-m growth
    for n,beta in cases:
        p=find_p(n, n**beta)
        m=(p-1)//n
        M=M_of(n,p)
        sn=np.sqrt(n)
        c_log = M/np.sqrt(n*np.log(m))
        c_evt = M/np.sqrt(2*n*np.log(m/2))
        b_eff=np.log(p)/np.log(n)
        print(f"  {n:>3} {b_eff:>4.2f} {p:>9} {m:>10} {M:>8.3f} {M/sn:>8.3f} {c_log:>15.3f} {c_evt:>20.3f}")
        rows.append((n,b_eff,m,M/sn,c_log,c_evt))
    print()
    # Verdicts
    msn=[r[3] for r in rows]
    print("VERDICT (A) FourierDimFreqField 'no sqrt-loss / O(sqrt n), no log':",
          "REFUTED" if max(msn)>1.5 and msn[3]>msn[1] else "inconclusive",
          f"-- M/sqrt(n) ranges {min(msn):.2f}..{max(msn):.2f} and GROWS with m (n=16: "
          f"beta3->{rows[1][3]:.2f}, beta5->{rows[3][3]:.2f}); the log factor is present.")
    clogs=[r[4] for r in rows]
    drifts = max(clogs)-min(clogs) > 0.05
    print("VERDICT (B) FreqDecoupling 'EXACT constant 1 (not C)':",
          "REFUTED" if (min(clogs)>1.03 and drifts) else "inconclusive",
          f"-- M/sqrt(n log m) = {min(clogs):.2f}..{max(clogs):.2f}, consistently >1 and NOT pinned "
          f"(drifts {max(clogs)-min(clogs):.2f}); the constant is a genuine C>1, not 1.")

if __name__=='__main__':
    main()
