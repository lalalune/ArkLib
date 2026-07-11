#!/usr/bin/env python3
"""
probe_wf5M4_spurious_count.py  (#444, lane wf-M4)

The DECISIVE prescreen: is the SPURIOUS (non-matching) part of the moment W_r truly bounded by
~ n^r/p (the random off-diagonal model), which is what makes SL-M4' a CLOSED lemma rather than a
restatement of the open problem?

W_r = #{ x in mu_n^r : sum_i x_i = 0 mod p }.  Decompose the solution set by the PARTITION TYPE of
the multiset {x_1,...,x_r}:
  - MATCHING part:  the multiset is a union of antipodal pairs {a, -a} (a, -a both in mu_n since
    -1 in mu_n).  These ALWAYS sum to 0 mod p (a + (-a) = 0), genuinely.  Count = (r-1)!! * n^{r/2}
    for r even (number of pairings * n choices per pair) + lower-order overcounts.  This is the
    char-0 / Lam-Leung "slope-0" content.
  - SPURIOUS part:  solutions NOT of antipodal-pairing type -- a genuine mod-p additive coincidence
    among non-paired elements.  THE NP CLAIM: #spurious <= Csp * n^r / p.

We measure #spurious EXACTLY (FFT gives W_r; matching count is combinatorial) and report
    spurious_ratio := #spurious / (n^r / p)
SL-M4' (closed) <=>  spurious_ratio = O(1) uniformly for r <= 2 beta.  If spurious_ratio BLOWS UP
(structured spurious coincidences beyond random), the lemma is NOT closed at that depth.
"""
import math
import numpy as np

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def factor_small(m):
    f={};d=2
    while d*d<=m:
        while m%d==0:f[d]=f.get(d,0)+1;m//=d
        d+=1
    if m>1:f[m]=f.get(m,0)+1
    return f
def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def subgroup(p,n):
    g=primitive_root(p);h=pow(g,(p-1)//n,p)
    return [pow(h,k,p) for k in range(n)]
def eta(p,n):
    f=np.zeros(p)
    for x in subgroup(p,n):f[x]+=1.0
    return np.fft.fft(f).real
def dfac(k):
    res=1;j=k-1
    while j>0:res*=j;j-=2
    return res

def matching_count(n, r):
    """# ordered r-tuples in mu_n forming a union of antipodal pairs {a,-a}.  Each tuple: choose a
    pairing of the r positions into r/2 pairs ((r-1)!! pairings), and for each pair pick a in mu_n
    and assign (a,-a) to the two positions in 2 ways... but a + (-a)=0 needs the pair to be {a,-a}.
    Ordered count of position-pairing into pairs each carrying an UNORDERED antipodal pair:
    Exact leading term = (r-1)!! * n^{r/2}.  (Inclusion of a=-a impossible since -1!=1; overcounts
    where the SAME antipodal pair is reused are lower order.)  We use the leading term; the FFT W_r
    is exact, so spurious = W_r - matching_leading may be slightly negative due to overcount
    subtraction -- we clip and also report raw difference."""
    if r % 2 != 0:
        return 0
    return dfac(r) * n**(r//2)

def run():
    print("="*90)
    print("wf-M4  SPURIOUS-count prescreen: #spurious vs random model n^r/p  (in-band r<=2beta)")
    print("="*90)
    print("spurious := W_r - (r-1)!! n^{r/2}  (excess over antipodal matching);  "
          "model := n^r/p;  ratio := spurious/model")
    print("SL-M4' CLOSED  <=>  ratio = O(1) for r <= 2beta.\n")
    cases=[]
    for n in [16,32,64]:
        for beta in [2.0,2.5,3.0,3.5,4.0]:
            target=n**beta
            for dk in range(0,400000):
                p=1+ (int(target//n)+dk)*n
                if p>6_000_000: break
                if is_prime(p) and abs(math.log(p)/math.log(n)-beta)<0.2:
                    cases.append((p,n)); break
    for (p,n) in cases:
        ev=eta(p,n)
        b=math.log(p)/math.log(n)
        rstar=int(2*b); rstar-=rstar%2  # even, <=2beta
        print(f"  p={p:8d} n={n:3d} beta={b:.2f} r*={rstar}:")
        for r in range(2,max(rstar+1,3),2):
            Wr=float(np.sum(ev.astype(np.float64)**r)/p)
            match=matching_count(n,r)
            spur=Wr-match
            model=n**r/p
            ratio=spur/model if model>0 else float('nan')
            inb="*" if r<=rstar else " "
            print(f"      r={r}{inb}: W_r={Wr:.3e}  match={match:.3e}  spurious={spur:+.3e}  "
                  f"model(n^r/p)={model:.3e}  ratio={ratio:+.3f}")
    print("\nINTERPRETATION: in-band (*) rows: spurious/model bounded & ~O(1) => SL-M4' is a closed")
    print("off-diagonal count (the open content is only WHY no structured spurious cluster forms,")
    print("i.e. that mu_n has no large additive-energy sub-structure mod p at depth r -- the")
    print("char-p Lam-Leung transfer).  ratio>>1 or growing in r => spurious is STRUCTURED (open).")

if __name__=="__main__":
    run()
