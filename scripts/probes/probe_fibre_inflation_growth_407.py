#!/usr/bin/env python3
"""
#407 — Does the char-p subset-sum max-FIBRE inflate above char-0 N_fib, and does the
inflation GROW with n?  (Decides whether prizeDeltaStar = 1-rho-H/log2(B) is the exact
floor, or only a ceiling with a lattice-relation correction.)

FIBRE = list size = worst-case codewords near a word (the operative quantity for the
SHARP delta*, per the in-tree proven ceiling: worst-case list = N_fib(n,r) = C(n/2,r/2)).

fibre(0) over F_p = sum_{c in L, ||c||_inf<=1} C(n/2 - w(c), (r-w(c))/2),  L = lattice of
relations sum_i c_i g^i = 0 mod p.  The c=0 term is the char-0 N_fib = C(n/2, r/2);
nonzero short relations are the INFLATION.

This probe:
  (1) validates the relation-sum inflation formula vs EXHAUSTIVE enumeration (n=32);
  (2) measures the inflation factor F = fibre_p(0)/N_fib at a fixed relative radius,
      worst over primes, for n = 32,64,128,256 -> does F grow?
  (3) reports w_min and the implied delta* shift.
"""
import itertools, math
from collections import defaultdict

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
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

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def find_primes_for_n(n, beta=3.5, count=8):
    lo=int(n**beta); lo += (1-lo)%n
    out=[]; p=lo
    while len(out)<count and p < n**(beta+1.0):
        if is_prime(p) and not ((p-1)&(p-2))==0:
            out.append(p)
        p+=n
    return out

def order_n_generator(p,n):
    fac=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in fac):
            return pow(h,(p-1)//n,p)
    raise RuntimeError

def relation_weight_counts(p,g,half,wmax):
    """N_w = #{c in {-1,0,1}^half : w(c)=w, sum c_i g^i = 0 mod p}, for 1<=w<=wmax.
    Meet in the middle, per-side weight <= ceil(wmax/2)."""
    powg=[pow(g,i,p) for i in range(half)]
    A=half//2
    side_cap=(wmax+1)//2
    def side(coords):
        res=defaultdict(lambda: defaultdict(int)); res[0][0]=1
        for w in range(1,side_cap+1):
            for supp in itertools.combinations(coords,w):
                base=[powg[i] for i in supp]
                for signs in itertools.product((1,-1),repeat=w):
                    v=0
                    for s,b in zip(signs,base): v=(v+s*b)%p
                    res[v][w]+=1
        return res
    L=side(list(range(A))); R=side(list(range(A,half)))
    N=defaultdict(int)
    for val,wdL in L.items():
        wdR=R.get((-val)%p)
        if wdR:
            for wl,cl in wdL.items():
                for wr,cr in wdR.items():
                    w=wl+wr
                    if 1<=w<=wmax: N[w]+=cl*cr
    return dict(sorted(N.items()))

def inflation_from_relations(N, half, r):
    """fibre_p(0)/N_fib - 1 = sum_w N_w * C(half-w,(r-w)/2) / C(half, r/2),
    over w with r-w even, 0<=(r-w)/2<=half-w."""
    if r%2!=0: return None  # use even r (v=0 fibre, antipodal main term)
    main=math.comb(half, r//2)
    infl=0
    for w,cnt in N.items():
        if (r-w)%2==0 and 0<=(r-w)//2<=half-w:
            infl += cnt*math.comb(half-w,(r-w)//2)
    return infl/main, main, infl

def exhaustive_fibre0(n,p,g,r):
    """EXACT fibre_p(0)=#{S:|S|=r, sum_S =0 mod p} and char-0 N_fib=C(n/2,r/2)."""
    half=n//2; powg=[pow(g,j,p) for j in range(n)]
    cnt0=0
    for S in itertools.combinations(range(n),r):
        if sum(powg[j] for j in S)%p==0: cnt0+=1
    return cnt0, math.comb(half, r//2)

# ---------------------------------------------------------------------------
print("="*78)
print("(1) VALIDATION: relation-sum inflation vs EXHAUSTIVE fibre_p(0), n=32")
print("="*78)
n=32; half=16
p=order=None
ps=find_primes_for_n(32,beta=3.5,count=3)
for p in ps:
    g=order_n_generator(p,n)
    N=relation_weight_counts(p,g,half,wmax=12)
    print(f"  p={p}  w->N_w: {N}")
    for r in (6,8,10):
        ex0,nfib=exhaustive_fibre0(n,p,g,r)
        approx=inflation_from_relations(N,half,r)
        if approx:
            f_approx=1+approx[0]
            print(f"    r={r:2d}: N_fib={nfib:6d}  exhaustive fibre_p(0)={ex0:6d} (F={ex0/nfib:.3f})"
                  f"   relation-sum F={f_approx:.3f}  {'OK' if abs(ex0/nfib-f_approx)<0.02 else 'MISMATCH(higher-wt tail)'}")

print()
print("="*78)
print("(2) INFLATION GROWTH: F = fibre_p(0)/N_fib at relative radius r=half/2,")
print("    WORST over primes.  Does F grow with n?  (n grows, beta=3.5 fixed)")
print("="*78)
print(f"{'n':>4} {'half':>4} {'r':>3} | {'w_min':>5} {'#prime':>6} {'F_med':>7} {'F_max':>7} {'F_min':>7}  worst-p")
for n in (32,64,128,256):
    half=n//2; r=half//2
    if r%2: r+=1
    wmax = 12 if half<=16 else (10 if half<=32 else 8)
    ps=find_primes_for_n(n,beta=3.5,count=8)
    Fs=[]; wmins=[]; worst=(0,None)
    for p in ps:
        g=order_n_generator(p,n)
        N=relation_weight_counts(p,g,half,wmax=wmax)
        wmins.append(min(N) if N else 99)
        approx=inflation_from_relations(N,half,r)
        F=1+approx[0] if approx else 1.0
        Fs.append(F)
        if F>worst[0]: worst=(F,p)
    Fs.sort()
    med=Fs[len(Fs)//2]
    print(f"{n:>4} {half:>4} {r:>3} | {min(wmins):>5} {len(ps):>6} {med:>7.3f} {max(Fs):>7.3f} {min(Fs):>7.3f}  p={worst[1]} F={worst[0]:.3f}")

print()
print("="*78)
print("(3) Implied delta* shift.  At budget B, char-0 crossover r0: N_fib(r0)~B.")
print("    char-p crossover r_p: N_fib(r_p)*F(r_p)~B.  delta* = 1 - r/n.  shift = (r_p-r0)/n.")
print("    (illustrative at B=n, full subgroup s=n)")
print("="*78)
for n in (64,128,256):
    half=n//2; B=n
    ps=find_primes_for_n(n,beta=3.5,count=6)
    # worst prime by inflation at mid radius
    best=None
    for p in ps:
        g=order_n_generator(p,n)
        wmax = 10 if half<=32 else 8
        N=relation_weight_counts(p,g,half,wmax=wmax)
        # find char-0 crossover r0: largest even r with C(half,r/2) <= B
        r0=0
        for r in range(2,half+1,2):
            if math.comb(half,r//2)<=B: r0=r
            else: break
        # char-p crossover
        rp=0
        for r in range(2,half+1,2):
            ap=inflation_from_relations(N,half,r)
            fib=math.comb(half,r//2)*(1+ap[0]) if ap else math.comb(half,r//2)
            if fib<=B: rp=r
            else: break
        shift=(rp-r0)/n
        cand=(shift,p,r0,rp,min(N) if N else 99)
        if best is None or shift>best[0]: best=cand
    sh,p,r0,rp,wm=best
    print(f"  n={n:4d}: worst-p={p}  w_min={wm}  char-0 r0={r0} (delta*={1-r0/n:.4f})"
          f"  char-p r_p={rp} (delta*={1-rp/n:.4f})  shift={sh:.4f} ~ {sh*math.log2(n):.2f}/log2(n)")
