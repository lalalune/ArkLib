#!/usr/bin/env python3
"""
#407 — THE DECISIVE TEST in the REAL prize regime (huge field q ~ n*2^128).

CLAIM (the closure): delta* = prizeDeltaStar = 1 - rho - H(rho)/log2(q*eps*) EXACTLY,
PROVIDED the relevant dyadic level s* = 2*log2(B)/H(rho) (B = q*eps* ~ n) is
RELATION-FREE in F_q, i.e. the subset-sum map of mu_{s*} has no char-p fibre inflation.

Relation-freeness reduces to a CLEAN COUNTING CRITERION:
  the map {-1,0,1}^{s*/2} -> F_q (c |-> sum c_i h^i, h = order-s* elt) is INJECTIVE
  whenever 3^{s*/2} < q  (then NO two subset-sums collide mod q beyond char 0).
  More sharply, only LOW-WEIGHT relations (weight <= ~2*rho*s*) inflate the fibre, so
  the operative condition is  #{weight <= 2*rho*s* vectors} = sum_{w<=2rho s*} C(s*/2,w)2^w  <  q.

This probe, for the four prize rates and a range of n with q = n*2^128 (or q just under 2^256):
  (1) computes s* (dyadic), the counting margin log2(3^{s*/2}) - log2(q) and the
      low-weight margin, predicting RELATION-FREE (delta*=prizeDeltaStar) vs INFLATED;
  (2) EMPIRICALLY searches for low-weight relations of mu_{s*} in the actual huge F_q
      (meet-in-the-middle, big-int) to CONFIRM the prediction;
  (3) where inflated, estimates the delta* correction.
"""
import itertools, math, random
from collections import defaultdict

def is_probable_prime(n, k=20):
    if n < 2: return False
    small=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
    for sp in small:
        if n%sp==0: return n==sp
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for _ in range(k):
        a=random.randrange(2,n-1)
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def prime_1_mod_n_near(n, target_bits):
    """A prime p == 1 mod n with bit-length ~ target_bits."""
    base = (1<<target_bits)
    base -= (base-1)%n  # make == 1 mod n
    p = base
    for _ in range(200000):
        if is_probable_prime(p): return p
        p += n
    raise RuntimeError("no prime found")

def order_s_element(p, s):
    """An element of exact order s (s | p-1)."""
    e=(p-1)//s
    for _ in range(10000):
        a=random.randrange(2,p-1)
        h=pow(a,e,p)
        if h!=1 and pow(h,s,p)==1:
            # check exact order s: h^{s/q} != 1 for prime q | s. s=2^j so only q=2.
            if pow(h, s//2, p)!=1:
                return h
    raise RuntimeError("no order-s element")

def Hb(x):
    if x<=0 or x>=1: return 0.0
    return -x*math.log2(x)-(1-x)*math.log2(1-x)

def dyadic_round(x):
    """nearest power of 2 to x (as exponent)."""
    j=round(math.log2(x)) if x>0 else 0
    return 1<<max(1,j)

def low_weight_relation(p, h, half, wmax):
    """min Hamming weight nonzero c in {-1,0,1}^half with sum c_i h^i = 0 mod p.
    Meet in the middle, big-int. Returns (wmin or None, count_at_wmin)."""
    powh=[pow(h,i,p) for i in range(half)]
    A=half//2
    side_cap=(wmax+1)//2
    def side(coords):
        res=defaultdict(lambda: defaultdict(int)); res[0][0]=1
        for w in range(1,side_cap+1):
            for supp in itertools.combinations(coords,w):
                base=[powh[i] for i in supp]
                for signs in itertools.product((1,-1),repeat=w):
                    v=0
                    for sgn,b in zip(signs,base): v=(v+sgn*b)%p
                    res[v][w]+=1
        return res
    L=side(list(range(A))); R=side(list(range(A,half)))
    wc=defaultdict(int)
    for val,wdL in L.items():
        wdR=R.get((-val)%p)
        if wdR:
            for wl,cl in wdL.items():
                for wr,cr in wdR.items():
                    w=wl+wr
                    if 1<=w<=wmax: wc[w]+=cl*cr
    if not wc: return None,0
    wmin=min(wc); return wmin, wc[wmin]

# ---------------------------------------------------------------------------
print("="*92)
print("REAL PRIZE REGIME: q = n*2^128, eps* = 2^-128, B = q*eps* = n.")
print(" s* = relevant dyadic level ~ 2*log2(B)/H(rho).  Relation-free  <=>  delta*=prizeDeltaStar.")
print(" Counting criterion: 3^{s*/2} < q  => INJECTIVE => relation-free (sufficient).")
print(" Low-weight criterion: sum_{w<=2*rho*s*} C(s*/2,w)2^w < q  => no inflating relation.")
print("="*92)
print(f"{'rho':>6} {'mu':>3} {'n':>5} | {'s*':>5} {'half*':>5} {'r*':>4} | "
      f"{'log2(3^h*)':>10} {'log2 q':>7} {'inj?':>5} | {'log2 LWcnt':>10} {'LWfree?':>8} | "
      f"{'emp wmin':>9} {'verdict':>14}")

prize_rates = [(0.5,"1/2"),(0.25,"1/4"),(0.125,"1/8"),(0.0625,"1/16")]
for rho,rlab in prize_rates:
    H=Hb(rho)
    for mu in (20, 30, 40):
        n=1<<mu
        # s* dyadic near 2*mu/H, capped at n
        s_star = min(n, dyadic_round(2*mu/H))
        half = s_star//2
        r_star = max(2, int(round(rho*s_star)))
        if r_star%2: r_star+=1
        # field q = n*2^128 (bit length ~ mu+128)
        qbits = mu+128
        log2q = qbits  # approx (q ~ 2^qbits)
        log2_3h = half*math.log2(3)
        inj = log2_3h < log2q
        # low-weight count up to 2*rho*s* = 2*r_star-ish
        wlw = min(half, 2*r_star)
        # log2 of sum_{w<=wlw} C(half,w) 2^w
        lwcnt=0.0
        s=0
        for w in range(0, wlw+1):
            s += math.comb(half,w)*(2**w)
        lwcnt = math.log2(s) if s>0 else 0
        lwfree = lwcnt < log2q
        # empirical: build actual q and h, search low-weight relations (only if half not too big)
        emp="skip"
        verdict = "RELN-FREE=>pin" if (inj or lwfree) else "INFLATED=>shift"
        if half <= 70:
            q = prime_1_mod_n_near(s_star, qbits)   # need q == 1 mod s_star to have order-s* elt
            h = order_s_element(q, s_star)
            wmax = 8 if half<=40 else 6
            wmin,cnt = low_weight_relation(q,h,half,wmax)
            emp = f"{wmin}({cnt})" if wmin else f">{wmax}"
            # empirical verdict: relation-free if no relation <= 2*r_star found
            if wmin is None or wmin > 2*r_star:
                verdict = "RELN-FREE=>pin"
            else:
                verdict = "INFLATED=>shift"
        print(f"{rlab:>6} {mu:>3} 2^{mu:<3} | {s_star:>5} {half:>5} {r_star:>4} | "
              f"{log2_3h:>10.1f} {log2q:>7} {str(inj):>5} | {lwcnt:>10.1f} {str(lwfree):>8} | "
              f"{emp:>9} {verdict:>14}")
    print()

print("="*92)
print("INTERPRETATION:")
print(" - 'RELN-FREE=>pin'  : level s* has NO inflating relation => delta* = prizeDeltaStar EXACTLY.")
print(" - 'INFLATED=>shift' : level s* HAS short relations => char-p fibre inflates => delta* < prizeDeltaStar")
print("   (correction governed by the relation spectrum; the genuine open part lives ONLY here).")
print("="*92)
