#!/usr/bin/env python3
"""
#407 -- is the odd-moment A_r = sum_{b!=0} eta_b^r (r odd, real) a STRUCTURED quantity
or just random-fluctuation noise? Honest follow-up to probe_407_odd_moment_thinness.

The naive bound |A_r| <= (p-1) M^r is loose. The QUESTION that matters for the prize:
does A_r encode M, or is it a separable count?

KEY IDENTITY (exact, no archimedean): A_r + n^r = sum_{ALL b} eta_b^r = p * W_r,
where W_r = #{ordered r-tuples in mu_n summing to 0 mod p} (an INTEGER, exact).
So A_r = p*W_r - n^r is EXACTLY an integer combinatorial quantity -- NO cancellation
mystery: it is fully determined by the additive zero-sum count W_r of mu_n.

So the odd-moment "signed cancellation" A_r/(p M^r) -> 0 is NOT a sqrt-cancellation
phenomenon at all: it's  (p*W_r - n^r)/(p*M^r).  For r odd, W_r counts SIGNED... no,
unsigned ordered tuples summing to 0. Let's just COMPUTE W_r exactly (integer, FFT or
direct) and confirm A_r = p*W_r - n^r to machine precision -> proves A_r is a pure
COUNT, hence thickness behavior of A_r = thickness behavior of the zero-sum count W_r.

This DECIDES whether odd-A_r is a new lever (NO -- it's the same W_r census object,
already mapped) or something new. Honesty: if A_r == p*W_r - n^r exactly, the odd-moment
'cancellation' is a NORMALIZATION artifact of dividing an O(p) count by p*M^r ~ p^{1+r/2}.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True
def factor(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f
def primitive_root(p):
    fac=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None
def find_prime(target,n,prefer_odd_m=True):
    k0=max(1,round(target/n))
    for delta in range(0,2000000):
        for s in (1,-1):
            kk=k0+s*delta
            if kk<1: continue
            p=kk*n+1
            if p>3 and is_prime(p):
                m=(p-1)//n
                if prefer_odd_m and m%2==0: continue
                return p
def subgroup(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e

def W_r_exact(elts,p,r):
    """W_r = #ordered r-tuples in mu_n summing to 0 mod p, via integer FFT-free convolution
    on the length-p count vector. f[t] = #{x in mu_n : x==t}. f^{*r}[0]."""
    f=[0]*p
    for x in elts: f[x%p]+=1
    # iterate convolution r-1 times (O(r * p * n) since f has only n nonzeros)
    cur=f[:]
    nz=[(t,1) for t in range(p) if f[t]]
    for _ in range(r-1):
        nxt=[0]*p
        for t,ct in enumerate(cur):
            if ct==0: continue
            for x in elts:
                nxt[(t+x)%p]+=ct
        cur=nxt
    return cur[0]

def periods_real(elts,p):
    w=2*math.pi/p
    out=[]
    for b in range(p):
        s=0.0
        for xx in elts: s+=math.cos(w*((b*xx)%p))
        out.append(s)
    return out

def run():
    print("Test: A_r (=sum_{b!=0} eta_b^r, float) vs p*W_r - n^r (exact integer). r ODD.")
    print("If equal -> odd-moment 'cancellation' is the W_r census count, NOT new.\n")
    for n in [8,16]:
        for beta in [2.5, 4.0]:
            p=find_prime(int(n**beta),n)
            e=subgroup(n,p)
            per=periods_real(e,p)
            for r in [3,5]:
                A_r=sum(per[b]**r for b in range(1,p))     # float
                Wr=W_r_exact(e,p,r)                          # exact int
                pred=p*Wr - n**r
                print(f"  n={n} beta~{math.log(p)/math.log(n):.2f} p={p} r={r}: "
                      f"A_r(float)={A_r:+.3f}  p*W_r-n^r={pred:+d}  W_r={Wr}  diff={A_r-pred:+.2e}")
        print()

if __name__=="__main__":
    run()
