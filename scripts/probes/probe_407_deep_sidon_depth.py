#!/usr/bin/env python3
"""
probe_407_deep_sidon_depth.py  (#407)

DEEP-ORDER Sidon-depth probe (the narrowed rule-3 frontier).

Prior result (DISPROOF_LOG, 82581fb79 + c7866d422): the moment certificate is
thickness-invariant and shallow (r=2,3) additive statistics are field-blind, so any
thinness-discriminating lever must live at DEEP additive order r ~ log n. This probes the
deepest accessible additive structure of mu_n EFFICIENTLY (FFT convolution, NOT n^r brute).

OBJECT. mu_n < F_p^* (proper 2-power subgroup). Let f = indicator of (mu_n as additive
subset of Z_p). The r-fold additive convolution f^{*r}(t) counts ordered r-tuples
(x_1..x_r) in mu_n^r with sum = t (mod p). Define:
  - W_r := f^{*r}(0)  = #{ordered r-tuples in mu_n summing to 0 mod p}  (the "zero-sum count")
  - The TRIVIAL/forced baseline for W_r: pairs x + (-x) = 0 contribute when -1 in mu_n
    (n even => -1 in mu_n), giving a forced n contribution at r=2, etc. We compare W_r to the
    RANDOM-MODEL expectation n^r/p (a random r-tuple sums to 0 with prob ~1/p).
  - EXCESS_r := W_r / (n^r/p) = p*W_r/n^r. Sidon-to-depth-ell means EXCESS_r ~ 1 (no additive
    structure beyond random) for r <= ell; EXCESS_r >> 1 signals additive coincidences (structure).

KEY (the actual M connection): by orthogonality,
  W_r = (1/p) sum_{b} |S(b)|^{2... } NO -- careful: W_r = f^{*r}(0) and
  sum_b eta_b^r * conj? Use: f^{*r}(0) = (1/p) sum_{b in Z_p} S_hat(b)^r  where
  S_hat(b) = sum_{x in mu_n} omega^{b x} = eta_b (the Gauss period!). So
     W_r = (1/p) sum_b eta_b^r.
  The b=0 term is n^r/p (DC). So EXCESS_r = p*W_r/n^r = 1 + (1/n^r) sum_{b!=0} eta_b^r.
  This DIRECTLY ties deep additive structure to the period sums eta_b -- and |sum_{b!=0} eta_b^r|
  <= (p-1) * M^r where M is the prize sup-norm. So a SMALL EXCESS at deep r is EQUIVALENT to
  cancellation in sum_{b!=0} eta_b^r -- the prize phenomenon. This is the right deep object.

THINNESS TEST. Compute EXCESS_r for r=2..rmax at matched n across thick (beta~2.5) and thin
(beta~4-4.5) primes. Does EXCESS_r stay ~1 (Sidon/random-like) DEEPER in thin than in thick?
A thinness signature: thin mu_n is Sidon to greater additive depth (excess departs from 1 later).
"""
import math, cmath

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def factor_small(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    fac=list(factor_small(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def find_prime(target, mod_n):
    k=max(1,round(target/mod_n))
    for delta in range(0,400000):
        for s in (1,-1):
            kk=k+s*delta
            if kk<1: continue
            p=kk*mod_n+1
            if p>3 and is_prime(p): return p
    return None

def subgroup(n,p):
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)
    e=[]; x=1
    for _ in range(n): e.append(x); x=(x*h)%p
    return e

def periods(elts,p):
    """eta_b = sum_{x in mu_n} omega^{b x} for all b in Z_p. O(n p)."""
    w=2*math.pi/p
    out=[]
    for b in range(p):
        s=0j
        for xx in elts: s+=cmath.exp(1j*w*((b*xx)%p))
        out.append(s)
    return out

def run():
    print("DEEP Sidon-depth: EXCESS_r = p*W_r/n^r = 1 + (1/n^r) sum_{b!=0} eta_b^r")
    print("(EXCESS~1 => Sidon/random-like to depth r; EXCESS>>1 => deep additive structure).")
    print("Thinness signature wanted: EXCESS stays ~1 DEEPER (larger r) in THIN than THICK.\n")
    for n in [8,16]:
        print(f"==== n={n}  (log2 n = {int(math.log2(n))}) ====")
        for beta in [2.5, 4.0, 4.5]:
            if n==16 and beta>4.0: continue  # keep p modest
            p=find_prime(int(n**beta),n)
            if not p: continue
            ab=math.log(p)/math.log(n)
            e=subgroup(n,p)
            eta=periods(e,p)
            # eta[0] should be n
            row=[]
            rmax = 2*int(math.log2(n))+2
            for r in range(2,rmax+1):
                # sum_{b!=0} eta_b^r  (complex); W_r real => take real part of total/p
                tot = sum(eta[b]**r for b in range(1,p))
                excess = 1.0 + tot.real/(n**r)
                row.append((r,excess))
            cells=" ".join(f"r{r}:{ex:.3f}" for r,ex in row)
            # depth where excess first exceeds 1.5 (departs from random)
            dep = next((r for r,ex in row if abs(ex-1.0)>0.5), None)
            print(f"  beta={ab:.2f} p={p}: {cells}")
            print(f"     -> first |EXCESS-1|>0.5 at r={dep}  (Sidon-random depth ~ {('>'+str(rmax)) if dep is None else dep-1})")
        print()

if __name__=="__main__":
    run()
