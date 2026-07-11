#!/usr/bin/env python3
"""#407: does B ~ sqrt(n log(p/n)) (exponent a=1/2) survive to LARGE n (=> conjecture TRUE
at prize scale), or grow toward the moment-method ceiling n^{3/4} (=> form REFUTED)?

Exact max over (p-1)/n cosets is infeasible for n>=512. Use EXTREME-VALUE SAMPLING with
OVERFLOW-SAFE modmul (16-bit-limb Horner, valid for p<2^47 -> covers n<=2048 at beta=4,
p~n^4~2^44). Draw S random cosets, take sample-max M_S ~ C_eff*sqrt(n log S); the law-constant
C_eff was ~1.33 in the exact n<=256 scans. Extrapolate to full population:
    impliedB = C_eff*sqrt(n*log(p/n)),  a = log(impliedB)/log(n).
a -> ~0.5 (+log corr) confirms the sqrt(n log) law at scale; a -> 0.75 refutes the form.
"""
import sys, math
import numpy as np
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root

def subgroup_xs(p,n):
    g=primitive_root(p); eta=pow(g,(p-1)//n,p)
    return np.array([pow(eta,i,p) for i in range(n)], dtype=np.int64)

def bx_mod_p(b, xs, p):
    """(b[:,None]*xs[None,:]) % p without overflow; p<2^47, xs<2^48. 16-bit-limb Horner."""
    bm = (b % p).astype(np.int64)[:,None]          # (S,1) < 2^47
    x2 = (xs >> 32)[None,:]; x1 = ((xs>>16)&0xFFFF)[None,:]; x0 = (xs&0xFFFF)[None,:]
    t = (bm * x2) % p                               # <2^47*2^16=2^63 ok
    t = (t << 16) % p
    t = (t + (bm * x1) % p) % p
    t = (t << 16) % p
    t = (t + (bm * x0) % p) % p
    return t

def sample_max(p, n, xs, S, rng):
    twp=2.0*math.pi/p; best=-1.0; done=0
    CH=max(1, min(40000, 20_000_000//n))
    while done<S:
        m=min(CH,S-done)
        b=rng.integers(1,p,size=m,dtype=np.int64)
        prod=bx_mod_p(b,xs,p)
        ang=prod.astype(np.float64)*twp
        mag=np.sqrt(np.cos(ang).sum(1)**2+np.sin(ang).sum(1)**2)
        mx=float(mag.max())
        if mx>best: best=mx
        done+=m
    return best

def find_p(n,beta):
    base=int(round(n**beta)); base-=base%n; base+=1; p=base
    while not(is_prime(p) and odd_part((p-1)//n)>1): p+=n
    return p

def verify_modmul():
    """sanity: bx_mod_p matches python for a small case."""
    p=find_p(64,4.0); xs=subgroup_xs(p,64)
    b=np.array([1, p-2, 123456, (p-1)//2], dtype=np.int64)
    got=bx_mod_p(b,xs,p)
    for i,bb in enumerate(b):
        for j,xx in enumerate(xs[:5]):
            assert got[i,j]==(int(bb)*int(xx))%p, (bb,xx,got[i,j],(int(bb)*int(xx))%p)
    return True

def main():
    assert verify_modmul(); print("modmul verified OK (overflow-safe)\n")
    rng=np.random.default_rng(407); S=800_000
    print(f"LARGE-n exponent test (beta=4, sample S={S}, EV-extrapolate to full population)")
    print(f"{'n':>6} {'p':>16} {'log2(p/n)':>9} {'sampleMax':>10} {'C_eff':>7} {'impliedB':>10} {'a=logB/logn':>11}")
    rows=[]
    for n in (128, 256, 512, 1024):
        p=find_p(n,4.0)
        if p >= (1<<47):
            print(f"{n:>6} p={p} exceeds 2^47 (modmul limit) -- skip"); continue
        xs=subgroup_xs(p,n)
        M=sample_max(p,n,xs,S,rng)
        Ceff=M/math.sqrt(n*math.log(S)); lnN=math.log(p/n)
        impliedB=Ceff*math.sqrt(n*lnN); a=math.log(impliedB)/math.log(n)
        print(f"{n:>6} {p:>16} {math.log2(p/n):>9.2f} {M:>10.2f} {Ceff:>7.3f} {impliedB:>10.2f} {a:>11.3f}")
        rows.append((n,Ceff,a))
    print("\nsqrt(n log) law => a ~ 0.5 + log-correction (slowly rising, bounded);")
    print("moment ceiling  => a -> 0.75.   C_eff flat ~1.3 across n => law constant holds at scale.")
    if rows:
        print(f"\nC_eff: {[round(c,2) for _,c,_ in rows]}   a: {[round(a,3) for _,_,a in rows]}")
    return 0

if __name__=="__main__": sys.exit(main())
