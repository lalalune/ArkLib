#!/usr/bin/env python3
"""δ* explicit upper bracket from the Kambiré subgroup-r-fold-sumset construction (#389).
δ* <= 1-ρ-2/s*, s*=min{s: C(s,floor(ρs)+2) >= ε*q}. Entropy form: η≈2H2(ρ)/log2(ε*q)."""
import math
def H2(x): return -x*math.log2(x)-(1-x)*math.log2(1-x) if 0<x<1 else 0
def s_star(rho, logB):
    for s in range(4,200000):
        r=round(rho*s)+2
        if 0<=r<=s and (math.lgamma(s+1)-math.lgamma(r+1)-math.lgamma(s-r+1))/math.log(2)>=logB:
            return s
    return None
if __name__=="__main__":
    print("rho  Johnson  delta*_upper(n=2^30, deployed eps*q=n)  delta*_upper(n=2^128)  capacity")
    for rho in [0.5,0.25,0.125,0.0625]:
        d30=1-rho-2/s_star(rho,30); d128=1-rho-2/s_star(rho,128)
        print(f" {rho:.4f}  {1-math.sqrt(rho):.3f}   {d30:.4f} (s*={s_star(rho,30)})   {d128:.4f}   {1-rho:.3f}  [H2={H2(rho):.3f}]")
