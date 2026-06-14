#!/usr/bin/env python3
"""Crossover: I(delta) is char-indep for q > T(tau)=(2k)^{2k/(tau-k)} (norm bound p^r|N(f(zeta)), r=tau-k).
At binding window-top delta*=1-rho-eta*, r*=eta* n, T=(2k)^{2rho/eta*}=n^{Theta(log n)}. Clean iff T<q=n^beta
iff eta* > 2rho/beta. Crossover n ~ e^{beta/2rho}. Prize n=2^30 >> crossover => dirty (esp. rho=1/2)."""
import math
def tab(rho,beta,c):
    print(f"\n rho={rho} beta={beta} eta*=c/ln n, c={c}:",flush=True)
    for m in (12,15,16,20,30):
        n=2**m;k=rho*n;eta=c/math.log(n);rstar=eta*n
        log2T=((2*k)/rstar)*math.log2(2*k);log2q=beta*m
        print(f"   n=2^{m}: log2 q={log2q:.0f} log2 T={log2T:.0f} -> {'CLEAN' if log2T<log2q else 'DIRTY'}",flush=True)
for rho in (0.25,0.5):
    print(f"crossover n ~ e^(beta/2rho) = 2^{math.log2(math.exp(5.27/(2*rho))):.1f} (rho={rho},beta=5.27)")
tab(0.25,5.27,1.0); tab(0.25,5.27,3.0); tab(0.5,5.27,1.0)
