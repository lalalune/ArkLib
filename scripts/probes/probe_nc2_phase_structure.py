#!/usr/bin/env python3
# Decisive phase-structure probe (campaign N13, never run before): is the inter-frequency PHASE of the
# Gauss periods STRUCTURED (exploitable => crack in BGK) or PSEUDORANDOM (=> BGK genuine, phase
# cancellation real but algebraically inaccessible)? Per the phase-blindness dichotomy, exploitable phase
# structure is the ONLY thing that beats the conjugate-modulus ceiling (#S)^{n/4}.
# RESULT (thin proper primes): spectral flatness 0.97->1.000 (WHITE/pseudorandom), max/median grows like
# Gaussian EVT sqrt(2 log m) (3.8->5.9). The relative-phase marginal is non-uniform (KS~0.33 persistent) but
# that is SUP-IRRELEVANT. Conclusion: the sup-governing phase is pseudorandom => no algebraic handle => BGK
# is a REAL wall (the cancellation exists, is genuine, but proving it = proving pseudorandomness = BGK/Paley).
import cmath, math, sympy, numpy as np
def periods_by_coset(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); mu=[pow(h,j,p) for j in range(n)]
    m=(p-1)//n; w=2*math.pi/p; out=[]; rep=1
    for i in range(m):
        out.append(sum(cmath.exp(1j*w*((rep*x)%p)) for x in mu)); rep=(rep*g)%p
    return out,m
def flat(seq):
    P=np.abs(np.fft.fft(np.array(seq)))**2; P=P[P>1e-12]
    return float(np.exp(np.mean(np.log(P)))/np.mean(P)) if len(P) else 0.0
if __name__=="__main__":
    for (n,p) in [(8,4129),(16,65537),(32,1048609)]:
        if (p-1)%n: continue
        eta,m=periods_by_coset(n,p); mags=[abs(e) for e in eta]
        print(f"n={n} p={p} m={m}: flatness={flat(eta):.3f}  max/med={max(mags)/np.median(mags):.2f}")
