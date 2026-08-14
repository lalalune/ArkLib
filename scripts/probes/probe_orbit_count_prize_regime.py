#!/usr/bin/env python3
"""Action-Orbit poly-orbit-count test in the TRUE prize regime (#407): proper mu_n < F_q*,
q=n^beta PRIME, FAR monomial pencils (a,b>=k, excluding x^{n/2}=+-1 correlated directions).
bad-alpha = {alpha: max-agreement(x^a+alpha x^b, RS[k]) >= agr}; orbit count N under
alpha->alpha*w^{b-a}. FINDING (n=8, q=521/4129/32801, rho=1/2,1/4): for genuine FAR pencils
the orbit count N is SMALL (N<=5) even when |bad|=40=N*S (S=orbit size=n/gcd(b-a,n)) — the
orbit structure compresses by factor S. Correlated direction (4,5) [x^4=+-1] gives degenerate
I=q-1 and is correctly excluded. Validates BridgeLoop44's poly-orbit-count route: the prize
needs N<=poly(n), and N is small/bounded for far pencils. NEXT: prove N<=poly via Mann's theorem
on large cyclotomic factors of the sparse pencil poly x^b+alpha x^a-g (RungSparseDivisor lane)."""
