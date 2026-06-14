import numpy as np, sympy
# Decisive: sign of the period's 4th cumulant kappa_4 = E[eta^4] - 3 Var^2.
# kappa_4 < 0: platykurtic/lighter tails (sub-Gaussian-leaning, max SMALLER, closable).
# kappa_4 > 0: leptokurtic/heavier tails (the arithmetic excess, harder).
# Also higher: is the whole sequence of cumulants sub-Gaussian (all kappa_{2r} controlled)?
def realperiods(p,n):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    return np.array([sum(np.exp(2j*np.pi*(b*x%p)/p) for x in mu).real for b in range(1,p)]), m
print(f"{'p':>7} {'n':>3} {'m':>5} {'Var':>7} {'kappa4':>9} {'kappa4/n^2':>10} {'kurtosis':>8} | tail")
for (p,n) in [(193,16),(769,16),(3329,16),(12289,16),(40961,16),(7681,32),(786433,16)]:
    if (p-1)%n: continue
    eta,m=realperiods(p,n)
    var=np.mean(eta**2); m4=np.mean(eta**4)
    k4=m4-3*var**2
    kurt=m4/var**2  # =3 for Gaussian
    print(f"{p:>7} {n:>3} {m:>5} {var:>7.3f} {k4:>9.2f} {k4/n**2:>10.4f} {kurt:>8.4f} | {'LIGHTER(sub-Gauss,GOOD)' if k4<0 else 'heavier(excess)'}")
