import numpy as np, sympy
# Decisive: is the period sub-Gaussian with proxy ~n?  E_b[e^{t*eta_b}] <= e^{n t^2 / 2} ?
# If yes at the prize-relevant t ~ sqrt(2 ln m)/sqrt(n), then max_b eta_b <= sqrt(2 n ln m) RIGOROUSLY (closes upper).
def periods(p, n):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    eta=[]
    for b in range(1,p):
        eta.append(sum(np.cos(2*np.pi*(b*x%p)/p) for x in mu).real)  # = (1/2)*real eta_b... actually full real part
    return np.array(eta), m
def realperiods(p,n):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    eta=[sum(np.exp(2j*np.pi*(b*x%p)/p) for x in mu).real for b in range(1,p)]  # real (mu neg-closed => eta real)
    return np.array(eta), m
print(f"{'p':>7} {'n':>3} {'m':>5} {'maxeta':>7} {'t*':>6} | {'MGF(t*)':>9} {'e^(n t*^2/2)':>12} {'subG proxy n?':>13}")
for (p,n) in [(193,16),(769,16),(3329,16),(12289,16),(7681,32),(40961,16)]:
    if (p-1)%n: continue
    eta,m=realperiods(p,n)
    mx=eta.max()
    tstar=np.sqrt(2*np.log(m))/np.sqrt(n)  # the t that makes Chernoff give sqrt(2n ln m)
    mgf=np.mean(np.exp(tstar*eta))
    bound=np.exp(n*tstar**2/2)  # sub-Gaussian proxy n
    # also find the minimal proxy c s.t. MGF<=e^{c t*^2/2}: c = 2 ln(MGF)/t*^2
    cproxy=2*np.log(mgf)/tstar**2 if mgf>1 else 0
    print(f"{p:>7} {n:>3} {m:>5} {mx:>7.3f} {tstar:>6.3f} | {mgf:>9.4f} {bound:>12.4f} {'YES' if mgf<=bound else 'NO':>6} (proxy={cproxy:.2f} vs n={n})")
