import numpy as np, sympy
# What does ORDER-k moment data buy for max|eta|? Chebyshev-Markov / Gauss-Radau upper bound on max-support
# of the period distribution, using EXACT moments to order 2r. Compare to true max and target sqrt(2n ln q).
def periods(p, n):
    g=sympy.primitive_root(p); m=(p-1)//n
    mu=[pow(g,(m*s)%(p-1),p) for s in range(n)]
    etas=[]
    for c in range(m):  # one b per coset; b = g^c representative... use all b!=0, eta constant on cosets
        b=pow(g,c,p)
        etas.append(sum(np.cos(2*np.pi*(b*x%p)/p) for x in mu))  # real part (periods are real for symmetric mu? use |.|)
    # actually use |eta_b| over all b, take distinct
    vals=[]
    for b in range(1,p):
        s=sum(np.exp(2j*np.pi*(b*x%p)/p) for x in mu)
        vals.append(abs(s))
    return np.array(vals)

def gauss_radau_max(absvals, r):
    # moments of X=|eta|^2 up to order r (so |eta| moments to 2r). Chebyshev-Markov upper bound on max(X).
    # Use the largest root of the degree-(r+1) orthogonal polynomial pinned at... simpler: the moment-matrix
    # bound max(X) <= largest eigenvalue achievable; we use the Hankel-ratio bound m_{r+1}/m_r >= ... 
    # Cleanest computable upper proxy: (sum X^r)^(1/r) -> max as r->inf. Track the trend.
    X=absvals**2
    return (X**r).mean()**(1.0/r)  # (E[X^r])^{1/r} -> max(X); times count gives sup proxy
for (p,n) in [(193,16),(769,16),(3329,16),(12289,16),(40961,16)]:
    if (p-1)%n: continue
    av=periods(p,n); truemax=av.max(); beta=np.log(p)/np.log(n)
    tgt=np.sqrt(2*n*np.log(p/n))
    # (E[|eta|^{2r}])^{1/2r} for r=1,2,3,...,8 : how fast does the moment-power-mean approach the true max?
    pm=[ (np.mean(av**(2*r)))**(1/(2*r)) for r in range(1,9) ]
    print(f"p={p} n={n} beta={beta:.2f}: true max|eta|={truemax:.3f}  target sqrt(2n ln(q/n))={tgt:.3f}")
    print(f"   (E|eta|^2r)^(1/2r) r=1..8: {[f'{v:.2f}' for v in pm]}")
    print(f"   ratio to truemax:        {[f'{v/truemax:.2f}' for v in pm]}  (->1 means that order pins the max)")
