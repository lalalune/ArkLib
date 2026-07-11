import numpy as np

def gauss_periods(p, n):
    # mu_n = subgroup of order n in F_p^*; need n | p-1
    assert (p-1) % n == 0
    g = None
    for cand in range(2, p):
        # find a generator of F_p^*
        seen=set(); x=1; ok=True
        # quick order check via factorization-free: just trust small p test below
        # find element of order exactly n: take primitive root power
        pass
    # primitive root
    def is_primroot(a):
        seen=set(); x=1
        for _ in range(p-1):
            x=(x*a)%p
            seen.add(x)
        return len(seen)==p-1
    pr=None
    for a in range(2,p):
        if is_primroot(a): pr=a; break
    # generator of mu_n
    h = pow(pr, (p-1)//n, p)
    mu = [pow(h,k,p) for k in range(n)]
    return mu

def eta(p,n,mu,b):
    # |sum_{x in mu} e_p(b x)|
    s = sum(np.exp(2j*np.pi*b*x/p) for x in mu)
    return abs(s)

def report(p,n):
    mu=gauss_periods(p,n)
    # restricted spectrum b != 0, b in 0..p-1
    norms=[eta(p,n,mu,b) for b in range(1,p)]  # b != 0
    norms=np.array(norms)
    maxnorm=norms.max()
    print(f"p={p} n={n} beta~={np.log(p)/np.log(n):.2f}  max|eta|={maxnorm:.4f}  sqrt(n)={np.sqrt(n):.3f}")
    # A_r = sum_{b!=0} |eta|^{2r}
    for r in range(1,8):
        Ar = np.sum(norms**(2*r))
        Ar1= np.sum(norms**(2*(r+1)))
        lower = np.sqrt(Ar1/Ar)            # (E_{r+1}/E_r)^{1/2} ratio-lower on max
        upper = Ar**(1.0/(2*r))            # moment-root upper on max
        print(f"  r={r}: lower(ratio^.5)={lower:.4f}  max={maxnorm:.4f}  upper(root)={upper:.4f}  width={upper-lower:.4f}")

for (p,n) in [(17,16),(97,16),(257,16),(65537,16),(193,32),(577,32)]:
    try:
        report(p,n); print()
    except Exception as e:
        print(p,n,"skip",e)
