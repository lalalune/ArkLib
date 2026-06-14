import numpy as np
from sympy import isprime

def find_ntt_prime(a, target):
    m = 1 << a
    p = target + ((1 - target) % m)
    if p < target: p += m
    while not isprime(p): p += m
    return p

def order_2a_root(p, a):
    m = 1 << a; e = (p-1)//m
    import random; random.seed(777 + p % 1000)
    for _ in range(300):
        g = pow(random.randrange(2, p-1), e, p)
        if pow(g, m//2, p) != 1: return g
    raise RuntimeError("no root")

def subgroup(p, a):
    g = order_2a_root(p, a); s=[]; x=1
    for _ in range(1<<a): s.append(x); x=(x*g)%p
    assert len(set(s))==(1<<a); return s

def moments(p, a, rmax):
    n = 1<<a
    ind = np.zeros(p); 
    for x in subgroup(p,a): ind[x]=1.0
    mag = np.abs(np.fft.fft(ind))
    # E_r = (1/p) sum_b |eta_b|^{2r}
    out = {}
    for r in range(2, rmax+1):
        out[r] = float(np.sum(mag**(2*r))/p)
    return out

# For each n, sweep p upward; find where E_r STABILIZES (= char-0 value). Report E_r / E_r(largest p) and detect threshold.
print("Per (a,n): E_r at increasing p; ratio to the value at the LARGEST p (proxy char-0 stable). threshold ~ where ratio->1")
for a in [3,4,5]:
    n = 1<<a
    ps = []
    for t in [n*n//2, n*n, n**3//4, n**3, n**4//4, n**4, n**4*16]:
        if t < n*2: continue
        try:
            p = find_ntt_prime(a, max(t, n*2+1))
            if p > 6_000_000: continue
            ps.append(p)
        except: pass
    ps = sorted(set(ps))
    rows = {p: moments(p,a,5) for p in ps}
    pbig = ps[-1]
    stable = rows[pbig]
    print(f"\n== a={a} n={n}  (stable proxy p={pbig}: E2={stable[2]:.0f} E3={stable[3]:.0f} E4={stable[4]:.0f} E5={stable[5]:.0f}) ==")
    print(f"{'p':>10} {'p/n^2':>7} {'p/n^3':>7} | " + " ".join(f"E{r}/stab" for r in range(2,6)))
    for p in ps:
        m = rows[p]
        ratios = " ".join(f"{m[r]/stable[r]:>6.3f} " for r in range(2,6))
        print(f"{p:>10} {p/n**2:>7.2f} {p/n**3:>7.3f} | {ratios}")
