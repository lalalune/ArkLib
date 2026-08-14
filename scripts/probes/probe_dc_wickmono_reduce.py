import numpy as np
# Probe (#444): DC-subtracted moments A_r = (1/p) sum_{b!=0} |eta_b|^{2r}.
# Test: (1) A_r is log-convex (A_r^2 <= A_{r-1} A_{r+1}); ALWAYS true (positive measure on b!=0).
# (2) WickMonotonicity f(r+1)<=f(r) with f=A_r/Wick_r  <=>  A_{r+1}/A_r <= (2r+1)*|G| per step.
# (3) A_{r+1}/A_r is monotone increasing with sup = max_{b!=0}|eta_b|^2.
# Prize-regime: PROPER subgroup mu_n in F_p^*, p large, n=2^a. Validate the reduction is exact
# (log-convexity is field-universal; the prize content is the DC-subtracted sup-norm value).

def specweights(p, n):
    assert (p-1) % n == 0
    g = None
    for cand in range(2, p):
        x = 1; order = 0
        for k in range(1, p):
            x = (x*cand) % p; order += 1
            if x == 1: break
        if order == p-1:
            g = cand; break
    h = pow(g, (p-1)//n, p)
    H = set(); x = 1
    for _ in range(n):
        H.add(x); x = (x*h) % p
    H = sorted(H)
    sw = []
    for b in range(p):
        s = sum(np.exp(2j*np.pi*((b*x) % p)/p) for x in H)
        sw.append(abs(s)**2)
    return np.array(sw)

def df_odd(r):
    v = 1
    for k in range(1, r+1):
        v *= (2*k-1)
    return v

cases = [(193,8),(257,16),(40961,16),(40961,32),(12289,16),(7681,32),(786433,16)]
for (p, n) in cases:
    if (p-1) % n != 0:
        continue
    sw = specweights(p, n)
    nz = sw[1:]
    G = n
    maxlam = nz.max()
    A = [(1.0/p)*np.sum(nz**r) for r in range(0, 9)]
    Wick = [df_odd(r)*(G**r) for r in range(0, 9)]
    f = [A[r]/Wick[r] for r in range(1, 9)]
    lc = all(A[r]**2 <= A[r-1]*A[r+1]*(1+1e-9) for r in range(1, 8))
    wm = all(f[i+1] <= f[i]*(1+1e-9) for i in range(len(f)-1))
    ratios = [A[r+1]/A[r] for r in range(1, 8)]
    red = all(ratios[r-1] <= (2*r+1)*G*(1+1e-9) for r in range(1, 8))
    ratmono = all(ratios[i+1] >= ratios[i]*(1-1e-9) for i in range(len(ratios)-1))
    beta = np.log(p)/np.log(n)
    sup_ok = abs(ratios[-1]-maxlam) < 0.05*maxlam or ratios[-1] <= maxlam*(1+1e-9)
    print(f"p={p} n={n} beta={beta:.2f} maxlam={maxlam:.1f} maxlam/G={maxlam/G:.3f} | Alogconv={lc} WickMono={wm} reducedCond={red} ratMono={ratmono} ratio<=maxlam={sup_ok}")
    print(f"   f      ={[round(x,4) for x in f]}")
    print(f"   A_r1/Ar={[round(x,2) for x in ratios]}  vs (2r+1)G={[(2*r+1)*G for r in range(1,8)]}")
