import numpy as np
# For Hermitian s: F(b) real => |F(b)|^2 = F(b).re^2 (no imag cross term).
# Also Parseval real form: sum_b |F(b)|^2 = sum_b F(b).re^2 = m * sum_k |s_k|^2 (Plancherel).
def test(m, trials=200):
    f_normsq = 0
    f_plancherel = 0
    for _ in range(trials):
        s = np.zeros(m, dtype=complex)
        s[0] = np.random.randn()
        for k in range(1, m):
            mk = (-k) % m
            if k < mk:
                z = np.random.randn()+1j*np.random.randn(); s[k]=z; s[mk]=np.conj(z)
            elif k == mk:
                s[k] = np.random.randn()
        w = np.exp(2j*np.pi/m)
        def F(b): return sum(s[k]*w**((k*b)%m) for k in range(m))
        tot = 0.0
        for b in range(m):
            fb = F(b)
            if abs(abs(fb)**2 - fb.real**2) > 1e-7: f_normsq += 1
            tot += abs(fb)**2
        energy_s = m*sum(abs(s[k])**2 for k in range(m))
        if abs(tot - energy_s) > 1e-6: f_plancherel += 1
    return f_normsq, f_plancherel
for m in [6,8,12,16,17,32]:
    a,b = test(m)
    print("m=%d: |F|^2=F.re^2 fails=%d | Plancherel sum|F|^2=m*sum|s|^2 fails=%d" % (m,a,b))
