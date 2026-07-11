import numpy as np

# s Hermitian. F(b)=sum_k s[k] w^{kb}. Test the THREE candidate frequency symmetries:
#  (1) F(-b) == conj(F(b))     [DFT-of-Hermitian-real should still relate -b to conj]
#  (2) |F(-b)| == |F(b)|       [magnitude evenness -- matters for max_b|F(b)| prize sup]
#  (3) F(-b) == F(b)           [already shown FALSE]

def test(m, trials=300):
    f1 = f2 = f3 = 0
    for _ in range(trials):
        s = np.zeros(m, dtype=complex)
        s[0] = np.random.randn()
        for k in range(1, m):
            mk = (-k) % m
            if k < mk:
                z = np.random.randn() + 1j*np.random.randn()
                s[k] = z; s[mk] = np.conj(z)
            elif k == mk:
                s[k] = np.random.randn()
        w = np.exp(2j*np.pi/m)
        def F(b): return sum(s[k]*w**((k*b) % m) for k in range(m))
        for b in range(m):
            fb = F(b); fnb = F((-b) % m)
            if abs(fnb - np.conj(fb)) > 1e-7: f1 += 1
            if abs(abs(fnb) - abs(fb)) > 1e-7: f2 += 1
            if abs(fnb - fb) > 1e-7: f3 += 1
    return f1, f2, f3

for m in [6, 8, 12, 16, 17, 32]:
    a, b, c = test(m)
    print("m=%d: F(-b)=conj F(b) fails=%d | |F(-b)|=|F(b)| fails=%d | F(-b)=F(b) fails=%d" % (m, a, b, c))
