import numpy as np
# For Hermitian s: claim  F(b) = sum_k Re( s[k] w^{k b} )  (each summand's real part).
# Equivalent (since F real): F(b) = Re(F(b)) and Re of a sum = sum of Re. TRIVIALLY true
# once F is real. But the Lean-useful identity is: F(b) = ((sum_k Re(s[k] w^{kb})) : R) cast to C,
# i.e. the DFT equals the COMPLEX-cast of an explicit real sum. Test the real value equality.
def test(m, trials=300):
    fail = 0
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
        for b in range(m):
            F = sum(s[k]*w**((k*b)%m) for k in range(m))
            R = sum((s[k]*w**((k*b)%m)).real for k in range(m))
            if abs(F - R) > 1e-7: fail += 1
    return fail
for m in [6,8,12,16,17,32]:
    print("m=%d: F(b)=sum_k Re(...) fails=%d" % (m, test(m)))
