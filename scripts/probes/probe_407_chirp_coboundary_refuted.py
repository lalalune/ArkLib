import numpy as np
from sympy import isprime, primitive_root

np.set_printoptions(precision=4, suppress=True)

def find_q(n, beta=4.5):
    target = int(n**beta)
    k = max(1, target//n)
    while True:
        q = 1 + k*n
        if isprime(q):
            return q
        k+=1

def analyze(mu, beta=4.5, verbose=True):
    n = 2**mu
    q = find_q(n, beta)
    m = (q-1)//n
    g = primitive_root(q)
    # mu_n = { g^(m*j) : j=0..n-1 }  (subgroup of order n)
    # Characters of F_q^* : chi_t(g^a) = exp(2 pi i t a/(q-1)), t=0..q-2.
    # chi trivial on mu_n  <=>  chi(g^m)=1 <=> exp(2pi i t m/(q-1))=1 <=> t*m ≡0 mod (q-1)
    #   <=> t multiple of n.  So Hhat = { chi_{n*s} : s=0..m-1 }, order m. Good.
    # gamma_chi = G(chi)/sqrt(q). We need these for the m-1 nontrivial chars chi_{n*s}, s=1..m-1.

    # Direct eta_b computation for validation: discrete log table
    # Build dlog: g^a -> a
    # m can be large (185364 for mu=5) -> q up to ~6M. dlog table size q. Feasible.
    dlog = np.zeros(q, dtype=np.int64)
    cur = 1
    for a in range(q-1):
        dlog[cur] = a
        cur = (cur*g) % q
    # mu_n elements as integers
    mun = []
    cur = 1
    gm = pow(g, m, q)
    for j in range(n):
        mun.append(cur)
        cur = (cur*gm)%q
    mun = np.array(mun, dtype=np.int64)

    # eta_b for b=1..q-1 (b!=0): eta_b = sum_{x in mu_n} exp(2pi i b x/q)
    # We'll compute for all b via: this is expensive O(q*n). For mu=5 q~6M*32=190M -- too slow in python.
    # Instead use FFT: define vector v over Z/q with v[x]=1 if x in mu_n else 0 (x in 0..q-1).
    # eta_b = sum_x v[x] exp(2pi i b x/q) = conj-DFT. Use np.fft on length q.
    v = np.zeros(q)
    for x in mun:
        v[x] = 1.0
    # DFT: F[b] = sum_x v[x] exp(-2pi i b x/q). We want +sign. eta_b = sum v[x] exp(+2pi i b x /q)= conj(F[b]) since v real.
    F = np.fft.fft(v)   # F[b]=sum v[x] exp(-2pi i b x/q)
    eta = np.conj(F)    # eta[b] for b=0..q-1; eta[0]=n.
    eta_nz = eta[1:]    # b=1..q-1
    B_direct = np.max(np.abs(eta_nz))

    # Now compute gamma_chi via Gauss sums. G(chi_{n s}) = sum_{x in F_q^*} chi(x) exp(2pi i x/q).
    # chi_{n s}(g^a) = exp(2 pi i (n s) a/(q-1)). Compute for s=1..m-1.
    # This is O(m * q) potentially huge. Instead: relate eta to P:
    #   P(b) = sum_{s=1}^{m-1} chibar_{n s}(b) gamma_{n s}, and eta_b=(-1+sqrt(q) P(b))/m.
    # So P(b) = (m*eta_b + 1)/sqrt(q).
    # gamma_{n s} = G(chi_{ns})/sqrt(q). And P over b is essentially an inverse-DFT of gamma over the group Hhat=Z/m.
    # Indexing: b = g^c (c=dlog[b]). chi_{ns}(b)=exp(2pi i n s c/(q-1))=exp(2pi i s c /m) since n/(q-1)=1/m.
    # chibar_{ns}(b)=exp(-2pi i s c/m). So P(b)=sum_{s=1}^{m-1} exp(-2pi i s c/m) gamma_s   (write gamma_s:=gamma_{ns}).
    # P depends on b only through c mod m! (c=dlog[b], c mod m). So P(b) takes only m distinct values.
    # P(c) = sum_{s=1}^{m-1} gamma_s exp(-2pi i s c/m), c=0..m-1. This is (m * IDFT of gamma) minus s=0 term.
    # Let's recover gamma_s from eta. P_vals[c] = (m*eta[b_with_dlog_c] + 1)/sqrt(q).
    # Pick representative b for each residue c0 in 0..m-1: b=g^(c0).
    sqrtq = np.sqrt(q)
    Pc = np.zeros(m, dtype=complex)
    gpow = 1
    # precompute g^c for c=0..m-1
    for c0 in range(m):
        b = pow(g, c0, q)
        Pc[c0] = (m*eta[b] + 1)/sqrtq
    # P(c) = sum_{s=1}^{m-1} gamma_s exp(-2pi i s c/m). This is DFT. Invert:
    # gamma_s = (1/m) sum_{c=0}^{m-1} P(c) exp(+2pi i s c/m)  for s=1..m-1, and the s=0 component should be ~0.
    gamma = np.fft.fft(Pc)/m  # gamma[s]=(1/m) sum_c P(c) exp(-2pi i s c/m)?? check sign
    # np.fft.fft: A[s]=sum_c P[c] exp(-2pi i s c/m). We defined P(c)=sum_s gamma_s exp(-2pi i s c/m).
    # So fft(P)[k] = sum_c sum_s gamma_s exp(-2pi i (s+k) c/m) = m * sum_s gamma_s [s+k ≡0] = m gamma_{(-k) mod m}.
    # => gamma_{(-k) mod m} = fft(P)[k]/m. So gamma_s = fft(P)[(-s) mod m]/m.
    ffP = np.fft.fft(Pc)
    gamma = np.array([ffP[(-s)%m]/m for s in range(m)])
    # gamma[0] should be ~0 (no s=0 term). Check.
    g0 = gamma[0]
    # unimodularity of gamma_s for s=1..m-1
    mods = np.abs(gamma[1:])
    if verbose:
        print(f"--- mu={mu} n={n} q={q} m={m} ---")
        print(f"B_direct (max|eta_b|) = {B_direct:.4f}")
        print(f"  conjectured sqrt(2 n ln(q/n)) = {np.sqrt(2*n*np.log(q/n)):.4f}")
        print(f"  sqrt(n) = {np.sqrt(n):.4f}, B/sqrt(n)={B_direct/np.sqrt(n):.4f}")
        print(f"gamma[0] (should be ~0): {g0:.4f}, |gamma[0]|={abs(g0):.4f}")
        print(f"|gamma_s| for s=1..m-1: mean={mods.mean():.5f} std={mods.std():.5f} min={mods.min():.4f} max={mods.max():.4f}")
    return dict(mu=mu,n=n,q=q,m=m,g=g,eta=eta,Pc=Pc,gamma=gamma,B_direct=B_direct,sqrtq=sqrtq)

R = analyze(3)
