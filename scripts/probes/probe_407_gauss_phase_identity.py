import numpy as np, sympy
# VERIFY the equality chain: eta_b = (-1 + sqrt(p)*P(b))/m, P(b)=sum_{chi!=1, chi in Hhat} conj(chi)(b) gamma_chi
# Hhat = characters of order dividing m=(p-1)/n (index-n subgroup of char group). gamma_chi = G(chi)/sqrt(p) unimodular.
def check(p, n):
    m = (p-1)//n
    g = sympy.primitive_root(p)
    # multiplicative characters of order dividing m: chi_j(g^t) = exp(2pi i * j*t/(p-1)) with j multiple of n
    # Hhat = {chi : chi^m = 1} = characters chi_j with j ≡ 0 mod n (order | m). j in {0,n,2n,...,(m-1)n}.
    # discrete log table
    dlog = {}
    x=1
    for t in range(p-1):
        dlog[x]=t; x=(x*g)%p
    def chi(j, a):  # chi_j(a) = exp(2pi i j * dlog(a)/(p-1))
        return np.exp(2j*np.pi*j*dlog[a]/(p-1))
    def gauss(j):  # G(chi_j) = sum_a chi_j(a) e_p(a)
        return sum(chi(j,a)*np.exp(2j*np.pi*a/p) for a in range(1,p))
    # mu_n = {x: x^n=1} = {g^{m*s}: s} 
    mu = [pow(g,(m*s)%(p-1),p) for s in range(n)]
    maxerr=0; etamax=0; Pmax=0
    Js = [ (j*n) for j in range(m) ]  # j-values for Hhat (order|m): multiples of n
    gammas = {jj: gauss(jj)/np.sqrt(p) for jj in Js if jj!=0}
    for b in range(1,p):
        eta = sum(np.exp(2j*np.pi*(b*x)/p) for x in mu)
        P = sum(np.conj(chi(jj,b))*gammas[jj] for jj in Js if jj!=0)
        rhs = (-1 + np.sqrt(p)*P)/m
        maxerr=max(maxerr, abs(eta-rhs))
        etamax=max(etamax, abs(eta)); Pmax=max(Pmax, abs(P))
    # check gammas unimodular
    unimod_err = max(abs(abs(v)-1) for v in gammas.values())
    return maxerr, unimod_err, etamax, Pmax, m
for (p,n) in [(193,16),(257,16),(769,16),(3329,16)]:
    err,ue,em,pm,m = check(p,n)
    # predicted: eta_max ~ (sqrt(p)/m)*P_max ; check P_max vs sqrt(m log m)
    import math
    print(f"p={p} n={n} m={m}: |eta=(−1+√p P)/m| max-err={err:.2e}  γ unimodular-err={ue:.2e}")
    print(f"     eta_max={em:.3f}  P_max={pm:.3f}  (√p/m)P_max={np.sqrt(p)/m*pm:.3f}  | P_max/√(m·2lnm)={pm/np.sqrt(m*2*max(np.log(m),1)):.3f}")
