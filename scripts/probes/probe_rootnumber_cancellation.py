"""
THE cancellation object: eta_b = (n/(p-1)) Sum_{chi trivial on mu_n} chibar(b) g(chi), |g(chi)|=sqrt(p).
So M(n)=max_b|eta_b| <= Csqrt(n log m) <=> the m root numbers w_chi = g(chi)/sqrt(p) = e^{i theta_chi}
exhibit SQUARE-ROOT cancellation when weighted by chibar(b). This is the EXACT prize (completed-sum form).
Attack: compute the root-number phases theta_chi, test:
 (1) are they equidistributed (=> generic cancellation, M~sqrt(p log)/... )?
 (2) is the weighted sum S_b = Sum_chi chibar(b) g(chi) actually = (p-1)/n * eta_b (verify the identity)?
 (3) the KEY: is there ALGEBRAIC STRUCTURE in {w_chi} (a relation forcing flatness) or are they 'random'?
     Test: autocorrelation of the phase sequence, and whether w_chi factors through a low-degree map.
"""
import cmath, math
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def primroot(p):
    facs=set(); m=p-1; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs): return g
def gauss_sum(p, g, k, m):
    """g(chi^k) where chi(g^j)=e^{2pi i j/(p-1)}; here we want chi trivial on mu_n i.e. chi=chi_0^{m*t}.
    Gauss sum g(chi) = sum_{x=1}^{p-1} chi(x) e_p(x). chi(g^j)=zeta_{p-1}^{kj}."""
    # chi index k (a character of F_p^*), g(chi)=sum_j zeta_{p-1}^{k j} e_p(g^j)
    total=0j
    x=1
    w=2*math.pi/p
    wc=2*math.pi/(p-1)
    for j in range(p-1):
        total += cmath.exp(1j*wc*k*j) * cmath.exp(1j*w*x)
        x=x*g%p
    return total

n=8
p=n+1
while not(p%n==1 and isprime(p) and p>500): p+=1   # a modest prize-ish prime
g=primroot(p); m=(p-1)//n
print(f"n={n} p={p} m=(p-1)/n={m}, primroot={g}")
# characters trivial on mu_n: chi=chi_0^{n*t} for t=0..m-1 (since mu_n = <g^m>, chi trivial on it iff n*t... )
# mu_n = {g^{m*i}}; chi_k(g^{m i})=zeta_{p-1}^{k m i}=1 forall i iff (p-1)|k*m*1 iff n|k. So k=n*t.
ws=[]
for t in range(m):
    k=(n*t)%(p-1)
    if k==0: continue  # trivial char (DC)
    G=gauss_sum(p,g,k,m)
    w=G/math.sqrt(p)
    ws.append((t, w))
print(f"  {len(ws)} nontrivial root numbers w_chi=g(chi)/sqrt p, |w|: {[round(abs(w),3) for _,w in ws[:8]]}")
# (2) verify eta_b = (n/(p-1)) S_b
def eta_b(b):
    S=set(pow(g,m*i,p) for i in range(n))  # mu_n
    return sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
def S_b(b):
    tot=-1+0j  # the trivial-char DC term g(chi_0)=-1
    for t in range(1,m):
        k=(n*t)%(p-1)
        G=gauss_sum(p,g,k,m)
        # chibar(b): chi_k(b)=zeta_{p-1}^{k*ind(b)}, need index of b
        # ind(b): b=g^{ind}
        ind=0; x=1
        while x!=b%p: x=x*g%p; ind+=1
        tot += cmath.exp(-1j*2*math.pi*k*ind/(p-1))*G
    return tot
b=g  # test b=primroot
lhs=eta_b(b); rhs=(n/(p-1))*S_b(b)
print(f"  identity check b={b}: eta_b={lhs:.3f}, (n/(p-1))S_b={rhs:.3f}, match={abs(lhs-rhs)<1e-6}")
# (3) phase structure: equidistribution + autocorrelation
phases=[cmath.phase(w) for _,w in ws]
import statistics
# autocorrelation at lag 1
mean_w=sum(w for _,w in ws)/len(ws)
print(f"  mean root number (should be ~0 if flat): |mean w|={abs(mean_w):.4f}  (m={m}, sqrt-cancel ~ 1/sqrt(m)={1/math.sqrt(m):.3f})")
