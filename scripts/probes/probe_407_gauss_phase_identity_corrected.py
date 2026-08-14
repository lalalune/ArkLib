import cmath, math
def primitive_root(p):
    if p==2: return 1
    phi=p-1; facs=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: facs.add(d); x//=d
        d+=1
    if x>1: facs.add(x)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in facs): return g
# The subgroup of n-th roots of unity = { x : x^n = 1 } has order gcd(n,p-1).
# We need mu_n = unique subgroup of ORDER n, which exists iff n | p-1, = {g^(m k): k} m=(p-1)/n.
# Characters trivial on mu_n  <-> characters chi_a with chi_a(g^m)=1 <-> exp(2pi i a m/(p-1))=1
#   <-> a*m ≡ 0 mod (p-1) <-> a ≡ 0 mod n  (since m=(p-1)/n).  So a in {0,n,2n,...}? NO.
# chi^n=1 means a*n≡0 mod (p-1) <-> a multiple of m. THAT is chars whose RESTRICTION... let's be careful.
# eta_b = sum_{y in mu_n} e_p(by).  mu_n = nth POWERS? No: mu_n = order-n subgroup = (p-1)/n = m-th powers? 
#   group of m-th powers has order (p-1)/m = n. YES mu_n = { x^m : x } = {g^(m k)}.  Good (matches factorize).
# Indicator of mu_n: 1_{mu_n}(x) = (1/|mu_n^perp|) sum over chars trivial on mu_n.
#  chars trivial on mu_n: chi_a(g^{m k})=1 all k <-> a*m*k≡0 (p-1) all k <-> a*m≡0 mod (p-1) <-> a≡0 mod n.
#  there are m such chars a in {0,n,2n,...,(m-1)n}.  |mu_n|=n, index=m. 1_{mu}(x)=(1/m)? no =(n/(p-1))? 
#  Actually 1_{mu_n}(x) = (1/m) sum_{a: a≡0 mod n, a in [0,p-1)} chi_a(x).  (m terms; at x in mu it gives m/m... )
# So eta_b = sum_{x in F_p^*} 1_{mu}(x) e_p(bx) = (1/m) sum_{a≡0 mod n} sum_{x≠0} chi_a(x) e_p(bx)
#          = (1/m)[ (a=0 term: -1) + sum_{a≡0 mod n, a≠0} chibar_a(b) G(chi_a) ].
# THE BUG: chars are a ≡ 0 mod n (m-1 of them), NOT a = m*j (n-1 of them). Fix and retest.
for (p,n) in [(13,3),(41,8),(97,8),(257,16),(241,8),(337,16)]:
    if (p-1)%n: continue
    g=primitive_root(p); phi=p-1; m=phi//n
    mu=sorted({pow(g,m*k,p) for k in range(n)})
    dlog={}; val=1
    for k in range(phi): dlog[val]=k; val=val*g%p
    def G(a):
        return sum(cmath.exp(2j*math.pi*a*dlog[x]/phi)*cmath.exp(2j*math.pi*x/p) for x in range(1,p))
    def chibar(a,b):
        return 0 if b%p==0 else cmath.exp(-2j*math.pi*a*dlog[b%p]/phi)
    a_list=[n*j for j in range(m)]   # a ≡ 0 mod n, m of them
    def eta(b): return sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in mu)
    err=0; mP=0; meta=0
    for b in range(1,p):
        eb=eta(b)
        form=(-1+sum(chibar(a,b)*G(a) for a in a_list if a!=0))/m
        err=max(err,abs(eb-form)); meta=max(meta,abs(eb))
        Pb=sum(chibar(a,b)*(G(a)/math.sqrt(p)) for a in a_list if a!=0)
        mP=max(mP,abs(Pb))
    bp=math.sqrt(2*m*math.log(m)) if m>1 else 1
    print(f"p={p:>4} n={n:>3} m={m:>3} #chars={len(a_list)-0:>3}  eta_err={err:.2e}  max|η|={meta:.3f}  max|P|={mP:.3f}  ratioP={mP/bp:.3f}")
