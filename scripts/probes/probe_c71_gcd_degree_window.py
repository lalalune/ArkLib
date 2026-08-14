# PROBE: explicit bound on deg gcd(X^n - 1, g) for m-sparse g over thin mu_n.
# Question A: is deg gcd(X^n-1, g) <= (top_exp - bot_exp) of g's support window? (window bound)
# Question B: is deg gcd(X^n-1, g) <= min(n, deg g)? (trivial bound, sanity)
# Question C: for g with support in [bot, top], does the gcd-degree EXACTLY equal #{nth roots of unity that are roots of g}?
# Probe-first rule 2: PROPER thin mu_n=2^a, p==1 mod n, p>n^3 included, NEVER n=q-1, multi-prime incl Fermat.
import itertools, random
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def inv(a,p): return egcd(a%p,p)[1]%p
def poly_mod_roots(coeffs, p):
    # coeffs: dict exp->coef ; return roots in F_p^* among nth-roots of unity handled by caller
    pass
def primroot(p):
    # find a generator of F_p^*
    fac=[]; phi=p-1; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g
    return None
def gcd_deg_via_roots(g, n, p):
    # g: dict exp->coef. mu_n = nth roots of unity in F_p^*. Need p==1 mod n.
    gen=primroot(p)
    w=pow(gen,(p-1)//n,p)  # primitive nth root
    mu=[pow(w,t,p) for t in range(n)]
    roots=[]
    for x in mu:
        val=sum(c*pow(x,e,p) for e,c in g.items())%p
        if val==0: roots.append(x)
    return len(roots)  # = deg gcd(X^n-1, g) since X^n-1 splits over mu_n
def run():
    random.seed(7)
    cases=0; winOK=0; winTight=0; minOK=0
    bad=[]
    for a in [2,3,4,5]:
        n=2**a
        primes=[pp for pp in range(n+1, 70000) if pp%n==1 and isprime(pp)]
        chosen=[primes[0]]
        big=[pp for pp in primes if pp>n**3]
        if big: chosen.append(big[0])
        # add a Fermat-type
        for f in [257,65537]:
            if f%n==1 and f not in chosen: chosen.append(f); break
        for p in chosen:
            for m in [2,3,4]:
                for _ in range(80):
                    # random m-sparse g with distinct exps in [0, 2n)
                    exps=sorted(random.sample(range(0,2*n), m))
                    coefs={e: random.randrange(1,p) for e in exps}
                    bot,top=exps[0],exps[-1]
                    window=top-bot
                    d=gcd_deg_via_roots(coefs,n,p)
                    cases+=1
                    if d<=window: winOK+=1
                    else: bad.append(('WIN',n,p,exps,d,window))
                    if d<window: winTight+=1
                    if d<=min(n,top): minOK+=1
    print(f"cases={cases}")
    print(f"WINDOW bound deg gcd <= (top-bot): {winOK}/{cases}  (strictly tighter than window in {winTight})")
    print(f"MIN bound deg gcd <= min(n, deg g): {minOK}/{cases}")
    if bad: 
        print("VIOLATIONS:", bad[:5])
    else:
        print("NO violations of window bound.")
def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
run()
