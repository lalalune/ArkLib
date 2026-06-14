import cmath, math
def is_prime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def find_prime(n,target):
    p=target-(target%n)+1
    for d in range(0,40*n,n):
        if is_prime(p+d):return p+d
    return None
def prim_root(p):
    facs=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:facs.add(d);m//=d
        d+=1
    if m>1:facs.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in facs):return g
def analyze(n,p):
    g=prim_root(p);f=(p-1)//n;tp=2*math.pi
    ind={};cur=1
    for i in range(p-1):ind[cur]=i;cur=cur*g%p
    # Gauss sums g(chi_s), chi_s(x)=e(2πi n s ind(x)/(p-1)), s=0..f-1
    Gphase=[]
    for s in range(f):
        gs=sum(cmath.exp(1j*tp*(n*s*ind[x])/(p-1))*cmath.exp(1j*tp*x/p) for x in range(1,p))
        Gphase.append(cmath.phase(gs))
    # IDEA A: is arg g(chi_s) structured in s? test against quadratic fit (Stickelberger ~ quadratic-ish)
    # unwrap not needed; test serial correlation of phases
    import statistics
    diffs=[(Gphase[s+1]-Gphase[s])%(tp) for s in range(1,f-1)]  # successive phase increments
    # if structured (arithmetic progression of phase), diffs constant; if random, uniform
    dvar=statistics.pvariance(diffs) if len(diffs)>1 else 0
    # IDEA B: period tail vs random-walk (Kluyver). |eta_b| distribution.
    H=[pow(g,f*i,p) for i in range(n)]
    mags=sorted(abs(sum(cmath.exp(1j*tp*((b*x)%p)/p) for x in H)) for b in range(1,p))
    M=mags[-1]
    # Rayleigh-ish tail: P(|eta|>r) ~ exp(-r^2/n). check rate at the top: r where survival=1/f, 10/p etc
    # large-deviation: -ln(survival)/r^2 should be ~1/n
    import bisect
    def surv(r): return (len(mags)-bisect.bisect_left(mags,r))/len(mags)
    rates=[]
    for r in [math.sqrt(n)*c for c in [1.5,2.0,2.5,3.0]]:
        sv=surv(r)
        if 0<sv<1: rates.append((r/math.sqrt(n), -math.log(sv)/(r*r/n)))
    print(f"n={n} p={p} f={f}: M/√n={M/math.sqrt(n):.2f}  M/√(2n ln f)={M/math.sqrt(2*n*math.log(f)):.3f}")
    print(f"  IDEA A (Gauss phase structure): phase-increment variance={dvar:.3f} (uniform={tp**2/12:.3f}=random; ≪ ⟹ structured)")
    print(f"  IDEA B (random-walk tail rate -ln(surv)/(r²/n), should→1 if Rayleigh): {[(f'{c:.1f}σ:{v:.2f}') for c,v in rates]}", flush=True)
for (n,beta) in [(8,4),(16,3),(16,4)]:
    p=find_prime(n,int(round(n**beta)))
    if p and p<70000: analyze(n,p)
