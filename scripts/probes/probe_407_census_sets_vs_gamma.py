#!/usr/bin/env python3
"""LEAN census probe: #distinct-GAMMA vs #alignable-SETS at deep band, structured worst lines.

Worst lines from the first probe = adjacent high-freq char lines (x^j, x^{j-1}), esp near n/2.
We compute BOTH the alignable-SET count (deployed CensusDomination object) and the
#distinct-GAMMA (the TRUE MCA budget object) at the deep ceiling band a0, prize regime.
Divided differences precomputed once per line.
"""
import itertools, math, sys

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_g(p, n):
    for h in range(2, 4000):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in prime_factors(n)):
            return x
    raise ValueError

def census(u0, u1, xs, p, k, a):
    n = len(xs)
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), k + 1):
        # divided diff
        t0=t1=0
        for i in T:
            den=1
            for j in T:
                if i!=j: den = den*((xs[i]-xs[j])%p)%p
            inv = pow(den,-1,p)
            t0 = (t0 + u0[i]*inv)%p; t1 = (t1 + u1[i]*inv)%p
        e0[T]=t0; e1[T]=t1
    def ratio(T):
        a_,b_=e0[T],e1[T]
        if b_!=0: return (-a_)*pow(b_,-1,p)%p
        return None if a_==0 else 'X'
    sets=0; gam=set()
    for S in itertools.combinations(range(n), a):
        r=None; ok=True; nd=False
        for T in itertools.combinations(S, k+1):
            rt=ratio(T)
            if rt is None: continue
            if rt=='X': ok=False; break
            nd=True
            if r is None: r=rt
            elif r!=rt: ok=False; break
        if ok and nd: sets+=1; gam.add(r)
    return sets, len(gam)

def run(n,k,a0,p):
    g=find_g(p,n); xs=[pow(g,i,p) for i in range(n)]
    assert len(set(xs))==n
    beta=math.log(p)/math.log(n)
    print(f"\n==== n={n} k={k} a0={a0} p={p} beta={beta:.2f} budget_n={n} ====")
    # structured worst family: adjacent high-freq lines around n/2 and high j
    cand = [(j, j-1) for j in range(2, n)] + [(n//2, n//2-1), (n//2+1, n//2-1)]
    cand = sorted(set(cand))
    ws=(0,None); wg=(0,None)
    for (aa,bb) in cand:
        u0=[pow(x,aa,p) for x in xs]; u1=[pow(x,bb,p) for x in xs]
        s,gm = census(u0,u1,xs,p,k,a0)
        if s>ws[0]: ws=(s,f"x^{aa},x^{bb}")
        if gm>wg[0]: wg=(gm,f"x^{aa},x^{bb}")
        if s>0:
            print(f"   x^{aa:>2},x^{bb:<2} | sets={s:>4}  gamma={gm:>4}")
    print(f"  WORST sets={ws[0]} ({ws[1]}); WORST gamma={wg[0]} ({wg[1]})")
    print(f"  -> SETS {'>n BLOWS UP' if ws[0]>n else '<=n'};  GAMMA {'>n BLOWS UP' if wg[0]>n else '<=n (true budget OK)'}")
    return n, ws[0], wg[0]

def main():
    configs=[(8,2,4,4129),(8,3,5,4129),(16,2,4,65537),(16,3,5,65537),(16,4,6,65537)]
    res=[]
    for c in configs:
        try: res.append(run(*c))
        except Exception as e: print(f"[skip {c}: {e}]")
    print("\n==== SUMMARY (structured worst lines) ====")
    print(f"  {'n':>3} | {'sets':>5} {'gamma':>5} {'n':>4} | verdict")
    for (n,s,gm) in res:
        print(f"  {n:>3} | {s:>5} {gm:>5} {n:>4} | sets:{'>n' if s>n else '<=n'} gamma:{'>n' if gm>n else '<=n'}")

if __name__=="__main__":
    sys.exit(main())
