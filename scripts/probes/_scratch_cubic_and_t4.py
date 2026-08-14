#!/usr/bin/env python3
"""#389 part 2: validate the Sylvester cubic (t=3) and settle the deep band (t>=4).

(1) SYLVESTER VALIDATION (k=2,m=0,t=3,cap=5): w(x)=x^3 on D=[-h,h].  Confirm
    #explainable-3-cores == #{distinct {a,b,c}<=D : a+b+c=0} ~ Theta(n^2),
    refuting any linear bound at the boundary band; AND it persists SPARSE.
(2) DEEP BAND t=4 (k=2,m=1,cap=6): does a super-linear construction exist?
    - test algebraic words x^d, and the hill-climb optimum's structure;
    - dense (n~q) vs sparse (n<<q): is t=4 super-linear sparse, or suppressed?
(3) The honest regime law: capped supply S*(n,q,t) ~ ? n^? in each regime.
"""
import math, random
from itertools import combinations

def comb(a,t): return math.comb(a,t) if a>=t else 0

def lines_of(w, dom, q):
    n=len(dom); lines={}
    for i,j in combinations(range(n),2):
        dx=(dom[j]-dom[i])%q
        a=((w[j]-w[i])*pow(dx,q-2,q))%q
        b=(w[i]-a*dom[i])%q
        lines.setdefault((a,b),set()).update((i,j))
    return lines

def supply(w,dom,q,t,cap):
    S=0
    for s in lines_of(w,dom,q).values():
        aL=len(s)
        if t<=aL<=cap: S+=comb(aL,t)
    return S

# ---------- (1) Sylvester cubic ----------
print("="*70)
print("(1) SYLVESTER CUBIC w=x^3, t=3, cap=5:  supply vs #triples(a+b+c=0)")
print("    D=[-h,h], n=2h+1, q chosen > 6h (no wraparound).")
for h in (3,5,8,12,18,25):
    n=2*h+1
    q=next(p for p in range(8*h, 16*h) if all(p%r for r in range(2,int(p**.5)+1)))
    dom=[x % q for x in range(-h,h+1)]
    w=[pow(x%q,3,q) for x in range(-h,h+1)]
    # direct triple count
    vals=list(range(-h,h+1))
    triples=sum(1 for a,b,c in combinations(vals,3) if (a+b+c)==0)
    S=supply(w,dom,q,3,5)
    # also the EXPLICIT injection lower bound h^2/9-ish
    lb=0
    A=range(1,h//3+1); B=range(h//3+1,2*h//3+1)
    for a in A:
        for b in B:
            c=-(a+b)
            if -h<=c<=h and len({a,b,c})==3: lb+=1
    print(f"  h={h:3d} n={n:3d} q={q:5d} | #triples(sum0)={triples:5d}  supply={S:5d}  "
          f"match={triples==S}  inj_lb={lb:4d}(~h^2/9={h*h//9})  S/n^2={S/n**2:.3f}")

print("\n  SPARSE check: w=x^3, fixed h, q huge -- does Theta(n^2) PERSIST?")
for h in (8,12,18):
    n=2*h+1; vals=list(range(-h,h+1))
    triples=sum(1 for a,b,c in combinations(vals,3) if a+b+c==0)
    for q in (next(p for p in range(8*h,16*h) if all(p%r for r in range(2,int(p**.5)+1))),
              10007, 1000003):
        dom=[x%q for x in range(-h,h+1)]; w=[pow(x%q,3,q) for x in range(-h,h+1)]
        S=supply(w,dom,q,3,5)
        print(f"  h={h:3d} n={n:3d} q={q:8d} n/q={n/q:.4f} | supply={S:5d} "
              f"(triples={triples}) match={S==triples}")

# ---------- (2) deep band t=4 ----------
print("\n"+"="*70)
print("(2) DEEP BAND t=4, cap=6:  algebraic words x^d, dense vs sparse")
def best_algebraic(n, q, t=4, cap=6):
    dom=list(range(n)); best=0; arg=None
    # try monomial and a few structured words on shifted/symmetric domains
    cands=[]
    for d in range(2,8):
        cands.append((f"x^{d}", [pow(x,d,q) for x in dom]))
        cands.append((f"(x-c)^{d}sym", [pow((x-n//2)%q,d,q) for x in dom]))
    for name,w in cands:
        S=supply(w,dom,q,t,cap)
        if S>best: best=S; arg=name
    return best,arg

def hill_t4(n,q,t=4,cap=6,iters=600,restarts=12,seed=7):
    rnd=random.Random(seed); dom=list(range(n)); best=0
    for r in range(restarts):
        w=[rnd.randrange(q) for _ in range(n)]; cur=supply(w,dom,q,t,cap)
        stale=0
        for _ in range(iters):
            i=rnd.randrange(n); old=w[i]; w[i]=rnd.randrange(q)
            nv=supply(w,dom,q,t,cap)
            if nv>=cur:
                if nv>cur: stale=0
                cur=nv
            else: w[i]=old; stale+=1
            if stale>5*n: break
        best=max(best,supply(w,dom,q,t,cap))
    return best

print("  DENSE (n up to ~q):")
for q in (61,127):
    row=[]
    for n in range(16,q,12 if q>100 else 8):
        hb=hill_t4(n,q); ab,_=best_algebraic(n,q)
        row.append((n,hb,ab))
    for n,hb,ab in row:
        print(f"   q={q} n={n:3d} n/q={n/q:.2f} | hill_S*={hb:4d} S*/n={hb/n:.2f} "
              f"S*/n^2={hb/n**2:.3f} | best_algebraic={ab}")
    # growth exponent fit
    xs=[math.log(n) for n,_,_ in row if _];
    pts=[(math.log(n),math.log(hb)) for n,hb,ab in row if hb>0]
    if len(pts)>=2:
        # least squares slope
        mx=sum(x for x,_ in pts)/len(pts); my=sum(y for _,y in pts)/len(pts)
        sl=sum((x-mx)*(y-my) for x,y in pts)/sum((x-mx)**2 for x,_ in pts)
        print(f"   --> q={q}: fitted growth exponent S* ~ n^{sl:.2f}")
    print()

print("  SPARSE (n<<q):  t=4 suppressed?")
for n in (16,24,32):
    for q in (127,1009,100003):
        hb=hill_t4(n,q,iters=500,restarts=10); ab,an=best_algebraic(n,q)
        print(f"   n={n:3d} q={q:7d} n/q={n/q:.4f} | hill_S*={hb:3d} algebraic={ab}({an})")
    print()
