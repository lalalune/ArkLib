# UDR-edge stress test: (q,12,3,4), j=2=w-2, UDR=4.5 (w=4 just inside).
# RESULT (q,12,3,4) j=w-2=2 (deepest window stratum, just inside UDR):
#   q=37: coset=3 random-max=3; q=73: 3,3; q=109: 3,3  -- all = n/w EXACTLY, q-stable.
# Combined with j=0 (Lean-pinned both sides) and j=1 (probe-exact 4=n/w): the working
# law for the WHOLE below-UDR window is per-stack max bad = n/w. Floor safe.
# Question: does per-stack max bad stay ~n/w = 3 as q grows, or grow?
import random
from itertools import combinations
exec(open('scripts/probes/probe_aboveudr_cost_law.py').read().split("def run(")[0])
random.seed(8)
def bad_count(q,n,k,w,dom,u0,u1):
    pw=[[pow(x,j,q) for j in range(k)] for x in dom]
    def cons(S,vals):
        rows=[pw[i][:]+[vals[i]%q] for i in S]
        m_,r=len(rows),0
        for c in range(k):
            p=next((i for i in range(r,m_) if rows[i][c]%q),None)
            if p is None: continue
            rows[r],rows[p]=rows[p],rows[r]
            inv=pow(rows[r][c],q-2,q); rows[r]=[(v*inv)%q for v in rows[r]]
            for i in range(m_):
                if i!=r and rows[i][c]%q:
                    f=rows[i][c]; rows[i]=[(a-f*b)%q for a,b in zip(rows[i],rows[r])]
            r+=1
        return not any(rows[i][k]%q for i in range(r,m_))
    subs=list(combinations(range(n),n-w))
    bad=0
    for gam in range(q):
        line=[(u0[i]+gam*u1[i])%q for i in range(n)]
        for S in subs:
            S=list(S)
            if not cons(S,line): continue
            if cons(S,list(u0)) and cons(S,list(u1)): continue
            bad+=1; break
    return bad
for q in (37, 73, 109):
    n,k,w = 12,3,4
    g = find_gen(q,n)
    if g is None: print(f"q={q}: no domain"); continue
    dom=[pow(g,i,q) for i in range(n)]
    best=0
    # random rational stacks
    for _ in range(300):
        l0=[random.randrange(q) for _ in range(w)]+[1]
        l1=[random.randrange(q) for _ in range(w)]+[1]
        if not all(evalp(l0,x,q) and evalp(l1,x,q) for x in dom): continue
        R0=[random.randrange(q) for _ in range(w+k)]
        R1=[random.randrange(q) for _ in range(w+k)]
        u0=tuple(evalp(R0,x,q)*pow(evalp(l0,x,q),q-2,q)%q for x in dom)
        u1=tuple(evalp(R1,x,q)*pow(evalp(l1,x,q),q-2,q)%q for x in dom)
        b=bad_count(q,n,k,w,dom,u0,u1)
        if b>best: best=b
    # coset family (w | n: 4 | 12, m = 3)
    m = n//w
    munw={pow(x,w,q) for x in dom}
    es=[e for e in range(2,q) if e not in munw][:2]
    if len(es)==2:
        e0,e1=es
        u0=tuple(pow((pow(x,w,q)-e0)%q,q-2,q) for x in dom)
        u1=tuple(pow((pow(x,w,q)-e1)%q,q-2,q) for x in dom)
        b=bad_count(q,n,k,w,dom,u0,u1)
        if b>best: best=b
        print(f"q={q}: coset family bad = {b}, random-max overall best = {best}  (n/w = {m})")
    else:
        print(f"q={q}: best = {best}")
