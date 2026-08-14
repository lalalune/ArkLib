#!/usr/bin/env python3
"""
GG25 (ell, delta, a, b)-curve-decodability: the COVERING curve degree of the mu_n close-list.

This reconciles the two facts:
  (P2) for a FIXED low ell, the count of gamma where ONE degree-ell pencil agrees with a word
       is tiny -- but it covers only the codewords ON that pencil, not the whole list.
  (P1) the WHOLE close-list at the lower window band fills the full k-dim message space.

The GG25 list-decoding bound I(delta) <= ell*n/(a-b) is useful ONLY IF the ENTIRE close-list of
the worst word lies on ONE curve of bounded degree ell (curve-decodability). So the relevant ell
is the MINIMAL degree of a single algebraic curve (rational arc) gamma -> sum_j gamma^j c_j whose
image CONTAINS the whole close-list.

A list of |L| message vectors in F_p^k lies on a degree-ell rational normal arc iff the |L|x(k)
matrix of coordinates has the points fitting a degree-ell Vandermonde parametrization; a clean
necessary condition is ell >= (affine span dimension of the list). We compute, per window band:
   |L|  = worst-word close-list size
   D    = affine span dim of the list (LOWER bound on covering ell; = ell when points generic)
   I_route = D * n / (a - (D+1))   (GG25 count using the covering curve)   vs threshold n.

Plus the implied count-route delta*: largest delta (smallest a, = past Johnson) with I_route <= n.
We compare to Johnson (1-sqrt rho) and capacity (1-rho).
"""
import itertools, math, sys

def is_prime(m):
    if m<2: return False
    for i in range(2,int(m**0.5)+1):
        if m%i==0: return False
    return True
def find_prime(n,lo):
    p=max(lo,n+1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        seen=set(); xx=1; full=True
        for _ in range(p-1):
            xx=(xx*g0)%p
            if xx in seen: full=False; break
            seen.add(xx)
        if full:
            g=pow(g0,(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
    raise RuntimeError
def interp_coeffs(p,xs,ys,k):
    coeffs=[0]*k
    for i in range(k):
        num=[1]; den=1
        for l in range(k):
            if l==i: continue
            new=[0]*(len(num)+1)
            for d,cc in enumerate(num):
                new[d]=(new[d]-cc*xs[l])%p; new[d+1]=(new[d+1]+cc)%p
            num=new; den=(den*((xs[i]-xs[l])%p))%p
        inv=pow(den,p-2,p); scale=(ys[i]*inv)%p
        for d in range(len(num)): coeffs[d]=(coeffs[d]+num[d]*scale)%p
    return tuple(coeffs)
def eval_coeffs(p,coeffs,H,k):
    return tuple(sum(coeffs[d]*pow(x,d,p) for d in range(k))%p for x in H)
def the_list(p,H,w,k,a_min):
    n=len(H); found={}
    for sub in itertools.combinations(range(n),k):
        xs=[H[i] for i in sub]; ys=[w[i] for i in sub]
        c=interp_coeffs(p,xs,ys,k); ev=eval_coeffs(p,c,H,k)
        if sum(1 for j in range(n) if ev[j]==w[j])>=a_min: found[c]=1
    return list(found.keys())
def mat_rank(rows,p):
    rows=[list(r) for r in rows]
    if not rows: return 0
    m=len(rows); nc=len(rows[0]); rk=0; col=0
    while col<nc and rk<m:
        piv=None
        for r in range(rk,m):
            if rows[r][col]%p!=0: piv=r;break
        if piv is None: col+=1;continue
        rows[rk],rows[piv]=rows[piv],rows[rk]
        inv=pow(rows[rk][col],p-2,p); rows[rk]=[(x*inv)%p for x in rows[rk]]
        for r in range(m):
            if r!=rk and rows[r][col]%p!=0:
                f=rows[r][col]; rows[r]=[(rows[r][c]-f*rows[rk][c])%p for c in range(nc)]
        rk+=1; col+=1
    return rk
def span_dim(L,k,p):
    if len(L)<=1: return 0
    c0=L[0]; diffs=[tuple((L[i][d]-c0[d])%p for d in range(k)) for i in range(1,len(L))]
    return mat_rank(diffs,p)

def run(n,k,max_p=200):
    p=find_prime(n,2*n)
    if p>max_p: return None
    H=subgroup(p,n); rho=k/n
    john=1-math.sqrt(rho); cap=1-rho
    a_cap=math.floor(rho*n); a_john=math.ceil(math.sqrt(rho)*n)
    cand={}
    for d in [k,k+1,n-2,n-1]: cand[f"x^{d}"]=[pow(x,d,p) for x in H]
    cand["x^k+x^(n-1)"]=[(pow(x,k,p)+pow(x,n-1,p))%p for x in H]
    cand["x^k+x^(n-2)"]=[(pow(x,k,p)+pow(x,n-2,p))%p for x in H]
    rows=[]
    for a in range(a_cap+1,a_john+1):
        best=0; bL=None
        for name,w in cand.items():
            L=the_list(p,H,w,k,a)
            if len(L)>best: best=len(L); bL=L
        D=span_dim(bL,k,p) if bL else 0
        delta=1-a/n
        if best>0 and a>D+1: Iroute=D*n/(a-(D+1))
        elif best==0: Iroute=0.0
        else: Iroute=float('inf')
        rows.append((a,round(delta,3),best,D,round(Iroute,1) if Iroute!=float('inf') else 'inf'))
    return dict(n=n,k=k,p=p,rho=round(rho,3),john=round(john,3),cap=round(cap,3),rows=rows)

if __name__=="__main__":
    print("GG25 COVERING curve degree D of the worst mu_n close-list, per window band.")
    print("I_route = D*n/(a-D-1) is GG25's count via the curve covering the WHOLE list.")
    print("If D ~ k = rho*n (full span) at the lower window band, I_route ~ Theta(n) = WALL.")
    print("="*92)
    for (n,k) in [(8,4),(8,2),(16,8),(16,4),(16,6)]:
        r=run(n,k)
        if not r: print(f"n={n} k={k} skipped"); continue
        print(f"\nn={n} k={k} p={r['p']} rho={r['rho']} window=({r['john']},{r['cap']}) "
              f"k={k} | threshold n={n}")
        print(f"   {'a':>3} {'delta':>6} {'|L|':>5} {'D(=cover ell)':>13} {'I_route=D*n/(a-D-1)':>20}")
        for (a,delta,L,D,Ir) in r['rows']:
            tag=""
            if isinstance(Ir,float) and L>0:
                tag=" <=n WINDOW" if Ir<=n else " >n"
            elif Ir=='inf': tag=" VACUOUS(D+1>=a)"
            full=" [FULL SPAN=k]" if D>=k-0 and L>0 else ""
            print(f"   {a:>3} {delta:>6.3f} {L:>5} {D:>13} {str(Ir):>20}{tag}{full}")
        sys.stdout.flush()
