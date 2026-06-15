# Route 36 first step: are smooth-domain (mu_n) deep holes the worst-case concentration points u0?
# Setup: RS[k] eval code on D=mu_n (n points). A received word u: D->F_p. 
# distance(u, RS) = n - max_{deg<k poly g} #{x in D: u(x)=g(x)}.  covering radius R = max_u distance.
# deep hole = u achieving distance = R.
# concentration object (the prize u0): for the pencil family, #bad-gamma = #{gamma: u0+gamma*u1 has
#   correlated agreement >= (1-delta)n with RS}. We test the SIMPLER deep-hole question first:
#   compute distance(u,RS) for structured u (monomials x^j, j=0..n-1) over mu_n, find the deep holes,
#   and SEPARATELY find which u maximize the single-word agreement-list (the concentration proxy).
import itertools, math
from sympy import primitive_root, isprime

def isp(x): return isprime(x)
def setup(n,beta=4):
    p=n**beta
    while not ((p-1)%n==0 and isp(p)): p+=1
    g=pow(primitive_root(p),(p-1)//n,p)
    mu=[pow(g,j,p) for j in range(n)]
    return p,mu

def dist_to_RS(u,mu,k,p):
    """distance = n - max over deg<k g of agreement. Compute max agreement by: for each k-subset of
       points, interpolate g, count agreement. (exact, feasible small n)."""
    n=len(mu)
    best=0
    # candidate g determined by any k points; enumerate k-subsets, interpolate, count agreement
    for T in itertools.combinations(range(n),k):
        # Lagrange interpolate g through (mu[i],u[i]) for i in T, eval at all points
        ag=0
        for x_idx in range(n):
            x=mu[x_idx]; val=0
            for i in T:
                num=1;den=1
                for j in T:
                    if i!=j:
                        num=num*((x-mu[j])%p)%p; den=den*((mu[i]-mu[j])%p)%p
                val=(val+u[i]*num*pow(den,p-2,p))%p
            if val==u[x_idx]: ag+=1
        best=max(best,ag)
    return n-best, best

def main():
    for n in [8,16]:
        p,mu=setup(n)
        k=3
        print(f"\n=== n={n} p={p} k={k} (RS[{k}] on mu_{n}); covering radius scan over monomials u=x^j ===")
        R=0; deep=[]
        rows=[]
        for j in range(n):
            u=[pow(mu[i],j,p) for i in range(n)]
            d,ag=dist_to_RS(u,mu,k,p)
            rows.append((j,d,ag))
            R=max(R,d)
        for (j,d,ag) in rows:
            mark=" <-- DEEP HOLE" if d==R else ""
            isRS = (j<k)
            print(f"  u=x^{j:2d}: dist={d:2d} max-agree={ag:2d} {'(in RS, dist~0)' if isRS else ''}{mark}")
        deep=[j for (j,d,ag) in rows if d==R]
        print(f"  covering-radius R={R}; deep-hole monomials j in {deep}")
        # the far-line worst pencil from wf-D2 had u0=x^a, u1=x^b with b-a composite (n/4). 
        # Q: is the deep-hole exponent set related to the worst-concentration pencil exponents?
        print(f"  (wf-D2 worst pencil exps ~ a,b with gcd(b-a,n)=n/4; deep-hole exps here: {deep})")

if __name__=="__main__": main()
