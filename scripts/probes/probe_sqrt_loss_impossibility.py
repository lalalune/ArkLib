"""Verify the crisp impossibility: the energy route (list <= sqrt(n*E)) can NEVER give list <= n,
because E(mu_n) >= n^2 always. So even a PERFECT energy bound E = n^2 (Sidon, the minimum) gives
list <= sqrt(n * n^2) = n^1.5 > n. The window needs list <= q*eps* = n. Energy route is fatally
short by a factor n^0.5, UNCONDITIONALLY. (Sharpens W2 from 'sub-Johnson' to a quantitative gap.)"""
# E(G) = #{(a,b,c,d) in G^4 : a+b = c+d}. Diagonal a+b=a+b: for every (a,b), set c=a,d=b => n^2 quads.
# So E >= n^2 ALWAYS (any abelian group, any subset of size n). Verify on small mu_n.
def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def subgroup(n,p):
    for g0 in range(2,p):
        g=pow(g0,(p-1)//n,p)
        if g!=1 and pow(g,n,p)==1 and all(pow(g,n//d,p)!=1 for d in range(2,n+1) if n%d==0):
            D=set()
            x=1
            for _ in range(n): D.add(x); x=x*g%p
            if len(D)==n: return sorted(D)
    return None
print("n | p | E(mu_n) | n^2 | E>=n^2? | sqrt(n*E) | n (budget) | energy-route list >= ?")
for n in [4,6,8,10,12,16]:
    p=n+1
    while not (is_prime(p) and (p-1)%n==0): p+=1
    D=subgroup(n,p)
    if D is None: continue
    Ds=set(D)
    from collections import Counter
    sums=Counter()
    for a in D:
        for b in D:
            sums[(a+b)%p]+=1
    E=sum(c*c for c in sums.values())
    import math
    print(f"{n} | {p} | E={E} | n^2={n*n} | {E>=n*n} | sqrt(nE)={math.sqrt(n*E):.1f} | n={n} | list >= n^1.5={n**1.5:.1f} > n={n}")
print()
print("CONCLUSION: E(mu_n) >= n^2 ALWAYS (diagonal). Energy route list <= sqrt(n*E) >= n^1.5 > n.")
print("=> The energy/2nd-moment route is UNCONDITIONALLY insufficient for the floor (list <= n),")
print("   short by a factor n^0.5 even with the impossible-to-beat minimum energy E = n^2.")
print("   The floor REQUIRES a route that is NOT 2nd-moment (the sqrt-loss is fatal, not just lossy).")
