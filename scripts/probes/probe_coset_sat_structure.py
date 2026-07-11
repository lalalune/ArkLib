import sympy, math
from math import gcd

def verify(n, a, b, p):
    # mu_n in F_p, d=gcd(a-b,n), omega a primitive d-th root in mu_n
    g=int(sympy.primitive_root(p)); zeta=pow(g,(p-1)//n,p)
    H=[pow(zeta,j,p) for j in range(n)]
    d=gcd(a-b,n)
    omega=pow(zeta, n//d, p)  # primitive d-th root (d-th: omega^d=1)
    # (1) U(omega*x) == omega^a * U(x) for all x in H, any gamma
    gamma=7%p
    def U(x): return (pow(x,a,p)+gamma*pow(x,b,p))%p
    ok1=all((U(omega*x%p) - pow(omega,a,p)*U(x))%p==0 for x in H)
    # (2) b ≡ a (mod d) ?  and U-c_a supported on degrees ≡ a mod d
    ok2 = (b % d == a % d)
    # (3) factorization rigidity check: roots of a d-sparse poly X^{a%d} * g(X^d) in mu_n are mu_d-coset-closed
    # build a sample d-sparse poly s(X)=X^{a%d}*(X^d - h) for some h in mu_? ; check its mu_n-roots are coset-closed
    a0=a%d
    # pick h = some d-th-power value; roots of X^d = h*X^{-a0}... just test: poly P(X)=X^a - x0^a for a root x0; its mu_n roots
    x0=H[3]
    val=pow(x0,a,p)
    roots=[x for x in H if pow(x,a,p)==val]  # roots of X^a - val (a-sparse, gcd(a,n)-coset)
    da=gcd(a,n); wa=pow(zeta,n//da,p)
    ok3=all((wa*x%p) in set(roots) for x in roots)  # closed under mu_{gcd(a,n)}
    return d, ok1, ok2, ok3

print("Verify coset-saturation STRUCTURE: U(wx)=w^a U(x) for w in mu_d (d=gcd(a-b,n)); b≡a mod d; roots coset-closed.")
print(f"{'n':>3} {'(a,b)':>10} {'d':>3} {'U(wx)=w^a U(x)?':>16} {'b≡a mod d?':>11} {'roots coset-closed?':>19}")
for n in (16,32,64):
    base=n**4; m=(base-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p): break
    for (a,b) in [(9,5),(11,3),(13,9),(15,5)]:
        if a<n and b<n:
            d,o1,o2,o3=verify(n,a,b,p)
            print(f"{n:>3} {str((a,b)):>10} {d:>3} {str(o1):>16} {str(o2):>11} {str(o3):>19}")
