# DECISIVE: does the char-p energy-Wick faithfulness threshold T(n,r) GROW with depth r, or stay ~n^2?
# T(n,r) = smallest prime p=1 mod n where E_r^{(p)}(mu_n) > (2r-1)!!*n^r (char-0 Wick ceiling).
# If T(n,r) ~ n^2 UNIFORMLY in r => potential CLOSURE (prove bound for p>Cn^2 all r).
# If T(n,r) GROWS with r (toward prize q~n^4 at r~log q) => irreducibly BGK.
import cmath, math, sympy
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def Er_charp(n,p,r):
    A=[abs(sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in musub(n,p))) for b in range(p)]
    return sum(a**(2*r) for a in A)/p
def dfact(r):
    v=1
    for i in range(1,2*r,2): v*=i
    return v
print("Faithfulness threshold T(n,r) = smallest prime p=1 mod n with E_r^p > Wick, vs depth r:")
print("(if T grows with r -> BGK; if T~n^2 flat in r -> closure path)")
for n in [8,16]:
    print(f"\n n={n} (n^2={n*n}, n^3={n**3}, n^4={n**4}):")
    for r in range(2,11):
        W=dfact(r)*n**r; T=None; m=1; cnt=0
        while cnt<120:
            p=n*m+1; m+=1
            if not sympy.isprime(p): continue
            cnt+=1
            if Er_charp(n,p,r)>W: T=p; break
        if T:
            exp=math.log(T)/math.log(n)
            print(f"   r={r:2d}: T(n,r)={T:7d} = n^{exp:.2f}  (Wick={W:.1e})")
        else:
            print(f"   r={r:2d}: T(n,r) > 120th prime (none small; bound robust)  (Wick={W:.1e})")
