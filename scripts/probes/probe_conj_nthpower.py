import sympy
from collections import Counter

def subgroup(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            return [pow(z,j,p) for j in range(n)], p

# M2 = #{(x,y) in mu_n^2 : (1+x)^n = (1+y)^n}  (the n-th-power fiber energy; structured even over huge p)
def M2(H,p,n):
    vals=[pow((1+x)%p, n, p) for x in H]
    c=Counter(vals)
    return sum(v*v for v in c.values())

def fibers(H,p,n):  # distinct (1+x)^n values, and max fiber size
    vals=[pow((1+x)%p, n, p) for x in H]
    c=Counter(vals)
    return len(c), max(c.values())

print("n-th-power shifted energy M2(n)=#{(1+x)^n=(1+y)^n}, and fiber structure.")
print(f"{'n':>3} {'fac':>9} {'M2':>5} {'#fibers':>8} {'maxfiber':>9} {'E+(mu_n)':>9}")
for n in [3,5,7,9,11,13,4,8,16,32,6,12,15]:
    H,p=subgroup(n)
    m2=M2(H,p,n); nf,mf=fibers(H,p,n)
    ep = (3*n*n-3*n) if n%2==0 else (2*n*n-n)
    print(f"{n:>3} {str(sympy.factorint(n)):>9} {m2:>5} {nf:>8} {mf:>9} {ep:>9}")
print("\nCheck: is E+(mu_n) = n*M2 ? (RepCountFiber link) or another closed form for M2?")
