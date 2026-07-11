import cmath, math, random
random.seed(31)
def Khat(u,k,m): return sum(u[a]*cmath.exp(-2j*math.pi*a*k/m) for a in range(1,m))
print("Spectral mean: sum_k |K_hat(k)|^2 == m*(m-1) ?")
for m in [3,5,7,11]:
    u=[0j]+[cmath.exp(1j*random.uniform(0,2*math.pi)) for _ in range(m-1)]
    s=sum(abs(Khat(u,k,m))**2 for k in range(m))
    print(f"  m={m}: sum={s:.6f}  m*(m-1)={m*(m-1)}  mean={s/m:.4f} (should be {m-1})")
