# PROBE: quantify the EXACT gap between proven SOTA bounds and the (G)-floor sqrt(2n log m)
# for the worst-case max Gaussian period M(n)=max_b|sum_{x in mu_n} e_p(bx)| over a PROPER
# 2-power subgroup mu_n of F_p* in the prize regime p ~ n^beta, beta in [4,5].
#
# SOTA proven bound (di Benedetto-Garaev-Garcia-Gonzalez-Shparlinski-Trujillo 2020, Thm 3.1):
#   for p^{1/2} > H > p^{1/4}:  M(H) <= H^{2689/2880} p^{1/72}  (= H^{1-31/2880} when H~p^{1/4})
# Trivial bound: M <= n. Floor needed by (G): sqrt(2 n log m), m=(p-1)/n.
import cmath, math

def isprime(q):
    if q < 2: return False
    if q % 2 == 0: return q == 2
    i = 3
    while i*i <= q:
        if q % i == 0: return False
        i += 2
    return True

def factor(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g

def maxperiod(n,p):
    g=primroot(p); m=(p-1)//n
    z=pow(g,m,p); G=[pow(z,i,p) for i in range(n)]
    mx=0.0; b=1
    for i in range(m):
        v=abs(sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in G))
        if v>mx: mx=v
        b=b*g%p
    return mx,m

def find_prime(n, beta):
    target=int(round(n**beta))
    q=target | 1
    # search upward for prime with (q-1) % n == 0
    while True:
        if (q-1)%n==0 and isprime(q): return q
        q+=2

print("Worst-case max Gaussian period M(n) vs proven SOTA bound vs (G)-floor")
print("mu_n = PROPER 2-power subgroup of F_p*, prize regime p~n^beta")
print("="*100)
# keep p modest so the m-coset sweep (m=(p-1)/n ~ n^{beta-1}) is feasible
for n in [16, 32, 64]:
    for beta in [4.0, 4.25, 4.5]:
        p = find_prime(n, beta)
        m = (p-1)//n
        if m > 600000:   # cap the sweep cost
            continue
        M, m = maxperiod(n,p)
        actual_beta = math.log(p)/math.log(n)
        floor = math.sqrt(2*n*math.log(m))
        # SOTA proven upper bound (valid since p^{1/4} < n < p^{1/2} i.e. 2 < beta < 4 ... check)
        sota = (n**(2689/2880)) * (p**(1/72))
        triv = n
        # exponent of n that SOTA proves M <= n^{e_sota}
        e_sota = math.log(sota)/math.log(n)
        e_M    = math.log(M)/math.log(n)      # actual exponent
        e_floor= math.log(floor)/math.log(n)  # floor exponent (~0.5 + tiny)
        print(f"n={n:3d} beta={actual_beta:.2f} p={p:>10d} m={m:>8d}")
        print(f"    actual M={M:8.2f} (n^{e_M:.3f})   floor sqrt(2n log m)={floor:7.2f} (n^{e_floor:.3f})   ratio M/floor={M/floor:.3f}")
        print(f"    SOTA proven UB={sota:11.1f} (n^{e_sota:.3f})   trivial=n={triv}")
        print(f"    GAP: SOTA proves exponent {e_sota:.3f}; floor needs {e_floor:.3f}; truth ~{e_M:.3f}.  SOTA bound / floor = {sota/floor:.3e}")
        print()
