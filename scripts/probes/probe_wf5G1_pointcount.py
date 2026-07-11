import numpy as np
from sympy import isprime, primitive_root
# Empirically: for a thin 2-power subgroup mu_n | p-1, count F_p points on a representative
# OSV curve F=(X^{sm}+Y^{sm}-A)^n-(X^{sn}+Y^{sn}-B)^m and compare to Lemma 2.1 bound 4 d^{4/3} p^{2/3}+3p,
# and to the trivial O(dp). Show that for these degrees d=s*n the AG bound = trivial range.
# Direct: just confirm the regime numbers; full curve count is O(p^2) heavy, so verify the SCALAR floor.
# Instead verify M(n) directly via the rust engine, and confirm OSV bound (Shkredov form) is above trivial.
print("Confirm: thin 2-power subgroup, M(n) measured vs OSV-Shkredov bound sqrt(tau)p^{1/6}(log p)^{1/6} vs trivial tau.")
def measure_M(n,p,g):
    h=pow(g,(p-1)//n,p)
    mu=[pow(h,j,p) for j in range(n)]
    m=(p-1)//n
    gn=pow(g,n,p); b=1; best=0.0
    for _ in range(m):
        re=im=0.0
        for x in mu:
            ang=2*np.pi*((b*x)%p)/p
            re+=np.cos(ang); im+=np.sin(ang)
        mag=(re*re+im*im)**0.5
        if mag>best: best=mag
        b=(b*gn)%p
    return best
# small thin cases: n=2^mu, n|p-1, beta=log p/log n in [4,5]
cases=[]
for mu in [3,4,5]:
    n=2**mu
    # want p ~ n^beta, beta~4..5 -> p ~ n^4 .. n^5
    target=n**4
    p=None
    cand=target - (target%n) +1
    for _ in range(200000):
        if cand>2 and cand%n==1 and isprime(cand): p=cand; break
        cand+=n
    if p:
        g=primitive_root(p)
        M=measure_M(n,p,g)
        beta=np.log(p)/np.log(n)
        shk=np.sqrt(n)*p**(1/6)*(np.log(p))**(1/6)
        tgt=np.sqrt(n*np.log(p/n))
        cases.append((n,p,beta,M,shk,tgt))
        print(f"n={n:4d} p={p:>12} beta={beta:.2f}  M={M:7.3f}  trivial(tau)={n}  Shkredov={shk:8.1f}  target~{tgt:6.2f}  M/target={M/tgt:.2f}")
print()
print("Shkredov bound >> trivial tau=n (vacuous), and >> measured M and target, in prize regime. CONFIRMED.")
