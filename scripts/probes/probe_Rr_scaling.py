import itertools, cmath, math
from collections import Counter
def E_char0(n,r):
    mu=[cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
    s=Counter()
    for x in itertools.product(range(n),repeat=r):
        z=sum(mu[i] for i in x); s[(round(z.real,3),round(z.imag,3))]+=1
    return sum(c*c for c in s.values())
def dfact(m):
    pr=1
    while m>0: pr*=m; m-=2
    return pr
# R_r = E_char0/Wick. Test the conjecture 1-R_r ~ r(r-1)/(2n) (leading Sidon/antipodal correction, valid r<<sqrt n).
# KEY: at fixed small r, does R_r -> 1 as n grows? (=> at PRIZE scale r=110<<sqrt(2^30)=32768, R_r~1 NOT ->0).
print("1-R_r  vs  leading conjecture r(r-1)/(2n).  Does R_r->1 at fixed r as n grows?")
print(f"{'n':>4}{'r':>3}{'R_r':>10}{'1-R_r':>10}{'r(r-1)/2n':>12}{'(1-R_r)*2n/(r(r-1))':>20}")
for n in [8,16,32]:
    rmax = 8 if n==8 else (6 if n==16 else 5)
    for r in range(2,rmax+1):
        E0=E_char0(n,r); Wick=dfact(2*r-1)*n**r
        R=E0/Wick; dev=1-R; conj=r*(r-1)/(2*n)
        ratio = dev/conj if conj>0 else float('nan')
        print(f"{n:>4}{r:>3}{R:>10.5f}{dev:>10.5f}{conj:>12.5f}{ratio:>20.4f}")
    print()
print("R_2 should be EXACTLY 1-1/n (from E_2=3n^2-3n):")
for n in [8,16,32]:
    E0=E_char0(n,2); print(f"   n={n}: R_2={E0/(dfact(3)*n*n):.6f}, 1-1/n={1-1/n:.6f}, E_2={E0} vs 3n^2-3n={3*n*n-3*n}")
print("\nPRIZE scale: n=2^30, r~110, sqrt(n)=2^15=32768 >> 110, so r<<sqrt(n):")
print(f"   leading 1-R_r ~ r(r-1)/(2n) = 110*109/(2*2^30) = {110*109/(2*2**30):.2e}  => R_r ~ 1 (NOT ->0)")
