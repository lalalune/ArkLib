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
# char-0 moment ratio R_r = E_char0(n,r)/((2r-1)!!*n^r).  Does R_r -> 0 (strict sub-Gaussian gap growing)?
# Fit against candidate rates: 1/sqrt(pi r), geometric c^r, const.
print("char-0 moment ratio R_r = E_char0/Wick.  Does it ->0?  rate?")
for n in [8,16]:
    rmax = 8 if n==8 else 6
    print(f"\n n={n}:")
    print(f"   {'r':>3}{'E_char0':>16}{'Wick':>18}{'R_r':>9}{'R_r*sqrt(r)':>12}{'R_{r}/R_{r-1}':>13}")
    prev=None
    Rs=[]
    for r in range(2,rmax+1):
        E0=E_char0(n,r); Wick=dfact(2*r-1)*n**r
        R=E0/Wick; Rs.append((r,R))
        ratio = (R/prev) if prev else float('nan')
        print(f"   {r:>3}{E0:>16}{Wick:>18}{R:>9.4f}{R*math.sqrt(r):>12.4f}{ratio:>13.4f}")
        prev=R
    # crude power-law fit R_r ~ A * r^{-s}: estimate s from last two
    if len(Rs)>=2:
        (r1,R1),(r2,R2)=Rs[-2],Rs[-1]
        s = -math.log(R2/R1)/math.log(r2/r1)
        print(f"   => local power-law exponent s (R_r~r^-s) between r={r1},{r2}: s={s:.3f}  (1/2 = 1/sqrt(r) law)")
        # geometric estimate
        g = R2/R1
        print(f"   => local geometric ratio R_r/R_{{r-1}} = {g:.4f} (const<1 => geometric decay to 0)")
