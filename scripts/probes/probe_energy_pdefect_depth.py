"""#407: WHERE does the deep-moment wall bite? Measure E_r(mu_n) mod p vs the char-0 value.

E_r(mu_n) = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_i (in F_p) }.
The char-0 value E_r^{(0)} = same count but over the COMPLEX r-th roots (no wraparound mod p);
by the in-tree Bessel even-moment law E_r^{(0)} = (2r)! [x^r] I0(2 sqrt x)^{n/2}.
The 'p-defect' = E_r - E_r^{(0)} >= 0 counts EXTRA additive coincidences that exist only mod p.
The prize needs E_r ~ E_r^{(0)} (no inflation) up to r ~ ln q; this probe finds the smallest r
where the defect becomes nonzero / non-negligible, for prize-sized (n=p^{1/beta}) primes.

Method (exact, via convolution of the sumset distribution): for r up to ~5, count r-fold sums
of mu_n by FFT-free integer convolution of the indicator over Z/p (p must be modest). Compare to
the char-0 count obtained by the same convolution over Z (no mod) -- i.e. embed mu_n as integers
in [0,p) and count integer solutions sum x_i = sum y_i WITHOUT reduction (that IS char-0 since the
roots are distinct reals... NO -- char-0 means roots of unity in C). We instead get E_r^{(0)} from
the Bessel law directly and compare E_r (mod p, measured) against it.
"""
import sys, math
import numpy as np
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root

def bessel_moment(n, r):
    """E_r^{(0)} = (2r)! [x^r] I0(2 sqrt x)^{n/2}, I0(2 sqrt x)=sum_k x^k/(k!)^2."""
    # power series of I0(2 sqrt x) up to x^r:
    a = [0.0]*(r+1)
    for k in range(r+1): a[k] = 1.0/math.factorial(k)**2
    # raise to power n/2 (n even) via repeated polynomial mult mod x^{r+1}
    def pmul(u,v):
        w=[0.0]*(r+1)
        for i in range(r+1):
            if u[i]==0: continue
            for j in range(r+1-i): w[i+j]+=u[i]*v[j]
        return w
    res=[0.0]*(r+1); res[0]=1.0
    base=a[:]; e=n//2
    while e>0:
        if e&1: res=pmul(res,base)
        e>>=1
        if e>0: base=pmul(base,base)
    return math.factorial(2*r)*res[r]

def Er_mod_p(p, n, r):
    """exact E_r mod p via r-fold convolution of mu_n indicator over Z/p."""
    g=primitive_root(p); eta=pow(g,(p-1)//n,p)
    ind=np.zeros(p, dtype=np.float64)
    x=1
    for _ in range(n): ind[x]+=1.0; x=x*eta%p
    # r-fold cyclic convolution via FFT
    F=np.fft.rfft(ind)
    Fr=F**r
    conv=np.fft.irfft(Fr, n=p)            # conv[s] ~ #{r-tuples summing to s mod p}
    conv=np.round(conv)
    Er=float((conv*conv).sum())          # sum_s c_s^2 = #{sum x = sum y}
    return Er

print("E_r(mu_n) mod p  vs  char-0 Bessel value E_r^(0);  defect ratio = E_r / E_r^(0)")
print("(ratio 1.000 = char-0 exact, no p-defect; >1 = extra mod-p coincidences => wall bites)")
for n, beta in ((16,4.0),(16,5.0),(32,4.0),(32,5.0)):
    base=int(round(n**beta)); base-=base%n; base+=1; p=base
    while not(is_prime(p) and odd_part((p-1)//n)>1): p+=n
    print(f"\n n={n}, beta~{beta}, p={p} (p/n={p//n}, r_max~2beta={2*beta:.0f}):")
    print(f"   {'r':>3} {'E_r mod p':>16} {'E_r^(0) char0':>16} {'ratio':>8}")
    for r in range(2, 6):
        if p > 6_000_000: 
            print(f"   {r:>3}  (p too large to convolve exactly)"); continue
        Er=Er_mod_p(p,n,r); E0=bessel_moment(n,r)
        print(f"   {r:>3} {Er:>16.0f} {E0:>16.0f} {Er/E0:>8.4f}")
print("\nReading: first r with ratio>1 = depth where char-0 (Gaussian) energy fails mod p.")
print("If ratio==1 through r=5 for prize-sized p, the Gaussian regime holds deep (good for the law).")
