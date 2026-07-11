import math
from sympy import primitive_root, isprime

# EXACT structural lower bound at Fermat prime p=2^k+1.
# The element 2 has order: 2^k = -1 mod p => 2^{2k}=1 => ord(2)=2k... wait p-1=2^k.
# Actually 2 is a QR or not? For p=2^k+1, 2 has order dividing p-1=2^k.
# Powers of 2: {1,2,4,...,2^{k-1}, 2^k=-1, -2, -4, ...}. So <2> has order 2k? No:
# 2^k = -1, 2^{2k}=1, but 2k may exceed p-1=2^k. For p=65537,k=16: 2^16=65536=-1, 2^32=1.
# ord(2)=32. So <2> = mu_32 (the order-32 subgroup)!
# General: ord(2) = 2k in Z, but in F_p, 2^k=-1 so ord(2)=2k ONLY if 2k | p-1=2^k.
# 2k=2^{?}: for k=16, 2k=32=2^5 | 2^16. YES. So <2>=mu_{2k}=mu_32.

# So mu_32 = {+-2^j : j=0..15} = {+-1,+-2,...,+-2^15} mod 65537. EXACT.
# eta_1 over mu_32 = sum_{j=0}^{15} [cos(2pi 2^j/p) + cos(2pi(-2^j)/p)]
#                  = 2 sum_{j=0}^{15} cos(2pi 2^j/p).
# Most 2^j << p so cos~1. Exact:
p=65537; k=16
eta1_32 = 2*sum(math.cos(2*math.pi*(2**j)/p) for j in range(k))
print(f"p={p}, mu_32 = <2> = signed powers of 2")
print(f"eta_1 over mu_32 (CLOSED FORM 2*sum_j cos(2pi 2^j/p)) = {eta1_32:.6f}")
print(f"  n=32, sqrt(n)=5.657, floor sqrt(2 n log m), m=2048: {math.sqrt(2*32*math.log(2048)):.4f}")
print(f"  M/sqrt(n) = {eta1_32/math.sqrt(32):.4f}")

# How big is the deficit n - eta_1?  n=2k. eta_1 = 2 sum cos(2pi 2^j/p).
# Deficit = 2 sum (1-cos(2pi 2^j/p)) = 2 sum 2 sin^2(pi 2^j/p) ~ 2 sum (2pi^2 (2^j/p)^2)
# = 4pi^2/p^2 sum_{j<k} 4^j = 4pi^2/p^2 * (4^k-1)/3.  4^k=(2^k)^2=(p-1)^2~p^2.
# => deficit ~ 4pi^2/3 = 13.16.  So eta_1 ~ 2k - 13.16. For k=16: 32-13.16=18.8? 
defi = 2*sum(2*math.sin(math.pi*(2**j)/p)**2 for j in range(k))
print(f"  exact deficit n - eta_1 = {2*k - eta1_32:.4f}, asymptotic 4pi^2/3 = {4*math.pi**2/3:.4f}")
# The DEFICIT is dominated by the LARGEST few 2^j (those near p/2). j=k-1: 2^{15}=32768~p/2.
# cos(2pi*32768/65537)=cos(pi*(1-1/p))~-1. So that term is ~ -1 not +1! deficit from it ~2.
print()
print("Largest terms (j near k-1): 2^j ~ p/2 contribute cos~-1, not +1")
for j in range(k-4,k):
    print(f"  j={j} 2^j={2**j} cos(2pi 2^j/p)={math.cos(2*math.pi*(2**j)/p):+.4f}")
