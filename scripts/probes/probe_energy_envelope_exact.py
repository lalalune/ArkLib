# Verify the EXACT-value envelope inequalities provable from the proven closed forms
# E2(n) = 3n^2 - 3n  (B4_closed, n=2m),  E3(n) = 15n^3 - 45n^2 + 40n  (B6_eq_E3)
# Goal: clean all-n>=1 polynomial inequalities a Lean `nlinarith`/`positivity` can discharge.
#   (U2) E2 <= 3 n^2                       (since -3n <= 0)
#   (L2) E2 >= 2 n^2   for n >= 3          (3n^2-3n - 2n^2 = n^2-3n = n(n-3) >= 0)
#   (U3) E3 <= 15 n^3                      (since -45n^2+40n = -5n(9n-8) <= 0 for n>=1)
#   (L3) E3 >= 11 n^3  for n >= ? :  15n^3-45n^2+40n - 11n^3 = 4n^3-45n^2+40n = n(4n^2-45n+40)
#        4n^2-45n+40 >= 0 when n >= (45+sqrt(2025-640))/8 = (45+sqrt1385)/8 ~ 10.27 -> n>=11
#   so for dyadic n=2^a (a>=4 => n>=16) both lower bounds clean.
#   Tightest clean integer lower const for ALL n>=1 that stays a multiple-free poly: E3>=n^3? check.
def E2(n): return 3*n*n - 3*n
def E3(n): return 15*n**3 - 45*n*n + 40*n
print("n   E2      3n^2    E2<=3n^2  E2>=2n^2(n>=3)   E3        15n^3      E3<=15n^3  E3>=11n^3(n>=11)  E3>=n^3")
for n in [1,2,3,4,8,16,32,64,128,256,1024]:
    u2 = E2(n) <= 3*n*n
    l2 = (n<3) or (E2(n) >= 2*n*n)
    u3 = E3(n) <= 15*n**3
    l3 = (n<11) or (E3(n) >= 11*n**3)
    ln = E3(n) >= n**3
    print(f"{n:<5}{E2(n):<8}{3*n*n:<8}{str(u2):<10}{str(l2):<16}{E3(n):<10}{15*n**3:<11}{str(u3):<11}{str(l3):<18}{ln}")
# all-n>=1 sanity for the polynomial sign facts
import sys
for n in range(1, 3000):
    assert E2(n) <= 3*n*n
    assert E3(n) <= 15*n**3
    assert E3(n) >= n**3        # 15n^3-45n^2+40n >= n^3 <=> 14n^3-45n^2+40n>=0 <=> n(14n^2-45n+40)>=0; disc=2025-2240<0 => always
    if n >= 3: assert E2(n) >= 2*n*n
print("\nALL polynomial envelope facts hold for n=1..2999  (U2,U3,E3>=n^3 all n>=1; L2 n>=3)")
print("14n^2-45n+40 discriminant =", 45*45 - 4*14*40, "(<0 => E3>=n^3 for ALL n>=1, no threshold)")
