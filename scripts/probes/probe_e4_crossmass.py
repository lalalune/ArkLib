# Verify the exact crossMass G 3 closed form + its margin below the 90 n^4 target.
def E3(n): return 15*n**3 - 45*n**2 + 40*n
def E4(n): return 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n

print("crossMass G 3 = E_4 - n*E_3 ; claimed closed form 90n^4 -585n^3 +1395n^2 -1155n")
print("n     E4-n*E3          closedform        match    target90n^4      slack=90n^4-cm")
for a in range(2, 8):
    n = 2 ** a
    cm = E4(n) - n * E3(n)
    cf = 90*n**4 - 585*n**3 + 1395*n**2 - 1155*n
    slack = 90*n**4 - cm
    print(f"{n:<5} {cm:<16} {cf:<16} {cm==cf}    {90*n**4:<16} {slack}")

# slack = 90n^4 - cm = 585n^3 - 1395n^2 + 1155n. Positive for n>=2? check.
print("\nslack closed form = 585n^3 - 1395n^2 + 1155n ; >0 for n>=1?")
for a in range(0, 8):
    n = 2 ** a
    s = 585*n**3 - 1395*n**2 + 1155*n
    print(f"n={n:<4} slack={s}  >0:{s>0}")
