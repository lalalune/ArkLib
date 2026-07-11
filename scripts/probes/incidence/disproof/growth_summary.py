import math
print("="*78)
print("MAX-LIST vs n at INTERIOR radii (verified exact counts; non-Fermat primes)")
print("="*78)
print()
print("rho=1/4 (k=n/4). capacity agreement=k, Johnson agreement=n/2.")
print(f"{'n':>4} {'k':>3} {'a=k+1':>14} {'a=k+2(MID)':>12} {'a=k+3':>10} {'budget~n':>9}")
print(f"{'':>4} {'':>3} {'(->capacity)':>14} {'(FIXED frac.5)':>12} {'(Johnson)':>10}")
# verified data
rows={
 8:  {'k':2,'kp1':7,  'kp2':None,'kp3':None},   # n=8: interior only a=3=k+1 (a=4 is Johnson)
 16: {'k':4,'kp1':273,'kp2':3,   'kp3':1},
 32: {'k':8,'kp1':'(LB pending)','kp2':'(LB pending)','kp3':None},
}
for n,r in rows.items():
    print(f"{n:>4} {r['k']:>3} {str(r['kp1']):>14} {str(r['kp2']):>12} {str(r['kp3']):>10} {n:>9}")
print()
print("CEILINGS C(n,k)/C(a,k) for reference:")
for n,rho in [(8,.25),(16,.25),(32,.25)]:
    k=round(rho*n)
    s=" ".join(f"a={a}:{math.comb(n,k)//math.comb(a,k)}" for a in [k+1,k+2,k+3] if k+1<=a<math.sqrt(rho)*n)
    print(f"  n={n}: {s}")
print()
print("KEY: a=k+1 -> CAPACITY as n grows (window-fraction halves each doubling: .5,.25,.125,...)")
print("     so its blow-up (7->273) is NEAR-CAPACITY, NOT fixed-interior-radius growth.")
print("     At FIXED interior radius (mid-window, frac=.5): n=16 -> 3 (heavy search). FLOOR.")
