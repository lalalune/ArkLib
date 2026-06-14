#!/usr/bin/env python3
"""
calibrate.py — the anti-fabrication calibration harness for the ConjectureBound deliverable (#389).

Every candidate form/bound MUST reproduce the kernel-verified exact data:
  n=16 worst-over-monomial #bad r=3..8 = 97,145,89,113,225,104     [O171/O172, reproduced this pass]
  n=32 r=3 = 897 (full sweep), r=4 = 3105 (e=n/2 row, NEW this pass), r=5 = 1441 (corner sweep)

All counts were produced by the residual-determinant ground-truth kernel
  scripts/probes/genlaw/o165_census_demand/cd_demand.c  (faithful BabyBear p=2013265921, p^2 >> C(n,a0))
at the pin: deep band, deficit a0-k_c=2, m=1, k_c=r-1, a0=r+1.

Tag: [COMPUTED] all data below (exact-integer, kernel). [CONJECTURED] the K/2 bound.
"""
from math import comb

# ---- THE EXACT DATA (kernel-verified, digit-for-digit) ----
# (n, r): worst #bad over all monomial lines (= global worst; wide search confirms monomial dominates)
WORST = {
 (16,3): 97, (16,4): 145, (16,5): 89, (16,6): 113, (16,7): 225, (16,8): 104,
 (32,3): 897, (32,4): 3105, (32,5): 1441,
}
# maximizer monomial (e,f) per point
MAXER = {
 (16,3):(8,7),(16,4):(8,5),(16,5):(9,15),(16,6):(8,10),(16,7):(10,15),(16,8):(9,11),
 (32,3):(16,15),(32,4):(16,9),(32,5):(17,31),
}

def K(n,r): return (2**r)*comb(n//2, r)

# ---- r=3 PROVEN closed form (O172): n*C(n/4,2)+1 = n^2(n-4)/32+1 ----
def r3form(n): return n*comb(n//4,2)+1

def check_r3():
    print("[1] r=3 PROVEN closed form  #bad = n*C(n/4,2)+1 = n^2(n-4)/32+1:")
    ok=True
    for n in (16,32,64):
        v=r3form(n); ref=WORST.get((n,3))
        m = "" if ref is None else (" == data" if v==ref else f" != data({ref}) FAIL")
        if ref is not None and v!=ref: ok=False
        print(f"    n={n}: {v}{m}")
    # the proven <=K identity, h=n/2: K-#bad=(h-2)h(13h-16)/12 - 1 > 0 for h>=4
    print("    <=K proof (h=n/2): K-#bad = (h-2)h(13h-16)/12 - 1 :")
    for n in (16,32,64,128):
        h=n//2; lhs=K(n,3)-r3form(n); rhs=(h-2)*h*(13*h-16)//12 - 1
        print(f"      n={n}: K-#bad={lhs}  identity={rhs}  {'match,>0' if lhs==rhs and lhs>0 else 'MISMATCH'}")
    print(f"    => r3 form reproduces data: {ok}; <=K PROVEN all n (polynomial identity).")
    return ok

# ---- CANDIDATE EXACT GENERAL-r FORMS (all must reproduce WORST; report pass/fail) ----
def test_exact_candidates():
    print("\n[2] EXACT general-r closed-form candidates (must reproduce ALL of WORST):")
    cands = {
      "n*C(n/4,r-1)+1 (naive r3-gen)": lambda n,r: n*comb(n//4, r-1)+1,
      "2^(r-1)*C(n/2,r-1)         ": lambda n,r: (2**(r-1))*comb(n//2, r-1),
      "C(n/2,2)*something          ": None,  # placeholder; no clean fit found
    }
    for name,f in cands.items():
        if f is None:
            print(f"    {name}: NO FORM (none found)")
            continue
        fails=[]
        for (n,r),b in sorted(WORST.items()):
            try: v=f(n,r)
            except Exception: v=None
            if v!=b: fails.append((n,r,v,b))
        print(f"    {name}: {'REPRODUCES ALL' if not fails else 'FAILS at '+', '.join(f'(n{n},r{r}):{v}!={b}' for n,r,v,b in fails[:4])}")

# ---- THE DELIVERABLE BOUND: #bad <= K/2 ----
def test_bound():
    print("\n[3] DELIVERABLE BOUND candidates (clean, must hold at EVERY point):")
    for c,label in [(1,"K"),(2,"K/2"),(4,"K/4"),(3,"K/3")]:
        worst_ratio=0.0; allok=True; binding=None
        for (n,r),b in WORST.items():
            ratio=b/K(n,r)
            if ratio>worst_ratio: worst_ratio=ratio; binding=(n,r,b,K(n,r))
            if b > K(n,r)//c: allok=False
        status = "HOLDS all 9 pts" if allok else "FAILS"
        print(f"    #bad <= K/{c} ({label}): {status}   worst ratio #bad/K = {worst_ratio:.4f} at n={binding[0]} r={binding[1]} ({binding[2]}/{binding[3]})")
    print("    => CLEANEST PROVABLE-TARGET BOUND consistent with all data: #bad <= K/2.")
    print("       Binding point: n=16 r=8 (last band r=n/2, smallest K=256), #bad=104=0.406*K.")

def table():
    print("\n[0] EXACT CALIBRATION TABLE (the anti-fabrication anchor):")
    print(f"    {'n':>3}{'r':>3}{'#bad':>6}{'K=2^r C(n/2,r)':>16}{'margin':>9}{'#bad/K':>9}  maximizer(e,f)")
    for (n,r),b in sorted(WORST.items()):
        Kv=K(n,r); ef=MAXER[(n,r)]
        print(f"    {n:>3}{r:>3}{b:>6}{Kv:>16}{Kv/b:>8.2f}x{b/Kv:>9.4f}  (x^{ef[0]},x^{ef[1]})")

if __name__=="__main__":
    print("="*78)
    print("CONJECTUREBOUND CALIBRATION — deep-band deficit-2 #bad-scalar (#389)")
    print("="*78)
    table()
    check_r3()
    test_exact_candidates()
    test_bound()
    print("\nVERDICT: no clean EXACT general-r form (refuted); the clean BOUND #bad<=K/2")
    print("holds at every computed (n,r). r=3 is the only band with a proven exact form + proven <=K.")
