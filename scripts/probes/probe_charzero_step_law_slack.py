#!/usr/bin/env python3
"""
#444 — char-0 Gaussian STEP-LAW discharge probe (lane stepslack).

The whole prize reduces (WF6F1 telescope + WF7W3 ladder) to the per-step Gaussian
step-law  E_{r+1} <= (2r+1)*n*E_r  (variance proxy s = n = |mu_n|) at depth r ~ ln q.
The char-0 exact energies E_2..E_8 of mu_{2^k} are IN-TREE and proven. Yet NO file has
discharged the step-law / its WF7W3 base R(1)<=1 on the actual in-tree char-0 energies.

This probe: (1) verify the step-law holds char-0 for every landed rung r=1..7 with
EXPLICIT positive slack, (2) extract the exact step-slack polynomial S_r(n) = (2r+1)*n*E_r
- E_{r+1}, (3) extract its leading coeff + sign, (4) confirm R(r) = E_{r+1}/((2r+1) n E_r)
< 1 (genuinely sub-Gaussian) on the prize grid. ONE sweep, decisive.

E_r exact (in-tree _CharZeroEnergyClosedForm; E_7,E_8 from _AvL2):
"""
import sympy as sp

n = sp.symbols('n', positive=True, integer=True)

E = {
 1: 1*n,                       # E_1 = n  (Sidon base; |G|)
 2: 3*n**2 - 3*n,
 3: 15*n**3 - 45*n**2 + 40*n,
 4: 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n,
 5: 945*n**5 - 9450*n**4 + 39375*n**3 - 77175*n**2 + 57456*n,
 6: 10395*n**6 - 155925*n**5 + 1022175*n**4 - 3534300*n**3 + 6246471*n**2 - 4370520*n,
 7: (135135*n**7 - 2837835*n**6 + 26801775*n**5 - 141891750*n**4
     + 433726293*n**3 - 708996288*n**2 + 471556800*n),
 8: (2027025*n**8 - 56756700*n**7 + 728377650*n**6 - 5439183750*n**5
     + 25055875845*n**4 - 69934975110*n**3 + 107438611995*n**2 - 68492499075*n),
}

def dfact(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

print("=== char-0 Gaussian STEP-LAW  E_{r+1} <= (2r+1) n E_r  (s = n) ===")
print("    step-slack  S_r(n) = (2r+1) n E_r - E_{r+1}\n")
all_ok = True
slack = {}
for r in range(1, 8):
    target = (2*r+1)*n*E[r]
    S = sp.expand(target - E[r+1])
    slack[r] = S
    p = sp.Poly(S, n)
    lead_coef = p.all_coeffs()[0]
    lead_deg = p.degree()
    # numeric check over prize-faithful thin grid n = 2^a
    vals_ok = all(S.subs(n, 2**a) > 0 for a in range(1, 21))
    # leading coeff of (2r+1) n E_r is (2r+1)*(2r-1)!! = (2r+1)!!; of E_{r+1} is (2r+1)!! -> cancels
    wick_r1 = dfact(2*(r+1)-1)
    lead_target = (2*r+1)*dfact(2*r-1)
    print(f"r={r}: S_r deg={lead_deg}, lead={lead_coef}  | "
          f"(2r+1)(2r-1)!!={lead_target} == (2(r+1)-1)!!={wick_r1} (top cancels: {lead_target==wick_r1}) | "
          f"S_r>0 on 2^1..2^20: {vals_ok}")
    print(f"      S_{r}(n) = {S}")
    all_ok = all_ok and vals_ok

print("\n=== R(r) = E_{r+1}/((2r+1) n E_r) < 1  (sub-Gaussian step ratio) ===")
for r in range(1, 8):
    Rn = sp.simplify(E[r+1] / ((2*r+1)*n*E[r]))
    samples = [(2**a, float(Rn.subs(n, 2**a))) for a in (4, 6, 8, 10, 20)]
    lt1 = all(v < 1 for _, v in samples)
    print(f"r={r}: R(r)<1 on grid: {lt1}  samples n=16,64,256,1024,2^20: "
          f"{[round(v,4) for _,v in samples]}")

print("\n=== WF7W3 base R(1) <= 1  i.e.  E_2 <= 3 n E_1 = 3 n^2 ===")
base = sp.expand(3*n*E[1] - E[2])  # 3n^2 - (3n^2-3n) = 3n
print(f"  3 n E_1 - E_2 = {base}   (>=0 for n>=0, strict for n>=1) -> R(1)<=1 PROVEN char-0")

print(f"\nVERDICT: char-0 step-law holds all landed rungs r=1..7 with positive slack: {all_ok}")


# === HONESTY EDGE (brick 2, r=6,7 on _AvL2 E_7,E_8) ===
# Step-law char-0 holds on the 2-power grid n=2^a for ALL landed r, but is NOT uniform in general
# integer n at r=7: S_7(n) is NEGATIVE at the off-regime n=3 (slack septic has a real root ~3.786),
# so E_8 <= 15 n E_7 FAILS at n=3. Holds at n=2 and for all n>=4. mu_n has n=2^a so the prize regime
# n>=16 is inside the valid band; step_law_seven is scoped n>=4, step_law_six holds n>=2.
