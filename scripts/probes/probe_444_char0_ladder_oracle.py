"""
PROBE (#444): independent SEMANTIC cross-validator for the char-0 energy ladder.

The avenue-L2 ladder Frontier/_AvL2_E{r}ClosedForm.lean defines a closed-form polynomial
E_r(n) and proves (by `decide`) anchors like `E23 2 = 8233430727600`. But `decide` only
certifies the *polynomial arithmetic* -- it does NOT verify that the polynomial actually IS
the char-0 additive energy of the n-th roots of unity (that semantic claim lives in the
docstring). The repo's probe_char0_energy_exact_formula computes the *generic* (relation-free)
energy, which is NOT the roots-of-unity energy for n = 2^k (antipodal relations matter).

This probe closes that gap: it recomputes the TRUE additive energy
    E_r(C) = #{(a,b) in mu_n^r x mu_n^r : sum_i z^{a_i} = sum_i z^{b_i}},  z = primitive n-th root
by an independent exact method, and checks it against the ladder's published anchor integers.

Two independent oracles (both exact integer arithmetic, no float):
  * n = 2:  mu_2 = {1, -1}, so E_r = sum_k C(r,k)^2 = C(2r, r)  (Vandermonde).
  * n = 4:  cyclotomic antipodal reduction. Phi_4 = x^2 + 1, basis {1, i}; z^a -> +-e_{a mod 2}.
            Equal complex sums <=> equal reduced integer vectors -> convolution over Z^2.
            (Same method valid for any n = 2^k; n=4 keeps the state space tiny even at r=23.)

It auto-reads the claimed E_r(2)/E_r(4) from the Lean files, so it covers every published rung
and any future one. NEVER fabricates: a rung with no parseable anchor is reported, not assumed.
"""
import sys, os, re, math
from collections import Counter

LADDER_DIR = os.path.join(os.path.dirname(__file__), "..", "..",
                          "ArkLib", "Data", "CodingTheory", "ProximityGap", "Frontier")

def Er_C_2power(n, r):
    """exact char-0 additive energy of the n-th roots of unity (n = 2^k) via antipodal reduction."""
    half = n // 2
    units = [(a, 1) if a < half else (a - half, -1) for a in range(n)]
    c = Counter({tuple([0] * half): 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for idx, s in units:
                w = list(v); w[idx] += s; nc[tuple(w)] += m
        c = nc
    return sum(m * m for m in c.values())

def oracle(n, r):
    if n == 2:
        return math.comb(2 * r, r)            # Vandermonde central binomial
    return Er_C_2power(n, r)                   # cyclotomic convolution (n = 4 here)

def main():
    out = open(os.path.join(os.path.dirname(__file__), "RESULTS-444-CHAR0-LADDER-ORACLE.md"), "w")
    def emit(*a):
        line = " ".join(str(x) for x in a)
        print(line); sys.stdout.flush(); out.write(line + "\n"); out.flush()

    emit("# Independent semantic cross-validation of the char-0 energy ladder (#444)")
    emit("# E_r(n) closed forms vs. the TRUE roots-of-unity additive energy.")
    emit("# n=2 oracle: C(2r,r) (Vandermonde). n=4 oracle: cyclotomic antipodal convolution.\n")

    pat = re.compile(r"\bE(\d+)\s+(2|4)\s*=\s*(\d+)")
    claims = {}   # r -> {2: val, 4: val}
    for fn in sorted(os.listdir(LADDER_DIR)):
        m = re.match(r"_AvL2_E(\d+)ClosedForm\.lean$", fn)
        if not m:
            continue
        txt = open(os.path.join(LADDER_DIR, fn)).read()
        for r_str, n_str, val in pat.findall(txt):
            r = int(r_str)
            if r != int(fn[len("_AvL2_E"):].split("ClosedForm")[0]):
                continue   # ignore stray E<k> mentions of other rungs
            claims.setdefault(r, {})[int(n_str)] = int(val)

    rungs = sorted(claims)
    emit(f"Found {len(rungs)} published ladder rungs: r in {rungs}")
    missing = [r for r in range(min(rungs), max(rungs) + 1) if r not in rungs]
    if missing:
        emit(f"NOTE: ladder gaps (no _AvL2_E{{r}}ClosedForm.lean) at r = {missing}")
    emit("")

    all_ok = True
    for r in rungs:
        for n in (2, 4):
            if n not in claims[r]:
                emit(f"  r={r:2d} n={n}: NO ANCHOR in file (skipped, not assumed)")
                continue
            claimed = claims[r][n]
            truth = oracle(n, r)
            ok = (claimed == truth)
            all_ok &= ok
            tag = "OK " if ok else "!! MISMATCH"
            emit(f"  r={r:2d} n={n}: claimed={claimed}  oracle={truth}  {tag}")
        emit("")

    emit(f"=== VERDICT: every published char-0 ladder anchor matches the independent "
         f"additive-energy oracle = {all_ok} ===")
    emit("This certifies the ladder polynomials ARE the roots-of-unity char-0 additive energy")
    emit("(the semantic claim `decide` cannot reach), at the verified anchors n=2,4. It says")
    emit("NOTHING about the open char-p transfer (the BGK/Paley wall), which remains open.")
    out.close()
    return 0 if all_ok else 1

if __name__ == "__main__":
    sys.exit(main())
