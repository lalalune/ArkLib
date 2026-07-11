from math import comb

# KKH26 bad-scalar supply at level (s, m=1, r): 2^r * C(s/2, r)   [s=2^mu, s/2=2^{mu-1}]
# After one s-step (r even): level (s/2, 1, r/2), supply 2^{r/2} * C(s/4, r/2).
def supply(s, r):
    return (2 ** r) * comb(s // 2, r)

print("PROBE: KKH26 s-step supply decay (r even).")
viol = 0
checked = 0
for mu in range(3, 12):            # s = 2^mu
    s = 2 ** mu
    for r in range(2, s // 2, 2):  # r even, prize-regime 0 < 2r < s
        s2 = s // 2
        r2 = r // 2
        if r2 < 1:
            continue
        if 2 * r2 >= s2:           # valid range at folded level
            continue
        base = supply(s, r)
        step = supply(s2, r2)
        if step <= 0:
            continue
        checked += 1
        if not (base > step):      # STRICT decay claim
            viol += 1
            print(f"  VIOLATION (s,r)=({s},{r}): base={base} step={step}")
        if mu <= 5 and r <= 6:
            print(f"  (s={s},r={r}): base=2^{r}*C({s2},{r})={base:>12} | "
                  f"step=2^{r2}*C({s2 // 2},{r2})={step:>10} | ratio={base / step:.3f}")

print(f"\nchecked={checked}  STRICT-decay violations={viol}")

print("\nFACTOR ANALYSIS: base/step vs 2^(r/2) and the binomial-ratio")
for mu in [6, 8, 10]:
    s = 2 ** mu
    for r in [4, 8, 16]:
        if 2 * r >= s:
            continue
        r2 = r // 2
        s2 = s // 2
        if 2 * r2 >= s2:
            continue
        base = supply(s, r)
        step = supply(s2, r2)
        print(f"  (s={s},r={r}): base/step={base / step:.4g}  2^(r/2)={2 ** (r // 2)}  "
              f"binom-ratio C({s2},{r})/C({s2 // 2},{r2})={comb(s2, r) / comb(s2 // 2, r2):.4g}")
