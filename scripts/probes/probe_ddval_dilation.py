import random
from fractions import Fraction as Fr


def ddval_pow(R, v, b):
    # R: list of indices; v: dict idx->value; data r_i = v_i^b (monomial)
    tot = Fr(0)
    for i in R:
        num = v[i] ** b
        den = Fr(1)
        for j in R:
            if j != i:
                den *= (v[i] - v[j])
        tot += num / den
    return tot


def main():
    random.seed(7)
    print("=== dilation homogeneity: ddVal R (g.v) x^b == g^(b-(|R|-1)) * ddVal R v x^b ===")
    allpass = True
    for trial in range(2000):
        cardR = random.randint(2, 6)
        vals = random.sample(range(-20, 21), cardR)
        R = list(range(cardR))
        v = {i: Fr(vals[i]) for i in R}
        g = Fr(random.choice([x for x in range(-9, 10) if x != 0]))
        b = random.randint(0, 8)
        gv = {i: g * v[i] for i in R}
        lhs = ddval_pow(R, gv, b)
        rhs = g ** (b - (cardR - 1)) * ddval_pow(R, v, b)
        if lhs != rhs:
            allpass = False
            print("FAIL", cardR, vals, "g", g, "b", b, lhs, rhs)
            if trial > 5:
                break
    print("VERDICT homogeneity:", "PASS" if allpass else "FAIL")

    print("=== Schur ratio: gamma(g.v) = g^(a-b) gamma(v) ===")
    allpass2 = True
    for trial in range(2000):
        cardR = random.randint(2, 6)
        vals = random.sample(range(-20, 21), cardR)
        R = list(range(cardR))
        v = {i: Fr(vals[i]) for i in R}
        g = Fr(random.choice([x for x in range(-9, 10) if x != 0]))
        a = random.randint(1, 9)
        b = random.randint(0, 8)
        gv = {i: g * v[i] for i in R}
        db = ddval_pow(R, v, b)
        if db == 0:
            continue
        gam = -ddval_pow(R, v, a) / db
        dbg = ddval_pow(R, gv, b)
        if dbg == 0:
            continue
        gamg = -ddval_pow(R, gv, a) / dbg
        if gamg != g ** (a - b) * gam:
            allpass2 = False
            print("FAIL2", cardR, vals, "g", g, "a", a, "b", b, gamg, g ** (a - b) * gam)
            if trial > 5:
                break
    print("VERDICT schur ratio:", "PASS" if allpass2 else "FAIL")


if __name__ == "__main__":
    main()
