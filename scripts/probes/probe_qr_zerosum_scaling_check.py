#!/usr/bin/env python3
"""Reproducible verification of QRZeroSumTripleScaling.lean (#389) + the general
zero-sum-triple decomposition (Fable QA, 2026-06-13).

Confirms across 13 primes p == 1 mod 4:
  (1) #{(a,b,c) in (QR*)^3 : a+b+c=0} == #QR* * M,  M = consecutive-QR-pair count;
  (2) M == (p-5)/4,  ordered count == (p-1)(p-5)/8;
  (3) the degenerate correction  ordered == 6*unordered + 3*D,  D == #{a in QR* : -2a in QR*}
      -- the GENERAL law  zeroSumTriples G = 6*Z3(G) + 3*D(G)  (char != 3, 0 not in G);
  (4) the unordered cubic-supply closed forms  n(p-5)/24 (p==5 mod 8) / n(p-17)/24 (p==1 mod 8).
All [OK]; the QR (additively-rich) cubic list is quadratic in n, vs = 0 on the 2-power NTT domain.
"""

# Verify QRZeroSumTripleScaling claims:
#  (1) #{(a,b,c) in (QR*)^3 : a+b+c=0} = #QR* * M, M = consecutive-QR-pair count
#  (2) closed form (q-1)(q-5)/8 when -1 is a square (q ≡ 1 mod 4)
#  (3) M = (q-5)/4
def check(q):
    QR = set()
    for x in range(1, q):
        QR.add((x*x) % q)
    QRstar = sorted(QR - {0})  # nonzero squares
    nQR = len(QRstar)
    QRset = set(QRstar)
    # ordered zero-sum triples of nonzero squares
    cnt = 0
    for a in QRstar:
        for b in QRstar:
            c = (-a - b) % q
            if c in QRset:
                cnt += 1
    # M = #{u : u in QR*, u+1 in QR*}
    M = sum(1 for u in QRstar if (u+1) % q in QRset)
    neg1_sq = (q-1) % q in QRset  # is -1 a square
    closed = (q-1)*(q-5)//8 if (q % 4 == 1) else None
    M_pred = (q-5)//4 if (q % 4 == 1) else None
    ok1 = (cnt == nQR * M)
    ok2 = (closed is None) or (cnt == closed)
    ok3 = (M_pred is None) or (M == M_pred)
    print(f"q={q:4d} (q%8={q%8}): #QR*={nQR}, M={M}, ordered_zerosum={cnt}, "
          f"nQR*M={nQR*M} [{'OK' if ok1 else 'FAIL'}], "
          f"closed (q-1)(q-5)/8={closed} [{'OK' if ok2 else 'FAIL'}], "
          f"M=(q-5)/4 [{'OK' if ok3 else 'FAIL'}], -1sq={neg1_sq}")
    return ok1 and ok2 and ok3

primes_1mod4 = [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]
allok = all(check(p) for p in primes_1mod4)
print("ALL QR-scaling claims verified:", allok)

print("\n--- Unordered cubic supply (the actual list size) + degenerate correction ---")
def check_unordered(q):
    QRset = set((x*x) % q for x in range(1, q)) - {0}
    QRstar = sorted(QRset)
    nQR = len(QRstar)
    # ordered zero-sum triples (incl degenerate)
    ordered = 0
    for a in QRstar:
        for b in QRstar:
            if (-a-b) % q in QRset: ordered += 1
    # unordered DISTINCT 3-subsets summing to 0
    unord = 0
    L = QRstar
    for i in range(nQR):
        for j in range(i+1, nQR):
            c = (-L[i]-L[j]) % q
            if c in QRset and c != L[i] and c != L[j] and c > L[j]:
                unord += 1
    # degenerate: 3 * #{a in QR* : -2a in QR*} = 3 * nQR * [-2 in QR] (char != 3)
    neg2_sq = (q-2) % q in QRset
    D = sum(1 for a in QRstar if (-2*a) % q in QRset)
    # relation: ordered = 6*unord + 3*D  (char != 3, 0 not in QR*)
    rel_ok = (ordered == 6*unord + 3*D)
    # sibling closed form: n(q-5)/24 (q≡5 mod8) / n(q-17)/24 (q≡1 mod8), n=#QR*
    if q % 8 == 5:
        closed = nQR*(q-5)//24
    elif q % 8 == 1:
        closed = nQR*(q-17)//24
    else:
        closed = None
    cf_ok = (closed is None) or (unord == closed)
    print(f"q={q:4d}(q%8={q%8}): ordered={ordered}, unord={unord}, D={D}(=nQR*[-2sq]={nQR*(1 if neg2_sq else 0)}), "
          f"6u+3D={6*unord+3*D}[{'OK' if rel_ok else 'FAIL'}], closed={closed}[{'OK' if cf_ok else 'FAIL'}]")
    return rel_ok and cf_ok

allok2 = all(check_unordered(p) for p in primes_1mod4)
print("ALL unordered + degenerate-correction claims verified:", allok2)
