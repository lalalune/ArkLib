#!/usr/bin/env python3
"""Exhaustive mu16 pair-cover matrices in the concrete prize field.

Only n=16 is enumerated. The source field has a much larger smooth domain;
this script makes no assertion about a pair cover on that domain.
The main loop uses two-by-two minors and cross-multiplication, not Gaussian
elimination or modular inverses per partition.
"""
from __future__ import annotations

import json
from math import comb
from pathlib import Path
import re

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 16
FULL = (1 << N)-1


def source_check():
    path = Path(__file__).resolve().parents[2]/"ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean"
    text = path.read_text()
    assert int(re.search(r"abbrev P : ℕ := ([0-9]+)",text)[1]) == P
    assert int(re.search(r"abbrev g : ZMod P := ([0-9]+)",text)[1]) == G
    assert P == 2**30*(2**128+192)+1
    assert pow(G,2**30,P) == 1 and pow(G,2**29,P) == P-1


def original_matrix_rank(A,B,C):
    def coefficient(f,i):
        return f[i] if 0 <= i < len(f) else 0
    matrix = [[coefficient(A,i-1),coefficient(A,i),coefficient(B,i-1),
               coefficient(B,i),coefficient(C,i)] for i in range(7)]
    rank = 0
    for column in range(5):
        pivot = next((i for i in range(rank,7) if matrix[i][column]),None)
        if pivot is None:
            continue
        matrix[rank],matrix[pivot] = matrix[pivot],matrix[rank]
        inverse = pow(matrix[rank][column],-1,P)
        matrix[rank] = [v*inverse % P for v in matrix[rank]]
        for i in range(rank+1,7):
            multiple = matrix[i][column]
            matrix[i] = [(v-multiple*w) % P for v,w in zip(matrix[i],matrix[rank])]
        rank += 1
        if column == 3:
            assert rank == 4
    return rank


def evaluate(f,x):
    result = 0
    for coefficient in reversed(f):
        result = (result*x+coefficient) % P
    return result


def main():
    source_check()
    generator = pow(G,2**26,P)
    assert pow(generator,16,P) == 1 and pow(generator,8,P) == P-1
    nodes = [pow(generator,i,P) for i in range(N)]
    assert len(set(nodes)) == N
    polynomials = [[1]]+[None]*FULL
    root_checks = 0
    for mask in range(1,FULL+1):
        bit = (mask & -mask).bit_length()-1
        previous = polynomials[mask & (mask-1)]
        current = [0]*(len(previous)+1)
        for i,value in enumerate(previous):
            current[i] = (current[i]-nodes[bit]*value) % P
            current[i+1] = value
        polynomials[mask] = current
        if len(current) in (6,7):
            assert current[-1] == 1
            for i,x in enumerate(nodes):
                assert (evaluate(current,x) == 0) == bool(mask & (1 << i))
            root_checks += 1
    assert root_checks == comb(16,5)+comb(16,6) == 12376
    assert polynomials[FULL] == [P-1]+[0]*15+[1]

    partitions = syzygies = paircovers = reference_checks = 0
    witnesses = []
    for ab in range(FULL+1):
        if ab & 1 or ab.bit_count() != 5:
            continue
        available = FULL ^ ab ^ 1
        ac = available
        while ac:
            if ac > ab and ac.bit_count() == 5:
                partitions += 1
                bc = FULL ^ ab ^ ac
                A,B,C = polynomials[ab],polynomials[ac],polynomials[bc]
                delta = [(A[i]-B[i]) % P for i in range(5)]
                beta = (B[4]-C[5]) % P
                v = [((delta[i-1] if i else 0)-delta[4]*B[i]) % P for i in range(5)]
                q = [((B[i-1] if i else 0)-C[i]-beta*B[i]) % P for i in range(5)]
                first = next(i for i in range(5) if delta[i])
                second = next(j for j in range(5) if (v[first]*delta[j]-v[j]*delta[first]) % P)
                determinant = (v[first]*delta[second]-v[second]*delta[first]) % P
                anumerator = (q[first]*delta[second]-q[second]*delta[first]) % P
                bnumerator = (v[first]*q[second]-v[second]*q[first]) % P
                solves = all((anumerator*v[i]+bnumerator*delta[i]-determinant*q[i]) % P == 0
                             for i in range(5))
                if partitions <= 32 or partitions % 997 == 0:
                    assert original_matrix_rank(A,B,C) == (4 if solves else 5)
                    reference_checks += 1
                if solves:
                    syzygies += 1
                    inverse = pow(determinant,-1,P)
                    a,b = anumerator*inverse % P,bnumerator*inverse % P
                    c,d = (-1-a) % P,(beta-a*delta[4]-b) % P
                    f_b,f_c = [],[]
                    for i in range(7):
                        pa = (a*(A[i-1] if i else 0)+b*(A[i] if i < 6 else 0)) % P
                        qb = (c*(B[i-1] if i else 0)+d*(B[i] if i < 6 else 0)) % P
                        assert (pa+qb+C[i]) % P == 0
                        f_b.append(-pa % P)
                        f_c.append(qb)
                    counts = [0,0,0]
                    exactly_two = True
                    for x in nodes:
                        fb,fc = evaluate(f_b,x),evaluate(f_c,x)
                        equalities = (fb == 0,fc == 0,fb == fc)
                        exactly_two &= sum(equalities) == 1
                        counts = [old+new for old,new in zip(counts,equalities)]
                    if exactly_two:
                        assert counts == [5,5,6]
                        paircovers += 1
                        if len(witnesses) < 32:
                            witnesses.append({"masks_AB_AC_BC":[ab,ac,bc],
                                "a_b_c_d_lambda":[a,b,c,d,1],"fA":[0],"fB":f_b,"fC":f_c})
            ac = (ac-1) & available
    assert partitions == 378378 and reference_checks == 411
    print(json.dumps({"status":"EXHAUSTIVE_MU16_PAIR_SYZYGIES_IN_PRIZE_FIELD_ONLY",
        "prime":P,"production_domain_generator":G,"mu16_generator":generator,"nodes":nodes,
        "domain_size_actually_enumerated":16,"production_domain_size_not_enumerated":2**30,
        "partitions_checked":partitions,"root_polynomials_checked":root_checks,
        "sampled_original_matrix_checks":reference_checks,
        "syzygies":syzygies,"exactly_two_paircovers":paircovers,
        "witnesses_truncated":paircovers > len(witnesses),"witnesses":witnesses},indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
