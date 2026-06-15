"""
wf407 / B2-curve: pin the EXACT logical bridge between
  - CurveDecodable (GG25 Def 3.1, over close set of SEEDS)
  - mcaEventCurve / epsMCACurve (curve MCA bad event, over a single seed gamma)

Goal: find the TRUE provable connection. We model small linear codes and
brute-force-check candidate implications, EXACTLY (no sampling).

Setup: F = F_q, code C = a linear subspace of F^n (an [n,k] code).
Curve stack u = (u_0,...,u_L) each in F^n. curveAt(u,gamma)[i] = sum_j gamma^j u_j[i].
"""
import itertools

def gf_prime(q):
    return list(range(q))

def vsub(a,b,q): return tuple((x-y)%q for x,y in zip(a,b))
def vadd(a,b,q): return tuple((x+y)%q for x,y in zip(a,b))
def smul(c,a,q): return tuple((c*x)%q for x in a)

def hamming(a,b): return sum(1 for x,y in zip(a,b) if x!=y)

def gen_code(gens, q, n):
    # all F_q-linear combinations of generator rows
    code=set()
    k=len(gens)
    for coeffs in itertools.product(range(q),repeat=k):
        w=tuple(0 for _ in range(n))
        for c,g in zip(coeffs,gens):
            w=vadd(w,smul(c,g,q),q)
        code.add(w)
    return code

def curve_at(u, gamma, q, n, L):
    # u: list of L+1 words. returns word of length n
    return tuple(sum((gamma**j)*u[j][i] for j in range(L+1))%q for i in range(n))

def main():
    q=5; n=4; k=2
    F=gf_prime(q)
    # RS-like code: evaluations of degree<k polys at points 1,2,3,4
    pts=[1,2,3,4]
    gens=[]
    # basis: poly x^0, x^1 -> k=2
    for d in range(k):
        gens.append(tuple((p**d)%q for p in pts))
    C=gen_code(gens,q,n)
    Clist=sorted(C)
    print(f"q={q} n={n} k={k}  |C|={len(C)}  min nonzero dist", 
          min(hamming(c,tuple(0 for _ in range(n))) for c in C if any(c)))

    L=1  # curve degree ell=1 => Fin 2 rows (affine line) ; but keep general
    # delta as a fraction with denominator n
    # mcaEventCurve at radius delta: exists S, |S|>= (1-delta)*n, exists w in C, w=curve on S,
    #   and NOT stackJointAgreesOn (no codeword stack agreeing with u rowwise on S)
    # We test for each stack u and each gamma.

    # We want to test candidate THEOREM:
    #   (T1) If for a-many seeds gamma the curve is delta-close to a codeword (codeword-valued f),
    #        and code is curve-decodable producing single stack cs with f=curveAt(cs) on b seeds,
    #        does that bound the mcaEventCurve probability?
    # The cleaner per-event fact we test exactly:
    #   (T2) mcaEventCurve C delta u gamma  =>  curve delta-close to C (already proven in tree).
    #   (T3) If u itself is a stack of codewords (all u_j in C), then for EVERY gamma
    #        the curve curveAt(u,gamma) is itself a codeword (linear code closed under the
    #        polynomial combination), hence stackJointAgreesOn holds (u agrees with itself),
    #        hence mcaEventCurve is FALSE for every gamma  => epsMCACurve contribution 0
    #        for codeword stacks. (sanity: the bad event needs u NOT all-codeword.)
    # Verify T3 exactly:
    def stack_joint_agrees_full(u,C,q,n,L):
        # there is codeword stack v (each v_j in C) with v_j = u_j on ALL of S; we test S=all positions
        # equivalent: every row u_j is itself in C (agreement on all positions => v_j=u_j)
        return all(u[j] in C for j in range(L+1))
    # Test T3: pick u all codewords
    cnt_bad=0; cnt_tot=0
    import random
    Crows=Clist
    # enumerate all stacks of codewords (small)
    for u0 in Crows:
        for u1 in Crows:
            u=[u0,u1]
            allcw=stack_joint_agrees_full(u,C,q,n,L)
            for gamma in F:
                cw=curve_at(u,gamma,q,n,L)
                is_codeword = cw in C
                cnt_tot+=1
                if allcw and not is_codeword:
                    cnt_bad+=1
    print(f"T3 check: stacks-of-codewords curve always a codeword? violations={cnt_bad}/{cnt_tot}")

    # T4: the KEY honest bridge. Consider the 'codeword-valued f' = curveAt of a FIXED codeword
    #     stack cs. Then for EVERY seed gamma, f gamma = curveAt(cs,gamma) is a codeword, and
    #     the close set is ALL of F (distance 0 <= delta). Curve-decodability then must return
    #     cs itself (or another) explaining b seeds. The MCA-relevant statement: when the tested
    #     stack u EQUALS a codeword stack cs on the close-set seeds via the curve, the no-stack
    #     clause of mcaEventCurve FAILS. We verify: if exists codeword stack cs with
    #     curveAt(cs,gamma)=curveAt(u,gamma) for the witness... that's automatically u rowwise? NO.
    # Instead verify the precise FALSE direction to AVOID over-claiming:
    #   Is "curve delta-close to codeword at gamma" ENOUGH to force stackJointAgreesOn? NO (that's
    #   exactly why MCA is nontrivial). Confirm a witness where curve is close but no stack agrees.
    found=False
    zero=tuple(0 for _ in range(n))
    for u0 in itertools.product(F,repeat=n):
        if found: break
        for u1 in itertools.product(F,repeat=n):
            u=[u0,u1]
            # need NOT all rows codewords (else stack agrees trivially on all positions)
            if u0 in C and u1 in C: continue
            for gamma in F:
                cw=curve_at(u,gamma,q,n,L)
                # delta=1/4 => floor((1-1/4)*4)=3 positions agree => hamming<=1
                # find codeword within hamming<=1 of cw on some S of size>=3
                for w in C:
                    agree=[i for i in range(n) if w[i]==cw[i]]
                    if len(agree)>=3:
                        S=set(agree[:3])
                        # check no codeword stack agrees with u rowwise on S
                        # row j: exists codeword matching u_j on S?
                        def row_ok(uj):
                            return any(all(w2[i]==uj[i] for i in S) for w2 in C)
                        if not (row_ok(u0) and row_ok(u1)):
                            found=True
                            print(f"T4: mcaEventCurve witness EXISTS: curve delta-close but no stack agrees.")
                            print(f"     u0={u0} u1={u1} gamma={gamma} S={S} w={w}")
                            break
                if found: break
            if found: break
    if not found:
        print("T4: no mcaEventCurve witness found at this scale (try larger).")

main()
