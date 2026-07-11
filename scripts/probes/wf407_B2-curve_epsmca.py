"""
wf407 / B2-curve, part 2: the EXACT epsMCACurve <-> curve-decodability bridge.

mcaEventCurve C delta u gamma needs:
  (a) exists S, |S| >= (1-delta)n, exists w in C with w = curveAt(u,gamma) on S
  (b) NOT stackJointAgreesOn C S u   (no codeword stack agrees with u rowwise on S)

KEY OBSERVATION to test exactly: clause (a) says the SINGLE curve point at gamma is
delta-close to C. Clause (b) is about the ROWS of u. These are decoupled in gamma.

The GG25/Jo26 'curve-decodability => MCA' content is really about the close set of SEEDS.
But epsMCACurve is sup over u of Pr_gamma[bad]. The honest bridge we CAN prove cleanly:

  PROPOSITION (provable): If every row u_j of the stack is a codeword (u in C^{L+1}),
  then mcaEventCurve C delta u gamma is FALSE for every gamma and every delta<1.
  Hence such stacks contribute 0 to epsMCACurve. (The bad event requires the tested
  stack to be 'genuinely non-codeword'.)

  Proof sketch: u_j in C for all j => taking v=u as the agreeing stack, stackJointAgreesOn
  holds on ANY S (v_j=u_j agree everywhere). So clause (b) is violated. QED.

  Verify exactly over ALL gamma, ALL delta thresholds, ALL codeword stacks.
"""
import itertools

def gf(q): return list(range(q))
def vadd(a,b,q): return tuple((x+y)%q for x,y in zip(a,b))
def smul(c,a,q): return tuple((c*x)%q for x in a)
def hamming(a,b): return sum(1 for x,y in zip(a,b) if x!=y)

def gen_code(gens,q,n):
    code=set()
    for coeffs in itertools.product(range(q),repeat=len(gens)):
        w=tuple(0 for _ in range(n))
        for c,g in zip(coeffs,gens): w=vadd(w,smul(c,g,q),q)
        code.add(w)
    return code

def curve_at(u,gamma,q,n,L): return tuple(sum((gamma**j)*u[j][i] for j in range(L+1))%q for i in range(n))

def stack_joint_agrees(u,C,S,L):
    # exists codeword stack v with v_j = u_j on S, for each j
    def row_ok(uj): return any(all(w[i]==uj[i] for i in S) for w in C)
    return all(row_ok(u[j]) for j in range(L+1))

def mca_event_curve(C,delta_num,delta_den,u,gamma,q,n,L):
    # delta = delta_num/delta_den ; |S|>=(1-delta)n  i.e. |S| >= n - delta*n
    cw=curve_at(u,gamma,q,n,L)
    minS = -(-(delta_den-delta_num)*n // delta_den)  # ceil((1-delta)*n) ... use >= with rational
    # |S|>=(1-delta)n  <=>  delta_den*|S| >= (delta_den-delta_num)*n
    for w in C:
        agree=[i for i in range(n) if w[i]==cw[i]]
        # need a subset S of agree with delta_den*|S| >= (delta_den-delta_num)*n and clause(b) fails
        # the BEST chance for clause(b) failing is the LARGEST agree set; but clause(b)
        # depends on S. We check: exists S subset of agree, |S| big enough, no stack agrees on S.
        import itertools as it
        m=len(agree)
        # minimal size
        need = -(-(delta_den-delta_num)*n // delta_den)
        if m < need: continue
        for sz in range(need, m+1):
            for S in it.combinations(agree, sz):
                S=set(S)
                if not stack_joint_agrees(u,C,S,L):
                    return True
    return False

def main():
    q=5; n=4; k=2
    F=gf(q); pts=[1,2,3,4]
    gens=[tuple((p**d)%q for p in pts) for d in range(k)]
    C=gen_code(gens,q,n); Clist=sorted(C)
    L=1
    # PROPOSITION test: all codeword stacks => no bad event, for delta in {1/4,1/2}
    violations=0; total=0
    for dn,dd in [(1,4),(1,2),(3,4)]:
        for u0 in Clist:
            for u1 in Clist:
                u=[u0,u1]
                for gamma in F:
                    total+=1
                    if mca_event_curve(C,dn,dd,u,gamma,q,n,L):
                        violations+=1
    print(f"PROP (codeword stacks => no mcaEventCurve): violations={violations}/{total}")

    # Also: count epsMCACurve numerator over ALL stacks at delta=1/4 to show it's nonzero
    dn,dd=1,4
    worst=0; worst_u=None
    # sample subset of stacks for speed: all u0 codeword? no, ALL stacks too big (5^8). 
    # Restrict u0,u1 to a manageable random-but-exact subset: enumerate u0 in C, u1 arbitrary small
    import itertools as it
    badcount_examples=0
    for u0 in it.product(F,repeat=n):
        for u1 in it.product(F,repeat=n):
            u=[u0,u1]
            bad=sum(1 for gamma in F if mca_event_curve(C,dn,dd,u,gamma,q,n,L))
            if bad>worst:
                worst=bad; worst_u=(u0,u1)
        # limit: only first few u0 to keep runtime bounded
        if u0==(0,0,1,1): break
    print(f"epsMCACurve numerator (max bad seeds over scanned stacks, delta=1/4): {worst}/{q}  at u={worst_u}")

main()
