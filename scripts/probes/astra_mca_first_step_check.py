"""Exact first-step arithmetic and dense spike controls; standard library only.

See docs/kb/astra_mca_first_step-2026-09-08.md for the written general
arguments. Dense controls do not prove the full production scalar bound."""
import json

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
S = N // 4
K = N // 2
T = 3 * S - 1
E = K - 1

assert N * 2**128 < P < (N + 1) * 2**128
assert 5*T*T-N*(T+4*E) == S*S-10*S+5 > 0
assert 4*T*T-(N-1)*(T+3*E) == S > 0
assert 3*T-N > 2*K-2
assert 3*(N-T) < N

def dense_control(n):
    s, k = n//4, n//2
    t = 3*s-1
    g = pow(G, N//n, P)
    dom = [pow(g, j, P) for j in range(n)]
    assert len(set(dom)) == n and pow(g, n, P) == 1
    roots = set(dom[:k-1])
    remaining = [x for x in dom if x not in roots]
    aa = set(remaining[:s])
    bb = set(remaining[s:])
    spike = remaining[0]
    def c(x):
        z = 1
        for r in roots:
            z = z*(x-r) % P
        return z
    u = {x: c(x) if x in aa else 0 for x in dom}
    v = {x: int(x == spike) for x in dom}
    witness = {x for x in dom if u[x] == c(x)}
    zero_joint_core = {x for x in dom if u[x] == 0 and v[x] == 0}
    assert witness == roots | aa and len(witness) == t
    assert len(bb) == s+1 and len(zero_joint_core) == t+1
    assert sum(v[x] == 0 for x in witness) == t-1 >= k
    assert v[spike] == 1 and spike in witness and c(spike) != 0
    return {"n":n,"k":k,"threshold":t,"witness":len(witness),
            "zero_joint_core":len(zero_joint_core),
            "spike_zero_constraints":t-1,"passed":True}

print(json.dumps({
    "production":{"n":N,"k":K,"threshold":T,"security_budget":P//2**128,
                  "five_list_gap":5*T*T-N*(T+4*E),
                  "four_list_puncture_gap":4*T*T-(N-1)*(T+3*E),
                  "determinant_degree":2*K-2,"forced_multiplicity":3*T-N,
                  "three_source_bound":3*(N-T)},
    "dense_controls":[dense_control(n) for n in (16,64,256)]
}, indent=2))
