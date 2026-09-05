#!/usr/bin/env python3
"""Actual split-locator pencil controls and actual-prime cubic census; no prize closure."""
from itertools import combinations
from math import comb
import json

PRODUCTION_P = 365375409332725729550921208179070755120141565953
PRODUCTION_G = 303645430271030343624574566109998498685964493478
PRODUCTION_N = 2**30


def mul(f, g, p):
    out = [0] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i+j] = (out[i+j] + x*y) % p
    return out


def evaluate(f, x, p):
    value = 0
    for c in reversed(f):
        value = (value*x + c) % p
    return value


def locator(nodes, p):
    out = [1]
    for x in nodes:
        out = mul(out, [-x % p, 1], p)
    return out


def rank(rows, p):
    rows = [[x % p for x in row] for row in rows]
    next_row = 0
    for column in range(len(rows[0])):
        pivot = next((i for i in range(next_row,len(rows)) if rows[i][column]),None)
        if pivot is None:continue
        rows[next_row],rows[pivot] = rows[pivot],rows[next_row]
        inverse = pow(rows[next_row][column],-1,p)
        rows[next_row] = [x*inverse % p for x in rows[next_row]]
        for i in range(next_row+1,len(rows)):
            coefficient = rows[i][column]
            rows[i] = [(x-coefficient*y) % p for x,y in zip(rows[i],rows[next_row])]
        next_row += 1
        if next_row == len(rows):break
    return next_row


def construct(p, omega, a, b, private_sets, common_errors, parameters):
    """Execute the converse construction and verify every agreement/error support."""
    n, k, agreement, e = 6*b-2, 3*b-1, 4*b-1, 2*b-2
    assert len(omega) == n and len(set(omega)) == n and a in omega
    private_union = set().union(*private_sets)
    assert len(private_union) == sum(map(len, private_sets))
    assert not (private_union & set(common_errors)) and a not in private_union
    assert a not in common_errors
    d = set(omega) - {a}
    assert private_union | set(common_errors) <= d
    s = len(private_sets[0]);g = len(common_errors)
    assert all(len(t) == s for t in private_sets)
    assert g+s == e and g <= b-3
    private_polys = [locator(t,p) for t in private_sets]
    assert len(set(parameters)) == len(parameters) == len(private_sets)
    first_difference = [(x-y) % p for x,y in zip(private_polys[1],private_polys[0])]
    assert any(first_difference)
    for i in range(1,len(private_polys)):
        difference = [(x-y) % p for x,y in zip(private_polys[i],private_polys[0])]
        assert [(parameters[1]-parameters[0])*x % p for x in difference] == [
            (parameters[i]-parameters[0])*x % p for x in first_difference]
    remaining = d - private_union - set(common_errors)
    rem = locator(remaining,p)
    fs = [[0]]
    for i in range(1,len(private_polys)):
        f = rem
        for j,u in enumerate(private_polys):
            if j not in (0,i):f = mul(f,u,p)
        fs.append([(parameters[0]-parameters[i])*x % p for x in f])
    v = {}
    for j,t in enumerate(private_sets):
        for x in t:
            vals = {evaluate(f,x,p) for i,f in enumerate(fs) if i != j}
            assert len(vals) == 1
            v[x] = next(iter(vals))
            assert evaluate(fs[j],x,p) != v[x]
    for x in remaining:
        assert all(evaluate(f,x,p) == 0 for f in fs)
        v[x] = 0
    for x in common_errors:
        vals = {evaluate(f,x,p) for f in fs}
        assert len(vals) == len(fs)
        v[x] = next(z for z in range(len(fs)+1) if z not in vals)
    assert set(v) == d
    values = []
    for i,f in enumerate(fs):
        assert len(f)-1 < k
        errors = {x for x in d if evaluate(f,x,p) != v[x]}
        assert errors == set(common_errors) | private_sets[i]
        assert len(errors) == e and sum(evaluate(f,x,p)==v[x] for x in d) == agreement
        gamma = evaluate(f,a,p)
        support = sorted((d-errors) | {a})
        matrix = [[pow(x,j,p) for j in range(k)] for x in support]
        assert rank(matrix,p) == k
        line = [row+[(gamma if x == a else v[x])] for row,x in zip(matrix,support)]
        joint = [row+[(0 if x == a else v[x]),int(x == a)]
                 for row,x in zip(matrix,support)]
        assert rank(line,p) == k and rank(joint,p) > k
        assert len(support) == 4*b
        values.append(gamma)
    assert len(set(values)) == len(fs)
    return {'n':n,'k':k,'punctured_agreement':agreement,'private_degree':s,
            'common_error_degree':g,'constructed_distinct_values':values,
            'exact_error_supports_verified':True,'same_support_mca_witnesses_checked':len(fs)}


def cubic_pencil_census():
    p,n,g = PRODUCTION_P,PRODUCTION_N,PRODUCTION_G
    w = pow(g,n//16,p)
    assert pow(w,16,p) == 1 and pow(w,8,p) == p-1
    nodes = [pow(w,j,p) for j in range(16)]
    polys,masks = [],[]
    for subset in combinations(range(1,16),3):
        polys.append(tuple(locator((nodes[j] for j in subset),p)[:-1]))
        masks.append(sum(1<<j for j in subset))
    lines = {};pair_count = 0
    for i,f in enumerate(polys):
        for j in range(i):
            if masks[i] & masks[j]:continue
            h = polys[j]
            difference = [(f[c]-h[c]) % p for c in range(3)]
            pivot = next(c for c in range(3) if difference[c])
            inverse = pow(difference[pivot],-1,p)
            direction = tuple(x*inverse % p for x in difference)
            anchor = tuple((f[c]-f[pivot]*direction[c]) % p for c in range(3))
            key = direction,anchor
            lines[key] = lines.get(key,0) | (1<<i) | (1<<j)
            pair_count += 1
    maximum = 2; witness = None; rich = 0
    for bits in lines.values():
        if bits.bit_count() < 3:continue
        rich += 1
        ids = [i for i in range(len(polys)) if bits>>i&1]
        for size in range(min(5,len(ids)),2,-1):
            found = None
            for subset in combinations(ids,size):
                union = 0
                for i in subset:
                    if union & masks[i]:break
                    union |= masks[i]
                else:
                    found = subset;break
            if found is not None:
                if size > maximum:
                    maximum = size
                    witness = [[j for j in range(16) if masks[i]>>j&1] for i in found]
                break
    assert len(polys) == 455 and pair_count == 50050
    assert rich == 28 and maximum == 3
    assert witness is not None
    witness_polys = [locator((nodes[j] for j in subset),p)[:-1] for subset in witness]
    left = [(x-y) % p for x,y in zip(witness_polys[1],witness_polys[0])]
    right = [(x-y) % p for x,y in zip(witness_polys[2],witness_polys[0])]
    assert all((left[i]*right[j]-left[j]*right[i]) % p == 0
               for i,j in combinations(range(3),2))
    return {'field':p,'subgroup_order':16,'omitted_exponent':0,
            'cubic_divisors':len(polys),'disjoint_pairs':pair_count,
            'rich_lines':rich,'maximum_disjoint_pencil_members':maximum,
            'three_member_witness_exponents':witness}


def main():
    p,n,g = PRODUCTION_P,PRODUCTION_N,PRODUCTION_G
    assert p > n and pow(g,n,p) == 1 and pow(g,n//2,p) == p-1
    w = pow(g,n//16,p)
    omega = [pow(w,j,p) for j in range(16)]
    c = [pow(w,4*j,p) for j in (1,2,3)]
    private = [{x for x in omega if pow(x,4,p)==ci} for ci in c]
    subgroup_control = construct(p,omega,1,3,private,[],[-ci % p for ci in c])
    # Sharp generic-domain control: four private 5-cosets, one shared error, hole at zero.
    p = 101;generator = 2
    assert pow(generator,50,p) != 1 and pow(generator,20,p) != 1
    private = [{pow(generator,j+20*t,p) for t in range(5)} for j in range(4)]
    common = [pow(generator,4,p)]
    omega = sorted(set().union(*private) | set(common) | {0})
    parameters = [-pow(generator,5*j,p) % p for j in range(4)]
    generic_control = construct(p,omega,0,4,private,common,parameters)
    # The m=2 endpoint uses an empty product in each difference formula.
    private = [set(range(1,6)),set(range(6,11))]
    endpoint_control = construct(p,list(range(22)),0,4,private,[11],[0,1])
    first,second = [locator(t,p) for t in private]
    assert any((x-y) % p for x,y in zip(first[1:-1],second[1:-1]))
    b = 178956971
    assert 6*b-2 == n
    s = n//4;g = (b-3)//2
    assert s+g == 2*b-2 and (n-1)-g-3*s == b
    assert b+s < 3*b-1
    choices = [2**j for j in range(31) if b+1 <= 2**j <= 2*b-2]
    assert choices == [n//4]
    ell = n//16
    low,high = b+1,(4*b-1)//3
    base_degrees = [d for d in range(1,16) if low <= d*ell <= high]
    assert base_degrees == [3]
    for power in (8,4,2,1):
        assert not [d for d in range(1,power) if low <= d*(n//power) <= high]
    base32_degrees = [d for d in range(1,32) if low <= d*(n//32) <= high]
    assert base32_degrees == [6,7]
    # The note proves the norm transfer. These checks verify its constants;
    # the census supplies a nonzero algebraic minor for each disjoint quadruple.
    cubic_coefficient_bound = max(comb(3,j) for j in range(1,4))
    difference_bound = 2*cubic_coefficient_bound
    minor_bound = 2*difference_bound**2
    cyclotomic_degree = 8
    norm_bound = minor_bound**cyclotomic_degree
    assert cubic_coefficient_bound == 3 and minor_bound == 72
    assert norm_bound == 722204136308736
    assert PRODUCTION_P > norm_bound and PRODUCTION_P % 16 == 1
    result = {'status':'PASS_ACTUAL_SPLIT_LOCATOR_PENCIL_CONTROLS',
              'actual_prime_three_value_control':subgroup_control,
              'generic_domain_four_value_control':generic_control,
              'non_binomial_two_member_endpoint':endpoint_control,
              'actual_prime_cubic_census':cubic_pencil_census(),
              'cubic_norm_transfer_arithmetic':{
                  'coefficient_embedding_bound':cubic_coefficient_bound,
                  'difference_embedding_bound':difference_bound,
                  'minor_embedding_bound':minor_bound,
                  'cyclotomic_degree':cyclotomic_degree,
                  'minor_norm_bound':norm_bound,
                  'production_prime_exceeds_bound':PRODUCTION_P > norm_bound},
              'production_private_binomial_degrees':choices,
              'production_four_member_power16_base_degrees':base_degrees,
              'unresolved_power32_base_degrees':base32_degrees,
              'production_over_budget_counterexample':False,
              'full_production_value_bound':False}
    print(json.dumps(result,sort_keys=True))

if __name__ == '__main__':main()
