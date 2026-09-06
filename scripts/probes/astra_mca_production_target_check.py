#!/usr/bin/env python3
"""Exact bounded arithmetic for the production target and published bound gates.
No codeword enumeration, field scan, floating-point root, or external package.
"""
from fractions import Fraction
from math import isqrt
import json
n=2**30;k=n//2;Q=2**128;p=n*(Q+192)+1
unsafe_errors=(n-1)//3
safe_candidate_errors=unsafe_errors-1
A=n-safe_candidate_errors
assert (unsafe_errors,safe_candidate_errors,A)==(357913941,357913940,715827884)
assert p//Q==n and n*Q<=p<(n+1)*Q
margin=(n+1)*Q-p
assert margin==340282366920938463463374607225609781247
# Exact Johnson floor: n-ceil(sqrt(n(k-1))).
radicand=n*(k-1);root_floor=isqrt(radicand)
assert root_floor**2<radicand<(root_floor+1)**2
johnson_floor=n-root_floor-1
steps=safe_candidate_errors-johnson_floor
assert (johnson_floor,steps)==(314491699,43422241)
# Exact least shortening t that satisfies (A-t)^2>(n-t)(k-t-1).
num=radicand-A*A;den=n+k-1-2*A
assert num>0 and den>0
shorten_min=num//den+1
assert shorten_min==357913932
assert A*A-radicand+(shorten_min-1)*den<=0
assert A*A-radicand+shorten_min*den>0
assert 400<shorten_min<k
# Every factor in C(n,t)/C(A,t) is >= n/A >7/5.
assert Fraction(n,A)>Fraction(7,5)
assert 7**400>p*5**400
# All-test-size MDS envelope U_b=C(n,b)/C(A-1,b-1) is increasing:
# U_(b+1)/U_b = b(n-b)/((b+1)(A-b)) >=1 iff b(n-A+1)>=A.
assert (k+1)*(n-A+1)>A
# Its minimum has k factors (n-1-j)/(A-1-j)>7/5 and factor n/(k+1)>1.
assert k>=400 and Fraction(n-1,A-1)>Fraction(7,5) and n>k+1
# Random-RS theorem rate condition requires eta <= (1-R-delta)/2.
R=Fraction(k,n);delta=Fraction(safe_candidate_errors,n)
eta_max=(1-R-delta)/2
L=(1-R)/eta_max
ceilL=-(-L.numerator//L.denominator)
assert ceilL==6
# Generic list-to-MCA radius gamma <1-sqrt(1-delta_list) would need
# delta_list>2gamma-gamma^2; this exceeds half-rate capacity 1/2 here.
required_list_radius=2*delta-delta*delta
assert required_list_radius>1-R
# BCPZZ parameter obstruction uses polynomial identity for theta in(0,1):
# 27-256theta^3(1-theta)=(4theta-3)^2(16theta^2+8theta+3).
def mul(f,g):
 h=[0]*(len(f)+len(g)-1)
 for i,a in enumerate(f):
  for j,b in enumerate(g):h[i+j]+=a*b
 return h
assert mul(mul([-3,4],[-3,4]),[3,8,16])==[27,0,0,-256,256]
assert Fraction(9,65536)<Fraction(1,2**12)
assert 2**158<p<2**159<2**180
print(json.dumps({'status':'PASS_EXACT_TARGET_AND_LITERATURE_GATES','n':n,'k':k,'prime':p,'scalar_budget':n,'unsafe_radius':[unsafe_errors,n],'predecessor_radius':[safe_candidate_errors,n],'predecessor_agreements':A,'strict_security_margin':margin,'johnson_error_floor':johnson_floor,'steps_beyond_johnson':steps,'minimum_johnson_shortening':shorten_min,'shortening_prefactor_exceeds_field':True,'all_test_mds_envelope_is_field_cap':True,'random_rs_minimum_displayed_list_multiplier':ceilL,'generic_list_to_mca_requires_beyond_capacity':True,'bcpzz_explicit_parameter_floor_exceeds_field':True,'production_scan_replayed':False,'new_mca_witness_constructed':False},indent=2))
