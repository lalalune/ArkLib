// wf-C1: effective-Chebotarev count of BAD prize primes for the M1 Spur_r reduction.
//
// The M1 reduction needs (S-M1): Spur_r(p) = #{antipodal-free T, |T|<=2r : p | N(sigma_T)} small.
// A prize prime p is "bad at depth r" iff p divides N(sigma_T) for SOME antipodal-free T of
// weight <= 2r, sigma_T = sum_{i in T} (+/-) zeta_n^i, N = Norm_{Q(zeta_n)/Q}.
//
// STRATEGY: enumerate antipodal-free T (weight w = |T|, sign pattern), compute the EXACT integer
// norm N(sigma_T) via the resultant Res(Phi_n(x), sigma_T(x)) over Z (sigma_T is a Laurent poly in
// zeta but antipodal-free reps live in {0..n/2-1} so we use the n/2 "half" exponents with the
// antipodal relation zeta^{i+n/2} = -zeta^i). Factor each |N|, collect the set of primes p ~ n^beta
// that divide SOME such norm. Density of bad primes among all prize primes p ≡ 1 (mod n) in a band
// = the effective-Chebotarev count. If density -> 0 (or stays a sparse set), (S-M1) holds with eps=0
// generically and the bad set is a measure-zero exceptional family.
//
// We compute N(sigma_T) exactly using f64-free integer arithmetic via resultant of integer polys.
//
// build: rustc -O c1_badprime_chebotarev.rs -o /tmp/c1bp

// ---------- big-ish integer norm via product of conjugates with i128, fallback to f64 log house ----------
// N(sigma_T) = prod_{k in (Z/n)^*} sigma_T(zeta_n^k). Antipodal-free T with exponents in [0,n)
// reduced to half via sign: rep as coefficient vector c[0..n) in {-1,0,1}, "antipodal-free" means
// not both i and i+n/2 chosen with opposite... actually antipodal-free := the signed multiset has no
// pair {+zeta^i, -zeta^i} = no i with c[i] and c[i+n/2] s.t. they'd cancel. We enumerate signed
// subsets of the n/2 lines L_i = {zeta^i, zeta^{i+n/2}=-zeta^i}, picking for line i one of
// {0, +zeta^i, -zeta^i} i.e. coefficient in {-1,0,1} at exponent i (i in [0,n/2)). This is exactly
// the antipodal-reduced representation: sigma = sum_{i<n/2} a_i zeta^i, a_i in {-1,0,1}, weight=#nonzero.
// N = prod_{k odd, 1<=k<n} sigma(zeta^k)  (conjugates = primitive n-th roots; n=2^mu so phi(n)=n/2,
// primitive roots = zeta^k for k odd).
//
// |N| computed exactly as the resultant of the integer polynomial A(x)=sum a_i x^i (deg < n/2) and
// the cyclotomic Phi_n(x) = x^{n/2}+1. We compute Res(Phi_n, A) = prod_{Phi_n(beta)=0} A(beta) up to
// sign = product over primitive roots. Use the resultant-as-determinant-free recurrence:
// Res(x^{n/2}+1, A) via repeated reduction. Simpler & exact: evaluate the NORM as the constant term
// of prod (x - sigma(zeta^k)) is heavy; instead use the integer resultant by the subresultant /
// polynomial-remainder over rationals with i128. For n<=64, deg A < 32, coeffs in {-1,0,1}; norms
// fit in i128 for small weight (we cap weight; large weight overflows -> we detect & use f64).

fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}

// Resultant Res(B, A) where B = x^d + 1 (Phi_{2d}, d=n/2 a power of 2), A given by coeff vec (len d).
// We compute prod over roots beta of B of A(beta). Roots of x^d+1: the 2d-th primitive roots... but
// for the NORM over Q(zeta_n) we need exactly the phi(n)=d primitive n-th roots which ARE the roots
// of x^d+1 (since x^d+1 = Phi_n for n=2d, n power of 2). So N(sigma) = Res(x^d+1, A) / leadcoef^... =
// prod_{beta: beta^d=-1} A(beta). Compute via polynomial arithmetic: reduce A mod (x^d+1) is identity
// (deg A<d). Use the formula Res(x^d+1,A) = prod A(beta). Evaluate exactly by complex f64 -> round,
// AND track an exact i128 path via the "norm = det of multiplication-by-A on Z[x]/(x^d+1)" using
// the circulant-like structure (mult by x is the negacyclic shift). The norm is det of the negacyclic
// matrix of A, an integer. We compute it modulo several primes (CRT) to get exact value, then factor.

// negacyclic matrix M: column j = x^j * A mod (x^d+1). (x^j*A) coefficient: shift with sign wrap.
// det(M) = N(sigma) exactly. Compute det mod q for several primes q, CRT to recover (with sign).

// Exact integer determinant of the negacyclic matrix of A via fraction-free Bareiss elimination.
// Entries in {-1,0,1}; for d<=16 intermediate values fit i128 comfortably (|N|<=16^8 here).
fn norm_exact(a:&[i64], d:usize)->i128{
    // build negacyclic matrix: column j = x^j * A mod (x^d+1)
    let mut m=vec![vec![0i128;d];d];
    for j in 0..d {
        for r in 0..d {
            let v = if r>=j { a[r-j] } else { -a[r-j+d] };
            m[r][j]=v as i128;
        }
    }
    // Bareiss fraction-free Gaussian elimination -> det = m[d-1][d-1] at end.
    let mut sign:i128=1;
    let mut prev:i128=1;
    for k in 0..d {
        if m[k][k]==0 {
            // find pivot below
            let mut piv=k+1; while piv<d && m[piv][k]==0 { piv+=1; }
            if piv==d { return 0; }
            m.swap(k,piv); sign=-sign;
        }
        for i in (k+1)..d {
            for j in (k+1)..d {
                m[i][j] = (m[i][j]*m[k][k] - m[i][k]*m[k][j]) / prev;
            }
            m[i][k]=0;
        }
        prev=m[k][k];
    }
    sign * m[d-1][d-1]
}

fn mpow128(mut a:i128,mut e:i128,m:i128)->i128{let mut r=1i128;a%=m;while e>0{if e&1==1{r=r*a%m;}a=a*a%m;e>>=1;}r}
fn isprime128(n:i128)->bool{
    if n<2{return false} for &q in &[2,3,5,7,11,13,17,19,23,29,31,37]{ if n%q==0 {return n==q;} }
    let mut d=n-1; let mut s=0; while d&1==0 {d>>=1;s+=1;}
    'w: for &a in &[2i128,3,5,7,11,13,17,19,23,29,31,37]{
        let mut x=mpow128(a,d,n); if x==1||x==n-1{continue;}
        for _ in 0..s-1 { x=x*x%n; if x==n-1 {continue 'w;} }
        return false;
    }
    true
}
// factor |N| (i128): pull all small primes, then if a cofactor remains, record its prime factors
// that land in the prize band. Records ALL prime factors in band (a prize prime is "bad" if it is
// such a factor), so we collect every band prime dividing any norm.
fn prime_factors(mut x:i128, big_lo:i128, big_hi:i128, out:&mut std::collections::BTreeSet<u64>){
    if x<0 { x=-x; }
    if x==0 || x==1 { return; }
    let mut d:i128=2;
    while d*d<=x {
        if x%d==0 {
            while x%d==0 { x/=d; }
            if d>=big_lo && d<=big_hi { out.insert(d as u64); }
        }
        d+=1;
    }
    if x>1 {
        // cofactor: if prime and in band, record; if composite of two band-ish primes we'd miss, but
        // such double-band-prime cofactors are >= big_lo^2 >> any small-weight norm, so impossible.
        if x>=big_lo && x<=big_hi && isprime128(x) {
            out.insert(x as u64);
        }
    }
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 16 };
    let wmax:usize = if args.len()>2 { args[2].parse().unwrap() } else { 6 };
    let d=(n/2) as usize; // phi(n)
    let beta=4.0f64;
    let plo=(n as f64).powf(beta) as i128;
    let phi=(n as f64).powf(beta+1.0) as i128; // band [n^4, n^5]
    let prize_p = fp(n, plo as u64);
    println!("== wf-C1 bad-prime / Chebotarev count: n={} phi(n)={} weight<={} ==", n, d, wmax);
    println!("   prize band p in [{}, {}] (~n^4..n^4.3); a sample prize prime = {}", plo, phi, prize_p);

    // enumerate antipodal-free configs: coeff vec a[0..d) in {-1,0,1}, weight (#nonzero) in 1..=wmax.
    // Norm is invariant under mult-by-zeta (N(zeta)=±1, the negacyclic shift) and under sigma->-sigma,
    // so we fix a[0]=+1 (first coeff = leading nonzero with positive sign). Each norm-orbit counted
    // once (up to the orbit-size factor, irrelevant to the BAD-prime SET). Threaded over a[1]'s value.
    use std::sync::{Arc,Mutex};
    use std::thread;
    let shared_bad:Arc<Mutex<std::collections::BTreeSet<u64>>>=Arc::new(Mutex::new(std::collections::BTreeSet::new()));
    let shared_hist:Arc<Mutex<Vec<u64>>>=Arc::new(Mutex::new(vec![0u64;64]));
    let shared_total:Arc<Mutex<u64>>=Arc::new(Mutex::new(0u64));
    // thread shards: value of a[1] in {-1,0,1} (3 shards) x value of a[2] in {-1,0,1} (9 shards)
    let mut handles=vec![];
    for s in 0..9i64 {
        let sb=Arc::clone(&shared_bad); let sh=Arc::clone(&shared_hist); let st=Arc::clone(&shared_total);
        handles.push(thread::spawn(move||{
            let a1=(s%3)-1; let a2=(s/3)-1;
            let mut a=vec![0i64;d]; a[0]=1;
            let mut used=1usize;
            a[1]=a1; if a1!=0 {used+=1;}
            if d>2 { a[2]=a2; if a2!=0 {used+=1;} }
            if used>wmax { return; }
            let mut lbad:std::collections::BTreeSet<u64>=std::collections::BTreeSet::new();
            let mut lhist=vec![0u64;64]; let mut ltot=0u64;
            fn rec(a:&mut Vec<i64>, pos:usize, d:usize, left:usize,
                   total:&mut u64, hist:&mut Vec<u64>, bad:&mut std::collections::BTreeSet<u64>,
                   plo:i128, phi:i128){
                if pos==d {
                    let nv=norm_exact(a,d); *total+=1;
                    let av=if nv<0 {-nv} else {nv};
                    if av>0 { let lb=(av as f64).log2() as usize; if lb<hist.len(){hist[lb]+=1;} }
                    prime_factors(nv,plo,phi,bad);
                    return;
                }
                a[pos]=0; rec(a,pos+1,d,left,total,hist,bad,plo,phi);
                if left>0 {
                    a[pos]=1; rec(a,pos+1,d,left-1,total,hist,bad,plo,phi);
                    a[pos]=-1; rec(a,pos+1,d,left-1,total,hist,bad,plo,phi);
                    a[pos]=0;
                }
            }
            let startpos=if d>2 {3} else {2};
            rec(&mut a,startpos,d,wmax-used,&mut ltot,&mut lhist,&mut lbad,plo,phi);
            { let mut g=sb.lock().unwrap(); for x in lbad {g.insert(x);} }
            { let mut g=sh.lock().unwrap(); for i in 0..64 {g[i]+=lhist[i];} }
            { let mut g=st.lock().unwrap(); *g+=ltot; }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let bad=shared_bad.lock().unwrap().clone();
    let norm_hist=shared_hist.lock().unwrap().clone();
    let total_configs=*shared_total.lock().unwrap();

    println!("   enumerated {} antipodal-free signed configs (weight<= {})", total_configs, wmax);
    print!("   |N| log2 histogram: ");
    for (i,&c) in norm_hist.iter().enumerate(){ if c>0 { print!("[2^{}:{}] ", i, c);} }
    println!();
    // count prize primes in band
    let mut band_primes:u64=0; let mut p=plo as u64; if p%n!=1 { p+=(1+n-p%n)%n; }
    while (p as i128) <= phi { if isp(p)&&p%n==1 { band_primes+=1; } p+=n; }
    println!("   BAD prize primes found (divide some weight<=2r norm in band): {}", bad.len());
    for &bp in bad.iter().take(20){ println!("       bad p = {}  (={:.3} = n^{:.3})", bp, bp as f64, (bp as f64).ln()/(n as f64).ln()); }
    println!("   total prize primes p≡1(mod {}) in band [{},{}]: {}", n, plo, phi, band_primes);
    if band_primes>0 {
        println!("   ==> BAD DENSITY = {}/{} = {:.6}", bad.len(), band_primes, bad.len() as f64/band_primes as f64);
    }
}
