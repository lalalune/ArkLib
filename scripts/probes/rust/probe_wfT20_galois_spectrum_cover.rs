// Probe for #444 candidate T20 (G4-5): Galois-equivariant covering of the large spectrum
// with a 2-power divisibility floor 2^nu(p), nu(p) = v2(ord(p mod n)).
//
// CANDIDATE: Spec_alpha = {b!=0 : |eta_b| >= alpha*n} is closed under BOTH
//   (i) dilation by mu_n  (PROVEN: eta_norm_const_on_coset)  -- orbits of size n
//   (ii) the decomposition-group Frobenius sigma_p acting on the spectrum, "permuting
//        Gauss periods preserving |eta_b|".
// claim: number of distinct large-orbit REPRESENTATIVES <= O((p/n)/2^nu(p)),
//        and Parseval over the few orbits forces M <= C sqrt(n log(p/n)) when
//        nu(p) >= log2 log(p/n).
//
// WHAT WE TEST (the architect's two honest cruxes):
//   CRUX #2 (the load-bearing reduction risk): does ANY natural "Frobenius" map sigma_p on
//     frequencies b preserve |eta_b| BEYOND the dilation already given by mu_n? The candidate
//     names sigma_p = Frobenius of p. We test the only natural candidates:
//        (a) b -> b^p mod p           (Frobenius on F_p: b^p = b -- IDENTITY, vacuous)
//        (b) b -> b * (something p-sensitive) -- the cyclotomic Frob on Q(zeta_n): the
//            period value eta_b depends only on coset b*mu_n in F_p^*/mu_n =: quotient Q of
//            order m=(p-1)/n. We test whether the map on Q induced by "raise the n-th-root
//            label to the p-th power" (i.e. the Gal(Q(zeta_n)/Q) Frobenius p mod n) gives a
//            NONTRIVIAL permutation of the coset values that preserves |eta|.
//   CRUX #1: even granting closure, is the representative count actually reduced by 2^nu(p)?
//
// Periods are REAL for n=2^mu (since -1 in mu_n), so |eta_b| = |real value|.
// We compute eta_b exactly enough (f64) at prize-shape primes p ~ n^4, p = 1 mod n.

use std::f64::consts::PI;

fn mpow(a:u64, mut e:u64, p:u64)->u64{
    let mut r:u128=1; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; }
    r as u64
}
fn is_prime(n:u64)->bool{ if n<2 {return false;} let mut d=2u64; while d*d<=n { if n%d==0 {return false;} d+=1; } true }
fn find_prime_cong1(n:u64, lo:u64)->u64{
    let mut p = lo + ((n + 1 - lo % n) % n);
    if p<=2 { p+=n; }
    loop { if p>2 && p%n==1 && is_prime(p) { return p; } p+=n; }
}
fn primitive_root(p:u64)->u64{
    let mut m=p-1; let mut fs=vec![]; let mut d=2u64;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 { m/=d; } } d+=1; }
    if m>1 { fs.push(m); }
    let mut g=2u64;
    loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g; } g+=1; }
}
fn v2(mut x:u64)->u32{ if x==0 {return 0;} let mut v=0; while x&1==0 { v+=1; x>>=1; } v }
// multiplicative order of a mod n
fn ord_mod(a:u64, n:u64)->u64{
    let a = a % n;
    if a==0 { return 0; }
    let mut k=1u64; let mut cur=a%n;
    while cur!=1 { cur = cur*a%n; k+=1; if k>n { return 0; } }
    k
}

fn eta_real(b:u64, mu:&[u64], p:u64)->f64{
    // real part (imag ~ 0 for n=2^mu); return signed real
    let mut re=0.0f64;
    for &x in mu {
        let t = ((b as u128 * x as u128) % p as u128) as u64;
        let ang = 2.0*PI*(t as f64)/(p as f64);
        re += ang.cos();
    }
    re
}

fn main(){
    println!("# T20 Galois-equivariant spectrum cover probe (prize-shape p ~ n^4, p=1 mod n)");
    for &n in &[8u64,16,32,64,128] {
        // pick several primes p = 1 mod n, p > n^4
        let base = n*n*n*n; // n^4
        let mut primes = vec![];
        let mut lo = base + 1;
        while primes.len() < 4 {
            let p = find_prime_cong1(n, lo);
            primes.push(p);
            lo = p + 1;
        }
        for &p in &primes {
            let g = primitive_root(p);
            let h = mpow(g, (p-1)/n, p);              // generator of mu_n
            let mu:Vec<u64> = (0..n).map(|j| mpow(h,j,p)).collect();
            let m = (p-1)/n;                          // number of cosets
            let gn = mpow(g, n, p);                   // generator of quotient F_p^*/mu_n (order m)

            // coset reps b_j = g^j, j=0..m-1 (each hits a distinct coset).
            // Compute signed real eta and |eta| for each coset rep.
            let mut reps = Vec::with_capacity(m as usize);
            let mut bj = 1u64;
            for _ in 0..m {
                let e = eta_real(bj, &mu, p);
                reps.push((bj, e, e.abs()));
                bj = (bj as u128 * gn as u128 % p as u128) as u64;
            }
            // M = max |eta_b|
            let mm = reps.iter().fold(0.0f64,|acc,&(_,_,a)| acc.max(a));
            let sqrt_n = (n as f64).sqrt();
            let logm = ((p as f64)/(n as f64)).ln();
            let c_floor = mm/(sqrt_n*logm.sqrt());

            // ord(p mod n) -- but p = 1 mod n, so ord = 1, nu = v2(1)=0!  THIS is the first red flag.
            let ord_p = ord_mod(p % n, n);
            let nu = v2(ord_p);

            // ===== CRUX #2 test: does a NONTRIVIAL Frobenius on the QUOTIENT preserve |eta|? =====
            // The candidate's sigma_p must permute COSETS (the m distinct period values) nontrivially.
            // Natural candidate: the map on the quotient Q = F_p^*/mu_n induced by b -> b^k for some
            // p-sensitive k. Test b -> b^p (Frobenius F_p): b^p = b, IDENTITY => vacuous on F_p.
            // The only frequency map preserving |eta_b| that is "p-sensitive" must come from the
            // structure of which cosets share |eta| values. We MEASURE the value-collision structure:
            // group coset reps by their |eta| value (rounded), count distinct |eta| values =: D_abs.
            // The candidate needs D_abs <= O(m / 2^nu). With nu=0 (forced by p=1 mod n) the claim is
            // D_abs <= O(m), i.e. NO reduction beyond dilation. We report D_abs and m.
            let mut vals:Vec<f64> = reps.iter().map(|&(_,_,a)| (a*1e6).round()/1e6).collect();
            vals.sort_by(|a,b| a.partial_cmp(b).unwrap());
            vals.dedup();
            let d_abs = vals.len();

            // Also test b -> b^p on RAW frequencies to confirm it is identity (vacuous Frobenius).
            // (b^p mod p == b for all b, Fermat) -- so the "Frobenius on F_p" is the identity.
            let frob_is_id = (1..n.min(50)).all(|t| mpow(t, p, p) == t % p);

            println!("n={:>3} p={:>14} m={:>10} M/sqrtn={:.4} C_floor={:.4} ord(p%n)={} nu={} D_abs={} D_abs/m={:.4} frobF_p_id={}",
                n, p, m, mm/sqrt_n, c_floor, ord_p, nu, d_abs, (d_abs as f64)/(m as f64), frob_is_id);
        }
        println!();
    }

    // ===== Direct check of the candidate's covering count claim at one (n,p) =====
    // claim: #distinct large-orbit reps of Spec_alpha <= (p/n)/2^nu(p).
    // Since p = 1 mod n forces ord(p mod n) = 1 => nu = 0 => 2^nu = 1 => NO reduction.
    println!("# NOTE: prize regime REQUIRES p = 1 mod n (so mu_n subset F_p^*).");
    println!("#       Then p mod n = 1, ord(p mod n) = 1, v2(ord) = nu = 0, 2^nu = 1.");
    println!("#       => the candidate's covering-count divisor 2^nu(p) is IDENTICALLY 1 in the prize regime.");
}
