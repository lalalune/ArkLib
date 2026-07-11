// Probe for #444 attack T10 (architect G2-5): Mahler-measure / Lehmer LOWER bound on the
// period polynomial UPPER-bounds the archimedean root (House) via 1/k_b division + a 2-adic
// content squeeze.  At prize-shaped parameters p = n^4, p = 1 mod n.
//
// The candidate's CENTRAL chain:
//   (S1)  House(theta_b) <= Mahler(Psi_b)^{1/k_b}        [k_b = #{conjugates of modulus > 1}]
//   (S2)  Mahler(Psi_b)  <= n^{k_b/2} * exp(-c * v2-content)
//   (=>)  M(n) = House    <= sqrt(n) * exp(-c * v2-content / k_b)   < wall when content = Omega(k_b)
//
// We DIRECTLY measure, for the *true* Gauss periods (the architect's theta_b is the lifted
// period; on F_p it is eta_b, the period whose max over b is the prize object M(n)):
//   * For each coset b, the COMPLEX conjugate set {sigma theta_b} = the phi(n) embeddings of the
//     period theta_b = sum_{x in mu_n} zeta_n^{ind(x) b}.  We compute these phi(n) Gauss periods
//     (Gaussian periods of the n-cyclotomic field) and from them: House (max modulus), the count
//     k_b of moduli > 1, Mahler = product of large moduli, and the geometric mean Mahler^{1/k_b}.
//   * We test S1: is House <= Mahler^{1/k_b}?  (candidate) or House >= Mahler^{1/k_b}? (AM/GM).
//
// NOTE on the object: the *archimedean* Gauss periods theta_b live in Q(zeta_n) and are
// independent of p.  Their House is O(1)-ish (sums of n/2 unit vectors / 2 ... bounded by phi(n)).
// The p-side eta_b = sum_{x in mu_n} e_p(b x) is the prize object with House ~ sqrt(n).  The
// candidate CONFLATES the two by claiming the *p-adic content* of the period polynomial squeezes
// the *archimedean* House.  We measure both and the count k_b to expose the direction.

use std::f64::consts::PI;

fn gcd(a:u64,b:u64)->u64{ if b==0 {a} else {gcd(b,a%b)} }

// phi(n) for n = 2^mu is n/2; general:
fn euler_phi(n:u64)->u64{ let mut r=n; let mut m=n; let mut p=2; while p*p<=m { if m%p==0 { while m%p==0 {m/=p;} r-=r/p; } p+=1; } if m>1 { r-=r/m; } r }

// The phi(n) ARCHIMEDEAN conjugates of the n-cyclotomic Gauss period for the subgroup mu_n^{(2-power)}.
// theta = sum_{j=0}^{n-1} zeta_n^{a_j}  for the index set being the subgroup; but the architect's
// period polynomial Psi_b has the conjugates = sums over the subgroup translated by the Galois group.
//
// We model the ARCHIMEDEAN object exactly the way the candidate does: theta_b = sum over the
// n-th-root subgroup of zeta_n^{(coefficient)}.  For n = 2^mu the relevant "Gauss period" the
// candidate refers to is the algebraic integer theta = sum_{x in subgroup} zeta where the subgroup
// is the full mu_n (order n) of (Z/N)^* -- but in cyclotomic Q(zeta_N) the conjugates are obtained
// by the Galois action c -> c*t, t in (Z/N)^*.  Concretely we take the canonical near-cyclotomic
// example: the conjugates of (1 + zeta_N + ... ) styles.  Since the architect's S1 is a PURELY
// algebraic statement (House vs geometric-mean-of-large-conjugates), we test it on the actual
// conjugate multiset of ANY algebraic integer that is a sum of roots of unity -- the direction of
// S1 is universal.  We test on:
//   (A) the eta_b prize object on F_p (the REAL target), and
//   (B) archimedean cyclotomic periods (to confirm the universal AM/GM direction).

fn mpow(mut a:u128,mut e:u128,p:u128)->u128{let mut r=1u128;a%=p;while e>0{if e&1==1{r=r*a%p;}a=a*a%p;e>>=1;}r}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2u64;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo - lo%n + 1; if p<lo {p+=n;} loop{ if p>2 && p%n==1 && is_prime(p){return p;} p+=n; }}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g as u128,((p-1)/f) as u128,p as u128)!=1){return g;}g+=1;}}

// ---- Part B: archimedean cyclotomic Gauss periods (independent of p) ----
// The period theta = sum_{x in H} zeta_N^x, H = subgroup of (Z/N)^* of index f. Its conjugates are
// theta_t = sum_{x in H} zeta_N^{t x}, t ranging over coset reps. Here we take N s.t. we get a
// genuine non-cyclotomic algebraic integer. We use N prime-ish or N=2^mu cyclotomic field with H
// the subgroup of squares (a generalized-Paley analogue) to mirror the prize's mu_n.

// Compute, for the cyclotomic field Q(zeta_N), the full conjugate set of theta = sum_{x in H} zeta^x.
// Conjugates indexed by t in (Z/N)^*: value_t = sum_{x in H} exp(2 pi i t x / N).
fn arch_period_conjugates(nn:u64, h:&Vec<u64>)->Vec<f64>{
    let units:Vec<u64>=(1..nn).filter(|&t| gcd(t,nn)==1).collect();
    let mut mags=vec![];
    for &t in &units {
        let mut re=0.0; let mut im=0.0;
        for &x in h {
            let ang = 2.0*PI*((t*x % nn) as f64)/(nn as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        mags.push((re*re+im*im).sqrt());
    }
    mags
}

// ---- Part A: the p-side eta_b conjugates ----
// For fixed p = 1 mod n, mu_n = subgroup of order n. The "conjugates" of the period over the
// quotient are eta_b for b ranging over coset reps of mu_n in F_p^* -- BUT the prize object M(n)
// is the MAX over b, and the algebraic period theta has phi(n) Galois conjugates = the eta_b for
// b in a transversal of the *decomposition* group. We compute eta_b for ALL coset reps b (m of
// them), which over-counts conjugates but contains them; House = max |eta_b| = M(n).
fn eta_conjugates(n:u64,p:u64)->Vec<f64>{
    let g=primitive_root(p); let h=mpow(g as u128,((p-1)/n) as u128,p as u128) as u64;
    let mu:Vec<u64>=(0..n).map(|j|mpow(h as u128,j as u128,p as u128) as u64).collect();
    let m=(p-1)/n;
    let gn=mpow(g as u128,n as u128,p as u128) as u64;
    let mut mags=vec![]; let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0; let mut im=0.0;
        for &x in &mu {
            let t=((b as u128 * x as u128)%p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        mags.push((re*re+im*im).sqrt());
        b=((b as u128 * gn as u128)%p as u128) as u64;
    }
    mags
}

fn analyze(label:&str, mags:&Vec<f64>, n:u64){
    let house = mags.iter().cloned().fold(0.0f64,f64::max);
    let large:Vec<f64> = mags.iter().cloned().filter(|&x| x>1.0+1e-9).collect();
    let kb = large.len();
    // Mahler = product of large moduli
    let log_mahler:f64 = large.iter().map(|x| x.ln()).sum();
    let mahler = log_mahler.exp();
    let geo_mean = if kb>0 { (log_mahler/(kb as f64)).exp() } else { 1.0 };  // = Mahler^{1/k_b}
    let sqrt_n = (n as f64).sqrt();
    println!("  [{}] n={} #conj={} House={:.4} k_b(large)={} Mahler={:.3e} Mahler^(1/k_b)={:.4} sqrt(n)={:.4}",
        label, n, mags.len(), house, kb, mahler, geo_mean, sqrt_n);
    // S1 test: candidate says House <= Mahler^{1/k_b}.  AM/GM says House >= Mahler^{1/k_b}.
    if kb>0 {
        let s1_candidate = house <= geo_mean + 1e-6;
        println!("       S1 candidate (House <= Mahler^(1/k_b))? {}   [House-geoMean = {:.4}]",
            s1_candidate, house-geo_mean);
        // The geometric mean of the large conjugates ALWAYS <= max (House). So candidate FALSE
        // unless all large conj equal.
        println!("       => Mahler^(1/k_b) <= House always (AM/GM): geomean<=house holds = {}", geo_mean <= house+1e-9);
    }
    // S2 sanity: is Mahler <= n^{k_b/2}? and does House ~ sqrt(n)?
    let n_pow = (n as f64).powf((kb as f64)/2.0);
    println!("       S2 partial (Mahler <= n^(k_b/2))? {}   Mahler={:.3e} n^(k_b/2)={:.3e}",
        mahler <= n_pow*(1.0+1e-6), mahler, n_pow);
    println!("       House/sqrt(n) = {:.4}", house/sqrt_n);
}

fn main(){
    println!("=== T10 probe: Mahler / k_b / House direction test ===\n");

    // Part A: the actual prize object eta_b on F_p, p=n^4 shaped (p=1 mod n).
    println!("Part A: prize object eta_b on F_p (p ~ n^4, p = 1 mod n):");
    for &mu in &[3u64,4,5,6,7,8,9,10] {
        let n = 1u64<<mu;
        // target p ~ n^4; cap to keep eta loop O(m*n) tractable: m=(p-1)/n ~ n^3.
        let target = (n as u128).pow(4);
        if target > 3_000_000 { println!("  n={} skipped (p~n^4={} too large for full eta sweep)", n, target); continue; }
        let p = find_prime_cong1(n, target as u64);
        let mags = eta_conjugates(n,p);
        analyze(&format!("eta p={}",p), &mags, n);
    }

    // Part B: archimedean cyclotomic periods (House and k_b for the algebraic theta).
    println!("\nPart B: archimedean cyclotomic Gauss periods theta (subgroup of squares), conjugates over (Z/N)^*:");
    for &nn in &[7u64, 11, 13, 16, 17, 32, 64, 128] {
        // H = subgroup of quadratic residues (index 2) -- the Paley analogue.
        let units:Vec<u64>=(1..nn).filter(|&t| gcd(t,nn)==1).collect();
        // squares:
        let mut hs:Vec<u64>=units.iter().map(|&u| u*u % nn).collect();
        hs.sort(); hs.dedup();
        let mags = arch_period_conjugates(nn,&hs);
        analyze(&format!("theta N={}",nn), &mags, nn);
    }

    println!("\n=== VERDICT TEST ===");
    println!("If 'S1 candidate' is FALSE everywhere with k_b>1 and 'geomean<=house' is TRUE,");
    println!("then T10 Step 1 (House <= Mahler^(1/k_b)) is the WRONG direction (AM/GM), refuting T10.");
}
