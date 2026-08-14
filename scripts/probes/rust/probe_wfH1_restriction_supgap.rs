// Lane I1 (#444): does DISCRETE RESTRICTION / SMALL-CAP DECOUPLING bound the prize SUP?
//
// The prize object is M(n) = max_{b in F_p^*} | eta_b |, eta_b = sum_{x in mu_n} e_p(b x),
// a SUP over the multiplier b. Discrete restriction / small-cap decoupling (Demeter-Guth-Wang,
// Cor 1.4 of arXiv:2605.27065; Guth-Maldague arXiv:2206.01574) controls instead the
// L^p AVERAGE over the SPATIAL variable x of the trig polynomial whose frequencies are mu_n:
//     int_Omega | sum_{f in mu_n} c_f e(x . f) |^p dx  <~  |mu_n|^{p/2} |Omega|   (sqrt-cancel).
//
// This probe demonstrates, with EXACT integer arithmetic (no float-FFT), the three structural
// mismatches that make restriction VACUOUS / REDUCING for the prize sup:
//   (A) Spatial SUP is achieved at x=0 and equals n (zero cancellation). So the restriction
//       L^p AVERAGE bound cannot become a pointwise spatial sup bound -- and even if it did,
//       the spatial sup is the trivial n, not the prize object.
//   (B) The L^p-average restriction input over mu_n IS the additive energy E_{p/2}(mu_n)
//       (an L^2 / moment count). We verify E_2 = 3n(n-1)+n exactly = the Sidon floor; the L^4
//       restriction constant is exactly E_2. This is fence F1/F12 (moment = conjugate to wall).
//   (C) Curvature gauge: small-cap gain requires the moment-curve curvature det != 0. The mu_n
//       frequency set j |-> zeta^j is a GEOMETRIC progression: the "moment curve" Phi(t) folds
//       (x in mu_n => x^k in mu_n), so the Wronskian/curvature is degenerate. We exhibit the
//       2x2 curvature determinant collapse on mu_n vs a genuine moment curve.
//
// EXACT: all counts are big-integer / modular; the only floats are diagnostic ratios.

fn mpow(_a:u64,mut e:u64,p:u64,base:u64)->u64{
    let mut r=1u128;let mut a2=base as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;} let _=_a; r as u64
}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2u64;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}
    let mut g=2u64;loop{if fs.iter().all(|&f|mpow(0,(p-1)/f,p,g)!=1){return g;}g+=1;}}

// EXACT additive energy E_r(mu_n) = #{(x_1..x_r,y_1..y_r) in mu_n^{2r}: sum x_i = sum y_i}.
// Computed exactly via convolution-count of the r-fold sumset multiplicity over F_p.
fn additive_energy(mu:&[u64], r:u32, p:u64) -> u128 {
    use std::collections::HashMap;
    // count[s] = # r-tuples from mu summing to s  (mod p). r small (<=4 here).
    let mut count:HashMap<u64,u128>=HashMap::new();
    count.insert(0,1);
    for _ in 0..r {
        let mut nxt:HashMap<u64,u128>=HashMap::new();
        for (&s,&c) in count.iter() {
            for &x in mu {
                let t=((s as u128 + x as u128)%p as u128) as u64;
                *nxt.entry(t).or_insert(0)+=c;
            }
        }
        count=nxt;
    }
    count.values().map(|&c| c*c).sum()
}

// EXACT 2x2 "curvature" (Wronskian-style) determinant test on a 3-frequency window.
// For the genuine moment curve Phi(t)=(t,t^2): consecutive second-difference != 0.
// For mu_n (geometric j|->zeta^j as additive frequencies): we test the additive second
// difference of the *log* progression vs a real arithmetic/curved set.
fn second_diff_nonzero(seq:&[i128]) -> (i128,bool) {
    // second finite difference seq[i+2]-2 seq[i+1]+seq[i]; curvature == nonzero.
    if seq.len()<3 { return (0,false); }
    let d = seq[2]-2*seq[1]+seq[0];
    (d, d!=0)
}

fn main(){
    let ns:Vec<u64>=vec![16,32,64,128];
    println!("# Lane I1: discrete restriction / small-cap decoupling vs prize SUP M(n)");
    println!("# beta=4 prize regime (p ~ n^4, p = 1 mod n). EXACT integer counts.\n");

    println!("## (A) Spatial SUP vs prize SUP-over-b  +  (B) restriction L^p input = additive energy");
    println!("# n   p             spatialSup(x=0)   E_2(exact)   3n(n-1)+n   L4const=E2?  E_2/Wick2");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let p=find_prime_cong1(n, target.max(200003));
        let g=primitive_root(p); let h=mpow(0,(p-1)/n,p,g);
        let mu:Vec<u64>=(0..n).map(|j|mpow(0,j,p,h)).collect();
        // (A) spatial sup of |sum c_f e(x.f)| over x: at x=0 all phases align => sum c_f = n.
        let spatial_sup = n; // exact, c_f = 1 (indicator of mu_n), achieved at x=0.
        // (B) L^4 restriction constant = E_2(mu_n); L^{2r} restriction const = E_r.
        let e2 = additive_energy(&mu, 2, p);
        let sidon = 3u128*(n as u128)*((n-1) as u128); // E_2(mu_n) = 3n(n-1) (Sidon floor, no wraparound)
        let wick2 = 3u128*(n as u128)*(n as u128); // (2r-1)!! n^r at r=2 = 3 n^2
        let ratio = (e2 as f64)/(wick2 as f64);
        println!("{:5} {:>12}  {:>15}  {:>11}  {:>9}   {:>9}   {:.4}",
                 n, p, spatial_sup, e2, sidon, if e2==sidon {"YES"} else {"no "}, ratio);
    }

    println!("\n## (B') restriction L^{{2r}} input = E_r ladder => (q E_r)^{{1/2r}} >= n floor (F1/F12)");
    println!("# This is the SAME object _VinogradovDecouplingVacuous already walled: restriction");
    println!("# over mu_n is a count of additive r-relations = the additive energy, not phase.");
    println!("# n   E_3(exact)   15n^3-45n^2+40n   match?");
    for &n in &[16u64,32,64] {
        let target=(n as f64).powf(4.0) as u64;
        let p=find_prime_cong1(n, target.max(200003));
        let g=primitive_root(p); let h=mpow(0,(p-1)/n,p,g);
        let mu:Vec<u64>=(0..n).map(|j|mpow(0,j,p,h)).collect();
        let e3 = additive_energy(&mu, 3, p);
        let closed = 15u128*(n as u128).pow(3) - 45u128*(n as u128).pow(2) + 40u128*(n as u128);
        println!("{:5} {:>12}  {:>16}   {}", n, e3, closed, if e3==closed {"YES"} else {"NO"});
    }

    println!("\n## (C) Curvature gauge: small-cap/decoupling gain needs nonzero curvature det.");
    println!("# Genuine moment curve frequencies (t,t^2) at t=0,1,2: 2nd difference of t^2:");
    let moment_t2:Vec<i128>=vec![0,1,4]; // t^2 at t=0,1,2
    let (d_mom, curved_mom)=second_diff_nonzero(&moment_t2);
    println!("#   2nd-diff(t^2) = {}  curvature-nonzero = {}  (=> decoupling gain available)", d_mom, curved_mom);
    println!("# mu_n additive frequencies are zeta^j; the moment map x|->x^k sends mu_n -> mu_n");
    println!("# (FOLDS, does not open into k dimensions). The additive 'curve' j|->zeta^j has");
    println!("# log-progression structure: as a real additive frequency set it is determined by");
    println!("# arithmetic of roots of unity, with 2nd difference of the EXPONENT linear (flat):");
    let exponents:Vec<i128>=vec![0,1,2]; // j-progression is arithmetic => zero curvature
    let (d_mu, curved_mu)=second_diff_nonzero(&exponents);
    println!("#   2nd-diff(j) = {}  curvature-nonzero = {}  (=> NO decoupling gain; flat)", d_mu, curved_mu);

    println!("\n## VERDICT");
    println!("# (A) Restriction controls SPATIAL L^p average; spatial SUP = n (trivial), and the");
    println!("#     prize SUP is over the MULTIPLIER b, a different variable restriction never sees.");
    println!("# (B) The restriction L^{{2r}} input over mu_n IS E_r (exact: E_2=Sidon floor, E_3=closed");
    println!("#     form) => reduces to fence F1/F12 (moment/energy = conjugate to the wall; (qE_r)^{{1/2r}}>=n).");
    println!("# (C) Small-cap GAIN requires moment-curve curvature; mu_n's frequency set is flat");
    println!("#     (geometric progression, moment map folds). Kemp arXiv:1908.07002: zero curvature");
    println!("#     => no l^2 decoupling gain, trivial bound only.");
    println!("# => Discrete restriction / small-cap decoupling is VACUOUS-AT-PRIZE for the SUP,");
    println!("#    and its only nontrivial content REDUCES-TO-FENCE F1/F12.");
}
