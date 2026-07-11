// wf-W1 (#444): WHAT controls the aggregate Gaussian MGF envelope, and is it robust at the prize?
//
// Object: Phi_p^nz(y*) = (1/q) sum_{b!=0} cosh(eta_b y*),  y* = sqrt(2 ln q / n).
// Envelope claim:  Phi_p^nz(y*) <= exp(n y*^2/2) = q.   I.e.  S := sum_{b!=0} cosh(eta_b y*) <= q^2.
//
// DECISIVE DECOMPOSITION (saddle analysis):
//   At the saddle, cosh(eta y*) ~ (1/2) exp(|eta| y*).  Write per-b "saddle excess"
//      xi_b := |eta_b| y* - n y*^2/2 = |eta_b| sqrt(2 ln q/n) - ln q
//   so each term contributes exp(xi_b)/2 toward S/q (relative to the q budget).
//   S/q^2 = (1/q) sum_{b!=0} cosh(eta_b y*)/q ~ (1/2q) sum_b exp(xi_b).
//   The MAX over b of xi_b is governed by M = max|eta_b| (the BGK object):
//      xi_max = M sqrt(2 ln q/n) - ln q = ln q (M/sqrt(n/2 ln q ... )) -- the BGK gate.
//   If M = c sqrt(n ln q): xi_max = c sqrt(2) ln q - ln q = (c sqrt2 - 1) ln q.
//   So a SINGLE b at M = c sqrt(n ln q) contributes exp((c sqrt2 -1) ln q)/2 = q^{c sqrt2 -1}/2 to S.
//   For the envelope S <= q^2 to hold via that worst term alone we need (counting multiplicity Nmax):
//      Nmax * q^{c sqrt2 - 1} <~ q^2  i.e.  c sqrt2 - 1 + log_q(Nmax) <= 2  i.e. c <= 3/sqrt2 = 2.12 (Nmax=O(1)).
//   THE PRIZE NEEDS c <= sqrt2 (the floor). The envelope's c-budget is ~2.12 (Nmax=O(1)) -- LOOSER
//   than the prize floor. So the envelope is implied by a WEAKER BGK bound c<=2.12, not the sqrt2 floor.
//   => the envelope is NOT a free lunch over BGK; it is a SMOOTHED BGK with constant ~3/sqrt2.
//
// THIS PROBE reports, exactly, at prize geometry (proper mu_n, multiple primes incl Fermat-structured):
//   (1) the saddle ratio R = S/q^2 = Phi^nz/q  (envelope holds iff R<=1),
//   (2) M/sqrt(n ln q) = c  (the BGK constant),
//   (3) the implied per-term worst excess exp(xi_max)/q^2 and how many b are within e^{-1} of it (Nmax),
//   (4) the CRITICAL c that would break the envelope: c_crit s.t. the worst-cluster term = q^2,
//       and the HEADROOM = c_crit - c_actual.  If headroom is generic (grows weakly) vs prize-tight.
//   (5) Fermat-structured prime comparison: does the envelope ratio DEGRADE at structured p like raw E_r does?

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

fn run(n:u64,p:u64,label:&str){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    // collect |eta_b| over all b!=0 (b ranges over reps of cosets; each rep r covers n shifts with same |eta|)
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re.abs()); b=((b as u128*gn as u128)%p as u128)as u64; }
    let pf=p as f64; let nf=n as f64;
    let lnq=pf.ln(); let beta=lnq/nf.ln();
    let ystar=(2.0*lnq/nf).sqrt();
    // (1) aggregate saddle: S = sum_{b!=0} cosh(eta_b y*) = n * sum over reps cosh(|eta| y*)
    let mut s=0.0; let mut mmax=0.0f64;
    for &e in &eta { s += nf*(e*ystar).cosh(); if e>mmax{mmax=e;} }
    let ratio = s/(pf*pf);  // R = S/q^2 = Phi^nz/q  (envelope holds iff <=1)
    // (2) BGK constant
    let c = mmax/(nf*lnq).sqrt();
    // (3) worst per-term excess xi_max and cluster count Nmax (reps within e^-1 of mmax in cosh-weight)
    let xi_max = mmax*ystar - nf*ystar*ystar/2.0;     // = |M| y* - ln q
    let worst_term_over_q2 = (mmax*ystar).cosh()/(pf*pf)*nf;  // single worst coset (n shifts) contribution to R
    // count reps whose cosh term is within factor e of the max
    let mut nmax=0u64; let thr = (mmax*ystar).cosh()/std::f64::consts::E;
    for &e in &eta { if (e*ystar).cosh()>=thr {nmax+=1;} }
    // (4) critical c: smallest c s.t. single worst coset term = q^2.  n*(1/2)exp(c sqrt(n lnq) y*)=q^2
    //     c sqrt(n lnq)*y* = 2 lnq + ln(2 q / n)  => c = (2 lnq + ln(2q/n))/(sqrt(n lnq)*y*)
    //     sqrt(n lnq)*y* = sqrt(n lnq)*sqrt(2 lnq/n)=lnq sqrt2.  => c_crit=(2 lnq+ln(2q/n))/(lnq sqrt2)
    let c_crit = (2.0*lnq + (2.0*pf/nf).ln())/(lnq*std::f64::consts::SQRT_2);
    let headroom = c_crit - c;
    let floor = std::f64::consts::SQRT_2;  // prize floor c<=sqrt2
    println!("{:>10} n={:4} p={} beta={:.2} lnq={:.2} y*={:.3}", label,n,p,beta,lnq,ystar);
    println!("           R=Phi^nz/q={:.5} {} | c=M/sqrt(n lnq)={:.4} | Nmax_cluster={} | worstcoset/q^2={:.4}",
        ratio, if ratio<=1.0{"OK"}else{"<<< ENVELOPE FAILS"}, c, nmax, worst_term_over_q2);
    println!("           c_crit(break)={:.4} headroom(c_crit-c)={:.4} | prize floor sqrt2={:.4} | c-floor={:+.4} xi_max={:.3}",
        c_crit, headroom, floor, c-floor, xi_max);
}

fn main(){
    println!("=== generic prize-geometry primes p ~ n^4..5 ===");
    run(16, fp(16,500000),"gen");
    run(32, fp(32,10000000),"gen");
    run(64, fp(64,200000000),"gen");
    // (5) Fermat-structured primes: p = 2^k+1 family or p with p-1 highly 2-divisible. Compare envelope.
    println!("=== Fermat-structured / highly-2-adic primes (raw E_r explodes here) ===");
    // p=65537=2^16+1 (Fermat), n=64,128,256 all divide p-1=2^16.
    run(64, 65537,"Fermat65537");
    run(128, 65537,"Fermat65537");
    run(256, 65537,"Fermat65537");
    // p=2^25*... pick a prime with large v2(p-1) but big: p = k*2^20+1 prime, n=2^16
    let p2 = fp(1<<20, 1<<28);  // p ≡1 mod 2^20, so v2(p-1)>=20
    run(1<<10, p2,"hi2adic");
    run(1<<14, p2,"hi2adic");
    // larger Fermat-like: p=2^16+1 too small for n=512. use p with v2 huge:
    // p = 13*2^28+1? check. Build prime =1 mod 2^25 near 2^33
    let p3 = fp(1<<25, 1u64<<33);
    run(1<<10, p3,"hi2adic2");
    run(1<<14, p3,"hi2adic2");
    run(1<<16, p3,"hi2adic2");
}
