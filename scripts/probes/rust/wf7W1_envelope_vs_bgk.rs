// wf-W1 (#444): DECISIVE — is the aggregate envelope a SMOOTHED BGK (inherits BGK fragility),
//   or genuinely independent of the per-coefficient BGK constant c=M/sqrt(n ln q)?
//
// PRIOR FINDING (wf7W1_envelope_mechanism): envelope FAILS at Fermat65537 n=64 where c=1.638>sqrt2,
//   and at Fermat65537 n=128/256 where beta=ln q/ln n ~ 2.0 (NOT prize geometry, p not >> n^3).
//   => two failure modes: (A) c>floor (genuine BGK explosion), (B) beta-too-small artifact.
//
// THIS PROBE isolates the question at PRIZE GEOMETRY (beta>=4, p>>n^3, proper mu_n, exclude X^{n/2}=+-1):
//   Scan MANY primes per (n,beta) including the most 2-adic ones reachable, and report:
//     - c = M/sqrt(n ln q)         (BGK constant)
//     - R = Phi^nz(y*)/q           (envelope ratio; fail iff >1)
//     - the EMPIRICAL law R ~ q^{c*sqrt2 - 2} * Nmax/2  (saddle theory):
//       log_q(R) should track (c sqrt2 - 2) + log_q(Nmax/2).  If so, envelope <=> c sqrt2 < 2 (i.e c<sqrt2=1.414)
//       PLUS log_q(Nmax) slack -- i.e. envelope holds AT THE FLOOR c=sqrt2 only with margin from beta.
//   KEY TEST: find ANY prize-geometry prime (beta>=4) where c approaches or exceeds sqrt2, and check
//   whether R approaches/exceeds 1 there. If c stays well below sqrt2 at beta>=4 for ALL reachable primes
//   incl most-2-adic, the envelope's safety is exactly the (unproven) BGK floor c<sqrt2 -- NOT a free lunch.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// metrics for one (n,p)
fn metrics(n:u64,p:u64)->(f64,f64,f64,u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let pf=p as f64; let nf=n as f64; let lnq=pf.ln(); let ystar=(2.0*lnq/nf).sqrt();
    let mut s=0.0; let mut mmax=0.0f64; let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}
        let e=re.abs(); s += nf*(e*ystar).cosh(); if e>mmax{mmax=e;} b=((b as u128*gn as u128)%p as u128)as u64;
    }
    let ratio=s/(pf*pf); let c=mmax/(nf*lnq).sqrt();
    // log_q(R)
    let logqR = ratio.ln()/lnq;
    (c,ratio,logqR,m)
}

// scan a band of primes p = n*k+1 prime with k>=kmin (beta>=target), prefer most-2-adic, report worst c and worst R.
fn scan(n:u64, kmin:u64, ntest:usize, label:&str){
    let nf=n as f64;
    let mut k=kmin; let mut tested=0;
    let mut worst_c=0.0f64; let mut wc_p=0u64; let mut wc_R=0.0; let mut wc_logqR=0.0;
    let mut worst_R=0.0f64; let mut wr_p=0u64; let mut wr_c=0.0;
    // also track the MOST 2-adic prime found (max v2(p-1)) in band
    let mut best_v2=0u32; let mut v2p=0u64; let mut v2c=0.0; let mut v2R=0.0;
    while tested<ntest {
        let p=n*k+1;
        if isp(p) {
            let (c,r,lqr,_m)=metrics(n,p);
            if c>worst_c {worst_c=c; wc_p=p; wc_R=r; wc_logqR=lqr;}
            if r>worst_R {worst_R=r; wr_p=p; wr_c=c;}
            let v2=(p-1).trailing_zeros();
            if v2>best_v2 {best_v2=v2; v2p=p; v2c=c; v2R=r;}
            tested+=1;
        }
        k+=1;
    }
    let lnq_w=(wc_p as f64).ln(); let beta_w=lnq_w/nf.ln();
    println!("{} n={} (beta~{:.1}, {} primes scanned):", label, n, beta_w, ntest);
    println!("   WORST c: c={:.4} @p={} (beta={:.2}) -> R={:.4} {} log_q R={:.3} [c sqrt2-2={:.3}]",
        worst_c, wc_p, beta_w, wc_R, if wc_R<=1.0{"OK"}else{"FAIL"}, wc_logqR, worst_c*std::f64::consts::SQRT_2-2.0);
    println!("   WORST R: R={:.4} @p={} c={:.4} {}", worst_R, wr_p, wr_c, if worst_R<=1.0{"OK"}else{"FAIL"});
    println!("   most-2adic: v2(p-1)={} @p={} c={:.4} R={:.4} {}", best_v2, v2p, v2c, v2R, if v2R<=1.0{"OK"}else{"FAIL"});
}

fn main(){
    // n=16: beta=4 means k>=n^3=4096. scan many.
    scan(16, 16u64.pow(3), 4000, "[beta>=4]");
    scan(16, 16u64.pow(4), 1000, "[beta>=5]");
    // n=32: beta=4 -> k>=32^3=32768
    scan(32, 32u64.pow(3), 1500, "[beta>=4]");
    // n=64: beta=4 -> k>=64^3=262144
    scan(64, 64u64.pow(3), 400, "[beta>=4]");
    // n=128: beta=4 -> k>=128^3=2.1M
    scan(128, 128u64.pow(3), 120, "[beta>=4]");
}
