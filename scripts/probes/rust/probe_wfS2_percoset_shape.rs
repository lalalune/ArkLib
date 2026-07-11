// wf-S2 (#444): the PER-COSET SHAPE of the char-p spurious energy.
//
// The S2 mission asks the genuinely-new question precisely: when E_r inflates at a STRUCTURED
// prime (spur_r > 0), do the spurious mod-p coincidences EQUIDISTRIBUTE over the m cosets of
// mu_n (flat per-coset distribution => no single |eta_b| accumulates => M bounded), or do they
// PEAK on a few cosets (=> M could spike)?
//
// This is decided by the SHAPE of the m-vector w_b := |eta_b|^2 (b over a transversal, b!=0).
// Identity (char-0): sum_b w_b = q*n - n^2 ~ q*n.  Mean per coset = (q*n - n^2)/m ~ n^2 (since
// m = (q-1)/n, mean ~ n^2). For a PERFECTLY FLAT spectrum each w_b = n^2 exactly and M = n
// (= the principal value), so M/sqrt(n) = sqrt(n): that is the MAXIMALLY SPREAD limit and it is
// already FAR below the worst case n. The prize wants M = O(sqrt(n log)), i.e. M/sqrt(n) =
// O(sqrt(log)) -- so the spectrum must be NEAR-FLAT (PAPR = max/mean = M^2/n^2 = O(log/n) -> 0).
//
// We report SHAPE STATISTICS of the per-coset w_b, comparing a STRUCTURED prime (max v2(p-1),
// where spur inflates at sub-prize beta) to a GENERIC prime at the SAME (n, beta):
//   * PAPR = max w_b / mean w_b   (= M^2/mean; prize wants this = O(log n), grows slowly)
//   * normalized entropy H/log(m)  (1.0 = perfectly flat/equidistributed; 0 = one coset)
//   * effective support participation ratio  PR = (sum w)^2 / (m * sum w^2)  in [1/m, 1]
//     (1.0 = flat; small = concentrated).  PR*m = effective # of equally-weighted cosets.
//   * the 4th-moment concentration: top-1 coset's share of sum w_b^2 (the E_2 carrier).
//   * spur_2 = E_2(p) - (3n^2-3n)  (the energy inflation indicator).
//
// THE DECISIVE READOUT: if at the structured prime spur_2 > 0 BUT PR ~ 1 and entropy ~ 1 and
// PAPR = O(log), the spurious mass is SPREAD/equidistributed over cosets => M bounded (prize-safe
// concentration route). If PR or entropy COLLAPSE while spur_2 > 0, the mass concentrates and the
// route is in danger.
//
// usage: probe_wfS2_percoset_shape [n1 n2 ...]   (default 16 32; also forces Fermat 32@65537)
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

fn percoset_w(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut out=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu { let t=((b as u128*x as u128)%p as u128)as u64; let a=2.0*PI*(t as f64)/p as f64; re+=a.cos(); im+=a.sin(); }
        out.push(re*re+im*im);
        b=((b as u128*g as u128)%p as u128)as u64;
    }
    out
}

fn analyze(tag:&str,n:u64,p:u64){
    let w=percoset_w(n,p);             // |eta_b|^2 over m cosets, b!=0 (includes the principal coset where b in mu_n: w=n^2)
    let m=w.len() as f64; let nn=n as f64; let q=p as f64;
    // separate the principal coset (w=n^2) from the nonprincipal ones for M; keep ALL for the
    // sum identities. The principal coset is the b in mu_n one (exactly one coset rep gives w=n^2).
    let s1:f64=w.iter().sum();          // ~ q*n - ... per Parseval (sum over cosets, each x n inside)
    let s2:f64=w.iter().map(|&x|x*x).sum();
    let s3:f64=w.iter().map(|&x|x*x*x).sum();
    let mean=s1/m;
    // M over nonprincipal cosets (exclude the w ~ n^2 principal one)
    let mut mmax=0.0f64; let mut wmax_all=0.0f64; let mut top1_e2=0.0f64;
    for &x in &w { if x>wmax_all {wmax_all=x;} if (x-nn*nn).abs()>0.5 { if x>mmax {mmax=x;} } }
    for &x in &w { if (x-nn*nn).abs()>0.5 { let e=x*x; if e>top1_e2 {top1_e2=e;} } }
    let mnorm=mmax.sqrt();
    let papr=mmax/mean;                 // peak-to-average of nonprincipal |eta|^2
    // normalized Shannon entropy of the w_b distribution (flat=1)
    let pos:f64=w.iter().filter(|&&x|x>0.0).map(|&x|x/s1).map(|pp| -pp*pp.ln()).sum();
    let hnorm= pos/ m.ln();
    // participation ratio (Kish effective sample size / m): 1=flat
    let pr= s1*s1/(m*s2);
    // 4th-moment concentration: top nonprincipal coset's share of sum w^2 (the E2 carrier)
    let sum_e2_np:f64=w.iter().filter(|&&x|(x-nn*nn).abs()>0.5).map(|&x|x*x).sum();
    let top1_frac= if sum_e2_np>0.0 {top1_e2/sum_e2_np} else {0.0};
    // E_2 (full, incl b=0 principal frequency n^2): E_r = (1/q)[ n^{2r} + n*sum_cos |eta|^{2r} ]
    let e2=( (nn*nn).powi(2) + nn*s2 )/q;
    let e2c0=3.0*nn*nn-3.0*nn;
    let spur2=e2-e2c0;
    let e3=( (nn*nn).powi(3) + nn*s3 )/q; let e3c0=15.0*nn*nn*nn; let spur3=e3-e3c0;
    let beta=q.ln()/nn.ln();
    let cprize=mnorm/(nn*(q/nn).ln()).sqrt();
    println!("[{}] n={} p={} v2={} beta={:.2} m={:.0} mean(w)={:.1} (n^2={:.0})",tag,n,p,v2(p-1),beta,m,mean,nn*nn);
    println!("    spur2={:+.2} (x{:.3})  spur3={:+.3e} (x{:.3})", spur2, e2/e2c0, spur3, e3/e3c0);
    println!("    M={:.3} M/sqrt(n)={:.3} C=M/sqrt(n log)={:.4}  PAPR=M^2/mean={:.3} (=O(log n)? log n={:.2})",
        mnorm, mnorm/nn.sqrt(), cprize, papr, m.ln()/nn.ln()*beta);  // (just a ref scale)
    println!("    ENTROPY H/log m = {:.5} (1=flat/equidistributed)   PR = {:.5} (eff#cosets={:.1}, 1.0=flat)",
        hnorm, pr, pr*m);
    println!("    E2-carrier: top-1 nonprincipal coset = {:.5} of nonprincipal sum w^2 (small=spread)", top1_frac);
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() } else { vec![16,32] };
    println!("# wf-S2 PER-COSET SHAPE: does spurious char-p energy equidistribute over cosets?");
    println!("# STRUCT=max v2(p-1) (spur inflates), GENERIC=min v2, same n. flat shape (PR,H~1) => M bounded.");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut p = target.max(100003); p = p - (p%n) + 1; if p<=2 {p+=n;}
        let mut best_s=(0u64,0u32); let mut best_g=(0u64,99u32); let mut c=0;
        while c<300 { if p%n==1 && isp(p) { let vv=v2(p-1); if vv>best_s.1 {best_s=(p,vv);} if vv<best_g.1 {best_g=(p,vv);} c+=1; } p+=n; }
        analyze("STRUCT",n,best_s.0);
        analyze("GENERIC",n,best_g.0);
        println!();
    }
    // The hard-verified structured/sub-prize Fermat case (dossier: r=2 energy inflated 2.58x).
    println!("# Fermat sub-prize structured case n=32 p=65537 (beta~3.2; spur2>0 expected):");
    analyze("FERMAT", 32, 65537);
    // a few more low-beta structured Fermat-like primes to see the inflated regime
    println!("# sub-prize structured primes (low beta, high v2) where spur2>0:");
    for &(n,p) in &[(16u64,40961u64),(16,12289),(32,40961),(8,12289)] {
        if p%n==1 && isp(p) { analyze("LOWBETA", n, p); }
    }
}
