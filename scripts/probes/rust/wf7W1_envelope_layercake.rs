// wf-W1 (#444): aggregate envelope = sub-Gaussianity of eta_B (B uniform on F_q\{0}).
//
// KEY identity: Var(eta_B) = (1/(q-1)) sum_{b!=0} eta_b^2 = (qn - n^2)/(q-1) ~ n  (Parseval).
// The MATCHED Gaussian N(0,n) has E[cosh(G y*)] = exp(n y*^2/2) = q  EXACTLY.
// So envelope R = (1/q) E_B[cosh(eta_B y*)] <= exp(ny*^2/2)=q  <=>  E_B[cosh] <= q*(matched-Gaussian E[cosh]) ...
// no: R = (1/q^2) sum_{b!=0} cosh = (q-1)/q^2 * E_B[cosh(eta_B y*)]. Envelope R<=1 <=> E_B[cosh] <= q^2/(q-1) ~ q.
// Matched Gaussian: E_G[cosh(G y*)] = exp(n y*^2/2) = q. So envelope <=> E_B[cosh(eta_B y*)] <= q ~ E_G[cosh].
// I.e. ENVELOPE <=> eta_B has cosh-MGF at y* NO LARGER than its matched Gaussian. (sub-Gaussianity, exactly.)
//
// This probe: for proper mu_n at prize geometry, report
//   (1) E_B[cosh(eta_B y*)] / exp(n y*^2/2)  = R*q/(q-1) ~ R  (the sub-Gaussian ratio)
//   (2) the LAYER decomposition: split the cosh-sum by |eta_b| bands and report what FRACTION of the
//       total comes from the top band (|eta|>0.9M), mid (0.5-0.9M), bulk (<0.5M). Tells if peak- or bulk-dominated.
//   (3) compare eta_B's empirical 2r-moments to Gaussian (2r-1)!! n^r at r=2,4,8 -- the kurtosis/tail check.
//   This separates "envelope holds because spectrum is sub-Gaussian (genuine)" from "holds by slack".

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

fn run(n:u64,p:u64,label:&str){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64; let mut mmax=0.0f64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} let e=re.abs(); eta.push(e); if e>mmax{mmax=e;} b=((b as u128*gn as u128)%p as u128)as u64; }
    let pf=p as f64; let nf=n as f64; let lnq=pf.ln(); let beta=lnq/nf.ln(); let ystar=(2.0*lnq/nf).sqrt();
    // variance
    let mut s2=0.0; for &e in &eta { s2+=nf*e*e; } let varB = s2/(pf-1.0);
    // cosh sum by bands
    let mut top=0.0; let mut mid=0.0; let mut bulk=0.0;
    for &e in &eta { let c=nf*(e*ystar).cosh(); if e>0.9*mmax{top+=c;} else if e>0.5*mmax{mid+=c;} else {bulk+=c;} }
    let total=top+mid+bulk;
    let eB_cosh = total/(pf-1.0);                 // E_B[cosh(eta_B y*)]
    let gauss = (nf*ystar*ystar/2.0).exp();        // exp(n y*^2/2) = matched-Gaussian E[cosh]
    let subg = eB_cosh/gauss;                      // sub-Gaussian ratio (<=1 desired)
    // 2r-moments vs Gaussian (2r-1)!! n^r
    let m2 = { let mut s=0.0; for &e in &eta { s+=nf*e.powi(2);} s/(pf-1.0) };
    let m4 = { let mut s=0.0; for &e in &eta { s+=nf*e.powi(4);} s/(pf-1.0) };
    let m8 = { let mut s=0.0; for &e in &eta { s+=nf*e.powi(8);} s/(pf-1.0) };
    let g2=nf; let g4=3.0*nf*nf; let g8=105.0*nf.powi(4);
    println!("{} n={} p={} beta={:.2} | Var(eta_B)={:.2} (n={}) | sub-Gauss ratio E_B[cosh]/exp(ny*^2/2) = {:.4} {}",
        label,n,p,beta,varB,n,subg, if subg<=1.0{"OK"}else{"FAIL"});
    println!("    cosh-mass: top(>0.9M)={:.1}% mid={:.1}% bulk(<0.5M)={:.1}%  (M={:.2}=c*{:.3}sqrt(n lnq))",
        100.0*top/total,100.0*mid/total,100.0*bulk/total, mmax, mmax/(nf*lnq).sqrt());
    println!("    moment/Gaussian:  m2/n={:.3}  m4/(3n^2)={:.3}  m8/(105 n^4)={:.3}  (=1 iff Gaussian; <1 sub-Gauss tail)",
        m2/g2, m4/g4, m8/g8);
}
fn main(){
    run(16, fp(16,16u64.pow(4)),"[b~4]");        // beta~4
    run(32, fp(32,32u64.pow(4)),"[b~4]");
    run(16, 65537, "[Fermat,b4]");                // most-2-adic at n=16 beta~4
    run(64, fp(64,64u64.pow(3)),"[b~3]");
}
