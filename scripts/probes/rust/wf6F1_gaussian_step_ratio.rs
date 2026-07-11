// wf-F1: the LOCAL load-bearing object for a Lean proof.  Define the moment STEP RATIO
//   rho(r) := M_{2(r+1)} / (n * M_{2r})         (M_2r = (1/m) sum_cosets eta^{2r})
// A Gaussian N(0,n) has M_{2r}=(2r-1)!! n^r  =>  rho(r) = (2r+1) EXACTLY.
// CLAIM (the sub-Gaussian step law):  rho(r) <= 2r+1  for all r.
//   Telescoping from M_2:  M_{2r} = M_2 * prod_{j=1}^{r-1} (n*rho(j))
//                                 <= n * prod_{j=1}^{r-1} (n*(2j+1))  [using M_2<=n]
//                                 = (2r-1)!! n^r   (since prod_{j=1}^{r-1}(2j+1)=(2r-1)!!/1).
//   So  rho(r)<=2r+1  for all r  =>  M_{2r}<=(2r-1)!! n^r  (THE TARGET, K=1).
// This is a PER-STEP inequality (Cauchy-Schwarz-like): much more tractable than the global ladder.
// MEASURE rho(r)/(2r+1) <= 1 ?  and the n,beta dependence.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let _=&mut a;let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

fn run(n:u64,p:u64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let mf=m as f64; let lnq=(p as f64).ln(); let nf=n as f64;
    let rmax=((1.8*lnq) as usize).max(8);
    let mut mom=vec![0.0;rmax+2];
    for r in 1..=rmax+1 { let mut s=0.0; for &e in &eta { s+=e.powi(2*r as i32); } mom[r]=s/mf; }
    let beta=lnq/nf.ln();
    let mut maxratio=0.0; let mut argr=0; let mut all_ok=true;
    for r in 1..=rmax {
        let rho = mom[r+1]/(nf*mom[r]);
        let ratio = rho/((2*r+1) as f64);     // <=1 is the claim
        if ratio>maxratio {maxratio=ratio; argr=r;}
        if ratio>1.0+1e-9 {all_ok=false;}
    }
    // also the GAUSSIAN-EXACT comparison at small r
    let rho1=mom[2]/(nf*mom[1]); // should be ~3
    println!("n={:4} beta={:.2} lnq={:.1} rmax={} | rho(1)/3={:.4} | max rho(r)/(2r+1)={:.4}@r{} | step-law-holds={} | M_2/n={:.4}",
        n,beta,lnq,rmax, rho1/3.0, maxratio, argr, all_ok, mom[1]/nf);
}
fn main(){
    // prize regime beta~4-5.5
    for &(n,lo) in &[(16u64,60000u64),(32,1_000_000),(64,16_000_000),(128,260_000_000)] {
        run(n, fp(n,lo));
    }
    // beta ~ 5.3 (prize beta) to be faithful
    run(16, fp(16, 2_000_000));
    run(32, fp(32, 50_000_000));
    run(64, fp(64, 2_000_000_000));
    // stress beta~2.5,3
    run(64, fp(64, 26000));     // beta~2.5
    run(64, fp(64, 260000));    // beta~3
    run(128, fp(128, 130000));  // beta~2.5
}
