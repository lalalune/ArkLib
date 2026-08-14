// wf-F1 followup: IS the Gaussian-normalized moment ladder antitone, and does the r=1 (Parseval)
// value cap it?  This is the load-bearing claim for the Lean brick:
//   define   R(r) := M_{2r} / [(2r-1)!! n^r]   (M_{2r} = (1/m) sum_cosets eta^{2r}).
//   CLAIM A: R(r) <= R(1) = M_2/n = 1 - n/q   for all r >= 1   (Gaussian-normalized ratio antitone).
//   If TRUE => sub-Gaussian moment bound M_{2r} <= (1-n/q)^? ... actually R(r)<=R(1)<=1 gives
//             M_{2r} <= (2r-1)!! n^r * R(1) <= (2r-1)!! n^r  (THE TARGET, with K=1).
//
// Also test the WEAKER but maybe-provable monotone form on R^{1/r} (K_eff). And whether
// R(r) is LOG-CONVEX-violating (i.e. the normalized ladder strictly decreasing, not just <=R(1)).
//
// And the KEY mechanism: decompose M_{2r}.  Hypercontractivity (Boolean cube) would give the
// (2r-1)!! factor structurally.  Here we just verify the numeric law to prize-relevant depth.

use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let _=&mut a;let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let mf=m as f64;
    let lnq=(p as f64).ln();
    // R(r) = M_2r / [(2r-1)!! n^r]
    let mut prevR = f64::INFINITY;
    let mut antitone_R = true;        // R(r+1) <= R(r) ?
    let mut capped_byR1 = true;       // R(r) <= R(1) ?
    let mut r1 = 0.0;
    let mut maxR = 0.0;
    let depth = (1.5*lnq) as usize;
    let rmax = rmax.max(depth);
    for r in 1..=rmax {
        let mut s=0.0; for &e in &eta { s+=e.powi(2*r as i32); }
        let m2r = s/mf;
        let c0 = dfact(r)*(n as f64).powi(r as i32);
        let rr = m2r/c0;
        if r==1 { r1=rr; }
        if rr>maxR { maxR=rr; }
        if rr > prevR + 1e-12 { antitone_R=false; }
        if rr > r1 + 1e-12 { capped_byR1=false; }
        prevR = rr;
    }
    let beta=lnq/(n as f64).ln();
    println!("n={:4} p={} beta={:.2} lnq={:.1} depth={} | R(1)={:.6} maxR={:.6} | R-antitone={} capped-by-R(1)={} | M_2/n=1-n/q={:.6}",
        n,p,beta,lnq,rmax,r1,maxR,antitone_R,capped_byR1, 1.0-(n as f64)/(p as f64));
}

fn main(){
    run(8,   fp(8,4000), 8);
    run(16,  fp(16,60000), 16);
    run(32,  fp(32,1_000_000), 22);
    run(64,  fp(64,16_000_000), 28);
    run(128, fp(128,260_000_000), 32);
    // also a SMALL beta (close prime) to stress: does antitonicity survive beta~2?
    run(64,  fp(64,4096), 28);   // beta ~ 2
    run(128, fp(128,16384), 32); // beta ~ 2
}
