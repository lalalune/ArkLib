// wf-W3 (hypercontractivity): test the STEP-RATIO ANTITONICITY ladder.
// R(r) := M_{2(r+1)} / ((2r+1)*n*M_{2r})  (normalized Gaussian step ratio; R=1 for N(0,n)).
// Claim of W3 reduction:  R(1) <= 1  AND  R(r+1) <= R(r) for r>=1  =>  R(r)<=1 all r => step-law => Wick floor.
// This isolates ONE hypercontractive object (the cumulant ratio is decreasing).
// MEASURE: is R antitone at depth r~ln q across prize primes? report R(1..rmax), antitone flag.
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
    let rmax=((1.6*lnq) as usize).max(8);
    let mut mom=vec![0.0;rmax+3];
    for r in 1..=rmax+2 { let mut s=0.0; for &e in &eta { s+=e.powi(2*r as i32); } mom[r]=s/mf; }
    let beta=lnq/nf.ln();
    // R(r) for r=1..rmax
    let mut rr=vec![0.0;rmax+2];
    for r in 1..=rmax+1 { rr[r]= mom[r+1]/(((2*r+1) as f64)*nf*mom[r]); }
    let mut antitone=true; let mut worst_inc=0.0f64; let mut worst_r=0;
    for r in 1..=rmax { let inc = rr[r+1]-rr[r]; if inc>1e-12 {antitone=false;} if inc>worst_inc {worst_inc=inc; worst_r=r;} }
    let r1le1 = rr[1]<=1.0+1e-12;
    print!("n={:4} beta={:.2} lnq={:.1} rmax={} | R(1)={:.4}<=1:{} antitone:{} worstInc={:.2e}@r{} | R: ",
        n,beta,lnq,rmax, rr[1], r1le1, antitone, worst_inc, worst_r);
    for r in [1usize,2,3,5,8,12,16,20,24].iter().filter(|&&r|r<=rmax) { print!("R{}={:.3} ",r,rr[*r]); }
    println!();
}
fn main(){
    // prize regime beta~4-5.3
    run(16, fp(16,60000)); run(16, fp(16,2_000_000));
    run(32, fp(32,1_000_000)); run(32, fp(32,50_000_000));
    run(64, fp(64,16_000_000)); run(64, fp(64,2_000_000_000));
    run(128, fp(128,260_000_000));
    run(256, fp(256,4_000_000_000));
}
