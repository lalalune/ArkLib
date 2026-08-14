// wf-G5 part 3: FFT the period spectrum to push M(H) to large n at prize beta, confirming
// (a) M/prize stays BOUNDED (not a growing disproof witness), (b) realized exponent logM/logn,
// (c) the energy stays ~3n^2 (minimal). We build the indicator of H on Z_p and FFT? p too big.
// Instead use the Gauss-PERIOD reformulation: M(H)=max_{b} |sum_{x in H} e_p(bx)|. As b ranges over
// the m=(p-1)/n cosets of H, the value depends only on the coset; there are m distinct period values.
// The eta_k = sum_{x in H} e_p(g^k x) for k=0..m-1 are the Gaussian periods; the m-vector
// (eta_k) is computable as: build histogram of H over residues, then for each coset multiply...
// Simplest exact O(p): direct, but p up to 4e9 too big for O(p*n). Use the multiset-of-(b*x) trick:
// eta over all b=1..p-1 takes only m distinct complex values (one per coset). Compute by: for each
// of the n elements x in H and each coset rep, ... still O(p). 
// We FFT: place H as a 0/1 vector of length p, real FFT gives ALL p Fourier coeffs = the periods.
// p~4e9 infeasible in RAM. So cap at p<=~1.5e8 (n<=128 at beta~3.8) using FFT, and n=256 beta~3.3.
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
// exact M via Gaussian periods: eta_k = sum_{j=0}^{n-1} e_p(g^k h^j). There are m=(p-1)/n cosets.
// O(m*n) = O((p-1)/n * n) = O(p). For p up to ~2e8 fine.
fn main(){
    println!("n      p           beta  M(H)     logM/logn  prize    M/prize");
    // pick largest beta we can afford with O(p)<~2e8 ops
    let cases: Vec<(u64,u64)> = vec![
        (16, fp(16, 65537)),
        (32, fp(32, 1_048_609)),
        (64, fp(64, 16_777_259)),     // beta 4
        (128, fp(128, 30_000_000)),   // beta ~3.55, p~3e7
        (256, fp(256, 60_000_000)),   // beta ~3.25, p~6e7
        (512, fp(512, 90_000_000)),   // beta ~2.94
        (1024, fp(1024,130_000_000)), // beta ~2.69
    ];
    for (n,p) in cases {
        let g=proot(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let m=(p-1)/n;
        let pf=p as f64; let nf=n as f64;
        let mut mmax=0.0f64;
        // for each coset k=0..m-1, rep = g^k, period = sum_x e_p(g^k * x mod p)
        let mut gk=1u64;
        for _k in 0..m {
            let mut re=0.0; let mut im=0.0;
            for &x in &mu { let t=((gk as u128 * x as u128)%pf as u128)as u64; let ang=2.0*PI*(t as f64)/pf; re+=ang.cos(); im+=ang.sin(); }
            let mag=(re*re+im*im).sqrt(); if mag>mmax{mmax=mag;}
            gk=((gk as u128 * g as u128)%p as u128)as u64;
        }
        let prize=(nf*((pf/nf).ln())).sqrt();
        println!("{:5} {:11} {:.2}  {:8.3}  {:.4}     {:7.3}  {:.4}", n,p,(pf.ln()/nf.ln()),mmax,mmax.ln()/nf.ln(),prize,mmax/prize);
    }
}
