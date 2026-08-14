// Is the Gauss-period field b -> log|S_b| LOG-CORRELATED (FHK applies) or WHITE-NOISE (refuted)?
// Measure Cov(log|S_b|, log|S_{b'}|) vs -log|b-b'| (archimedean) and vs 2-adic dist. mu_n, n=2^mu.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn main(){
    let n=64u64; let p=fp(n,(n as f64).powf(4.0) as u64);
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // compute log|S_b| for b=1..B (a contiguous block of frequencies)
    let bmax=4000usize;
    let mut lg=vec![0.0f64;bmax+1];
    for b in 1..=bmax {
        let mut re=0.0;let mut im=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;let a=2.0*PI*(t as f64)/p as f64;re+=a.cos();im+=a.sin();}
        lg[b]=0.5*(re*re+im*im).max(1e-12).ln();
    }
    let xs:Vec<f64>=(1..=bmax).map(|b|lg[b]).collect();
    let mean=xs.iter().sum::<f64>()/xs.len() as f64;
    let var=xs.iter().map(|v|(v-mean).powi(2)).sum::<f64>()/xs.len() as f64;
    println!("n={} p={} mean(log|S|)={:.3} var={:.3} (white-noise: cov(d)~0 for d>=1; log-corr: cov(d)~-c*ln d)",n,p,mean,var);
    // covariance at lag d (archimedean |b-b'|=d)
    for d in [1usize,2,4,8,16,32,64,128,256,512] {
        let mut c=0.0;let mut cnt=0;
        for b in 1..=(bmax-d){ c+=(lg[b]-mean)*(lg[b+d]-mean); cnt+=1; }
        c/=cnt as f64;
        println!("  lag d={:4}  cov={:+.4}  cov/var={:+.4}   (-ln d={:+.3})", d, c, c/var, -(d as f64).ln());
    }
}
