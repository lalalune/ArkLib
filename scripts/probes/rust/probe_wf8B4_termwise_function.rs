// W1-MGF lane B4 (CORRECT normalization): sum over ALL b != 0 (eta_b not coset-constant).
// Phi_nz(y) = (1/q) sum_{b!=0} cosh(eta_b y) ; compare to exp(n y^2/2).
// a_r := (1/q) sum_{b!=0} eta_b^{2r} = (q E_r - n^{2r})/q ; W_r = (2r-1)!! n^r.
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(k:i64)->f64{let mut r=1.0f64; let mut i=k; while i>0 { r*=i as f64; i-=2;} r}
fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // eta_b for ALL b in 1..p  (real; mu_n=-mu_n so Im=0)
    let mut eta=Vec::with_capacity((p-1) as usize);
    for b in 1..p { let mut re=0.0; for &x in &mu { let t=((b as u128*x as u128)%p as u128) as u64; re+=(2.0*PI*(t as f64)/p as f64).cos(); } eta.push(re); }
    let q=p as f64; let nn=n as f64;
    println!("=== n={} p={} (beta={:.2}) #b={} ===", n, p, q.ln()/nn.ln(), eta.len());
    println!(" r       a_r              W_r          a_r/W_r");
    let mut termwise_ok = true;
    for r in 1..=rmax {
        let mut s = 0.0f64; for &e in &eta { s += e.powi(2*r as i32); }
        let a_r = s / q;
        let w_r = dfact(2*r as i64 - 1) * nn.powi(r as i32);
        let ratio = a_r/w_r; if ratio>1.0 {termwise_ok=false;}
        println!(" {:2} {:>16.4} {:>16.4} {:>9.4} {}", r, a_r, w_r, ratio, if ratio<=1.0 {"OK"} else {"FAIL"});
    }
    println!(" termwise a_r<=W_r all r<={}: {}", rmax, termwise_ok);
    let ystar=(2.0*q.ln()/nn).sqrt();
    let mut worst=0.0f64; let mut atw=0.0;
    let steps=4000; let ymax=ystar*1.4;
    for i in 1..=steps { let y=ymax*(i as f64)/(steps as f64); let bound=(nn*y*y/2.0).exp();
        let mut snz=0.0; for &e in &eta { snz+=(e*y).cosh(); } snz/=q;
        let ratio=snz/bound; if ratio>worst{worst=ratio; atw=y;} }
    println!(" max_y Phi_nz/exp(ny^2/2) = {:.6} at y={:.3} (y*={:.3}) {}", worst, atw, ystar, if worst<=1.0{"[W1 HOLDS]"}else{"[W1 FAILS]"});
    println!();
}
fn main(){
    run(8, fp(8,4000), 8);
    run(8, 4099, 8);              // beta~4
    run(16, 65537, 8);           // Fermat, beta=4.00
    run(16, fp(16,60000), 8);
    run(32, fp(32,1000000), 6);
    run(32, fp(32,1048576), 6);
    run(64, fp(64,16000000), 5);
    run(64, fp(64,16777216), 5); // beta=4 exactly
}
