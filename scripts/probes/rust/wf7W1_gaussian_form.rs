// wf-W1 (#444): the CORRECTED sharp sub-lemma -- the GAUSSIAN form (NOT the K=1/Bessel form).
//
// FINDING (wf7W1_charp_le_char0_mgf): the strong K=1 form Phi_p^nz <= I0(2y)^{n/2} FAILS at n=128
//   (ratio 1.091 at y=0.4 < saddle). So char-p A_r > (2r-1)!!n^r at some intermediate r for n>=128.
//   => K=1 char-p is FALSE; the spurious mod-p excess is real at intermediate r.
//
// BUT the GAUSSIAN form has slack:  Phi_0 = I0(2y)^{n/2} <= exp(n y^2/2) loses a factor, and the
//   char-p excess at intermediate r fits inside that slack. So the SHARP sub-lemma the MGF route
//   actually needs (and that the consumer period_le_of_mgfBound consumes) is the GAUSSIAN form:
//
//   SUB-LEMMA S-W1':  Phi_p^nz(y) := (1/q) sum_{b!=0} cosh(eta_b y)  <=  exp(n y^2 / 2)   for all y>=0.
//
// This is WEAKER than K=1 (it allows K_eff up to the Bessel->Gaussian slack ratio) but STRONGER than
// needed only at the saddle. Equivalent per-r form: A_r <= K^r (2r-1)!! n^r with K = the worst-r
// (exp/Bessel)-slack -- an ABSOLUTE constant (n-independent envelope exp(y^2)/I0(2y) <= e^{...}).
//
// This probe: FINE sweep of Phi_p^nz/exp(ny^2/2) to find its true global max, n=16..256, beta~4-5.
// If the max stays < 1 uniformly, S-W1' is the right target and the prize floor follows.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn i0_2y(y:f64)->f64{ let mut s=1.0; let mut term=1.0; let y2=y*y; for r in 1..3000 { term *= y2/((r as f64)*(r as f64)); s+=term; if term< s*1e-18 {break;} } s }

fn run(n:u64,p:u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let pf=p as f64; let nf=n as f64;
    let lnq=(p as f64).ln(); let beta=lnq/(nf).ln();
    let ystar=(2.0*lnq/nf).sqrt();
    // fine sweep of Phi_p^nz / exp(n y^2/2)
    let mut maxg=0.0f64; let mut maxgy=0.0;
    let mut maxb=0.0f64; let mut maxby=0.0; // also track vs Bessel for record
    let mut y=0.01;
    while y<2.6 {
        let mut s=0.0; for &e in &eta { s+=(e*y).cosh(); }
        let phi=nf*s/pf;
        let gr=phi/(nf*y*y/2.0).exp();
        if gr>maxg {maxg=gr; maxgy=y;}
        let br=phi/i0_2y(y).powf(nf/2.0);
        if br>maxb {maxb=br; maxby=y;}
        y+=0.01;
    }
    // value AT saddle
    let mut ss=0.0; for &e in &eta { ss+=(e*ystar).cosh(); }
    let sad=nf*ss/pf/(nf*ystar*ystar/2.0).exp();
    println!("n={:4} p={} beta={:.2} lnq={:.2} y*={:.3} | MAX Phi^nz/Gauss={:.5} @y={:.2} {} | @saddle={:.5} | (record max/Bessel={:.4}@y={:.2})",
        n,p,beta,lnq,ystar, maxg,maxgy,
        if maxg>1.0+1e-7{"<<<GAUSS FORM FAILS"}else{"<=1 OK"}, sad, maxb,maxby);
}
fn main(){
    run(16, fp(16,500000));
    run(32, fp(32,10000000));
    run(64, fp(64,200000000));
    run(128, fp(128,300000000));
    run(256, fp(256,2000000000));
}
