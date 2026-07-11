// Decisive test of M1/M3 sufficient lemma in the K^r form: is char-p E_r <= K^r (2r-1)!! n^r
// for an ABSOLUTE K (=> prize with C*sqrt(K)), or does (E_r/char0)^{1/r} GROW (route dead)?
// E_r = (1/p) sum_b eta_b^{2r}  (periods real, negation-closed). char0 = (2r-1)!! n^r.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v} // (2r-1)!!
fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    // real periods: eta_b = sum cos (imaginary parts cancel over the full coset orbit since negation-closed)
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let beta=(p as f64).ln()/(n as f64).ln();
    println!("-- n={} p={} m={} beta={:.2} (ln q={:.1}, opt depth r*~{:.0}) --", n,p,m,beta,(p as f64).ln(),(p as f64).ln()/2.0);
    println!("   r   E_r/char0     (ratio)^(1/r)=K_eff   M_bound/prize");
    let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
    let eta0=n as f64; // eta_0 = n (the trivial coset); exclude it (b!=0 means nonprincipal; b ranges over nonzero so all included incl coset of 1). We want max over b!=0; eta_0=n is the principal -> exclude.
    for r in 1..=rmax {
        // E_r including all cosets; subtract principal eta_0=n contribution to char-p E_r? Standard E_r counts all; keep all.
        let mut s=0.0; for &e in &eta { s += e.powi(2*r as i32); }
        let er = s/(p as f64);
        let c0 = dfact(r)*(n as f64).powi(r as i32);
        let ratio = er/c0;
        let keff = ratio.powf(1.0/r as f64);
        // moment->sup bound on max_{b!=0}: (q * E_r')^{1/2r}, E_r' excludes principal
        let mut s2=0.0; for &e in &eta { if (e-eta0).abs()>0.5 { s2+=e.powi(2*r as i32);} }
        let mbound = (p as f64 * (s2/(p as f64))).powf(1.0/(2.0*r as f64));
        println!("  {:3}  {:11.3}  {:8.3}            {:.3}", r, ratio, keff, mbound/prize);
    }
}
fn main(){
    run(16, fp(16,60000), 16);
    run(32, fp(32,1000000), 20);
    run(64, fp(64,16000000), 22);
}
