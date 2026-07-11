// wf-G5 part 2: At prize beta~4, E2(H) ~ |H|^2 (Sidon regime, since |H|^3/p -> 0). The energy
// is OPTIMAL. So what M(H) bound does the energy/sum-product route GIVE, and how far from prize?
// The standard energy->charsum step (e.g. via the d-th moment / Holder): with the r-th additive
// energy E_r(H) (=#solutions a1+..+ar=b1+..+br), the sup-norm satisfies a moment relation but the
// ROUTE to the exponent saving is sum-product amplification of E_2 below |H|^{5/2}. At beta=4 E_2
// is ALREADY ~|H|^2, so the saving is MAXIMAL but the resulting exponent is what we read here.
//
// We compute, exactly: M(H)=max_{b!=0}|sum_{x in H} e_p(bx)|, the realized exponent
// log M / log|H|, and compare to prize sqrt(n log(p/n)) and to di Benedetto n^{1-31/2880}.
// Also fit E2 = c2*n^2 + c3*n^3/p to confirm Sidon regime, and report the di-Benedetto-style
// exponent that the MEASURED energy would yield via the textbook E_2 -> charsum bound:
//   the "second-moment" charsum bound is M(H)^2 <= ... but the real subgroup bound uses higher r.
use std::collections::HashMap;
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn energy2(mu:&[u64], p:u64)->u128{
    let mut cnt:HashMap<u64,u64>=HashMap::with_capacity(mu.len()*mu.len());
    for &a in mu { for &b in mu { let t=((a as u128 + b as u128)%p as u128)as u64; *cnt.entry(t).or_insert(0)+=1; } }
    let mut e:u128=0; for(_,&c) in &cnt { e += (c as u128)*(c as u128); } e
}
fn main(){
    println!("n      p          beta  E2        E2/n^2  c3=(E2-n^2)*p/n^3   M(H)    logM/logn  prize  M/prize  diBen_exp");
    for a in 4..=8u32 {
        let n=1u64<<a; let lo=((n as f64).powf(4.0))as u64; let p=fp(n,lo);
        let g=proot(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let e2=energy2(&mu,p) as f64;
        let nf=n as f64; let pf=p as f64;
        let c3=(e2 - nf*nf)*pf/(nf*nf*nf); // if E2 = n^2 + c3 n^3/p then c3~3 (random); Sidon if e2~n^2
        // exact M(H): Fourier sup over b!=0, O(p*n) -- ok up to p~ a few e6; for big p use FFT? cap a<=7
        let mut mmax=0.0f64;
        if p < 80_000_000 {
            for b in 1..p { let mut re=0.0; let mut im=0.0;
                for &x in &mu { let t=((b as u128*x as u128)%p as u128)as u64; let ang=2.0*PI*(t as f64)/pf; re+=ang.cos(); im+=ang.sin(); }
                let mag=(re*re+im*im).sqrt(); if mag>mmax{mmax=mag;} }
        } else { mmax=f64::NAN; }
        let logm = mmax.ln()/nf.ln();
        let prize=(nf*((pf/nf).ln())).sqrt();
        let diben = nf.powf(1.0-31.0/2880.0);
        println!("{:5} {:10} {:.2}  {:.3e}  {:.3}   {:8.4}            {:8.2}  {:.4}     {:7.2}  {:.3}    {:.0}",
            n,p,(pf.ln()/nf.ln()), e2, e2/(nf*nf), c3, mmax, logm, prize, mmax/prize, diben);
    }
}
