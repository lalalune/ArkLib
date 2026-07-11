// wf-F2: the DECISIVE bootstrap quantities, isolated and at PRIZE-SCALE depth.
// Computes E'_r(G), E'_r(H=mu_{n/2}) in the SAME field, and reports, AT THE OPTIMAL DEPTH r*(n)=round(ln q /2):
//   K_eff(n)        = (E'_{r*}(G)/((2r*-1)!! n^{r*}))^{1/r*}
//   K_eff(n/2)      = (E'_{r*}(H)/((2r*-1)!! (n/2)^{r*}))^{1/r*}     [same r*, comparable]
//   dK := K_eff(n)-K_eff(n/2)   (the per-level K-increment; if -> 0 from below/above, bounded)
//   rho* := E'_{r*}(G)/(2 E'_{r*}(H))   (descent contractivity at depth)
//   M_bound/prize = (q E'_{r*}(G))^{1/2r*} / sqrt(n ln(q/n))
// Plus: the running PRODUCT of kappa from base n0=32 up to n, to see if it converges (=> K_eff bounded).
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ln_dfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn periods(g:u64,ord:u64,p:u64)->Vec<f64>{
    let base=mpow(g,(p-1)/ord,p);
    let sub:Vec<u64>=(0..ord).map(|j|mpow(base,j,p)).collect();
    let m=(p-1)/ord; let gord=mpow(g,ord,p);
    let mut out=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &sub{let t=((b as u128*x as u128)%p as u128)as u64; re+=(2.0*PI*(t as f64)/p as f64).cos();} out.push(re); b=((b as u128*gord as u128)%p as u128)as u64; }
    out
}
// ln E'_r (works in log space to avoid overflow at large r); returns ln of sum eta^{2r} over nonprincipal, minus ln p
fn ln_er(eta:&[f64], ord:f64, p:f64, r:usize)->f64{
    // sum |eta|^{2r}; use log-sum-exp on 2r*ln|eta|
    let mut terms:Vec<f64>=Vec::new();
    for &e in eta { if (e-ord).abs()>0.5 && e.abs()>1e-12 { terms.push(2.0*(r as f64)*e.abs().ln()); } }
    if terms.is_empty(){return f64::NEG_INFINITY;}
    let mx=terms.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
    let s:f64=terms.iter().map(|t|(t-mx).exp()).sum();
    mx + s.ln() - p.ln()
}
fn main(){
    println!("== wf-F2 K_eff trend at OPTIMAL depth r*=round(ln q/2), beta=4, prime field n^4 ==");
    println!(" n      p          r*    K_eff(n)   K_eff(n/2)   dK         rho*     Mbound/prize   prod_kappa(from32)");
    let beta=4.0;
    let ns=[8u64,16,32,64,128];
    let mut prevk=f64::NAN; let mut prod=1.0f64;
    for &n in &ns {
        let p=fp(n,(n as f64).powf(beta)as u64);
        let g=proot(p);
        let lnq=(p as f64).ln(); let rstar=(lnq/2.0).round().max(1.0) as usize;
        let etaG=periods(g,n,p); let etaH=periods(g,n/2,p);
        let lneg=ln_er(&etaG,n as f64,p as f64,rstar);
        let lneh=ln_er(&etaH,(n/2) as f64,p as f64,rstar);
        // ln D(n) = lneg - ln c0 ; ln c0(n)=ln_dfact(r)+ r ln n
        let lnc0g=ln_dfact(rstar)+(rstar as f64)*(n as f64).ln();
        let lnc0h=ln_dfact(rstar)+(rstar as f64)*((n/2) as f64).ln();
        let keffn=((lneg-lnc0g)/rstar as f64).exp();
        let keffh=((lneh-lnc0h)/rstar as f64).exp();
        let dk=keffn-keffh;
        let rho=(lneg-( (2.0f64).ln()+lneh)).exp();
        // M_bound = (q E'_{r*})^{1/2r*}; ln = (ln p + lneg)/(2 r*)
        let lnmb=(lnq+lneg)/(2.0*rstar as f64);
        let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        let mbr=lnmb.exp()/prize;
        // product of per-level kappa (using K_eff ratio at each step's own r* — approximate self-improving product)
        let kappa= if prevk.is_finite(){keffn/prevk}else{1.0};
        if n>=64 {prod*=kappa;}
        prevk=keffn;
        println!(" {:4}  {:11}  {:3}   {:8.5}   {:8.5}    {:+8.5}   {:7.3}   {:8.4}        {:.5}",
            n,p,rstar,keffn,keffh,dk,rho,mbr,prod);
    }
    println!("\nINTERPRETATION:");
    println!(" * dK = K_eff(n)-K_eff(n/2) at the SAME depth r*(n): the per-dyadic-level K increment.");
    println!("   If dK -> 0 (or <0) for large n, the dyadic bootstrap caps K_eff (bounded => prize).");
    println!(" * rho* = E'(G)/(2E'(H)) at depth: >1 means descent is NOT contractive at that depth;");
    println!("   but K_eff comparison (dK) already normalizes by char-0, which is the right object.");
    println!(" * Mbound/prize <~1.3 with C=sqrt(K): the moment route delivers the prize constant.");
}
