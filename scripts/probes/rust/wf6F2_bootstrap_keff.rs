// wf-F2: SELF-IMPROVING / BOOTSTRAP test for K_eff(n) boundedness.  DIRECT PERIOD METHOD.
//
// E_r'(G) := (1/q) sum_{b!=0} eta_b^{2r}  (NONPRINCIPAL: principal coset eta=n excluded).
// We compute all real periods eta_b once (O(m*n)=O(p)), then all powers cheaply.
// H = mu_{n/2} is an index-2 subgroup of G = mu_n, SAME field F_p. Its periods are
//   eta^H_b = sum_{x in H} e_p(bx), grouped into m'=(p-1)/(n/2)=2m cosets.
//
// char-0 normalizer c0(n,r)=(2r-1)!! n^r.  D(n,r)=E'_r(G)/c0(n,r)=K_eff(n,r)^r.
// Per-level ratios:
//   rho(n,r)  := E'_r(G)/(2 E'_r(H))                  (descent contractivity; rho<=1 => K non-incr)
//   kappa(n,r):= [D(n,r)/D(n/2,r)]^{1/r} = (rho * 2)^... = (E'_r(G)/E'_r(H))^{1/r} / 2^{1}*?  -- computed exactly below.
// CLAIM under test (bootstrap): kappa(n,r) -> 1 as n grows at fixed r  =>  K_eff(n) bounded
//   uniformly in n by a self-improving induction with a vanishing per-level increment.
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
// all real periods of subgroup of order ord, one per coset of <g^ord>. returns Vec of length (p-1)/ord.
fn periods(g:u64,ord:u64,p:u64)->Vec<f64>{
    let sub:Vec<u64>=(0..ord).map(|j|mpow(mpow(g,(p-1)/ord,p),j,p)).collect();
    let m=(p-1)/ord; let gord=mpow(g,ord,p);
    let mut out=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &sub{let t=((b as u128*x as u128)%p as u128)as u64; re+=(2.0*PI*(t as f64)/p as f64).cos();} out.push(re); b=((b as u128*gord as u128)%p as u128)as u64; }
    out
}
// E'_r from periods: sum eta^{2r} over nonprincipal, /p. principal = the coset with eta~ord.
fn ers(eta:&[f64], ord:f64, p:f64, rmax:usize)->Vec<f64>{
    let mut acc=vec![0.0f64;rmax+1];
    for &e in eta { if (e-ord).abs()>0.5 { let mut e2=1.0; let ee=e*e; for r in 1..=rmax { e2*=ee; acc[r]+=e2; } } }
    for r in 0..=rmax { acc[r]/=p; } acc
}
fn main(){
    println!("== wf-F2 bootstrap K_eff (direct periods): rho=E'(G)/2E'(H), kappa, K_eff(G,n), trend in n ==");
    let beta=4.0;
    for &n in &[8u64,16,32,64,128,256] {
        let p=fp(n,(n as f64).powf(beta)as u64);
        let g=proot(p);
        let lnq=(p as f64).ln(); let ropt=(lnq/2.0).round().max(1.0) as usize;
        let rmax=(ropt+3).min(22);
        let etaG=periods(g,n,p); let etaH=periods(g,n/2,p);
        let eg=ers(&etaG,n as f64,p as f64,rmax);
        let eh=ers(&etaH,(n/2) as f64,p as f64,rmax);
        println!("\n-- n={} (H=mu_{}) p={} beta={:.2} lnq={:.1} r_opt~{} --",n,n/2,p,(p as f64).ln()/(n as f64).ln(),lnq,ropt);
        println!("   r      E'_r(G)         rho=G/2H    kappa=(D_G/D_H)^1/r   K_eff(G)");
        for r in 1..=rmax {
            let rho=eg[r]/(2.0*eh[r]);
            let dg=eg[r]/(dfact(r)*(n as f64).powi(r as i32));
            let dh=eh[r]/(dfact(r)*((n/2)as f64).powi(r as i32));
            let kappa=(dg/dh).powf(1.0/r as f64);
            let keff=dg.powf(1.0/r as f64);
            println!("  {:3}  {:14.4}    {:8.4}    {:10.5}            {:.5}", r, eg[r], rho, kappa, keff);
        }
    }
}
