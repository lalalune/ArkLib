// wf-W1 (MGF/saddle route, #444): the SINGLE OPEN INEQUALITY directly.
//
// The cosh-MGF identity (CoshMGFIdentity.lean, PROVEN) gives
//     sum_b cosh(|eta_b| y) = sum_r (q E_r /(2r)!) y^{2r}.
// So the single open inequality "sum_r (q E_r/(2r)!) y^{2r} <= q exp(n y^2/2)" is EXACTLY
//     Phi_p(y) := (1/q) sum_b cosh(|eta_b| y)  <=  exp(n y^2 / 2)     (the char-p saddle bound).
// Proving Phi_p(y) <= exp(n y^2/2) for ALL y closes A_r <= Wick for ALL r at once.
//
// char-0 reference: Phi_0(y) = I0(2y)^{n/2} <= exp(n y^2/2) is TERMWISE-elementary
//     (I0(2y)=sum y^{2r}/(r!)^2 <= sum y^{2r}/r! = exp(y^2)).
// So the question = does the char-p MGF stay under the char-0 Bessel MGF (=> under Gaussian)?
//
// This probe computes EXACTLY (real periods, all b incl principal & b!=0 variants):
//   - Phi_p(y) = (1/q) sum_{all b} cosh(eta_b y)        [matches the Lean identity LHS exactly]
//   - Phi_p^{nz}(y) = (1/q) sum_{b!=0} cosh(eta_b y)     [DC-subtracted: the A_r object]
//   - Phi_0(y) = I0(2y)^{n/2}  (char-0 Bessel MGF)
//   - G(y) = exp(n y^2/2)      (the Gaussian target)
// at the SADDLE y* = sqrt(2 ln q / n) (depth r* ~ ln q) AND a y-sweep around it.
// FLAG: report ratio Phi_p/G at saddle; if > 1 anywhere the single open inequality is FALSE as stated.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
// modified Bessel I0(x) = sum_{r} (x/2)^{2r}/(r!)^2 ; here we want I0(2y) = sum y^{2r}/(r!)^2
fn i0_2y(y:f64)->f64{ let mut s=1.0; let mut term=1.0; let y2=y*y; for r in 1..2000 { term *= y2/((r as f64)*(r as f64)); s+=term; if term< s*1e-17 {break;} } s }

fn run(n:u64,p:u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    // real periods over the m nonprincipal cosets b = g^{0}, g^{n}, ... wait: b ranges over ALL nonzero.
    // eta_b depends only on the coset b mu_n; there are m=(p-1)/n cosets, each of size n.
    // The full sum over b!=0 = n * sum over coset-reps. b=0 gives eta_0 = n (principal). Total q = p.
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let beta=(p as f64).ln()/(n as f64).ln();
    let lnq=(p as f64).ln();
    let ystar=(2.0*lnq/(n as f64)).sqrt(); // saddle; r* ~ ln q
    println!("== n={} p={} m={} beta={:.2} ln q={:.2}  y*={:.4} (depth r*~{:.1}) ==",n,p,m,beta,lnq,ystar,lnq);
    println!("   y       Phi_p(y)/G      Phi_p^nz/G      Phi_0/G       [G=exp(n y^2/2)]");
    let pf=p as f64; let nf=n as f64;
    // sweep y around y*: fractions of y*
    let fracs=[0.25,0.5,0.75,0.9,1.0,1.1,1.25,1.5,2.0,3.0];
    for &fr in &fracs {
        let y=fr*ystar;
        // Phi_p(y) = (1/p)[ cosh(n*y)   (b=0, principal, eta_0=n)
        //                 + n * sum_{coset reps} cosh(eta_b y) ]   (each coset rep counted n times)
        let mut snz=0.0; for &e in &eta { snz += (e*y).cosh(); }
        let s_nonprincipal_full = nf*snz; // all b!=0
        let s_full = (nf*y).cosh() + s_nonprincipal_full;
        let phi_p   = s_full / pf;
        // DC-subtracted: only b!=0. But the principal coset rep b=1 (eta=n) IS among the m reps (b=1 -> eta=n).
        // The "A_r" DC-subtraction removes the n^{2r}/p term = principal eta_0=n? NO: A_r removes the
        // b=0 frequency. b!=0 includes the coset of mu_n itself which has eta_b possibly = n? eta_1=sum cos(2pi x/p) over x in mu_n. Not n in general. So Phi_p^nz = all b!=0.
        // We approximate "b=0 excluded" by phi_p minus the b=0 cosh term:
        let phi_p_nz = s_nonprincipal_full / pf;
        let phi0 = i0_2y(y).powf(nf/2.0);
        let gauss = (nf*y*y/2.0).exp();
        println!("  {:.4}  {:11.5}    {:11.5}    {:11.5}    fr={:.2}{}",
            y, phi_p/gauss, phi_p_nz/gauss, phi0/gauss, fr,
            if phi_p/gauss>1.0+1e-9 {"  <<< Phi_p>G !!"} else {""});
    }
    // explicit saddle line
    let y=ystar;
    let mut snz=0.0; for &e in &eta { snz += (e*y).cosh(); }
    let s_full=(nf*y).cosh()+nf*snz; let gauss=(nf*y*y/2.0).exp();
    println!("  SADDLE y*={:.4}: Phi_p/G={:.5}  Phi_p^nz/G={:.5}  Phi_0/G={:.5}",
        y, s_full/pf/gauss, (nf*snz)/pf/gauss, i0_2y(y).powf(nf/2.0)/gauss);
    println!();
}
fn main(){
    run(16, fp(16,60000));
    run(16, fp(16,500000));
    run(32, fp(32,1000000));
    run(32, fp(32,10000000));
    run(64, fp(64,16000000));
    run(64, fp(64,200000000));
    run(128, fp(128,300000000));
    run(256, fp(256,4000000000));
}
