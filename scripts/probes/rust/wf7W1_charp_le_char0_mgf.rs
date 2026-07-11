// wf-W1 (#444): the SHARP sub-lemma the MGF route reduces to.
//
// CLAIM (sub-lemma S-W1):  Phi_p^nz(y) := (1/q) sum_{b!=0} cosh(eta_b y)  <=  I0(2y)^{n/2} =: Phi_0(y)
//   for ALL y >= 0  (char-p DC-subtracted even-moment MGF <= char-0 Bessel MGF).
//
// WHY this is the whole game:
//   * Termwise in y^{2r}: Phi_p^nz coeff = A_r/(2r)!  where A_r = E_r - n^{2r}/p (the DC-subtracted
//     moment, EXACTLY the prize object). Phi_0 coeff = E_r^{char0}/(2r)! = (2r-1)!! n^r/(2r)! = n^r/(2^r r!).
//   * So Phi_p^nz <= Phi_0 for all y  <=>  A_r <= (2r-1)!! n^r for ALL r simultaneously = WICK with K=1.
//   * And Phi_0(y) = I0(2y)^{n/2} <= exp(n y^2/2) is TERMWISE-elementary (I0(2y)=sum y^{2r}/(r!)^2,
//     exp(y^2)=sum y^{2r}/r!, (r!)^2>=r!). So S-W1 => the single open inequality => the prize.
//
// This probe: trace Phi_p^nz/Phi_0 across a fine y-grid (esp. SMALL y = low r, where spurious mod-p
// relations would first appear) and report max ratio. If ever >1 the K=1 form fails (then K>1 needed).
// Also extract per-r:  A_r/(2r-1)!!n^r  by reading off via small-y series? No -- compute E_r directly
// AND A_r and ratio at depth r = round(ln q) and neighbors (the saddle depth).

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn i0_2y(y:f64)->f64{ let mut s=1.0; let mut term=1.0; let y2=y*y; for r in 1..3000 { term *= y2/((r as f64)*(r as f64)); s+=term; if term< s*1e-18 {break;} } s }
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

fn run(n:u64,p:u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let pf=p as f64; let nf=n as f64;
    let lnq=(p as f64).ln(); let beta=lnq/(nf).ln();
    println!("== n={} p={} m={} beta={:.2} ln q={:.2} ==",n,p,m,beta,lnq);
    // (1) MGF ratio sweep over fine y-grid: Phi_p^nz / Phi_0
    let mut maxr=0.0f64; let mut maxy=0.0;
    let mut y=0.02;
    while y < 2.5 {
        let mut s=0.0; for &e in &eta { s += (e*y).cosh(); }
        let phi_nz = nf*s/pf;
        let phi0 = i0_2y(y).powf(nf/2.0);
        let r = phi_nz/phi0;
        if r>maxr {maxr=r; maxy=y;}
        y += 0.02;
    }
    println!("   sweep y in (0,2.5): MAX Phi_p^nz/Phi_0 = {:.6} at y={:.3}  {}",
        maxr, maxy, if maxr>1.0+1e-7 {"<<< S-W1 FALSE (K=1 fails)"} else {"<= 1  (S-W1 holds: A_r<=Wick all r)"});
    // (2) per-r at saddle depth: A_r/((2r-1)!! n^r)  for r near ln q
    let r0 = lnq.round() as usize;
    println!("   per-r A_r/Wick (Wick=(2r-1)!!n^r), DC-subtracted A_r=E_r - n^{{2r}}/p:");
    print!("     ");
    for dr in -2i32..=3 {
        let r = (r0 as i32 + dr).max(1) as usize;
        let mut s=0.0; for &e in &eta { s += (nf*e.powi(2*r as i32)); } // n*sum over reps = sum over all b!=0
        let er = s/pf;                 // E_r restricted to b!=0 part... careful: E_r total = (1/p) sum_ALL b eta_b^{2r}
        // full E_r includes b=0 term eta_0^{2r}=n^{2r}; A_r = E_r_full - n^{2r}/p.
        // E_r_full = (n^{2r} + n*sum_reps eta^{2r})/p ; A_r = n*sum_reps eta^{2r}/p = er above. GOOD.
        let wick = dfact(r)*nf.powi(r as i32);
        print!(" r={}:{:.4}", r, er/wick);
    }
    println!();
    println!();
}
fn main(){
    run(16, fp(16,500000));
    run(32, fp(32,10000000));
    run(64, fp(64,200000000));
    run(128, fp(128,300000000));
}
