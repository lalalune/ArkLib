// wf-B3: ANATOMY of the antitone failure -- is it a refutation of the PRIZE inequality
// (some R(r) > 1) or only an obstruction to the ANTITONE proof STRATEGY (R stays <=1 but the
// monotone DESCENT fails)?  Also: char-0 reference (Bessel besselCoeff) vs char-p, to show the
// spurious mass is exactly what breaks monotonicity while leaving R(r)<=1 intact (when it does).
//
// We print, for a chosen (n,p), the FULL R-vector, max over r of R(r) (the prize-relevant
// quantity: prize needs R(r)<=1 i.e. m_r<=1), and the char-0 R-vector for the same d=n/2 via
// besselCoeff for direct delta_r = E_r^charp - E_r^char0 comparison.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=&mut a; r as u64}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// char-0 besselCoeff d r = [x^r] I0(2 sqrt x)^d via convolution of single-factor coeffs 1/(k!)^2.
fn bessel_coeffs(d:usize,rmax:usize)->Vec<f64>{
    // single factor a_k = 1/(k!)^2
    let mut fact=vec![1.0f64;rmax+1];
    for k in 1..=rmax { fact[k]=fact[k-1]*(k as f64); }
    let single:Vec<f64>=(0..=rmax).map(|k|1.0/(fact[k]*fact[k])).collect();
    let mut cur=vec![0.0f64;rmax+1]; cur[0]=1.0;
    for _ in 0..d {
        let mut nxt=vec![0.0f64;rmax+1];
        for i in 0..=rmax { if cur[i]==0.0 {continue;} for j in 0..=rmax-i { nxt[i+j]+=cur[i]*single[j]; } }
        cur=nxt;
    }
    cur
}

fn main(){
    // genuine NON-sampled prize-scale failure: n=32, p=1001153 (beta=3.99, m=(p-1)/32=31285 cosets full)
    for (n,p) in [(32u64,1001153u64),(32,4129),(64,4801),(128,15233)] {
        let g=proot(p);let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let m=(p-1)/n; let gn=mpow(g,n,p);
        let lnq=(p as f64).ln(); let nf=n as f64;
        let rmax=((1.6*lnq) as usize).max(12);
        let mut mom=vec![0.0f64;rmax+3];
        let mut b=1u64;
        for _ in 0..m {
            let mut re=0.0;
            for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}
            let e2=re*re; let mut pw=1.0;
            for r in 1..=rmax+2 { pw*=e2; mom[r]+=pw; }
            b=((b as u128*gn as u128)%p as u128)as u64;
        }
        let mf=m as f64;
        for r in 0..=rmax+2 { if r==0 {mom[0]=1.0;} else {mom[r]/=mf;} }
        // Wick-normalized m_r = M(r)/((2r-1)!! n^r); R(r)=M(r+1)/((2r+1) n M(r))
        let mut rr=vec![0.0;rmax+2];
        for r in 1..=rmax+1 { rr[r]= mom[r+1]/(((2*r+1) as f64)*nf*mom[r]); }
        // char-0 reference
        let d=(n/2) as usize;
        let bc=bessel_coeffs(d, rmax+3);
        // char-0 R0(r) = (r+1) c_{r+1} / (d c_r)
        let mut r0=vec![0.0;rmax+2];
        for r in 1..=rmax+1 { r0[r]= ((r+1) as f64)*bc[r+1]/((d as f64)*bc[r]); }
        // max R over r (prize needs <=1)
        let mut maxr=f64::MIN; let mut argr=0;
        for r in 1..=rmax { if rr[r]>maxr {maxr=rr[r]; argr=r;} }
        let prize_ok = maxr<=1.0+1e-9;
        println!("==== n={} p={} beta={:.2} m={} rmax={} ====",n,p,lnq/nf.ln(),m,rmax);
        println!("  PRIZE quantity max_r R(r) = {:.5} @ r{}  => R(r)<=1 (prize moment bound) : {}",maxr,argr,prize_ok);
        print!("  char-p R: "); for r in 1..=12.min(rmax) {print!("R{}={:.4} ",r,rr[r]);} println!();
        print!("  char-0 R: "); for r in 1..=12.min(rmax) {print!("R{}={:.4} ",r,r0[r]);} println!();
        // antitone check + where it breaks
        let mut breaks=vec![];
        for r in 1..=rmax { if rr[r+1]-rr[r]>1e-9 {breaks.push((r,rr[r+1]-rr[r]));} }
        print!("  char-p antitone breaks (r where R(r+1)>R(r)): ");
        for (r,inc) in &breaks {print!("[r{}->{} +{:.2e}] ",r,r+1,inc);} println!();
        // char-0 antitone breaks (should be NONE -- sharp Newton)
        let mut breaks0=vec![];
        for r in 1..=rmax { if r0[r+1]-r0[r]>1e-12 {breaks0.push(r);} }
        println!("  char-0 antitone breaks: {:?} (empty = char-0 monotone, sharp-Newton holds)",breaks0);
        println!();
    }
}
