// wf-S11 FRESH/ALIEN angle: the SPECTRAL-DEFECT / INCOMPRESSIBILITY reading of K-boundedness.
//
// THE OBJECT.  n=2^mu, n|p-1, p prime, p~n^beta (beta=4 prize). mu_n = order-n subgroup of F_p^*.
//   For each nonprincipal additive char b in F_p^*, the Gauss period is
//       eta_b = sum_{x in mu_n} e_p(b x)    (real, since mu_n is +-1 closed for mu>=1).
//   Normalize  t_b := |eta_b|^2 / n   (so the "Gaussian/Sato-Tate" prediction is E[t_b] = 1).
//   The char-p nonprincipal 2r-energy is
//       E_r' = (1/p) sum_{b!=0} eta_b^{2r} = (n^r / p) * sum_{b!=0} t_b^r * (sign handled by even power).
//   K_eff(r) = (E_r' / [(2r-1)!! n^r])^{1/r}.  K bounded  <=>  the moments  M_r := (1/p) sum_b t_b^r
//   grow no faster than (2r-1)!! * K^r  i.e.  t_b is uniformly sub-Gaussian in its SQUARE-ROOT.
//
// FRESH CLAIM TO TEST (incompressibility / thin-resonance).  The MOMENT excess over the
//   Gaussian floor is carried by a THIN set of "resonant" characters:  characters with t_b
//   above a fixed threshold T have density (over b) that DECAYS, and the count of b with
//   t_b >= T*log-scale is o(p) uniformly.  If the upper tail  P(t_b >= s)  is sub-exponential
//   (<= A exp(-c s)) with c,A ABSOLUTE (n,p-independent at beta=4), then ALL moments
//   M_r <= r! / c^r  <= K^r (2r-1)!! holds with absolute K  => K BOUNDED => prize via S1.
//
//   The ALTERNATIVE (kills K): a HEAVY (power-law) tail P(t_b>=s) ~ s^{-a} with a small, OR a
//   GROWING resonant peak max_b t_b that scales like n^{eps} or log p — then high moments blow up.
//
// WHAT WE MEASURE (exact, all b in 1..p-1 by FFT-free direct since n*p small enough; for the
//   period we exploit eta is constant on cosets of mu_n, so only m=(p-1)/n DISTINCT values):
//   (A) max_b t_b  (the worst resonance height) vs n, log p  -- does the PEAK grow?
//   (B) the upper-tail survival  S(s)=#{b: t_b>=s}/p  at s=2,3,4,6,8 -- exponential or power?
//   (C) fit c from  log S(s) ~ -c*s  ; report c (the sub-Gaussian rate). c bounded below => K bounded.
//   (D) the moments M_r and K_eff directly, cross-checking the S1 number ~0.64.
//   (E) STRUCTURED-PRIME robustness: good / high-v2 / rough primes (the S1 honesty controls).
//
// HONESTY: proper subgroup, n=2^mu, n|p-1, p PRIME, p~n^4 (beta=4 prize regime), m=(p-1)/n>1.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1}v}
fn largest_pf(mut x:u64)->u64{let mut L=1;let mut d=2;while d*d<=x{while x%d==0{L=d;x/=d}d+=1}if x>1{L=x}L}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

fn run(n:u64,p:u64,tag:&str){
    let g=proot(p);
    let h=mpow(g,(p-1)/n,p);                 // generator of mu_n
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;                            // # distinct period values (eta const on mu_n cosets)
    let gn=mpow(g,n,p);                       // generator of the m coset reps
    // distinct period values eta_b for b a coset rep; each occurs for n values of b
    let mut t:Vec<f64>=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0;
        for &x in &mu { let z=((b as u128*x as u128)%p as u128) as u64; re+=(2.0*PI*(z as f64)/p as f64).cos(); }
        t.push((re*re)/(n as f64));          // t_b = |eta_b|^2/n
        b=((b as u128*gn as u128)%p as u128) as u64;
    }
    // (A) peak resonance
    let tmax=t.iter().cloned().fold(0.0f64,f64::max);
    let mean=t.iter().sum::<f64>()/(m as f64);
    // (B) upper-tail survival  S(s)=#{b:t_b>=s}/p ; each coset rep covers n of the p-1 chars
    let surv=|s:f64|->f64{ let c=t.iter().filter(|&&v|v>=s).count() as f64; (c*(n as f64))/(p as f64) };
    let (s2,s3,s4,s6,s8)=(surv(2.0),surv(3.0),surv(4.0),surv(6.0),surv(8.0));
    // (C) fit c: log S(s) ~ const - c*s on s in {2,4,6,8} where S>0 (least squares slope)
    let mut xs=vec![]; let mut ys=vec![];
    for &s in &[2.0f64,4.0,6.0,8.0] { let sv=surv(s); if sv>0.0 { xs.push(s); ys.push(sv.ln()); } }
    let crate_c = if xs.len()>=2 {
        let nn=xs.len() as f64; let sx:f64=xs.iter().sum(); let sy:f64=ys.iter().sum();
        let sxx:f64=xs.iter().map(|v|v*v).sum(); let sxy:f64=xs.iter().zip(&ys).map(|(a,b)|a*b).sum();
        let slope=(nn*sxy-sx*sy)/(nn*sxx-sx*sx); -slope          // c = -slope (decay rate)
    } else { f64::NAN };
    // (D) moments / K_eff (account: each coset rep covers n chars, divide by p)
    let lnq=(p as f64).ln(); let rmax=(1.4*lnq) as usize;
    print!("{} n={:4} p={:>11} v2={:2} rough={:>9} beta={:.2} | tmax={:.2} (tmax/lnp={:.3}) mean={:.3} | S(s): 2={:.3} 3={:.3} 4={:.4} 6={:.4} 8={:.5} | c_rate={:.3} | K_eff:",
        tag,n,p,v2(p-1),largest_pf((p-1)/n),lnq/(n as f64).ln(), tmax, tmax/lnq, mean, s2,s3,s4,s6,s8, crate_c);
    let mut maxk=0.0f64;
    for r in [1usize,2,3,5,8,12].iter().filter(|&&r|r<=rmax.max(6)) {
        let r=*r;
        // M_r = (1/p) sum_{b!=0} t_b^r ; coset rep covers n chars
        let mut mr=0.0; for &v in &t { mr+=v.powi(r as i32); } mr=mr*(n as f64)/(p as f64);
        // E_r' = n^r * M_r ; K_eff=(E_r'/((2r-1)!! n^r))^{1/r}=(M_r/(2r-1)!!)^{1/r}
        let k=(mr/dfact(r)).powf(1.0/r as f64);
        if k>maxk{maxk=k;}
        print!(" r{}={:.3}",r,k);
    }
    println!(" | MAXK={:.3}", maxk);
}

fn main(){
    println!("=========================================================================================");
    println!("wf-S11 RESONANCE SPECTRUM: is K bounded BECAUSE the period-energy tail is sub-exponential?");
    println!("t_b=|eta_b|^2/n ; M_r=(1/p)sum t_b^r ; K_eff=(M_r/(2r-1)!!)^(1/r). c_rate=sub-Gaussian decay.");
    println!("Sub-exp tail S(s)<=A e^{{-c s}} with c bounded => M_r<=r!/c^r<=K^r(2r-1)!! => K BOUNDED => prize.");
    println!("=========================================================================================");
    for mu in 5u32..=10 {                    // n = 32 .. 1024
        let n=1u64<<mu;
        let lo=n*n*n*n;                       // p ~ n^4 (beta=4 prize)
        let pg=fp(n,lo);
        run(n,pg,"good ");
        // high-v2 control
        let mut p=pg; for _ in 0..30000 { let q=fp(n,p+1); if v2(q-1)>= (mu+5).min(20) {run(n,q,"hi-v2"); break;} p=q; }
        // rough control: (p-1)/n has a big prime factor
        let mut p=pg; for _ in 0..30000 { let q=fp(n,p+1); if largest_pf((q-1)/n) > (q-1)/n/3 {run(n,q,"rough"); break;} p=q; }
        println!("-----------------------------------------------------------------------------------------");
    }
}
