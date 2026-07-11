// wf-B3: ADVERSARIAL pre-screen of R(r) ANTITONICITY robustness to spurious mod-p mass.
// R(r) := M(r+1) / ((2r+1)*n*M(r)),  M(r)=(1/m) sum_{b!=0} eta_b^{2r}, eta_b real (negation-closed coset sums).
// W3-anti claim: R(r+1) <= R(r) for all r>=1 (log-convexity of Wick-normalized moments m_r).
// PROVEN char-0 (Lam-Leung gives m_r<=1; here we test the RELATIVE step monotonicity in char-p).
//
// B3 KEY QUESTION: char-p has spurious mod-p mass (wrap-around coincidences x_i+x_j == x_k+x_l mod p
// that are NOT char-0 collisions). Does this break antitonicity?  We hunt for ANY (n,p,r) at band
// depth where R(r+1) > R(r). To MAXIMIZE spurious mass we choose ADVERSARIAL primes:
//   - SMALL beta (p barely > n): most wrap-around, strongest pollution.
//   - rough primes (p-1 has large prime factors) vs smooth.
//   - many primes per n to sweep the spurious-incidence landscape.
// We need p%n==1 for mu_n (the order-n subgroup) to exist.  band depth r up to ~1.6 ln q.
//
// PERF: eta-table is the cost (m=(p-1)/n cosets, each n char-values). For giant primes we
// cap the cosets enumerated at COSET_CAP, walking representatives g^{j*n}. A sub-coset SAMPLE
// is a VALID adversarial under-screen: if a sample stays antitone it does not certify the full
// set, so giant cases are LABELLED SAMPLED and treated as suggestive only, not as a proof input.
use std::f64::consts::PI;
use std::io::Write;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=&mut a; r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn lpf(mut m:u64)->u64{let mut l=1;let mut d=2;while d*d<=m{if m%d==0{while m%d==0{m/=d}l=d}d+=1}if m>1{l=m}l}
fn primes_mod(n:u64,lo:u64,cnt:usize)->Vec<u64>{let mut v=vec![];let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}while v.len()<cnt{if p>2&&p%n==1&&isp(p){v.push(p);}p+=n;}v}

const COSET_CAP:u64 = 1_500_000;

// returns (R(1)<=1, antitone, worstInc, worst_r, beta, sampled, ncoset)
fn analyze(n:u64,p:u64)->(bool,bool,f64,usize,f64,bool,u64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let mfull=(p-1)/n; let gn=mpow(g,n,p);
    let sampled = mfull>COSET_CAP;
    let m = if sampled {COSET_CAP} else {mfull};
    let mut b=1u64;
    let lnq=(p as f64).ln(); let nf=n as f64;
    let rmax=((1.6*lnq) as usize).max(10);
    let mut mom=vec![0.0f64;rmax+3];
    for _ in 0..m {
        let mut re=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}
        let e2=re*re; let mut pw=1.0;
        for r in 1..=rmax+2 { pw*=e2; mom[r]+=pw; }
        b=((b as u128*gn as u128)%p as u128)as u64;
    }
    let mf=m as f64;
    for r in 1..=rmax+2 { mom[r]/=mf; }
    let mut rr=vec![0.0;rmax+2];
    for r in 1..=rmax+1 { rr[r]= mom[r+1]/(((2*r+1) as f64)*nf*mom[r]); }
    let mut antitone=true; let mut worst_inc=f64::MIN; let mut worst_r=0;
    for r in 1..=rmax { let inc = rr[r+1]-rr[r]; if inc>1e-9 {antitone=false;} if inc>worst_inc {worst_inc=inc; worst_r=r;} }
    let r1le1 = rr[1]<=1.0+1e-9;
    let beta=lnq/nf.ln();
    (r1le1, antitone, worst_inc, worst_r, beta, sampled, m)
}
fn sweep(n:u64,lo:u64,cnt:usize,tag:&str){
    println!("=== n={} ({}) : primes p>={} with p%n==1, cnt={} ===", n, tag, lo, cnt);
    std::io::stdout().flush().ok();
    let ps=primes_mod(n,lo,cnt);
    let mut any_fail=false; let mut worst_overall=f64::MIN; let mut worst_p=0; let mut worst_r=0;
    for p in ps {
        let (r1,anti,winc,wr,beta,sampled,nc)=analyze(n,p);
        let rough=lpf(p-1);
        let flag = if !anti {" *** ANTITONE FAILS ***"} else if !r1 {" (R1>1)"} else {""};
        let smp = if sampled {format!(" SAMPLED({} of {})",nc,(p-1)/n)} else {String::new()};
        if winc>worst_overall{worst_overall=winc;worst_p=p;worst_r=wr;}
        if !anti{any_fail=true;}
        println!("  p={:>11} beta={:.2} lpf(p-1)={:>10} | R1<=1:{} antitone:{} worstInc={:+.3e}@r{}{}{}",
            p,beta,rough,r1,anti,winc,wr,flag,smp);
        std::io::stdout().flush().ok();
    }
    println!("  -> SUMMARY n={}: any antitone failure: {} | worst Inc over all primes: {:+.3e} @ p={} r{}\n",
        n, any_fail, worst_overall, worst_p, worst_r);
    std::io::stdout().flush().ok();
}
fn main(){
    println!("######## REGIME A: SMALL beta (p barely > n) -- MAX spurious mass ########");
    sweep(16, 17, 40, "tiny-p");
    sweep(32, 33, 40, "tiny-p");
    sweep(64, 65, 40, "tiny-p");
    sweep(128, 129, 30, "tiny-p");
    sweep(256, 257, 20, "tiny-p");

    println!("######## REGIME B: MODERATE beta ~ 2-3 ########");
    sweep(16, 256, 25, "beta~2");
    sweep(32, 1024, 25, "beta~2");
    sweep(64, 4096, 25, "beta~2");
    sweep(128, 16384, 20, "beta~2");
    sweep(256, 65536, 15, "beta~2");

    println!("######## REGIME C: PRIZE beta ~ 4-5 (band depth) ########");
    sweep(16, 60000, 15, "beta~4");
    sweep(32, 1000000, 15, "beta~4");
    sweep(64, 16000000, 12, "beta~4");
    sweep(128, 260000000, 8, "beta~4");
    sweep(256, 4000000000, 4, "beta~4");
}
