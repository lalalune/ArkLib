// A10 anatomy (#444): WHY the tower-chaining entropy does NOT dissolve the sqrt(log) wall.
//
// The first A10 probe found: (i) the near-maximizer index set collapses to O(1) at large n
// (NMcount=2 = the maximizer + its conjugate), so the INDEX metric entropy along the tower IS
// bounded -- the chaining-entropy hope was numerically PLAUSIBLE on the index side. BUT
// (ii) the two doubling halves A=eta_b(mu_prev), B=eta_{zeta b}(mu_prev) at the maximizer are
// PERFECTLY phase-aligned (cos(A,B)=1.0000) at EVERY level. Perfect alignment is the OBSTRUCTION:
// a Gaussian/sub-Gaussian increment requires the halves to be roughly INDEPENDENT (cos~0,
// |A+B|^2 ~ |A|^2+|B|^2), which gives the chaining/floor scaling. Perfect alignment gives
// |A+B| = |A|+|B|, the COHERENT (deterministic-reinforcement) regime where the tower process is
// NOT sub-Gaussian and chaining provides NO entropy reduction over the union bound.
//
// THIS PROBE pins the anatomy decisively at deeper levels and a FRESH prime:
//  (1) per-level alignment cos(A,B) at the maximizer -- is it EXACTLY 1 (forced) or ~1 (incidental)?
//  (2) the half magnitudes |A|,|B| at the maximizer -- are they EQUAL (the worst case |A|=|B|=M(prev),
//      forcing M(2n)=2M(prev) exactly) or submaximal?
//  (3) the genuine per-level increment in the CHAINING sense: define the tower process
//      Y_mu = M(2^mu)^2 / 2^mu (the normalized energy at the worst frequency). Sub-Gaussian tower
//      <=> Y_mu - Y_{mu-1} BOUNDED with summable increments -> Y_mu = O(1)+O(#levels)... the floor
//      needs Y_mu = O(1) (M~sqrt n), the wall has Y_mu ~ log(p/2^mu) (M~sqrt(n log)).
//      Measure Y_mu directly and its increment.
//  (4) DECISIVE: the alignment is between eta_b over the EVEN powers vs ODD powers of h_{2n}.
//      Perfect alignment <=> eta_b(mu_n)[even half] and [odd half] have the SAME argument <=>
//      the worst b is the one for which the half-period arguments coincide. This is a RIGIDITY
//      (not randomness) -- the manifesto's "worst peak is DILATION-FIXED". Confirm by checking
//      whether the maximizer b*(2n) satisfies the alignment EXACTLY (cos=1 to machine eps) and
//      report how the half-magnitude RATIO |B|/|A| behaves (=1 forces the no-gain doubling).
//
// PRIZE-FAITHFUL: p PRIME, n=2^mu, n|p-1, beta~4, m=(p-1)/n>1, NEVER n=p-1.
// build: rustc -O probe_wfA10_alignment_anatomy.rs -o /tmp/wfA10b
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=&mut a; r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}
    let mut d=3u64;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}
    loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;
    while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}
    let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn eta(b:u64, mu:&[u64], p:u64)->(f64,f64,f64){
    let mut re=0.0f64; let mut im=0.0f64;
    for &x in mu { let t=((b as u128 * x as u128)%p as u128) as u64;
        let ang=2.0*PI*(t as f64)/(p as f64); re+=ang.cos(); im+=ang.sin(); }
    (re,im,(re*re+im*im).sqrt())
}
fn mu_elems(p:u64,g:u64,n:u64)->Vec<u64>{let h=mpow(g,(p-1)/n,p);(0..n).map(|j|mpow(h,j,p)).collect()}
fn sweep(mu:&[u64],p:u64,g:u64,n:u64)->(f64,u64){
    let m=(p-1)/n; let gn=mpow(g,n,p); let mut best=0.0f64; let mut argb=1u64; let mut b=1u64;
    for _ in 0..m { let (_,_,mag)=eta(b,mu,p); if mag>best{best=mag;argb=b;} b=((b as u128*gn as u128)%p as u128) as u64; }
    (best,argb)
}
fn main(){
    let levels:Vec<u32>=vec![2,3,4,5,6,7];
    let topmu=*levels.iter().max().unwrap(); let topn=1u64<<topmu;
    let modulus=1u64<<topmu;
    // fresh prime: start search higher than the previous run to avoid the same p
    let target=(topn as f64).powf(4.0) as u64;
    let p=find_prime_cong1(modulus, target.max(1<<20)+5_000_000);
    let g=primitive_root(p);
    eprintln!("# p={} g={} beta_top={:.3}",p,g,(p as f64).ln()/(topn as f64).ln());
    eprintln!("# mu  n     M(n)   Y=M^2/n   dY      cosAB(@max)   |A|     |B|    |B|/|A|  |A|+|B|  M(2n)  ratio");
    let mut prev_m=0.0f64; let mut prev_mu_set:Vec<u64>=vec![]; let mut prev_n=0u64; let mut prev_y=0.0f64;
    for (idx,&mu) in levels.iter().enumerate(){
        let n=1u64<<mu;
        let mun=mu_elems(p,g,n);
        let (mm,argb)=sweep(&mun,p,g,n);
        let y=mm*mm/(n as f64);
        if idx>0 && prev_n*2==n {
            // halves of mu_n at the level-2n maximizer argb: even powers = mu_prev, odd = zeta*mu_prev
            let hn=mpow(g,(p-1)/n,p); let zeta=hn;
            let half_a=&prev_mu_set;
            let zeta_half:Vec<u64>=half_a.iter().map(|&x|((zeta as u128*x as u128)%p as u128) as u64).collect();
            let (ra,ia,na)=eta(argb,half_a,p);
            let (rb,ib,nb)=eta(argb,&zeta_half,p);
            let dotp=ra*rb+ia*ib; let cosab=if na>1e-9&&nb>1e-9{dotp/(na*nb)}else{0.0};
            let sumab=na+nb;
            eprintln!("{:3} {:5} {:7.3} {:8.4} {:8.4}   {:9.6}  {:6.3} {:6.3} {:6.4} {:7.3} {:7.3} {:6.4}",
                mu,n,mm,y,y-prev_y,cosab,na,nb,nb/na,sumab,mm,mm/prev_m);
        } else {
            eprintln!("{:3} {:5} {:7.3} {:8.4}     --          --        --     --     --      --      --    --",mu,n,mm,y);
        }
        prev_m=mm; prev_mu_set=mun; prev_n=n; prev_y=y;
    }
    let _=prev_m;
    eprintln!("# floor <=> Y bounded (dY->0); wall <=> Y grows ~log(p/n). cosAB=1 & |B|/|A|=1 => M(2n)=2M(n) (NO chaining gain).");
}
