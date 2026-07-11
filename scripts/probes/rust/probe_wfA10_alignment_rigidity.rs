// A10 rigidity check (#444): is the perfect half-alignment cos(A,B)=1 at the maximizer a
// STRUCTURAL forced rigidity, or an artifact? If forced, generic chaining is permanently void
// (coherent, not sub-Gaussian, increments). Test:
//  (1) cos(A,B) at the maximizer across MULTIPLE primes and betas (3.0, 4.0, 5.0).
//  (2) cos(A,B) at a RANDOM (non-maximizing) b -- if random b also has cos~1, alignment is a
//      trivial coset symmetry (then it carries no info); if random b has cos spread in [-1,1]
//      while ONLY the maximizer pins cos=1, alignment is the worst-case rigidity (the obstruction).
//  (3) the FORCED-ALIGNMENT explanation: b*(2n) is real-axis-aligned? compute arg(eta_{b*}(2n)).
//      The antipodal symmetry eta_{-b}=conj(eta_b) means the max can be taken on a real-positive
//      representative; within mu_{2n}=mu_n u zeta mu_n, if b* is chosen so eta over BOTH halves
//      is real-positive, cos=1 is forced. Report arg(A), arg(B) at the maximizer.
// build: rustc -O probe_wfA10_alignment_rigidity.rs -o /tmp/wfA10c
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
fn halfcos(argb:u64,prev_mu:&[u64],zeta:u64,p:u64)->(f64,f64,f64,f64,f64){
    let zeta_half:Vec<u64>=prev_mu.iter().map(|&x|((zeta as u128*x as u128)%p as u128) as u64).collect();
    let (ra,ia,na)=eta(argb,prev_mu,p); let (rb,ib,nb)=eta(argb,&zeta_half,p);
    let dotp=ra*rb+ia*ib; let cosab=if na>1e-9&&nb>1e-9{dotp/(na*nb)}else{0.0};
    (cosab, ia.atan2(ra), ib.atan2(rb), na, nb)
}
fn run(beta:f64, topmu:u32){
    let topn=1u64<<topmu; let modulus=1u64<<topmu;
    let target=(topn as f64).powf(beta) as u64;
    let p=find_prime_cong1(modulus, target.max(1<<20));
    let g=primitive_root(p);
    eprintln!("## beta_req={:.1}  p={}  beta_actual={:.3}",beta,p,(p as f64).ln()/(topn as f64).ln());
    // for each level (>=3), maximizer cos and 3 RANDOM-b cos
    let mut prev_mu_set:Vec<u64>=vec![]; let mut prev_n=0u64;
    let mut rng:u64=0x9e3779b97f4a7c15 ^ p;
    for mu in 2..=topmu {
        let n=1u64<<mu; let mun=mu_elems(p,g,n);
        let (mm,argb)=sweep(&mun,p,g,n);
        if prev_n*2==n {
            let hn=mpow(g,(p-1)/n,p); let zeta=hn;
            let (cmax,aA,aB,_,_)=halfcos(argb,&prev_mu_set,zeta,p);
            // 3 random b in F_p^*
            let mut rc:Vec<f64>=vec![];
            for _ in 0..200 { rng=rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let rb=1+(rng%(p-1)); let (cr,_,_,_,_)=halfcos(rb,&prev_mu_set,zeta,p); rc.push(cr); }
            rc.sort_by(|a,b|a.partial_cmp(b).unwrap());
            let rmed=rc[rc.len()/2]; let rmin=rc[0]; let rmax=rc[rc.len()-1];
            let nge=rc.iter().filter(|&&c|c>0.999).count();
            eprintln!("  n={:4} M={:7.3} cos@MAX={:9.6} argA={:+.3} argB={:+.3} | rand-b cos: med={:+.3} min={:+.3} max={:+.3} (#>.999 of 200: {})",
                n,mm,cmax,aA,aB,rmed,rmin,rmax,nge);
        }
        prev_mu_set=mun; prev_n=n;
    }
}
fn main(){
    for &beta in &[3.0f64,4.0,5.0] { run(beta, 6); } // top n=64 for speed across 3 betas
}
