// A10 (#444): chaining / metric entropy of the DILATION-TOWER-structured period process.
//
// MANIFESTO ROUTE 54 (never attacked): the worst-u0 excess is the sup of a Gaussian-like
// process; generic chaining (Talagrand majorizing measures) bounds it by the ENTROPY of the
// index metric. Plain chaining over the dual frequency c in Z/m is FLAT => union bound =>
// sqrt(log m) (=W4, the prior I031/Salem-Zygmund self-refutation). THE A10 DISTINCTION: index
// the process by the DILATION TOWER (vary n=2^mu up the 2-adic tower), exploiting the in-tree
// L^2-doubling self-similarity mu_{2n} = mu_n u zeta*mu_n. IF the tower-coherent metric entropy
// is o(log q), the sqrt(log) is ABSORBED and the floor M <= C sqrt(n) follows.
//
// eta_b = sum_{x in mu_n} e_p(b x),  M(n) = max_{b!=0} |eta_b|,  p=1 mod n, beta=log_n p ~ 4.
//
// THE PRECISE TEST (the one place the catalog says the barrier could DISSOLVE):
//
// (A) TOWER-COHERENCE OF THE MAXIMIZER. Let b*(n) be an argmax for mu_n. Under the doubling
//     mu_{2n}=mu_n u zeta*mu_n, eta_b(2n) = eta_b(n) + eta_{zeta b}(n) [restricting the
//     character to the two halves]. We test: is b*(2n) the SAME coset class (mod the doubling)
//     as b*(n)? i.e. does the worst frequency THREAD coherently up the tower (entropy O(1) along
//     the thread) or jump to a fresh, uncorrelated coset (fresh entropy log m per level)?
//     Measure: overlap_n = | <eta(n) at b*(2n)> | vs M(n) -- how close the level-(n) value at the
//     level-(2n) maximizer is to the level-n max. coherence = (value at b*(2n)) / M(n).
//
// (B) INCREMENTAL METRIC ENTROPY ALONG THE TOWER. The Dudley/gamma_2 floor needs the entropy
//     integral of the index. The tower has mu levels; if each contributes BOUNDED log-covering
//     (a self-similar fixed number of near-maximizer clusters), the total entropy is O(mu) =
//     O(log log q) << log q and the floor follows. If each level's near-maximizer set has size
//     growing like the level's coset count, the entropy is Theta(log m) = Theta(log q) (wall).
//     Measure at each level n: NMcount(n) = # frequencies c with |eta_c| >= (1-tau) M(n)
//     (the near-maximizer / top-cluster count, tau small), and its growth in n.
//
// (C) THE TELESCOPE TEST (decisive). The doubling gives eta_b(2n) = A + B with A=eta_b(n),
//     B=eta_{zeta b}(n) (each |.| <= M(n)). M(2n) = max |A+B|. If A,B at the maximizer are
//     PHASE-ALIGNED (the #407 observation cos~1), then M(2n) ~ |A|+|B| ~ 2 M(n) (NO chaining
//     gain, ratio -> 2, this is the refuted sqrt2-descent direction). If they are INDEPENDENT
//     (sub-Gaussian), M(2n)^2 ~ M(n)^2 + (fresh fluctuation) and the increment is sub-Gaussian
//     => chaining over the tower gives M(n)^2 ~ n * (accumulated increments) ~ n * sum_levels.
//     Measure: align_n = cos(angle(A,B)) at the level-2n maximizer, and the per-level
//     increment ratio R_n = M(2n)/M(n). Floor (sub-Gaussian tower) <=> R_n -> ~1 (sqrt(1+o(1)));
//     Wall (aligned/coherent) <=> R_n bounded away above 1 by a sqrt(log)-driven amount.
//
// PRIZE-FAITHFUL: p PRIME, n=2^mu, n|p-1, beta=log_n(p)~4 (p~n^4), m=(p-1)/n>1, NEVER n=p-1.
//
// build: rustc -O probe_wfA10_tower_chaining_entropy.rs -o /tmp/wfA10
use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=a;a=0;let _=a; r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}
    let mut d=3u64;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}
    loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;
    while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}
    let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// eta_b for b given, mu_n given as element list. returns (re, im, |.|)
fn eta(b:u64, mu:&[u64], p:u64)->(f64,f64,f64){
    let mut re=0.0f64; let mut im=0.0f64;
    for &x in mu {
        let t=((b as u128 * x as u128) % p as u128) as u64;
        let ang=2.0*PI*(t as f64)/(p as f64);
        re+=ang.cos(); im+=ang.sin();
    }
    (re,im,(re*re+im*im).sqrt())
}

// full sweep over coset reps b=g^j, j=0..m-1: returns (M, argmax_b, all (b,|eta|) for NM analysis)
fn sweep(mu:&[u64], p:u64, g:u64, n:u64)->(f64,u64,Vec<(u64,f64)>){
    let m=(p-1)/n;
    let gn=mpow(g,n,p);
    let mut best=0.0f64; let mut argb=1u64;
    let mut vals:Vec<(u64,f64)>=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let (_,_,mag)=eta(b,mu,p);
        vals.push((b,mag));
        if mag>best{best=mag;argb=b;}
        b=((b as u128 * gn as u128)%p as u128) as u64;
    }
    (best,argb,vals)
}

fn mu_elems(p:u64,g:u64,n:u64)->Vec<u64>{
    let h=mpow(g,(p-1)/n,p);
    (0..n).map(|j|mpow(h,j,p)).collect()
}

fn main(){
    // tower of levels n=2^mu, mu=2..=8 (n=4..256), each at a prize-faithful beta~4 prime.
    // KEY: use ONE prime p chosen so that ALL tower levels n=4..N divide p-1 (i.e. 2^MU | p-1),
    // so the doubling tower is genuinely nested in F_p^*. Choose p ~ N^4 (beta=4 at the TOP level).
    let levels:Vec<u32>=vec![2,3,4,5,6,7]; // mu; top n=2^7=128 (full exact sweep tractable at beta=4)
    let topmu=*levels.iter().max().unwrap();
    let topn=1u64<<topmu;
    // beta=4 at top: p ~ topn^4. require 2^topmu | p-1.
    let target=(topn as f64).powf(4.0) as u64;
    // find prime p = 1 mod 2^topmu with p ~ target (so all sub-levels nest).
    let modulus=1u64<<topmu;
    let p=find_prime_cong1(modulus, target.max(1<<20));
    let g=primitive_root(p);
    let beta_top=(p as f64).ln()/(topn as f64).ln();
    eprintln!("# p={} g={} top n={} beta_top={:.3}  (2^{} | p-1: {})",p,g,topn,beta_top,topmu,(p-1)%modulus==0);
    eprintln!("# mu  n    M(n)  M/sqrtn  C=M/sqrt(n*ln(p/n))  R=M(2n)/M(n)  coher(b*2n@n/Mn)  align(cosAB)  NMcount  log2(NM)");

    // precompute per-level: mu elems, M, argmax. NMcount tau=0.02.
    let tau=0.02f64;
    let mut prev_m=0.0f64; let mut prev_argb=0u64; let mut prev_mu:Vec<u64>=vec![];
    let mut prev_n=0u64;
    let mut nm_logs:Vec<f64>=vec![];
    for (idx,&mu) in levels.iter().enumerate(){
        let n=1u64<<mu;
        let mun=mu_elems(p,g,n);
        let (mm,argb,vals)=sweep(&mun,p,g,n);
        // NM count: # coset reps within (1-tau) of M
        let thr=(1.0-tau)*mm;
        let nmcount=vals.iter().filter(|&&(_,v)|v>=thr).count();
        let logn_nm=(nmcount as f64).ln()/2.0f64.ln();
        nm_logs.push(logn_nm);
        let c=mm/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
        // tower coherence / telescope vs PREVIOUS level (n=2n means current is double of prev)
        let (rstr, coher_str, align_str) = if idx>0 && prev_n*2==n {
            // R = M(n)/M(prev_n)  (current is the doubling of prev)
            let r = mm/prev_m;
            // coherence: value of eta at level prev_n evaluated at CURRENT maximizer argb
            // (b*(2n) maps down: does the prev level already see a large value there?)
            let (_,_,prevval_at_curarg)=eta(argb,&prev_mu,p);
            let coher = prevval_at_curarg/prev_m;
            // alignment of the two halves A=eta_b(prev), B=eta_{zeta b}(prev) at b=argb (current max)
            // doubling: mu_n = mu_prev u zeta*mu_prev, zeta = generator-of-mu_n-not-in-mu_prev
            // zeta = h_n^1 where h_n = g^{(p-1)/n}; mu_prev = {h_n^{2k}}, zeta*mu_prev={h_n^{2k+1}}
            let hn=mpow(g,(p-1)/n,p);
            let zeta=hn; // h_n itself is the "odd" coset rep generator
            let half_a=&prev_mu; // = {h_n^{2k}} = mu_prev (h_prev = h_n^2)
            let zeta_half:Vec<u64>=half_a.iter().map(|&x|((zeta as u128 * x as u128)%p as u128) as u64).collect();
            let (ra,ia,_)=eta(argb,half_a,p);
            let (rb,ib,_)=eta(argb,&zeta_half,p);
            let dotp=ra*rb+ia*ib;
            let na=(ra*ra+ia*ia).sqrt(); let nb=(rb*rb+ib*ib).sqrt();
            let cosab= if na>1e-9 && nb>1e-9 { dotp/(na*nb) } else { 0.0 };
            (format!("{:6.4}",r), format!("{:7.4}",coher), format!("{:7.4}",cosab))
        } else {
            ("  --  ".to_string()," --   ".to_string()," --   ".to_string())
        };
        eprintln!("{:3} {:5} {:7.3} {:7.4} {:8.4}        {}        {}       {}      {:4}    {:6.3}",
            mu,n,mm,mm/(n as f64).sqrt(),c,rstr,coher_str,align_str,nmcount,logn_nm);
        prev_m=mm; prev_argb=argb; prev_mu=mun; prev_n=n;
    }
    let _=prev_argb;
    // ENTROPY VERDICT: total tower entropy = sum of per-level incremental log(NM).
    // If self-similar/bounded NM => sum ~ (#levels)*O(1) = O(log log q). If NM ~ m per level => Theta(log q).
    let total_nm_entropy:f64=nm_logs.iter().sum();
    let nlevels=nm_logs.len() as f64;
    let log2_m=((p-1) as f64/(topn as f64)).ln()/2.0f64.ln();
    eprintln!("# --- ENTROPY VERDICT ---");
    eprintln!("# sum_levels log2(NMcount) = {:.3}  over {} levels (avg {:.3}/level)",total_nm_entropy,nm_logs.len(),total_nm_entropy/nlevels);
    eprintln!("# log2(m) at top level = {:.3}  (union-bound/W4 cost)",log2_m);
    eprintln!("# floor needs per-level NM-entropy BOUNDED (O(1)); wall if NM-entropy ~ log2(m_level)");
}
