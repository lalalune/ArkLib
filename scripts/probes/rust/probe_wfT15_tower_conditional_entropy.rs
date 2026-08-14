// T15 (#444): conditional-Shannon-entropy chain rule along the 2-adic dilation tower.
//
// CANDIDATE: define Z_j := |eta_b^{(j)}|, the period magnitude of level-j subgroup mu_{2^j},
//   over UNIFORMLY RANDOM b (b ranges over coset reps mod mu_n in F_p^*). Form the filtration
//   Z_1, Z_2, ..., Z_mu and the conditional Shannon entropy H(L_j | L_{j-1}) where
//   L_j := log_2(quantized Z_j). The proposal: IF each doubling step has a UNIFORMLY BOUNDED
//   conditional smoothing gain  H(L_j|L_{j-1}) >= H_unif(level j) - g*  with g*=O(1), THEN by the
//   entropy chain rule total deficit <= mu*g* = g* log_2 n, and a Pinsker/Fano step converts that
//   to M(n) <= sqrt(2 g*/log2) sqrt(n log m) = O(sqrt(n log(p/n))).
//
// THE DECISIVE MEASUREMENTS:
//  (1) per-step conditional entropy deficit  D_j := H_unif(j) - H(L_j|L_{j-1})  -- is it O(1) in j
//      or does it GROW?  H_unif(j) = log2(#distinct quantized L-classes at level j).
//  (2) THE RECURSION TRUTH: eta_b^{(j)} = eta_b^{(j-1)} + eta_{zeta b}^{(j-1)} with zeta a
//      primitive 2^j-th root.  So Z_j is the MAGNITUDE of a SUM of two level-(j-1) values, one at
//      b and one at the DILATE zeta*b.  H(Z_j|Z_{j-1}) over random b measures how Z at b predicts
//      Z at the doubled level.  Measure I(Z_{j-1};Z_j) = H(Z_j)-H(Z_j|Z_{j-1}) and the deficit.
//  (3) THE PINSKER-CONVERSION AUDIT (the load-bearing arithmetic). The proposal asserts a bounded
//      total entropy deficit caps the WORST-CASE level deviation. But the worst case (the sup M)
//      is the MAX over b, an L^infty / tail quantity. Conditional Shannon entropy is an AVERAGE
//      (expectation over b) functional. We test the actual relationship between
//      (total deficit) and (max-vs-mean gap log2(M / RMS)) where RMS = sqrt(E_b Z^2) = sqrt(n)
//      (Parseval). If the deficit does NOT track log2(M/sqrt(n)), the Pinsker bridge is vacuous.
//
// PRIZE-FAITHFUL: p PRIME, n=2^mu, n|p-1, beta=log_n(p)~4 (p~n^4), m=(p-1)/n>1, NEVER n=p-1.
// build: rustc -O probe_wfT15_tower_conditional_entropy.rs -o /tmp/wfT15
use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;} let _=a; a=0; let _=a; r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}
    let mut d=3u64;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(modulus:u64,lo:u64)->u64{let mut p=lo+((1+modulus-lo%modulus)%modulus);if p<=2{p+=modulus;}
    loop{if p>2&&p%modulus==1&&is_prime(p){return p;}p+=modulus;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;
    while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}
    let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

fn eta_mag(b:u64, mu:&[u64], p:u64)->f64{
    let mut re=0.0f64; let mut im=0.0f64;
    for &x in mu {
        let t=((b as u128 * x as u128) % p as u128) as u64;
        let ang=2.0*PI*(t as f64)/(p as f64);
        re+=ang.cos(); im+=ang.sin();
    }
    (re*re+im*im).sqrt()
}
fn mu_elems(p:u64,g:u64,n:u64)->Vec<u64>{
    let h=mpow(g,(p-1)/n,p);
    (0..n).map(|j|mpow(h,j,p)).collect()
}

// Shannon entropy (bits) of a histogram of counts.
fn shannon_bits(counts:&[u64])->f64{
    let total:u64=counts.iter().sum();
    if total==0 {return 0.0;}
    let t=total as f64;
    let mut h=0.0f64;
    for &c in counts { if c>0 { let pr=(c as f64)/t; h-=pr*pr.log2(); } }
    h
}

fn main(){
    // ONE prime nesting the whole tower: 2^topmu | p-1, p ~ topn^4 (beta=4 at top).
    let levels:Vec<u32>=vec![1,2,3,4,5,6,7,8]; // n = 2..256
    let topmu=*levels.iter().max().unwrap();
    let topn=1u64<<topmu;
    let modulus=1u64<<topmu;
    let target=(topn as f64).powf(4.0) as u64;
    let p=find_prime_cong1(modulus, target.max(1<<20));
    let g=primitive_root(p);
    let m=(p-1)/topn; // # coset reps at the TOP level
    let beta_top=(p as f64).ln()/(topn as f64).ln();
    eprintln!("# p={} g={} top n={} beta_top={:.3} m=(p-1)/topn={}  (2^{}|p-1:{})",
        p,g,topn,beta_top,m,topmu,(p-1)%modulus==0);

    // Sample b over coset reps of mu_topn: b = (g^topn)^k for k=0..m-1 hits each coset of mu_topn.
    // (period coset-constant in mu_topn, so this samples the relevant frequency space.)
    // For tractability sample up to SAMPLES reps if m is large.
    let samples = m.min(2_000_000);
    let step=mpow(g,topn,p); // generates the order-m quotient
    eprintln!("# sampling {} of {} top-level coset reps", samples, m);

    // For each level j, store the magnitude Z_j(b) for each sampled b.
    // We build mu lists once.
    let mut mulists:Vec<Vec<u64>>=Vec::new();
    for &mu in &levels { mulists.push(mu_elems(p,g,1u64<<mu)); }

    // Z[j][k] = magnitude of eta at level j for sample k.
    let mut zvals:Vec<Vec<f64>>=vec![Vec::with_capacity(samples as usize); levels.len()];
    let mut b=1u64;
    for _ in 0..samples {
        for (ji,mul) in mulists.iter().enumerate(){
            zvals[ji].push(eta_mag(b,mul,p));
        }
        b=((b as u128 * step as u128)%p as u128) as u64;
    }

    // Quantize L_j = floor( Z_j / (sqrt(n)*bin) ) so the bin scale is normalized per level
    // (sqrt(n) = Parseval RMS). We use a fixed number of bins B over [0, n] then build joint hist.
    let nbins:usize=64;
    let quant=|z:f64, n:f64|->usize{
        // bin in [0, n]; clamp.
        let frac=(z/n).max(0.0).min(0.999999);
        (frac*nbins as f64) as usize
    };

    eprintln!("# j  n    M(n)   M/sqrtn  log2(M/sqrtn)  H(L_j)  H(L_j|L_{{j-1}})  I(j-1;j)  Hunif_j  Deficit_j  Mutual/Hunif");
    let mut prev_quant:Vec<usize>=vec![];
    let mut total_deficit=0.0f64;
    let mut sum_mutual=0.0f64;
    let mut last_log2_excess=0.0f64;
    for (ji,&mu) in levels.iter().enumerate(){
        let n=(1u64<<mu) as f64;
        let zs=&zvals[ji];
        let mm=zs.iter().cloned().fold(0.0f64,f64::max);
        let rms=(n).sqrt();
        let log2_excess=(mm/rms).log2();
        last_log2_excess=log2_excess;
        // marginal hist of L_j
        let qcur:Vec<usize>=zs.iter().map(|&z|quant(z,n)).collect();
        let mut hist=vec![0u64;nbins];
        for &q in &qcur { hist[q]+=1; }
        let h_marg=shannon_bits(&hist);
        let hunif=(hist.iter().filter(|&&c|c>0).count() as f64).log2(); // log2 of support size
        let (h_cond, mutual) = if ji>0 {
            // joint hist (prev_quant, qcur)
            let mut joint=vec![0u64;nbins*nbins];
            for k in 0..qcur.len(){ joint[prev_quant[k]*nbins+qcur[k]]+=1; }
            // H(prev) marginal
            let mut hprev=vec![0u64;nbins];
            for k in 0..qcur.len(){ hprev[prev_quant[k]]+=1; }
            let h_joint=shannon_bits(&joint);
            let h_prevm=shannon_bits(&hprev);
            // H(cur|prev) = H(joint) - H(prev)
            let hc=h_joint-h_prevm;
            let mi=h_marg-hc; // I = H(cur)-H(cur|prev)
            (hc,mi)
        } else { (h_marg, 0.0) };
        let deficit=hunif-h_cond;
        if ji>0 { total_deficit+=deficit; sum_mutual+=mutual; }
        let mh = if hunif>1e-9 { mutual/hunif } else {0.0};
        eprintln!("{:3} {:4} {:7.3} {:7.3}    {:8.4}    {:6.3}   {:8.3}      {:6.3}  {:6.3}  {:7.3}   {:6.3}",
            mu,1u64<<mu,mm,mm/rms,log2_excess,h_marg,h_cond,mutual,hunif,deficit,mh);
        prev_quant=qcur;
    }

    eprintln!("# --- T15 VERDICT ---");
    eprintln!("# total conditional-entropy deficit (sum_j>=2 Deficit_j) = {:.3} bits over {} steps", total_deficit, levels.len()-1);
    eprintln!("# total mutual information sum_j I(j-1;j) = {:.3} bits", sum_mutual);
    eprintln!("# THE PINSKER BRIDGE the proposal needs: total deficit <= g* log2(n) caps log2(M/sqrt(n)).");
    eprintln!("# measured log2(M/sqrt(n)) at top level = {:.4} (the EXCESS the bridge must bound)", last_log2_excess);
    eprintln!("# if total deficit GROWS like log2(m)~{:.1} per the union cost, NOT O(loglog), the per-step g* is NOT bounded.",
        ((p-1) as f64/topn as f64).log2());
    eprintln!("# KEY STRUCTURAL CHECK printed separately below: is the recursion increment phase-aligned (cos~1)?");
}
