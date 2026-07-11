// probe_wfT24_affine_koopman_density.rs
// ATTACK T24 (architect G5-4): "Sarnak-Xue DENSITY (multiplicity count) of the affine Koopman
//   operator caps the number of non-tempered frequencies, not the spectral edge."
//
// CLAIM under test:
//   Let U = Koopman operator of the affine ax+b action on L^2(F_p), b ranging over translations.
//   The matrix coefficients <U_b xi, xi> = eta_b. A frequency b is "tau-non-tempered" if
//   |eta_b| > t*sqrt(n). CONJECTURE (affine Sarnak-Xue density):
//       #{ b != 0 : |eta_b| >= n^{1/2+s} } <= p^{1-2s+o(1)}   for 0<=s<=1/2,
//   and in sharp log-refined form  #{|eta_b|>=t*sqrt(n)} <= m*e^{-(1-o(1)) t^2},  giving
//       M(n) <= sqrt(2 n log(p/n)).
//
// THREE prize-faithful measurements (n=2^mu, p PRIME, n|p-1, m=(p-1)/n>1, p>>n^3, NEVER n=p-1;
//   beta = log_p(n) ~ 0.25 -> p ~ n^4 wherever tractable):
//
//  (M0) KOOPMAN = ABELIAN.  The affine Koopman operator U_b is the translation-by-b operator on
//       L^2(F_p): (U_b f)(x) = f(x - b)?  No -- the relevant matrix coefficient for the period is
//       the *additive-character* coefficient.  Concretely the cyclic vector xi = (indicator of mu_n)
//       gives <U_b xi, xi> over the additive translation = the autocorrelation of mu_n, whose
//       Fourier transform at frequency c is |eta_c|^2.  The decomposition of U over the AFFINE
//       principal series still has, as its abelian (F_p-translation) matrix coefficients, exactly
//       the numbers eta_b.  We VERIFY: the diagonal spectral content the density bound counts is
//       {eta_b}, identical to the abelian Cayley eigenvalues.  (Verified by: the affine group's
//       principal series pi_chi restricted to the translation subgroup F_p decomposes as the
//       regular rep of F_p, whose matrix coefficients are the additive characters; pairing the
//       period vector picks out eta_b.  The "count of non-tempered frequencies" is literally a
//       count over b in F_p^* of |eta_b|, the SAME multiset C12 already measured.)
//       => we just confirm the multiset {|eta_b|} is what any honest "density count" must use.
//
//  (M1) DENSITY EXPONENT.  Measure  N(s) := #{ b != 0 : |eta_b| >= n^{1/2+s} }  over a transversal
//       of mu_n (m coset reps; each is one distinct eigenvalue with graph multiplicity n).
//       Compare the empirical exponent  log_p( N(s) * n )  [the count over ALL p-1 nonzero freqs]
//       to the CLAIMED Sarnak-Xue exponent  1 - 2s.  Report for a grid of s.
//
//  (M2) PARSEVAL CEILING (the reduction).  Parseval/trace gives EXACTLY
//          sum_{b!=0} |eta_b|^{2r} = p * E_r(mu_n) - n^{2r}        (E_r = rEnergy)
//       and the level-set <-> moment duality (Markov):
//          N(s) * (n^{1/2+s})^{2r}  <=  sum_b |eta_b|^{2r}  =>  N(s) <= (sum/ (n^{(1/2+s)2r})).
//       The BEST density bound obtainable from the period spectrum (2nd-order arithmetic + all
//       higher moments) is THIS Markov bound.  We compute, at each s, the Markov density bound
//       (min over r) and compare to the claimed p^{1-2s}.  KEY TEST: does the affine "Plancherel
//       weight" give ANY count strictly below the Markov/Parseval bound?  If the measured N(s)
//       and the Markov bound TRACK each other (and both = the moment ladder), the density count
//       is Parseval = F1, and integrating it back gives M <= sqrt(2 n log(p/n)) ONLY IF the
//       energy E_r <= (2r-1)!! n^r transfer holds -- i.e. density IS the char-p transfer, not new.
//
//  (M3) THE INTEGRATION IDENTITY.  Show that "density integrated against Parseval mass" reproduces
//       the moment bound bit-for-bit:  M^{2r} <= sum_b |eta_b|^{2r} (the r=top term dominates the
//       level-set sum).  So the sharp log-refined density  #{|eta_b|>=t sqrt n} <= m e^{-t^2}
//       is EQUIVALENT to the sub-Gaussian moment law E_r <= (2r-1)!! n^r (Gaussian tail <-> Wick
//       moments).  => density-form and edge/moment-form are the SAME open statement (the transfer).
//
// build: rustc -O probe_wfT24_affine_koopman_density.rs -o /tmp/wfT24 && /tmp/wfT24
use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128 % p as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
// p prime, n | p-1, m=(p-1)/n>1, p as close to n^beta as we can while keeping the full b-sweep tractable
fn find_p(n:u64, beta:f64)->u64{
    let target = (n as f64).powf(beta) as u64;
    let mut p = (target/n + 1)*n + 1;
    loop{ if is_prime(p) && (p-1)%n==0 && (p-1)/n>1 { return p; } p+=n; }
}

fn main(){
    println!("{}","=".repeat(82));
    println!("T24 affine-Koopman Sarnak-Xue DENSITY probe (prize-faithful, beta->4 where tractable)");
    println!("{}","=".repeat(82));
    // n=2^mu; pick p ~ n^beta. Full b-sweep is O(p*n); keep p <= ~3e5.
    let cells: Vec<(u64,f64)> = vec![(8,4.0),(16,4.0),(32,3.6),(64,3.0),(128,2.6),(256,2.3)];
    for (n,beta) in cells {
        let p = find_p(n,beta);
        if (p as u128)*(n as u128) > 60_000_000u128 { println!("\n n={} p={} skip (sweep too big)",n,p); continue; }
        let m=(p-1)/n;
        let beta_eff = (n as f64).ln()/(p as f64).ln();
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        // distinct eigenvalues = one per coset; coset reps b = g^j, j=0..m-1 (transversal of mu_n)
        let gn=mpow(g,n,p);
        let mut mags=Vec::with_capacity(m as usize);
        let mut b=1u64;
        let mut max_imag=0.0f64;
        for _ in 0..m {
            let mut re=0.0f64; let mut im=0.0f64;
            for &x in &mu {
                let t=((b as u128*x as u128)%p as u128) as u64;
                let ang=2.0*PI*(t as f64)/(p as f64);
                re+=ang.cos(); im+=ang.sin();
            }
            if im.abs()>max_imag{max_imag=im.abs();}
            mags.push((re*re+im*im).sqrt());
            b=(b as u128*gn as u128 %p as u128) as u64;
        }
        mags.sort_by(|a,c|c.partial_cmp(a).unwrap()); // descending
        let mm=mags[0];
        let sqn=(n as f64).sqrt();
        let bgk=( (n as f64) * (p as f64/n as f64).ln() ).sqrt();
        println!("\n--- n={} (mu={})  p={}  m={}  beta_eff={:.3} ---",n,(n as f64).log2() as u32,p,m,beta_eff);
        println!("  M=max|eta|={:.4}  M/sqrt(n)={:.4}  BGK sqrt(n log(p/n))={:.4}  C=M/BGK={:.4}",
                 mm, mm/sqn, bgk, mm/bgk);
        println!("  (M0) max|Im eta_b|={:.2e} (eta REAL for n even -> abelian Cayley spectrum confirmed)",max_imag);

        // (M1) density exponent N(s) over ALL p-1 nonzero freqs (= m-coset-count * n graph mult)
        println!("  (M1) DENSITY EXPONENT  N(s)=#{{b!=0:|eta|>=n^(1/2+s)}}  vs claimed 1-2s:");
        println!("       s    | thresh n^(1/2+s) | N(s)(all freqs) | emp_exp=log_p(N) | claim 1-2s | Markov-min");
        let sgrid=[0.0f64,0.05,0.10,0.15,0.20,0.25,0.30];
        for &s in &sgrid {
            let thr=(n as f64).powf(0.5+s);
            // count over coset reps, multiply by n (graph mult) for total over F_p^*
            let cnt_coset = mags.iter().filter(|&&v| v>=thr).count() as u64;
            let n_all = cnt_coset.saturating_mul(n);
            let emp_exp = if n_all>0 {(n_all as f64).ln()/(p as f64).ln()} else {f64::NEG_INFINITY};
            // Markov density bound from moments: N <= (sum_b|eta|^{2r})/thr^{2r}, min over r
            // sum over ALL freqs = n * sum_coset |eta|^{2r}
            let mut markov_min=f64::INFINITY;
            for r in 1..=10u32 {
                let mut sm=0.0f64;
                for &v in &mags { sm += v.powi(2*r as i32); }
                sm *= n as f64; // graph mult
                let bnd = sm / thr.powi(2*r as i32);
                if bnd<markov_min{markov_min=bnd;}
            }
            let markov_exp = if markov_min.is_finite() && markov_min>0.0 {markov_min.ln()/(p as f64).ln()} else {f64::NEG_INFINITY};
            println!("       {:.2} | {:14.2} | {:14} | {:13.4} | {:9.4} | {:.4} (exp {:.3})",
                     s, thr, n_all, emp_exp, 1.0-2.0*s, markov_min, markov_exp);
        }

        // (M2)/(M3) integration identity: does Markov density reproduce the moment bound for M?
        // M^{2r} <= sum_b|eta|^{2r}; the level-set sum is dominated by the top term.
        // Compare best moment bound (sum_coset|eta|^{2r})^{1/2r} [coset = m terms, no graph-mult inflation]
        // to M and BGK.  Also the SHARP density <-> sub-Gaussian: K_eff = (E_r/Wick)^{1/r}.
        println!("  (M2/M3) MOMENT LADDER (the Parseval ceiling the density count obeys):");
        println!("       r | (sum_coset|eta|^2r)^(1/2r) | K_eff=(E_r/Wick)^(1/r) | M | BGK");
        let mut best_mom=f64::INFINITY;
        for r in 1..=((m as f64).ln() as u32 + 3).max(4) {
            let mut sm=0.0f64;
            for &v in &mags { sm += v.powi(2*r as i32); }
            let mom = sm.powf(1.0/(2.0*r as f64));
            best_mom=best_mom.min(mom);
            // E_r(mu_n) = (sum over ALL p freqs of eta^{2r})/p = (n*(sum_coset) + n^{2r})/p
            let er = ((n as f64)*sm + (n as f64).powi(2*r as i32))/(p as f64);
            // Wick = (2r-1)!! n^r
            let mut wick=1.0f64; for k in 0..r { wick *= (2*k+1) as f64; } wick *= (n as f64).powi(r as i32);
            let keff = (er/wick).powf(1.0/r as f64);
            if r<=8 {
                println!("       {:2} | {:24.4} | {:20.4} | {:.4} | {:.4}", r, mom, keff, mm, bgk);
            }
        }
        println!("       best moment bound min_r (sum_coset)^(1/2r) = {:.4}   M={:.4}  BGK={:.4}", best_mom, mm, bgk);
    }
    println!("\n{}","=".repeat(82));
    println!("VERDICT SWITCHES:");
    println!("  - (M0) eta REAL & = abelian Cayley eigenvalues -> 'affine Koopman' wrapping is cosmetic.");
    println!("  - (M1) if empirical N(s) exponent TRACKS the Markov-min exponent (both governed by");
    println!("         sum_b|eta|^2r) -> the density count IS Parseval (F1), no Plancherel improvement.");
    println!("  - (M2/M3) if best moment bound = M's controlling quantity and K_eff stays FLAT ~0.64,");
    println!("         the sharp density (Gaussian tail) <=> the char-p energy transfer E_r<=(2r-1)!!n^r.");
    println!("         => density-form REDUCES to the SAME open transfer; not a new lever.");
    println!("{}","=".repeat(82));
}
