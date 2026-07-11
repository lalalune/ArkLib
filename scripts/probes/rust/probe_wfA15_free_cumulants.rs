// probe_wfA15_free_cumulants.rs  (CRITIC angle A15: FREE PROBABILITY of the dilation-trace period family)
//
// CONTEXT / WHY THIS IS NOT A01..A14, NOT C12-SX, NOT REFUTED:
//   The period family eta_b = sum_{x in mu_n} e_p(b x) are the eigenvalues of the SYMMETRIC abelian
//   Cayley graph A = Cay(F_p, mu_n) (n=2^mu | p-1, even so mu_n contains -1 => A symmetric, eta_b real).
//   The empirical spectral distribution nu = (1/p) sum_{b in F_p} delta_{eta_b} has moments
//        m_r = (1/p) [ n^r  +  n * sum_{c coset reps} eta_c^r ]
//   (eta_0 = n once; the m=(p-1)/n nontrivial coset values each carry graph multiplicity n).
//   The FREE-PROBABILITY conjecture (E24 in deltastar-444-fifty-novel-directions, FLAGGED "never done"):
//   under the dilation trace the periods are FREELY (not classically) independent, so nu is asymptotically
//   SEMICIRCULAR of radius 2 sqrt(n): equivalently the FREE CUMULANTS kappa_r (moment<->free-cumulant
//   Speicher NC-partition inversion) vanish for r>2 up to a defect kappa_r <= n^{-1}. If true the spectral
//   support edge = 2 sqrt(n) + defect = NEAR-RAMANUJAN, closing the wall. If kappa_r GROW with r the
//   bulk is non-semicircular and free probability gives NO edge gain (the higher free cumulants ARE the
//   BGK content, conservation-law collapse).
//
// THE DECISIVE MEASUREMENT (never computed): the FREE CUMULANTS kappa_2..kappa_{2R} of the EXACT
// char-p empirical period distribution at PRIZE SCALE beta = log_n p = 4 (p ~ n^4, p prime, n|p-1,
// m=(p-1)/n > 1). Speicher recursion:  m_r = sum_{pi in NC(r)} prod_{block} kappa_{|block|}.
// We invert it via the standard recurrence over the FIRST block containing element 1:
//        m_r = sum_{s=1}^{r} kappa_s * sum over the (r-s) remaining points split into the
//              intervals cut by the s-block, i.e.  m_r = sum_{s} kappa_s * [coeff], using the
//              well-known NC recurrence  m_r = sum_{s=1}^{r} kappa_s * B_{r,s}  where
//              B_{r,s} = sum over compositions of (r-s) into s nonneg parts of prod m_{parts}.
// We use the clean recursive form via the "free moment-cumulant" generating identity in finite form.
//
// VERDICT SWITCHES (printed):
//   * if kappa_4, kappa_6,... -> 0 (relative to kappa_2^{r/2}) as n grows  => SEMICIRCLE => edge 2sqrt(n) => GAIN
//   * if free cumulants STAY O(1)-of-semicircle or GROW                    => non-semicircular bulk => NO free edge
//   * the free max (edge of support) for a measure with these free cumulants: compare to actual M.

use std::f64::consts::PI;

fn mpow(mut _a:u64, mut e:u64, p:u64)->u64{let mut r:u128=1;let mut a2=_a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3u64;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p%n!=1{p=((p/n)+1)*n+1;}loop{if p>2 && p%n==1 && (p-1)/n>1 && is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// exact-ish period magnitudes; we need REAL eta (symmetric set => real). Compute Re only (Im ~ 0 to fp tol).
fn coset_periods(n:u64, p:u64)->Vec<f64>{
    let g=primitive_root(p);
    let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let gn=mpow(g,n,p);
    let mut vals=Vec::with_capacity(m as usize);
    let mut b=1u64;
    let invp = 1.0/(p as f64);
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=((b as u128 * x as u128)%(p as u128)) as u64;
            let ang=2.0*PI*(t as f64)*invp;
            re+=ang.cos(); im+=ang.sin();
        }
        // symmetric set => eta_b is real; record Re (im is numerical noise)
        let _=im;
        vals.push(re);
        b=((b as u128 * gn as u128)%(p as u128)) as u64;
    }
    vals
}

// moments of the FULL empirical spectral distribution nu = (1/p)[ delta_n + n * sum_c delta_{eta_c} ]
fn moments(n:u64, p:u64, coset:&[f64], rmax:usize)->Vec<f64>{
    let nf=n as f64; let pf=p as f64;
    let mut m=vec![0.0f64; rmax+1];
    m[0]=1.0;
    for r in 1..=rmax {
        // contribution from eta_0 = n (mult 1) and the m coset values (each mult n)
        let mut s = nf.powi(r as i32); // eta_0^r * 1
        let mut acc=0.0f64;
        for &v in coset { acc += v.powi(r as i32); }
        s += nf*acc;
        m[r] = s/pf;
    }
    m
}

// Free cumulants from moments via the NC-partition recurrence (Speicher).
// Use: m_r = sum_{s=1}^{r} kappa_s * P(r-s, s)  where P(k, s) = sum over the s "gaps" left by the
// first block (which contains point 1 and s-1 others) of products of moments of the gap sizes.
// The standard finite recursion (e.g. Nica-Speicher Lec.11) :
//   m_n = sum_{s=1}^{n} kappa_s * sum_{ i_1+...+i_s = n-s, i_j>=0 } prod_j m_{i_j}.
// Define T(k,s) = sum over compositions of k into s nonneg parts of prod m_{part}. Then
//   kappa_s = m_s - sum_{ s'=1 }^{s-1} kappa_{s'} * T(s-s', s')   ... wait we must solve for kappa_n.
// Rearranged to solve for kappa_n (the s=n term gives kappa_n * T(0,n)=kappa_n*1):
//   kappa_n = m_n - sum_{s=1}^{n-1} kappa_s * T(n-s, s).
fn free_cumulants(m:&[f64], rmax:usize)->Vec<f64>{
    // T(k,s): compositions of k into s nonneg parts, weighted by prod m_part. m[0]=1.
    // Build via DP: Tdp[s][k]. Tdp[0][0]=1, Tdp[0][k>0]=0. Tdp[s][k]=sum_{j=0}^{k} Tdp[s-1][k-j]*m[j].
    let mut t=vec![vec![0.0f64; rmax+1]; rmax+1];
    t[0][0]=1.0;
    for s in 1..=rmax {
        for k in 0..=rmax {
            let mut acc=0.0f64;
            for j in 0..=k { acc += t[s-1][k-j]*m[j]; }
            t[s][k]=acc;
        }
    }
    let mut kappa=vec![0.0f64; rmax+1];
    for nn in 1..=rmax {
        let mut s=m[nn];
        for ss in 1..nn {
            s -= kappa[ss]*t[ss][nn-ss];
        }
        kappa[nn]=s; // T(0,nn)=1
    }
    kappa
}

fn main(){
    println!("================================================================================");
    println!("A15 FREE-CUMULANT probe -- free probability of the char-p Gauss-period family");
    println!("  empirical nu = (1/p)[delta_n + n*sum_c delta_{{eta_c}}], beta=log_n(p)~4 (PRIZE)");
    println!("  semicircle radius 2sqrt(n) => kappa_2=n, kappa_{{r>2}}=0; defect = higher free cumulants");
    println!("================================================================================");
    // prize scale beta=4. p ~ n^4. m=(p-1)/n ~ n^3 cosets -> O(n*m)=O(n^4) ops; cap so it finishes.
    let cells: Vec<u64> = vec![16, 32, 64];
    let rmax=10usize;
    for &n in &cells {
        let target = (n as f64).powf(4.0) as u64;
        let p = find_prime_cong1(n, target.max(1009));
        let m=(p-1)/n;
        let beta=(p as f64).ln()/(n as f64).ln();
        println!("");
        println!("--- n={} (mu={})  p={}  m={}  beta=log_n(p)={:.3} ---", n, (n as f64).log2() as u32, p, m, beta);
        if m > 6_000_000 { println!("   [skip: m={} too large]", m); continue; }
        let coset=coset_periods(n,p);
        let nf=n as f64;
        // M and edge
        let mmax = coset.iter().cloned().fold(0.0f64,|a,b|a.max(b.abs()));
        println!("   M=max|eta|={:.4}  M/sqrt(n)={:.4}  2sqrt(n)={:.4}  (M-2sqrt(n))/sqrt(n)={:.4}",
                 mmax, mmax/nf.sqrt(), 2.0*nf.sqrt(), mmax/nf.sqrt()-2.0);
        let mom=moments(n,p,&coset,rmax);
        // sanity: m_2 should be ~ n*(p-n)/p ~ n  (variance of spectrum)
        println!("   moments m_2={:.4} (target ~ n - n^2/p = {:.4}),  m_4={:.4}", mom[2], nf - nf*nf/(p as f64), mom[4]);
        let kappa=free_cumulants(&mom,rmax);
        println!("   FREE CUMULANTS kappa_r:");
        // normalize by semicircle prediction: kappa_2 ~ n (variance). Higher kappa_r normalized by kappa_2^{r/2}.
        let k2=kappa[2];
        for r in 2..=rmax {
            let norm = if r%2==0 { kappa[r]/k2.powf(r as f64/2.0) } else { kappa[r] };
            println!("     kappa_{:<2} = {:>14.4}   normalized (kappa_r / kappa_2^(r/2)) = {:.6}", r, kappa[r], norm);
        }
        // free edge of support: for a symmetric measure given by free cumulants, the support edge is the
        // sup of the support of the free measure; a robust proxy: the R-transform R(z)=sum kappa_{r+1} z^r,
        // and the support edge x_+ = sup over z>0 of [ 1/z + R(z) ] minimized... use the variational
        // formula x_+ = min_{z>0} ( 1/z + sum_{r>=1} kappa_{r+1} z^r ) (Cauchy/G inverse edge).
        // (For semicircle kappa_2=n only: 1/z + n z, min at z=1/sqrt(n) => 2 sqrt(n). EXACT.)
        let mut edge=f64::INFINITY;
        let mut zz=1e-4;
        while zz < 5.0/nf.sqrt() {
            let mut val=1.0/zz;
            for r in 1..rmax { val += kappa[r+1]*zz.powi(r as i32); }
            if val<edge { edge=val; }
            zz += 1e-4;
        }
        println!("   FREE-PROB support edge (min_z 1/z + R(z))  = {:.4}   vs actual M = {:.4}   semicircle 2sqrt(n)={:.4}",
                 edge, mmax, 2.0*nf.sqrt());
        println!("   free-edge / sqrt(n) = {:.4}   M/sqrt(n) = {:.4}", edge/nf.sqrt(), mmax/nf.sqrt());
    }
    println!("");
    println!("================================================================================");
    println!("VERDICT SWITCHES:");
    println!("  * if normalized kappa_{{r>2}} -> 0 as n grows: SEMICIRCLE => free edge 2sqrt(n) => GAIN");
    println!("  * if normalized kappa_{{r>2}} stays O(1) or grows: NON-semicircular => higher free cumulants");
    println!("    ARE the BGK content => free probability gives NO edge gain (conservation-law collapse)");
    println!("  * compare FREE edge to actual M: if free edge << M, free model UNDER-shoots the true edge");
    println!("    (free model misses the rare-alignment tail) => free prob CANNOT certify the true wall");
    println!("================================================================================");
}
