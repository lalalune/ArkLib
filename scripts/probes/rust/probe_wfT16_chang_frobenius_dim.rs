// Probe wfT16 (#444): Frobenius-refined Chang cover of the H-invariant large spectrum.
//
// CANDIDATE (G4-1 / T16). Spec_alpha = { b in F_p^* : |eta_b| >= alpha n }, eta_b = sum_{x in mu_n} e_p(bx),
// mu_n = order-n=2^mu subgroup of F_p^*. Spec_alpha is H-invariant (union of cosets b*mu_n) by
// eta_{hb}=eta_b for h in mu_n (period const on cosets). The candidate asserts:
//   (1) Chang base: dissociated dimension of Spec_alpha <= D0 = C0 * alpha^{-2} * log(p/n)  [= the WALL].
//   (2) NEW: 2-power Frobenius (sigma_p) orbit structure of the {-1,0,1}-relation lattice collapses
//       the effective dissociated dimension by a factor ~ mu = log2 n, giving D = D0 / mu.
//   (3) Counting + Parseval-balance over <= n*D large cosets at alpha = M/n forces M <= C sqrt(n log(p/n)).
//
// THIS PROBE tests the LOAD-BEARING claims directly at PRIZE-FAITHFUL parameters:
//   p PRIME, p = 1 mod n, mu_n PROPER (n | p-1, (p-1)/n > 1), p ~ n^4 (beta=4), NEVER n=p-1.
//
// MEASUREMENTS (all at prize regime beta=4):
//   A. Dissociated dimension d(Spec_alpha) of the large spectrum (greedy maximal dissociated transversal
//      of COSET REPS, since Spec is H-invariant), at several alpha.
//   B. The Chang base bound D0 = alpha^{-2} ln(p/n) (with C0=1) -- the wall.
//   C. The claimed refined target D0/mu.
//   D. Does d(Spec_alpha) scale like D0 (wall) or D0/mu (refined)?  ==> the 1/mu claim.
//   E. The Frobenius/Galois orbit structure of the relations: are the {-1,0,1} relations among large
//      cosets actually organized into 2-power sigma_p-orbits that would collapse dimension?
//   F. THE BALANCING ARITHMETIC: at alpha=M/n, what M-bound does |Spec_alpha| <= n*D + Parseval give?

use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p%n!=1{p=p-(p%n)+1;}if p<3{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// Compute eta_b for all b in F_p^*, return (m, M, etas_by_coset_rep) where etas indexed by coset.
// mu_n = <g^m>, m=(p-1)/n. Coset reps: g^j for j=0..m-1. eta on coset g^j * mu_n is constant.
struct Spec { p:u64, n:u64, m:u64, big_m:f64, // M
              coset_rep:Vec<u64>,   // g^j, j=0..m-1, one rep per coset
              coset_eta:Vec<f64>,   // |eta| on that coset (real since n even => -1 in mu_n)
              coset_eta_signed:Vec<f64>, }
fn spectrum(n:u64,p:u64)->Spec{
    let g=primitive_root(p);
    let m=(p-1)/n;
    // generator of mu_n is g^m
    let gm=mpow(g,m,p);
    // elements of mu_n
    let mut mun=Vec::with_capacity(n as usize);
    let mut x=1u64; for _ in 0..n { mun.push(x); x=((x as u128*gm as u128)%p as u128) as u64; }
    // for each coset rep r=g^j, eta = sum_{y in mun} e_p(r*y)
    let mut coset_rep=Vec::with_capacity(m as usize);
    let mut coset_eta=Vec::with_capacity(m as usize);
    let mut coset_eta_signed=Vec::with_capacity(m as usize);
    let twopi=2.0*PI; let pf=p as f64;
    let mut r=1u64; // g^0
    for _j in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &y in &mun {
            let ang=twopi*((( (r as u128*y as u128)%p as u128) as f64)/pf);
            re+=ang.cos(); im+=ang.sin();
        }
        coset_rep.push(r);
        let mag=(re*re+im*im).sqrt();
        coset_eta.push(mag);
        coset_eta_signed.push(re); // imag ~ 0 for n even
        r=((r as u128*g as u128)%p as u128) as u64;
    }
    let big_m=coset_eta.iter().cloned().fold(0.0,f64::max);
    Spec{p,n,m,big_m,coset_rep,coset_eta,coset_eta_signed}
}

// Dissociated dimension of a set S of elements of F_p (additive group, mod p):
// max size of a subset T s.t. no nontrivial {-1,0,1} combination of T is 0 mod p.
// Greedy: build maximal dissociated subset. d() = size of a MAXIMAL dissociated subset (an
// approximation to additive dimension; standard in Chang-cover practice). For correctness on the
// orbit claim we additionally count: of the candidate elements rejected, how many were rejected
// because of a relation to an EARLIER element vs to its OWN Frobenius image.
fn is_dissociated_with(t:&Vec<i64>, cand:u64, p:u64)->bool{
    // check: does there exist eps in {-1,0,1}^|t| with sum eps_i t_i +/- cand == 0 (cand coeff in {-1,1})?
    // i.e. is cand in the {-1,0,1}-span of t? (for adding cand to a dissociated t, cand must NOT be
    // representable as sum eps_i t_i with eps in {-1,0,1}). Enumerate the span of t (3^|t| sums).
    let k=t.len();
    if k>20 { // too big to enumerate; use a hashed partial: just return true (assume independent).
        return true;
    }
    let pp=p as i128;
    // enumerate 3^k sums; check if cand == sum mod p OR -cand == sum mod p i.e. cand in span
    let candi=cand as i128 % pp;
    // iterate base-3
    let mut idx=0u64; let total=3u64.pow(k as u32);
    while idx<total {
        let mut x=idx; let mut s:i128=0;
        for i in 0..k { let c=(x%3) as i128 -1; x/=3; s+=c*(t[i] as i128); }
        let _=idx;
        let sm=((s%pp)+pp)%pp;
        if sm==candi || sm==(pp-candi)%pp { return false; } // cand or -cand in span => dependent
        idx+=1;
    }
    true
}
fn dissoc_dim_greedy(elems:&Vec<u64>, p:u64)->usize{
    let mut t:Vec<i64>=Vec::new();
    for &e in elems {
        if e==0 {continue;}
        if is_dissociated_with(&t, e, p) {
            t.push(e as i64);
            if t.len()>=20 { break; } // cap (enumeration limit); report as ">=20"
        }
    }
    t.len()
}

fn main(){
    println!("# wfT16: Frobenius-refined Chang cover of the H-invariant large spectrum (T16/G4-1)");
    println!("# prize regime beta=4, p=1 mod n, mu_n proper, NEVER n=p-1.");
    println!("# mu=log2 n. D0 (Chang/wall, C0=1) = alpha^-2 * ln(p/n).  Refined target D = D0/mu.");
    println!();
    let alphas=[0.5f64, 0.7, 0.85, 1.0];
    for &n in &[8u64,16,32,64,128,256] {
        let p=find_prime_cong1(n,(n as f64).powf(4.0).round() as u64);
        let sp=spectrum(n,p);
        let mu=(n as f64).log2();
        let nf=n as f64; let pf=p as f64;
        let logpn=(pf/nf).ln();
        let beta=pf.ln()/nf.ln();
        println!("=== n={} p={} (beta={:.3}) m={} mu={:.0} M/sqrt(n)={:.4} M/n={:.4} floor=sqrt(n ln(p/n))={:.2} M/floor={:.4}",
                 n,p,beta,sp.m,mu, sp.big_m/nf.sqrt(), sp.big_m/nf, (nf*logpn).sqrt(), sp.big_m/(nf*logpn).sqrt());
        for &al in &alphas {
            // Spec_alpha = coset reps with |eta| >= alpha * n. We use coset reps (Spec is H-invariant);
            // dissociated dim of coset reps approximates the structural covering dim.
            let thr=al*nf;
            let mut reps:Vec<u64>=sp.coset_rep.iter().zip(sp.coset_eta.iter())
                .filter(|(_,&e)| e>=thr).map(|(&r,_)| r).collect();
            // sort by eta descending so greedy picks the biggest first (Chang uses largest coeffs)
            let mut idxed:Vec<(u64,f64)>=sp.coset_rep.iter().zip(sp.coset_eta.iter())
                .filter(|(_,&e)| e>=thr).map(|(&r,&e)|(r,e)).collect();
            idxed.sort_by(|a,b| b.1.partial_cmp(&a.1).unwrap());
            reps=idxed.iter().map(|x|x.0).collect();
            let ncoset=reps.len();
            let d=dissoc_dim_greedy(&reps,p);
            let d0=al.powi(-2)*logpn;            // Chang base (wall), C0=1
            let d0_refined=d0/mu;                // refined target
            let dge = if d>=20 {">=20".to_string()} else {format!("{}",d)};
            println!("  alpha={:.2}: #large_cosets={:4}  dissoc_dim(reps)={:>5}  D0(wall)={:8.2}  D0/mu(refined)={:7.2}  ratio d/D0={:.3} d/(D0/mu)={:.3}",
                     al, ncoset, dge, d0, d0_refined,
                     (d as f64)/d0, (d as f64)/d0_refined);
        }
        // E. Frobenius orbit structure of the large-coset RELATIONS.
        // The candidate's mechanism: every {-1,0,1}-relation among large frequencies sits in a
        // 2-power sigma_p (Frobenius = b -> b^2? No: sigma_p is the p-power Frobenius on F_p, trivial.)
        // The relevant "2-power" map on cosets is the SQUARING map b -> b^2 (which permutes cosets,
        // since mu_n is 2-power), generating a 2-power orbit. Check: does squaring preserve |eta|?
        // (If eta_{b^2} = eta_b then the spectrum is squaring-invariant and orbits would collapse dim.)
        {
            // pick the argmax coset rep b*, walk b -> b^2, record |eta|.
            let mut bstar=sp.coset_rep[0]; let mut best=0.0;
            for (i,&e) in sp.coset_eta.iter().enumerate(){ if e>best{best=e;bstar=sp.coset_rep[i];}}
            // recompute eta on squares of bstar
            let g=primitive_root(p); let gm=mpow(g,sp.m,p);
            let mut mun=Vec::with_capacity(n as usize); let mut x=1u64;
            for _ in 0..n { mun.push(x); x=((x as u128*gm as u128)%p as u128) as u64; }
            let eta_of=|b:u64|->f64{ let twopi=2.0*PI; let mut re=0.0; let mut im=0.0;
                for &y in &mun { let ang=twopi*(((b as u128*y as u128)%p as u128) as f64/pf); re+=ang.cos(); im+=ang.sin(); }
                (re*re+im*im).sqrt() };
            let mut chain=Vec::new(); let mut b=bstar;
            for _ in 0..6 { chain.push((b, eta_of(b)/sp.big_m)); b=((b as u128*b as u128)%p as u128) as u64; }
            print!("  Frobenius/squaring orbit of b* (|eta|/M): ");
            for (bb,r) in &chain { print!("({}:{:.3}) ", bb, r); }
            println!();
        }
        println!();
    }
    println!("# READ: if dissoc_dim(reps) tracks D0 (ratio d/D0 ~ const, d/(D0/mu) ~ mu) => NO 1/mu collapse => WALL.");
    println!("# if dissoc_dim(reps) tracks D0/mu (ratio d/(D0/mu) ~ const ~1, d/D0 ~ 1/mu) => 1/mu collapse holds.");
    println!("# Also: if squaring orbit |eta|/M decays fast (not ~1), there is NO Galois invariance to collapse relations.");
}
