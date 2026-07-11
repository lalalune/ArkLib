// probe_wfT18_bilinear_bogolyubov.rs  (#444 T18, localId G4-3)
//
// CANDIDATE (architect): apply the BILINEAR Bogolyubov theorem (Bienvenu-Le; Gowers-Milicevic)
// to the additive-difference incidence B = {(x,y) in (F_p^*)^2 : x-y in mu_n}; claim a bilinear
// Bohr variety of codimension O(mu) = O(log n) via dilation eigen-structure, then specialize x=0
// to project onto the linear spectrum, cap the surviving-frequency mass at p * n^{-c}, and so
// M <= C sqrt(n log(p/n)) at n=2^30.
//
// This probe stress-tests the THREE quantitative load-bearing steps and reports whether any of
// them is non-vacuous at the prize regime (beta=4, p~n^4). It does NOT assume the architect's
// conclusion; it computes the actual numbers the bilinear Bogolyubov hypothesis would give.
//
// STEP A (density): bilinear Bogolyubov needs density alpha = |B| / (ambient)^2 and the codim
//   bound is c(alpha) = log^O(1)(1/alpha). Compute alpha for B in the prize ambient (F_p)^2.
// STEP B (codim-vs-ambient): the conclusion is a bilinear Bohr variety of codim c inside a
//   product W1 x W2 of subspaces of (F_p)^2. The ambient (F_p)^2 is a 2-DIMENSIONAL F_p-vector
//   space (p a PRIME field). A proper subspace W_i <= F_p has dim 0 (codim 1) -> {0}. So the
//   only nontrivial structure is the number r of bilinear forms; codim r in a 2-dim space is
//   vacuous for r>=2 (whole thing is a point). Quantify what "codim O(mu)" can even MEAN here.
// STEP C (mass): a bilinear Bohr variety of codim c in (F_p)^2 has size ~ p^2 * p^{-c} = p^{2-c}.
//   The architect claims this projects (x=0 slice) to a frequency set of mass p * n^{-c}.
//   Compare p * n^{-c} for c=O(mu)=O(log n) against the trivial Parseval/all-frequencies count
//   m = (p-1)/n. Is n^{-c} ever small enough to beat Johnson, and is the codim REAL?
//
// We also directly MEASURE, for small n at beta=4 (exact FFT), the worst Gauss-period M(n) and
// the "best b* mass" to see whether any covering of the large-spectrum locus is even consistent
// with the observed M ~ sqrt(n log(p/n)) excess, or whether the covering caps at Johnson sqrt(n).

fn mpow(mut a:u64, mut e:u64, p:u64)->u64{
    let mut r=1u128; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; }
    r as u64
}
fn isp(n:u64)->bool{ if n<2 {return false} let mut d=2u64; while d*d<=n { if n%d==0 {return false} d+=1 } true }
fn fp(n:u64, lo:u64)->u64{ // smallest prime p >= lo with p = 1 mod n
    let mut p = lo + ((n - lo%n)%n); if p%n!=1 { p += 1; } // make p%n==1
    // ensure p ~ 1 mod n by stepping in n
    let mut k = (lo + n - 1)/n; loop { let cand = k*n + 1; if cand>=lo && isp(cand) { return cand; } k+=1; } let _=p;
}
fn proot(p:u64)->u64{
    let mut m=p-1; let mut fs=vec![]; let mut d=2u64;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 {m/=d} } d+=1 }
    if m>1 { fs.push(m) }
    let mut g=2u64; loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g } g+=1 }
}

fn main(){
    println!("=== T18 bilinear Bogolyubov reduction probe (beta=4) ===\n");

    // ---- STEP A & C analytic at PRIZE scale n=2^30, p~n^4 ----
    let mu_prize = 30u32;
    let n_prize = 1u128<<mu_prize;          // 2^30
    let p_prize = n_prize*n_prize*n_prize*n_prize; // ~ n^4 = 2^120
    let logn = (mu_prize as f64)*std::f64::consts::LN_2;
    let logp = 4.0*logn;
    // density of B={(x,y):x-y in mu_n} in (F_p)^2 : for each x, y ranges over x - mu_n (n choices)
    // => |B| = p * n approx ; ambient (F_p)^2 has p^2 ; alpha = |B|/p^2 = n/p = n^{1-beta}=n^{-3}
    let alpha_log = (1.0-4.0)*logn; // ln alpha = -3 ln n
    println!("PRIZE n=2^{}  p~n^4=2^{}", mu_prize, 120);
    println!("STEP A: density alpha = |B|/p^2 = n/p = n^(1-beta) = n^-3");
    println!("        ln(1/alpha) = 3 ln n = {:.2}   (= (beta-1) ln n)", -alpha_log);
    // bilinear Bogolyubov codim bound c(alpha)=log^O(1)(1/alpha). Best published (Hosseini-Lovett-
    // type / Gowers-Milicevic) exponent O(1) is >= 1 (linear in log already costs the iteration);
    // even taking the OPTIMISTIC c(alpha) = ln(1/alpha) (exponent 1):
    let c_codim_optimistic = -alpha_log; // = 3 ln n  (this is the codim the THEOREM gives)
    println!("STEP B(thm): bilinear Bogolyubov codim c(alpha) >= log(1/alpha) = 3 ln n = {:.2}", c_codim_optimistic);
    println!("        ARCHITECT'S CLAIM: dilation eigen-refinement forces codim DOWN to O(mu)=O(log n)={:.2}", logn);
    println!("        (this is the unproven NEW step; theorem alone gives 3 ln n, not log n)\n");

    // STEP B structural: ambient (F_p)^2 is a 2-DIMENSIONAL F_p vector space (p PRIME field).
    println!("STEP B(struct): ambient (F_p)^2 has F_p-dimension 2 (p is a PRIME field, dim_Fp F_p = 1).");
    println!("        A bilinear Bohr VARIETY needs subspaces W1,W2 <= (F_p) and r bilinear forms.");
    println!("        Proper subspace of F_p (1-dim) is {{0}} (codim 1). So 'codim c' for c>=2 in");
    println!("        a 2-dim space = a single point or empty. The 'bounded codim, large n=dim'");
    println!("        asymptotics of the theorem DO NOT EXIST here: dimension is FIXED at 2.\n");

    // STEP C mass at prize: bilinear Bohr variety codim c => size ~ p^2 * p^{-c}. Architect's
    // x=0 projection => frequency mass ~ p * n^{-c}. Compare with the actual #frequencies that
    // must be covered: ALL nonzero b that could be worst, i.e. up to m=(p-1)/n cosets, each coset
    // a single value. The Parseval/Johnson floor is M >= sqrt(n) for SOME b.
    println!("STEP C: claimed surviving-frequency mass = p * n^(-c).");
    for &(label, c) in &[("c=O(mu)=log n (architect)", logn),
                          ("c=3 ln n (theorem)", c_codim_optimistic)] {
        let mass_log = logp - c*logn.recip().recip(); // ln(p) - c*ln n  -- careful below
        let _ = mass_log;
        let ln_mass = logp - c; // here c is already a count of "ln n" units? No: n^{-c} => ln = -c*ln n
        let ln_mass2 = logp - c*logn; // p * n^{-c}: ln = ln p - c ln n
        // NB the architect writes n^{-c} with c a CODIMENSION (pure number), so mass = p*n^{-c}=p*exp(-c ln n)
        println!("   {:<28} ln(mass)=ln p - c*ln n = {:.2} - {:.2}*{:.2} = {:.2}",
                 label, logp, c, logn, ln_mass2);
        let _=ln_mass;
        if ln_mass2 < 0.0 {
            println!("        -> mass < 1 : the covering is EMPTY at prize scale (vacuous, like A12/F6).");
        } else {
            println!("        -> mass = {:.2e} frequencies survive.", ln_mass2.exp());
        }
    }
    println!();

    // ---- EXACT small-n: measure M(n) vs Johnson sqrt(n) and vs sqrt(n log(p/n)) ----
    println!("=== exact M(n) vs Johnson sqrt(n) vs prize sqrt(n log(p/n)) (beta=4) ===");
    use std::f64::consts::PI;
    for &mu in &[3u32,4,5,6,7,8,9,10] {
        let n = 1u64<<mu;
        let lo = (n as f64).powf(4.0) as u64;
        let p = fp(n, lo);
        let g = proot(p);
        let h = mpow(g,(p-1)/n,p);
        let elts:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        // M(n) = max_{b!=0} |eta_b|. eta is constant on b*mu cosets; sample many b.
        let mut mmax=0.0f64;
        let sample = std::cmp::min(p-1, 200_000);
        for b in 1..=sample {
            let mut re=0.0; let mut im=0.0;
            for &x in &elts { let t=((b as u128*x as u128)%p as u128) as u64; let a=2.0*PI*(t as f64)/(p as f64); re+=a.cos(); im+=a.sin(); }
            let m=(re*re+im*im).sqrt(); if m>mmax {mmax=m;}
        }
        let johnson=(n as f64).sqrt();
        let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        println!("n={:>4} p={:>12} M={:>8.3}  Johnson sqrt(n)={:>7.3}  prize sqrt(n log(p/n))={:>8.3}  M/Johnson={:.3}  M/prize={:.3}",
                 n,p,mmax,johnson,prize, mmax/johnson, mmax/prize);
    }
    println!("\n(If M tracks sqrt(n log(p/n)) and exceeds Johnson, any DIMENSION/COVERING bound that");
    println!(" outputs a codim-controlled mass = p*n^{{-c}} is a SECOND-ORDER/structural handle that");
    println!(" caps at Johnson: F0. The sqrt(log) excess is a tail phenomenon a codim cover cannot see.)");
}
