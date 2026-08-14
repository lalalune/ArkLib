// A13 (#444): ENTROPY-COMPRESSION / Shannon bound on the (r+1)-subset-sum distribution
// (manifesto route 10 / open-avenue C7, never attacked).
//
// SETUP. X_1..X_r iid uniform on mu_n = order-n 2-power subgroup of F_p^*. Subset-sum
// S_r = X_1+...+X_r in F_p, distribution P_r(a)=Pr[S_r=a]. Fourier:
//     hat P_r(b) = E[e_p(-b S_r)] = (eta_b / n)^r,   eta_b = sum_{x in mu_n} e_p(b x).
// (eta_b is REAL since mu_n is negation-closed for n even; eta_{-b}=eta_b.)
//
// INFORMATION FUNCTIONALS of the subset-sum measure P_r:
//   * Collision prob (Renyi-2)  CP_r = sum_a P_r(a)^2 = (1/p) sum_b |hat P_r(b)|^2
//                                     = E_r/(p n^{2r}),  E_r = sum_b |eta_b|^{2r}.
//     Renyi-2 entropy  H2 = -log2 CP_r.
//   * Min-entropy / MAX LOAD  L_r = max_a P_r(a),  H_inf = -log2 L_r.
//   * Shannon entropy  H1 = -sum_a P_r log2 P_r.
//   * Support size |supp P_r|.
//
// THE A13 TEST (route 10): the manifesto hopes "the worst-case list <= entropy of the
// (r+1)-subset-sum measure, which the 2-power rigidity CAPS BELOW THE BUDGET (log2 p)".
// We measure whether the 2-power structure forces these entropies LOW (vs the budget log2 p),
// AND -- decisively -- the DIRECTION of the M <-> entropy relation.
//
// DUAL RELATION (the crux): M = max_{b!=0}|eta_b| means max_{b!=0}|hat P_r(b)| = (M/n)^r.
//   - High entropy (near-uniform S_r) <=> all nonprincipal hat P_r tiny <=> M SMALL.
//   - M large <=> a Fourier spike <=> low entropy.
// So "2-power rigidity caps entropy LOW" would force M LARGE -- the WRONG way. We test this.
//
// We also compute the EXACT char-0 (dilute) reference: P_r over the cross-polytope net,
// and the BUDGET log2 p, to see how far below budget the entropies sit and how they scale.
//
// PRIZE-FAITHFUL: p PRIME, n=2^mu, n|p-1, beta=log_n(p)~4 (p~n^4), m=(p-1)/n>1, NEVER n=p-1.
// build: rustc -O probe_wfA13_subsetsum_entropy.rs -o /tmp/wfA13 ; /tmp/wfA13

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// Exact subset-sum distribution P_r(a) for a in F_p, by direct convolution of the mu_n
// uniform measure with itself r times. p must be small enough to hold a length-p array.
fn subset_sum_dist(mu:&[u64], p:u64, r:usize)->Vec<f64>{
    let pn = p as usize;
    // base measure: uniform 1/n on each mu element (with multiplicity if collisions, but
    // mu elements are distinct nonzero residues)
    let inv_n = 1.0/(mu.len() as f64);
    let mut base = vec![0.0f64; pn];
    for &x in mu { base[x as usize]+=inv_n; }
    let mut cur = base.clone(); // r=1
    for _ in 2..=r {
        let mut next = vec![0.0f64; pn];
        // convolution mod p: next[c] = sum_a cur[a]*base[(c-a) mod p]
        // do it via the base support (n terms) for speed
        for (c, nc) in next.iter_mut().enumerate() {
            // sum over base support
            let mut s=0.0;
            for &x in mu {
                let xu = x as usize;
                let a = if c>=xu { c-xu } else { c+pn-xu };
                s += cur[a]*inv_n;
            }
            *nc = s;
        }
        cur = next;
    }
    cur
}

fn entropies(p:&[f64])->(f64,f64,f64,usize){
    // returns (H_inf=-log2 max, H2=-log2 sum sq, H1 shannon, support)
    let mut mx=0.0f64; let mut sq=0.0f64; let mut sh=0.0f64; let mut supp=0usize;
    for &v in p {
        if v>1e-15 { supp+=1; sq+=v*v; sh -= v*v.log2(); if v>mx{mx=v;} }
    }
    (-mx.log2(), -sq.log2(), sh, supp)
}

fn run_exact(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let beta=(p as f64).ln()/(n as f64).ln();
    let budget = (p as f64).log2();
    println!("===== EXACT subset-sum entropy: n={} p={} m={} beta={:.2} budget=log2 p={:.2} =====", n,p,m,beta,budget);
    println!("   r |  H_inf  H2(Renyi)  H1(Shannon)  supp/p  |  Hinf/bud  H2/bud  |  L_r=maxload  CP_r");
    // precompute eta_b over coset reps for the M relation
    let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    use std::f64::consts::PI;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let mm = eta.iter().cloned().fold(0.0f64, f64::max); // includes eta_0=n
    // M = max over b!=0 : exclude the principal coset (eta_0=n). principal is b in mu_n coset of 0? b ranges nonzero; b=1.. all nonzero -> the coset rep b=1 has eta_1 etc. eta_0 would be b=0 (excluded). So all our eta entries ARE b!=0. The value n appears only if some coset sums to n.
    let mmax_nonprinc = eta.iter().cloned().fold(0.0f64, f64::max);
    let _ = mm;
    let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
    println!("        | (entropy->M upper bound)  M_H2 = n*(p*CP_r - 1)^(1/2r) ; ratio M_H2/M");
    for r in 1..=rmax {
        let dist = subset_sum_dist(&mu, p, r);
        let (hinf,h2,h1,supp) = entropies(&dist);
        let lr = dist.iter().cloned().fold(0.0f64, f64::max);
        let cp: f64 = dist.iter().map(|v|v*v).sum();
        // the ACTUAL entropy->M bound: M^{2r} <= n^{2r}(p CP_r - 1) = n^{2r}(p 2^{-H2} - 1)
        let pcp_m1 = (p as f64)*cp - 1.0;
        let m_h2 = if pcp_m1>0.0 { (n as f64)*pcp_m1.powf(1.0/(2.0*r as f64)) } else { 0.0 };
        println!("  {:3} | {:6.3}  {:7.3}   {:9.3}   {:.4}  |  {:6.3}  {:6.3}  | {:.3e}  {:.3e} | M_H2={:7.2} r={:.2}",
            r, hinf, h2, h1, supp as f64/p as f64, hinf/budget, h2/budget, lr, cp,
            m_h2, m_h2/mmax_nonprinc);
    }
    println!("  M=max_{{b!=0}}|eta_b| = {:.3}  (M/sqrt(n)={:.3}, M/prize={:.3})  -- the wall",
        mmax_nonprinc, mmax_nonprinc/(n as f64).sqrt(), mmax_nonprinc/prize);
    // The dual identity check at the prize-binding depth r*=round(log p /2): does max load track (M/n)^?
    println!();
}

fn main(){
    // small exact n where length-p convolution is affordable (p up to a few million)
    // n=8: p~8^4=4096 region; n=16: p~16^4=65536; n=32 beta=4 p~1e6 (length-1e6 array, ok)
    run_exact(8,  fp(8, 4000), 12);
    run_exact(16, fp(16,60000), 16);
    run_exact(32, fp(32, 1_000_000), 20);
}
