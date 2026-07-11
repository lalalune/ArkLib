// A07 FKM-sheaf / parameter-space cancellation probe (#444).
//
// THE ANGLE: relocate the cancellation from the n-point DOMAIN sum eta_b (Weil vacuous, n<sqrt q)
// to a PARAMETER family where Deligne is sharp. The far-line incidence carries a Krawtchouk
// weight K_w. We test whether the Krawtchouk-WEIGHTED parameter-family trace function
//      T(b) = sum_{x in mu_n} w(x) * e_p(b x),   w(x) a Krawtchouk/binomial weight,
// has a SMALLER conductor (= L2 second moment over the parameter b, = generic rank of any
// middle-extension realization, by orthogonality) than the unweighted eta_b, which the C2 no-go
// proved is FORCED to rank n by Parseval: sum_b |eta_b|^2 = p*n - n^2, avg -> n.
//
// FKM/Deligne completed-sum: |sum_x t(x)| <= cond(F)*sqrt(p). The prize needs cond=O(sqrt(n log p))
// i.e. cond << n. The decisive measurement: cond_proxy(weight) = avg_{b!=0} |T(b)|^2 / (peak^2/...).
// Concretely we report the SECOND MOMENT  M2(weight) := (1/(p-1)) sum_{b!=0} |T(b)|^2  which lower
// bounds the generic rank hence the conductor of ANY sheaf whose trace is T(b). If M2 ~ n for every
// reasonable weight, the relocation inherits the rank=n wall (A07 fails like C2). If some weight
// gives M2 << n WHILE keeping sum |T| large, A07 has a genuine handle.
//
// We sweep: (a) unweighted (control, must reproduce M2=n), (b) binomial/Krawtchouk weights
// w_k(x) = K_k(position) realized on the subgroup, (c) the "far-line" weight = indicator of a
// Hamming shell pulled back to mu_n. For each we report M2 and sup|T| and the ratio sup/sqrt(M2 log).
//
// Build: rustc -O probe_wfA07_fkm_conductor.rs -o /tmp/wfA07 && /tmp/wfA07
use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;let _=&mut a;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// weight families on mu_n (indexed by exponent j=0..n-1, x = h^j):
// 0: unweighted  w=1                         (control: should give M2 = n exactly by Parseval)
// 1: linear ramp w_j = (j+1)/n  (real, smooth) — does a smooth nonconstant weight cut the rank?
// 2: binomial central  w_j = C(n-1, j) normalized to max 1 (Krawtchouk-type concentration)
// 3: alternating       w_j = (-1)^j   (the K_1 / parity Krawtchouk weight)
// 4: half-shell indicator w_j = 1 if j<n/2 else 0 (a "far-line shell" pullback)
fn weight(family:usize, j:usize, n:usize)->f64{
    match family{
        0=>1.0,
        1=>((j+1) as f64)/(n as f64),
        2=>{ // log C(n-1,j) for stability, exp-normalized to peak 1
            let mut lg=0.0f64; for t in 0..j { lg += (((n-1-t) as f64).ln() - ((t+1) as f64).ln()); }
            // peak at j=(n-1)/2; subtract that
            let mut lgpk=0.0f64; let mid=(n-1)/2; for t in 0..mid { lgpk += (((n-1-t) as f64).ln() - ((t+1) as f64).ln()); }
            (lg-lgpk).exp()
        },
        3=>if j%2==0 {1.0} else {-1.0},
        4=>if j< n/2 {1.0} else {0.0},
        _=>1.0,
    }
}

// returns (M2 = avg_{b!=0}|T(b)|^2, supabs = max_{b!=0}|T(b)|, l1weight = sum|w|)
fn measure(family:usize, n:u64, p:u64)->(f64,f64,f64){
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let w:Vec<f64>=(0..n as usize).map(|j| weight(family,j,n as usize)).collect();
    let l1:f64 = w.iter().map(|x|x.abs()).sum();
    let m=(p-1)/n; // T(b) is coset-constant ONLY for family 0; for weighted families it is NOT,
    // so we must range b over ALL of F_p^* for a true second moment. That's p-1 ~ n^4 terms -> too big.
    // Instead range b over the m coset reps AND note: the weighted period T(ub) for u in mu permutes
    // the weights cyclically, so the full second moment = (1/(p-1)) sum_{all b} = average over cosets of
    // the cyclic-average of |T|^2. We compute the per-coset cyclic average exactly (n shifts), giving the
    // EXACT full-family second moment without enumerating p-1 terms.
    let mut sum2=0.0f64; let mut cnt=0u64; let mut supabs=0.0f64;
    let mut brep=1u64; let gn=mpow(g,n,p); // coset rep stepper, order m
    for _ in 0..m {
        // for this coset rep, average |T(u*brep)|^2 over the n elements u in mu (u = h^s)
        // T(u*brep) = sum_j w_j e_p(brep * h^{j} * h^{s}) = sum_j w_j e_p(brep h^{j+s}).
        // So the s-shift just cyclically rotates the weight indices. Compute base angles a_j = 2pi brep h^j /p.
        let ang:Vec<f64>=(0..n as usize).map(|j|{
            let t=((brep as u128 * mu[j] as u128)%p as u128) as u64; 2.0*PI*(t as f64)/(p as f64)
        }).collect();
        // cos/sin of base
        let cs:Vec<f64>=ang.iter().map(|a|a.cos()).collect();
        let sn:Vec<f64>=ang.iter().map(|a|a.sin()).collect();
        for s in 0..n as usize {
            let mut re=0.0f64; let mut im=0.0f64;
            for j in 0..n as usize {
                let idx=(j+s)%(n as usize); // weight at j, angle index shifted: T = sum_j w_j * e^{i ang_{j+s}}
                re += w[j]*cs[idx]; im += w[j]*sn[idx];
            }
            let mag2=re*re+im*im; sum2+=mag2; cnt+=1; let mag=mag2.sqrt(); if mag>supabs{supabs=mag;}
        }
        brep=(( brep as u128 * gn as u128)%p as u128) as u64;
    }
    (sum2/(cnt as f64), supabs, l1)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() }
                     else { vec![32,64,128,256] };
    let fams=["unweighted","linramp","binomial","alt(-1)^j","halfshell"];
    println!("# A07: Krawtchouk-weighted parameter-family second moment M2 (= generic rank = conductor floor)");
    println!("# prize regime p ~ n^4 (beta=4). M2 lower-bounds cond of ANY sheaf with trace T(b).");
    println!("# FKM gives prize iff cond=O(sqrt(n log p)) << n. So we need M2 << n.");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let p=find_prime_cong1(n, target.max(200003));
        let beta=(p as f64).ln()/(n as f64).ln();
        println!("\n## n={} p={} beta={:.2}  (n={} is the rank-floor target)", n, p, beta, n);
        println!("{:<12} {:>12} {:>12} {:>10} {:>12} {:>14}", "weight","M2","M2/n","sup|T|","l1(w)","sup/sqrt(M2*lnN)");
        let m=(p-1)/n; let lnn=(m as f64).ln().max(1.0);
        for (fi,fname) in fams.iter().enumerate(){
            let (m2,sup,l1)=measure(fi,n,p);
            let ratio=sup/((m2*lnn).sqrt().max(1e-9));
            println!("{:<12} {:>12.3} {:>12.4} {:>10.3} {:>12.3} {:>14.4}", fname, m2, m2/(n as f64), sup, l1, ratio);
        }
    }
}
