// wf-A02 (#444): the MULTIPLICATIVE / DILATION-ACTION large sieve on {eta_b}.
//
// ANGLE A02 [MILDER]: alternative route to the S2 equidistribution constant kappa via a
// multiplicative large sieve / almost-orthogonality on the per-coset spectrum.
//
// SETUP. eta_b = sum_{x in mu_n} e_p(b x) is coset-constant (eta_{ub}=eta_b, u in mu_n), so it is
// a function on the cyclic quotient Q = F_p^*/mu_n of order m=(p-1)/n. The dilation b -> b*t (t a
// coset rep) cyclically permutes the m cosets: the index set is Z/m and the dilation by the
// generator-coset is the +1 shift. Parseval: sum_{b!=0}|eta_b|^2 = pn - n^2, and each of the m
// cosets carries n equal frequencies, so the per-coset mass vector w = (w_0,...,w_{m-1}),
// w_j = |eta_{g^j}|^2, has  sum_j w_j = (pn-n^2)/n = p - n.  Its mean is (p-n)/m = n(p-n)/(p-1) ~ n.
//
// THE A02 QUESTION (almost-orthogonality of the dilation orbit).
// The ADDITIVE large sieve over ALL of F_q (separation 1/q, support q) is already known to
// collapse to 2x Parseval (LargeSieveParsevalCollapse.lean) => vacuous. A02 asks the DIFFERENT
// question: expand the per-coset mass vector w (a function on Z/m) in the MULTIPLICATIVE characters
// of Q (= the m-th roots of unity, i.e. the DFT of Z/m):
//     w_j = sum_{k=0}^{m-1} W(k) e(jk/m),   W(k) = (1/m) sum_j w_j e(-jk/m).
// W(0) = mean(w) ~ n. A large-sieve / almost-orthogonality statement is: max_j w_j is bounded by a
// bounded multiple of the average IFF the DFT spectrum W(k) decays / has bounded l1 mass:
//     max_j w_j <= sum_k |W(k)|  (trivial),  and  kappa_2 := max_j w_j / mean(w) = max/W(0).
// The genuine multiplicative-large-sieve hope: the dilation spectrum W(k) for k!=0 is small
// (almost-orthogonality => |W(k)| << W(0)/sqrt(m) Ramanujan-flat, or at least sum_{k!=0}|W(k)| =
// o(W(0))), forcing kappa_2 = O(1). We MEASURE:
//   (1) the DFT spectrum {|W(k)|}_k of the per-coset mass w: its l1 mass L1 = sum_k |W(k)|, its
//       l2 mass (= Parseval = sqrt(mean of w^2)), and the ratio L1/W(0) = (max possible PAPR).
//   (2) kappa_2 = max_j w_j / mean(w)  (the depth-1 equidistribution constant on the cosets).
//   (3) the SPECTRAL large-sieve constant for the dilation action: build the autocorrelation
//       R(t) = (1/m) sum_j w_j w_{j+t}; its DFT is |W(k)|^2 m; the spectral-norm/trace ratio
//       Lambda_max/Lambda_avg = m*max_k|W(k)|^2 / sum_k|W(k)|^2.  =1 flat; large = concentrated.
//   (4) whether kappa_2 grows with n (the prize-relevant question): is kappa_2 = O(log n) or O(1)?
//
// VERDICT LOGIC. If the dilation spectrum is Ramanujan-flat (|W(k)|=O(W(0)/sqrt m) for k!=0) then
// L1 ~ W(0)*sqrt(m) and PAPR could be as large as sqrt(m) ~ sqrt(p)/n -- USELESS (that is the BGK
// wall again). If instead the spectrum is l1-BOUNDED (sum_{k!=0}|W(k)| = O(W(0))) then kappa_2=O(1)
// FOR FREE -- a genuine milder win. The probe DECIDES which regime holds at beta=4.
//
// usage: probe_wfA02_multiplicative_largesieve [n1 n2 ...]   default 16 32 64 128 256
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// per-coset mass vector w_j = |eta_{g^j}|^2 over the m cosets (j over Z/m). Principal coset is j=0
// (b=1 in mu_n) where w=n^2. We keep ALL cosets for the DFT/sum identities; the NONprincipal
// max excludes the principal one.
fn percoset_w(n:u64,p:u64)->(Vec<f64>,u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut out=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu { let t=((b as u128*x as u128)%p as u128)as u64; let a=2.0*PI*(t as f64)/p as f64; re+=a.cos(); im+=a.sin(); }
        out.push(re*re+im*im);
        b=((b as u128*g as u128)%p as u128)as u64;
    }
    (out,m)
}

// naive O(m^2) DFT magnitude |W(k)| = |(1/m) sum_j w_j e(-2pi i jk/m)|, for k = 0..K-1 plus we
// also compute full l1/l2 over ALL k (the load-bearing quantities). For large m we subsample the
// reported list but compute the full sums exactly via a single O(m^2) pass.
fn dft_stats(w:&[f64])->(f64,f64,f64,f64,Vec<(u64,f64)>){
    let m=w.len();
    let mf=m as f64;
    let mut l1=0.0f64;       // sum_k |W(k)|
    let mut l2sq=0.0f64;     // sum_k |W(k)|^2  (= (1/m) sum_j w_j^2 by Parseval)
    let mut w0=0.0f64;       // W(0) = mean(w)
    let mut maxnz=0.0f64;    // max_{k!=0} |W(k)|
    let mut report:Vec<(u64,f64)>=Vec::new();
    // step for reporting a few k's
    let rep_ks:Vec<usize> = {
        let mut v=vec![0usize,1,2,3];
        if m>8 { v.push(m/4); v.push(m/2); v.push(m-1); }
        v.into_iter().filter(|&k|k<m).collect()
    };
    for k in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        let ang0 = -2.0*PI*(k as f64)/mf;
        for j in 0..m {
            let a=ang0*(j as f64);
            re+=w[j]*a.cos(); im+=w[j]*a.sin();
        }
        let wk=((re*re+im*im).sqrt())/mf;
        l1+=wk; l2sq+=wk*wk;
        if k==0 { w0=wk; } else if wk>maxnz { maxnz=wk; }
        if rep_ks.contains(&k) { report.push((k as u64, wk/w0)); }
    }
    (w0,l1,l2sq.sqrt(),maxnz,report)
}

fn analyze(tag:&str,n:u64,p:u64){
    let (w,m)=percoset_w(n,p);
    let mf=m as f64; let nn=n as f64; let q=p as f64;
    let beta=q.ln()/nn.ln();
    let mean:f64 = w.iter().sum::<f64>()/mf;
    // nonprincipal max (exclude the principal coset w~n^2)
    let mut mmax_np=0.0f64;
    for &x in &w { if (x-nn*nn).abs()>0.5 && x>mmax_np {mmax_np=x;} }
    let kappa2 = mmax_np/mean;          // depth-1 equidistribution constant on cosets
    let m_norm = mmax_np.sqrt();        // M = max_{b!=0}|eta_b|
    let c_prize = m_norm/(nn*(q/nn).ln()).sqrt();
    // DFT / multiplicative-character spectrum of w (skip for huge m)
    println!("[{}] n={} p={} v2={} beta={:.2} m={} mean(w)={:.2} (n={})", tag,n,p,v2(p-1),beta,m,mean,n);
    if m<=20000 {
        let (w0,l1,l2,maxnz,rep)=dft_stats(&w);
        // l1/W0 = the largest possible PAPR via triangle ineq (sum_k|W(k)|/W(0))
        // l2/W0 = sqrt of normalized 2nd moment = sqrt(mean(w^2))/mean(w) -- the energy PAPR^{1/2}
        // Ramanujan-flat would give l1/W0 ~ sqrt(m); l1-bounded would give l1/W0 = O(1).
        let spec_norm_ratio = mf*maxnz*maxnz/(l2*l2);  // m*max|W|^2 / sum|W|^2 : spectral-large-sieve const
        println!("    W(0)=mean={:.3}  L1=sum|W(k)|={:.3}  L1/W0={:.4} (sqrt(m)={:.2}; O(1)?)  L2/W0={:.4}",
            w0,l1,l1/w0,mf.sqrt(),l2/w0);
        println!("    max_{{k!=0}}|W(k)|/W0={:.5}  spectral-LS Lambda_max/Lambda_avg={:.3}  kappa2=max/mean={:.4}",
            maxnz/w0, spec_norm_ratio, kappa2);
        print!("    |W(k)|/W0 sample: ");
        for (k,r) in &rep { print!("k={}:{:.4} ",k,r); }
        println!();
    } else {
        println!("    (m={} too large for O(m^2) DFT; reporting kappa2 only)", m);
    }
    println!("    M={:.3} M/sqrt(n)={:.4} C=M/sqrt(n ln(q/n))={:.4}  kappa2={:.4}",
        m_norm, m_norm/nn.sqrt(), c_prize, kappa2);
    println!();
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() } else { vec![16,32,64,128,256] };
    println!("# wf-A02 MULTIPLICATIVE / DILATION-ACTION large sieve on the per-coset spectrum w_j=|eta_{{g^j}}|^2.");
    println!("# Q: is the dilation DFT spectrum W(k) l1-BOUNDED (=> kappa2=O(1) milder win) or Ramanujan-FLAT");
    println!("#    (|W(k)|~W0/sqrt(m) => L1/W0~sqrt(m) => useless, = BGK wall)?  Decided at beta=4 below.");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut p = target.max(100003); p = p - (p%n) + 1; if p<=2 {p+=n;}
        let mut best_s=(0u64,0u32); let mut best_g=(0u64,99u32); let mut cnt=0;
        while cnt<300 { if p%n==1 && isp(p) { let vv=v2(p-1); if vv>best_s.1 {best_s=(p,vv);} if vv<best_g.1 {best_g=(p,vv);} cnt+=1; } p+=n; }
        analyze("STRUCT",n,best_s.0);
        analyze("GENERIC",n,best_g.0);
    }
}
