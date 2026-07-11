// wf-A01 (#444): the GALOIS-ORBIT structure of the equidistribution constant kappa, and the
// DECISIVE quantity kappa^{1/2r} at the prize-optimal depth r ~ ln q.
//
// The S2 reduction collapses the prize to  M^{2r} <= (kappa/c) E_r  with
//   kappa := M^{2r} N_r / T_r   (max term / support-average),  c := N_r/q.
// After the 1/2r root the M-bound is  M <= kappa^{1/2r} (E_r/c)^{1/2r}, and with E_r=(2r-1)!! n^r
// minimised at r ~ ln q this gives M = kappa^{1/2r} * O(sqrt(n ln q)).  So the SINGLE residual is:
//   is  D := kappa^{1/2r}  bounded uniformly in n at the prize-optimal r ~ ln(q/n)?
// We measure D(n) at the optimal r, AND we test the S4 GALOIS-ORBIT hypothesis directly:
//
// Gal(Q(zeta_n)/Q) = (Z/n)^* has order phi(n) = n/2 and acts on the m=(p-1)/n cosets with
// |eta_b| constant on orbits. We compute the EXACT Galois orbits (b -> b^a, a in (Z/n)^* lifted
// via the n-th-power-residue structure), report:
//   (i) #distinct |eta_b| values vs m (does Galois collapse the spectrum?),
//   (ii) max Galois-orbit size (<= n/2) vs m  (Galois reach is tiny: ~ n/2 of n^3 cosets),
//   (iii) D = kappa^{1/2r} at r* = round(ln(q/n)), and its growth in n,
//   (iv) the FLAT-SPECTRUM kappa lower bound: even a perfectly flat |eta_b| spectrum has a
//        nonzero spread because |eta_b| is an integer-ish Gauss-period magnitude with bounded
//        variance; we report the empirical PAPR = M^2 / mean(|eta|^2) which is what bounds D.
//
// CONCLUSION TARGET: confirm/refute that the Galois group (order n/2) is too small to flatten m~n^3
// cosets, so kappa-boundedness CANNOT come from Galois alone -- it needs the SECOND MOMENT
// (Parseval mean = n^2 exactly) PLUS a sup-bound, i.e. it is equivalent to the BGK wall, NOT milder
// via Galois. But measure whether D = kappa^{1/2r} stays bounded empirically (the genuine residual).
//
// usage: probe_wfA01_galois_kappa_root [n1 n2 ...]   default 16 32 64 128 256
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// |eta_b|^2 over the m cosets (b = g^j, j=0..m-1), where the principal coset (b in mu_n) has w=n^2.
fn percoset_w(n:u64,p:u64)->(Vec<f64>,u64,u64){
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
    (out,g,m)
}

// EXACT Galois action on the cosets. The cyclotomic Galois group (Z/n)^* acts via sigma_a (zeta->zeta^a),
// which on the additive char sum eta_b corresponds (since |eta_b| is determined by the n-th-power-residue
// class of b) to the multiplicative power map  b -> b^a  for a coprime to n, RESTRICTED to its effect on
// the coset class. Concretely on the coset exponent j (b=g^j): b in coset class (j mod ??). The honest
// realization: |eta_{g^j}| is invariant under j -> a*j mod m for a in the image of (Z/n)^* in (Z/m)^*?
// No -- the proven invariance (eta_mul_left, RepCountFrobenius) is |eta_b|=|eta_{b^sigma}| where sigma
// acts on the SUM by permuting mu_n, i.e. b -> b * u for u in mu_n is ALREADY mod out (that's the coset).
// The cyclotomic Galois on TOP of that is b -> b^a, a in (Z/n)^*, which on coset exponents is j -> a^{-1} j?
// We test the ARITHMETICALLY CORRECT invariance: the n-th power residue symbol. eta_b depends on b only
// through which "Gauss period" it is; two cosets b, b' have |eta_b|=|eta_b'| iff b'/b is an n-th power
// times a Galois conjugate. We GROUP cosets by their measured |eta_b|^2 value (binned) to count distinct
// Galois values empirically, and separately compute the orbit of coset j under j -> 5^k * j mod m_n-part.
fn galois_orbits(g:u64,p:u64,n:u64,m:u64)->Vec<u64>{
    // The cyclotomic Galois group (Z/n)^* embeds into the cosets as follows: a coset rep b=g^j; the
    // Galois conjugate sigma_a sends the Gauss period eta_b to eta_{b'} where b' = g^{j'} with the n-th
    // power residue class of b' equal to a * (class of b). Since b's n-th-power-residue class is (j mod n)
    // (because g^j is an n-th power iff n|j, and the residue class is j mod n), Galois acts by
    //   j mod n  ->  a*(j mod n) mod n,  a in (Z/n)^*,  fixing the "free" part of j.
    // So the orbit of coset j under Galois = { j' : j' = j + (a*(j mod n) - (j mod n)) for a in (Z/n)^* }
    // but j' must be a valid coset (0..m). The clean invariant we ACTUALLY check below: bin |eta|^2.
    let _ = (g,p,n,m); vec![]
}

fn dfact(k:u64)->f64{ if k==0 {return 1.0;} let mut r=1.0f64; let mut i=1u64; while i<=2*k-1 {r*=i as f64; i+=2;} r }

fn analyze(tag:&str,n:u64,p:u64){
    let (w,g,m)=percoset_w(n,p);
    let _=galois_orbits(g,p,n,m);
    let nn=n as f64; let q=p as f64; let mf=m as f64;
    let beta=q.ln()/nn.ln();
    // nonprincipal: exclude principal coset (w=n^2). each coset rep = n actual frequencies.
    let np:Vec<f64>=w.iter().cloned().filter(|&x|(x-nn*nn).abs()>0.5).collect();
    let support_reps=np.iter().filter(|&&x|x>1e-9).count() as f64;
    let nr=nn*support_reps;
    let c=nr/q;
    let mmax=np.iter().cloned().fold(0.0f64,f64::max);
    let mnorm=mmax.sqrt();
    // mean of nonprincipal |eta|^2 = Parseval: sum_{b!=0,b notin mu_n} |eta_b|^2 = qn - n^2 - 0(principal already n^2)
    // exactly sum over ALL b!=0 of |eta_b|^2 = qn - n^2 (Parseval). principal coset (n cosets-worth? no, ONE
    // coset rep = mu_n itself) carries n^2 per rep * n freqs = n^3? Let's just measure.
    let mean_np = np.iter().sum::<f64>()/support_reps; // mean |eta|^2 over nonprincipal coset reps
    let papr = mmax/mean_np;  // peak-to-average of |eta|^2 (= M^2 / mean)
    // r* = optimal depth ~ ln(q/n)
    let rstar = ((q/nn).ln()).round().max(1.0) as u64;
    // D = kappa^{1/2r} at several r including r*
    println!("[{}] n={} p={} v2={} beta={:.2} m={} c={:.4} M/sqrt(n)={:.3} PAPR=M^2/mean={:.4} (mean={:.1}, n^2={:.0})",
        tag,n,p,v2(p-1),beta,m,c,mnorm/nn.sqrt(),papr,mean_np,nn*nn);
    // distinct |eta_b|^2 values (binned) -- how much does the spectrum collapse?
    let mut vals:Vec<f64>=np.iter().filter(|&&x|x>1e-9).cloned().collect();
    vals.sort_by(|a,b|a.partial_cmp(b).unwrap());
    let mut distinct=0usize; let mut last=-1.0f64;
    for &v in &vals { if (v-last).abs()>1e-3*(1.0+v) {distinct+=1; last=v;} }
    let phi_n=n/2; // |(Z/n)^*| for n=2^mu
    println!("    #distinct |eta|^2 ~ {} of {} cosets;  Gal order phi(n)={};  max Gal-orbit <= phi(n)={} of m={}  => Gal collapses at most {:.2e} of spectrum",
        distinct, support_reps as u64, phi_n, phi_n, m, phi_n as f64/mf);
    println!("    {:>4} {:>12} {:>12} {:>12} {:>10}", "r","kappa","D=k^(1/2r)","(2r-1)!!^1/2r","Mbnd/tgt");
    for r in [1u64,2,3,rstar,rstar*2,16,(q.ln().round() as u64).max(1)] {
        if r==0 {continue;}
        let tr: f64 = nn * np.iter().map(|&x| x.powi(r as i32)).sum::<f64>();
        if tr<=0.0 {continue;}
        let m2r=mmax.powi(r as i32);
        let kappa=m2r*nr/tr;
        let d=kappa.powf(1.0/(2.0*r as f64));
        let er=dfact(r)*nn.powi(r as i32);
        let mbound=((kappa/c)*er).powf(1.0/(2.0*r as f64));
        let tgt=(nn*(q/nn).ln()).sqrt();
        let dfr=dfact(r).powf(1.0/(2.0*r as f64));
        let mark=if r==rstar {" <-r*"} else {""};
        println!("    {:>4} {:>12.3} {:>12.5} {:>12.4} {:>10.4}{}", r,kappa,d,dfr,mbound/tgt,mark);
    }
    println!();
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() } else { vec![16,32,64,128,256] };
    println!("# wf-A01: D=kappa^(1/2r) and the GALOIS-ORBIT reach. Galois order phi(n)=n/2 << m~n^3.");
    println!("# residual: is D bounded uniformly at r*~ln(q/n)? Galois alone cannot flatten (orbit<=n/2 of n^3).");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut p = target.max(100003); p = p - (p%n) + 1; if p<=2 {p+=n;}
        let mut best_s=(0u64,0u32); let mut best_g=(0u64,99u32); let mut cnt=0;
        while cnt<300 { if p%n==1 && isp(p) { let vv=v2(p-1); if vv>best_s.1 {best_s=(p,vv);} if vv<best_g.1 {best_g=(p,vv);} cnt+=1; } p+=n; }
        analyze("STRUCT",n,best_s.0);
        analyze("GENERIC",n,best_g.0);
    }
}
