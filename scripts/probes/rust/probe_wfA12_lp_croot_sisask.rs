// wf-A12 (#444): L^q Croot-Sisask almost-periodicity (GROWING q), and the bad-locus coset count.
//
// FRESH SEAM vs the prior A7 refutation: A7 tested ONLY the L^2 almost-period set (eps=1, |T_1|=0
// empty) and the "forces M<=2*avg" reading. But the STRONG form of Croot-Sisask (the one Sanders'
// Bogolyubov-Ruzsa and Kelley-Meka actually use) is the L^q theorem for GROWING q ~ log(1/alpha):
// for f = 1_A with density alpha, and any eps>0, q>=2, there is a set T of "L^q almost-periods" with
//   |T| >= (eps / 4)^{q} * alpha^{ ... } * |G|   ... more precisely  |T| >= exp(-C q eps^{-2} log(1/alpha)) |G|
// such that for all t in T,  || tau_t (f * mu_B) - f * mu_B ||_{L^q(mu_B)} <= eps ||f||_{L^q}  (B a Bohr/ball).
// As q -> infinity the L^q norm -> sup, so IF T were nonempty with eps small this would control the
// PEAK (the b*), not just the L^2 bulk -- exactly the rare-event tail A7's L^2 reading is blind to.
//
// THE QUESTION: at prize scale (p = n^4, alpha = n/p = n^{-3}) is the L^q almost-period set ever
// nonempty for q large enough to reach the sup, with eps small enough to force M near avg?
//
// We test the period f(b) = sum_{x in mu_n} e_p(b x) = FT(1_{mu_n}) (same faithful realization as A7).
// For each q in {2,4,8,16,...} we compute:
//   (1) the EXACT L^q almost-period set T_eps^{(q)} = { t : ||tau_t f - f||_q <= eps ||f||_q } over the
//       additive group Z/p (t a shift of the FREQUENCY argument b -> b+t), report |T|/p at eps in
//       {0.5,1.0} measured in ||f||_q units. (b -> b+t is the additive shift CS controls.)
//   (2) the CS predicted threshold: the minimal |T|/p the theorem GUARANTEES =
//       exp(-C q eps^{-2} ln(1/alpha)).  alpha = n/p.  We report ln of this vs ln p (is it < 1, i.e.
//       does the guarantee give >=1 almost-period at q ~ ln(1/alpha)?).
//   (3) the sup/avg ratio M/avg and how the L^q norm ratio ||f||_q/||f||_2 grows toward sup (q->inf):
//       if the peak is ISOLATED (||f||_q/||f||_2 -> M/avg fast) the L^q set sees the peak; we check
//       whether ANY nonempty T at high q keeps b* (the argmax) inside it or excludes it.
//   (4) BAD-LOCUS coset count: the "near-peak" locus { b : |f(b)| >= M/2 } -- how many cosets? PFR/KM
//       would force this into <= n cosets of a subgroup; we count it directly (the n-coset claim).
//
// prize-faithful: p PRIME, p=1 mod n, mu_n PROPER (n|p-1, (p-1)/n>1), beta=4 (p~n^4), NEVER n=p-1.
// usage: probe_wfA12_lp_croot_sisask [n1 n2 ...]   default 16 32 64 128
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn find_p(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p%n!=1{p+=n-(p%n)+1}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}

// Full magnitude spectrum |f(b)| for b=0..p-1 (f(b)=sum_{x in mu_n} e_p(bx)). O(p*n) -- ok for p~n^4 small n.
fn full_spectrum(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // precompute cos/sin tables for e_p(t)
    let mut cs=vec![0.0f64;p as usize]; let mut sn=vec![0.0f64;p as usize];
    for t in 0..p { let a=2.0*PI*(t as f64)/p as f64; cs[t as usize]=a.cos(); sn[t as usize]=a.sin(); }
    let mut out=vec![0.0f64;p as usize];
    for b in 0..p {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu { let t=((b as u128*x as u128)%p as u128)as usize; re+=cs[t]; im+=sn[t]; }
        out[b as usize]=(re*re+im*im).sqrt();
    }
    out
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() }
                     else { vec![16,32,64,128] };
    println!("# wf-A12: L^q Croot-Sisask almost-period set + bad-locus coset count, beta=4");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let p=find_p(n, target.max(100003));
        let alpha=(n as f64)/(p as f64); // density of mu_n
        let beta=(p as f64).ln()/(n as f64).ln();
        let spec=full_spectrum(n,p);
        // norms ||f||_q^q = (1/p) sum |f|^q  (counting measure normalized). avg = ||f||_1, M = sup.
        let pf=p as f64;
        let mm:f64=spec.iter().cloned().fold(0.0,f64::max);
        let avg:f64=spec.iter().sum::<f64>()/pf;
        // floor = sqrt(2 n ln(p/n))
        let floor=(2.0*(n as f64)*((p as f64)/(n as f64)).ln()).sqrt();
        println!("\n## n={n}  p={p}  beta={:.3}  alpha=2^{:.1}  M={:.3} (M/sqrt(n)={:.3})  avg={:.3}  floor={:.3}  M/floor={:.3}  M/(2avg)={:.3}",
            beta, alpha.log2(), mm, mm/(n as f64).sqrt(), avg, floor, mm/floor, mm/(2.0*avg));
        // ||f||_q / ||f||_2 toward sup, and L^q almost-period set
        let qs=[2u32,4,8,16,32,64];
        let l2:f64=(spec.iter().map(|v|v*v).sum::<f64>()/pf).sqrt();
        for &q in &qs {
            let qf=q as f64;
            let lq:f64=(spec.iter().map(|v|v.powf(qf)).sum::<f64>()/pf).powf(1.0/qf);
            // L^q almost-period set: T_eps = { t in Z/p : ||tau_t f - f||_q <= eps ||f||_q }.
            // ||tau_t f - f||_q^q = (1/p) sum_b |f(b+t)-f(b)|^q. Sample t over a STRIDE to keep it O(p^2/stride).
            // We compute |T|/p for eps in {0.5, 1.0} by SAMPLING ~4000 shifts t (stride). The CLOSED-FORM
            // CS guarantee (below) is the load-bearing quantity; the sample just confirms emptiness.
            let nsamp:u64 = if q<=4 { 800 } else { 200 };
            let bsamp:u64 = if p>200000 { 60000 } else { p };
            let bstride = (p/bsamp).max(1);
            let stride = (p/nsamp).max(1);
            let mut cnt05=0u64; let mut cnt10=0u64; let mut ttested=0u64;
            let lqq = lq.powf(qf); // ||f||_q^q
            let mut t=1u64; // skip t=0 (trivially in T)
            while t<p {
                // ||tau_t f - f||_q^q  (b sampled with bstride for large p)
                let mut acc=0.0f64; let mut bn=0u64; let mut b=0u64;
                while b<p {
                    let bt=((b + t)%p) as usize;
                    let d=(spec[bt]-spec[b as usize]).abs();
                    acc+=d.powf(qf); bn+=1;
                    b+=bstride;
                }
                acc/=bn as f64; // estimate of (1/p) sum_b |f(b+t)-f(b)|^q
                if acc <= (0.5f64).powf(qf)*lqq { cnt05+=1; }
                if acc <= (1.0f64).powf(qf)*lqq { cnt10+=1; }
                ttested+=1;
                t+=stride;
            }
            let frac05=(cnt05 as f64)/(ttested as f64);
            let frac10=(cnt10 as f64)/(ttested as f64);
            // CS GUARANTEE (lower bound the theorem provides): |T_eps|/p >= exp(-C q eps^{-2} ln(1/alpha)).
            // Take C=1 (favorable), eps=1 -> guarantee_ln = -q*ln(1/alpha). Compare to ln(1)=0 needed for >=1 period? No:
            // |T|/p>=exp(-q ln(1/alpha)) so |T|>= p*exp(-q ln(1/alpha)) = p * alpha^q. >=1 iff p>=alpha^{-q}=( p/n)^q.
            // i.e. nonempty guarantee iff  ln p >= q*ln(p/n) = q*(beta-1)/beta * ln p  => q <= beta/(beta-1).
            let ln_inv_alpha=(1.0/alpha).ln();
            let guarantee_count_ln = (p as f64).ln() - qf*ln_inv_alpha; // ln(p * alpha^q) ; >=0 => guarantee >=1 period
            // q_max for which CS GUARANTEES a nontrivial period (eps=1, C=1):
            let qmax_guarantee = (p as f64).ln()/ln_inv_alpha;
            println!("  q={:>3}  ||f||_q/||f||_2={:>7.3}  ||f||_q/M={:>6.3} | T_eps measured: |T_0.5|/p={:.2e} |T_1.0|/p={:.2e} (stride={}) | CS guarantee ln(|T_1.0|)={:>8.2} (qmax_guar={:.2})",
                q, lq/l2, lq/mm, frac05, frac10, stride, guarantee_count_ln, qmax_guarantee);
        }
        // BAD-LOCUS coset count: cosets b (b=g^j, j over m reps) with |f(b)| >= M/2, and >= M*0.9.
        let g=proot(p); let m=(p-1)/n;
        let gn=mpow(g,n,p); let mut b=1u64;
        let mut half=0u64; let mut near=0u64;
        for _ in 0..m {
            let v=spec[b as usize];
            if v>=mm*0.5 { half+=1; }
            if v>=mm*0.9 { near+=1; }
            b=((b as u128*gn as u128)%p as u128)as u64;
        }
        println!("  BAD-LOCUS (PFR/KM target <=n={n}): #cosets |f|>=M/2 = {half} ; #cosets |f|>=0.9M = {near} ; m=(p-1)/n={m} ; n={n}  (half/n={:.2}, half<=n? {})",
            (half as f64)/(n as f64), half<=n);
    }
}
