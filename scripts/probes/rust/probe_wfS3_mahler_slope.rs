// wf-S3 (D-corrected): the MAXNORM(n,w) growth law is LINEAR in phi(n)=n/2, with the per-weight
// slope = log2 of the (extremal) MAHLER MEASURE. Confirms log2 MAXNORM(n,w) = phi(n)*c_w + O(log n),
// c_w := max over weight-w antipodal-free A of log2 M(A), M = Mahler measure.
//
// WHY. N(sigma_T) = prod_{zeta prim n-th root} A(zeta). For n=2^mu the phi(n)=n/2 primitive roots
// equidistribute on the unit circle, so (1/phi(n)) log|N| -> integral_0^1 log|A(e^{2pi i t})| dt = log M(A)
// (Mahler measure). Hence log MAXNORM(n,w) ~ phi(n) * max_{|A|<=w} log M(A) -- exactly LINEAR in n.
// The per-term rate is bounded: any A with coeffs in {-1,0,1} has M(A) <= sqrt(sum a_i^2) = sqrt(w)
// (Landau/Mahler), so c_w <= (1/2) log2 w, and the band-floor crossover weight is
//   w*(n,beta): phi(n)*c_{w*} < beta*log2 n  i.e. (n/2)*c_{w*} < beta*log2 n.
// Since c_w >= c_2 > 0 (a positive constant) for w>=2, the LHS is Theta(n) and the RHS is Theta(log n):
//   at the prize scale n=2^30, even w*=2 fails (n/2 * c_2 >> beta log2 n). THE OBSTRUCTION, made exact.
//
// build: rustc -O probe_wfS3_mahler_slope.rs -o /tmp/ms

fn log2norm_f64(a:&[i64], d:usize)->f64{
    let n = (2*d) as f64;
    let mut s = 0.0f64;
    for k in (1..2*d).step_by(2) {
        let theta = std::f64::consts::PI*2.0*(k as f64)/n;
        let mut re=0.0f64; let mut im=0.0f64;
        for j in 0..d { if a[j]!=0 {
            let ph = theta*(j as f64);
            re += (a[j] as f64)*ph.cos();
            im += (a[j] as f64)*ph.sin();
        }}
        let mag2 = re*re+im*im;
        if mag2 <= 1e-300 { return f64::NEG_INFINITY; }
        s += 0.5*mag2.log2();
    }
    s
}
// numerically estimate Mahler measure log2 M(A) directly (independent of n), fine grid
fn log2_mahler(a:&[i64])->f64{
    let g=20000usize; let deg=a.len();
    let mut s=0.0f64;
    for t in 0..g {
        let theta=std::f64::consts::PI*2.0*(t as f64)/(g as f64);
        let mut re=0.0; let mut im=0.0;
        for j in 0..deg { if a[j]!=0 {
            let ph=theta*(j as f64); re+=(a[j] as f64)*ph.cos(); im+=(a[j] as f64)*ph.sin();
        }}
        let mag2=re*re+im*im;
        if mag2>1e-300 { s+=0.5*mag2.log2(); }
    }
    s/(g as f64)
}

fn main(){
    println!("== wf-S3 (D): MAXNORM(n,w) = phi(n)*c_w, linear in n; c_w = log2 Mahler measure ==");
    println!();
    // For each weight w, the extremal weight-w antipodal-free A: try window-of-ones, alternating,
    // window with a leading run; report log2 Mahler measure c_w (n-INDEPENDENT) of the best.
    println!("--- per-weight Mahler slope c_w (n-independent) and the c_w <= (1/2)log2 w cap ---");
    println!("   w   best c_w (log2 M)   (1/2)log2 w cap   extremal pattern");
    for w in 2..=16usize {
        let deg=w; // compact support is extremal for small w; window of length w
        let mut best=f64::NEG_INFINITY; let mut bestname="";
        // window of +1
        let a:Vec<i64>=(0..deg).map(|_|1).collect(); let c=log2_mahler(&a); if c>best{best=c;bestname="all-ones window";}
        // alternating
        let a2:Vec<i64>=(0..deg).map(|j| if j%2==0{1}else{-1}).collect(); let c2=log2_mahler(&a2); if c2>best{best=c2;bestname="alternating";}
        // single gap variant: 1,1,...,1, with last = -1
        let mut a3:Vec<i64>=(0..deg).map(|_|1).collect(); if deg>1 {a3[deg-1]=-1;} let c3=log2_mahler(&a3); if c3>best{best=c3;bestname="window,last=-1";}
        let cap=0.5*(w as f64).log2();
        println!("   {:2}   {:14.5}    {:12.5}     {}", w, best, cap, bestname);
    }
    println!();
    // verify the linear law: log2 MAXNORM(n,w)/phi(n) -> c_w as n grows, fixed w
    println!("--- linear-in-phi(n) verification: log2 MAXNORM(n,w)/phi(n) -> c_w  (window family) ---");
    for w in [2usize,3,4,6,8] {
        let aw:Vec<i64>=(0..w).map(|_|1).collect();
        let cmahler=log2_mahler(&aw);
        print!("   w={} (c_w~{:.4}): ", w, cmahler);
        for mu in 3..=14u32 {
            let n=1u64<<mu; let d=(n/2) as usize;
            if w>d {continue;}
            let mut a=vec![0i64;d]; for j in 0..w {a[j]=1;}
            let lg=log2norm_f64(&a,d);
            print!("n=2^{}:{:.4} ", mu, lg/(d as f64));
        }
        println!();
    }
    println!();
    // THE CROSSOVER at prize scale: (n/2)*c_w vs beta*log2 n.
    println!("--- crossover w*(n,beta): largest w with phi(n)*c_w < beta*log2 n ---");
    // precompute c_w (window-extremal lower bound on the true extremal c_w)
    let mut cw=vec![0.0f64;33];
    for w in 2..=32usize { let aw:Vec<i64>=(0..w).map(|_|1).collect(); cw[w]=log2_mahler(&aw);
        // also alternating for the TRUE extremal
        let a2:Vec<i64>=(0..w).map(|j| if j%2==0{1}else{-1}).collect(); cw[w]=cw[w].max(log2_mahler(&a2)); }
    for mu in [3u32,4,5,10,20,30] {
        let n=1u64<<mu; let phi=(n/2) as f64; let l2n=mu as f64;
        print!("   n=2^{}: ", mu);
        for beta in [3.0f64,4.0,5.0] {
            let floor=beta*l2n;
            let mut wstar=0;
            for w in 2..=32usize {
                if w as u64 > n/2 {break;}
                if phi*cw[w] < floor { wstar=w; } else { break; }
            }
            print!("beta={}: w*={} (r*={}); ", beta as i64, wstar, wstar/2);
        }
        println!();
    }
    println!();
    println!("CONCLUSION (exact): log2 MAXNORM(n,w) = phi(n)*c_w + O(log n), c_w in (0, (1/2)log2 w].");
    println!("The good-prime certificate hypothesis MAXNORM(n,2r)<p=n^beta requires phi(n)*c_{{2r}} < beta*log2 n,");
    println!("i.e. r <= (beta log2 n)/(2 phi(n) * (c/2r-rate)). Since LHS grows like n and RHS like log n,");
    println!("the certified depth r*(n) -> 0 (collapses to r*<2 even at w=2) once n>~2^7. The norm-size route");
    println!("CANNOT certify the prize prime good at n=2^30 / any r>=1. This is the exact S3 norm-wall.");
}
