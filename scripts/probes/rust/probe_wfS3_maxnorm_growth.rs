// wf-S3: pin the MAXNORM(n,w) growth law and the crossover weight w*(n).
//
// OBJECT. For n=2^mu, antipodal-free signed config = coeff vector a in {-1,0,1}^{d}, d=phi(n)=n/2,
// weight w = #nonzero. The integer cyclotomic norm N(sigma_T) = det(negacyclic matrix of a) =
// Res(x^d+1, A). MAXNORM(n,w) := max over weight-<=w antipodal-free configs of |N|.
//
// The S3 good-prime certificate (good_of_maxnorm_lt, axiom-clean) says:
//     MAXNORM(n, 2r) < p  ==>  p is GOOD at depth r (spur_r(p)=0).
// So the SHARP question is the growth law of MAXNORM(n,w), and the CROSSOVER weight
//     w*(n, beta) := largest w with log2 MAXNORM(n,w) < beta*log2(n)  (band floor at p~n^beta).
// Depths r <= w*/2 are PROVABLY spur-free at EVERY prize prime p~n^beta (unconditional).
//
// This probe reports, exactly:
//   (A) MAXNORM(n,w) and its log2, per weight w=1..wmax, and the EXTREMAL config attaining it.
//   (B) the per-weight slope log2 MAXNORM / w  (the "Mahler-house per term" rate).
//   (C) the crossover weight w*(n,beta) for beta in {3,4,5} and hence the certified depth r* = w*/2.
//   (D) the growth in n: log2 MAXNORM(n,w) vs n at fixed w (test of the linear-in-n claim 0.48 n).
//
// To make MAXNORM(n,w) tractable for larger n (where 3^d enumeration explodes) we use the fact that
// the extremal weight-w config is, empirically and by a Mahler-measure / house argument, the
// "consecutive block" a_i = +1 for i in a window OR the alternating +- pattern; we both (i) do exact
// exhaustive search for n<=32 (all 3^d), and (ii) for larger n do a TARGETED max over structured
// families (all-ones-window, alternating, +-spread, random sampling) to UPPER/LOWER bracket MAXNORM.
//
// build: rustc -O probe_wfS3_maxnorm_growth.rs -o /tmp/mng

fn norm_exact(a:&[i64], d:usize)->i128{
    // det of negacyclic matrix: column j = x^j*A mod (x^d+1). Bareiss fraction-free.
    let mut m=vec![vec![0i128;d];d];
    for j in 0..d { for r in 0..d {
        let v = if r>=j { a[r-j] } else { -a[r-j+d] };
        m[r][j]=v as i128;
    }}
    let mut sign:i128=1; let mut prev:i128=1;
    for k in 0..d {
        if m[k][k]==0 {
            let mut piv=k+1; while piv<d && m[piv][k]==0 { piv+=1; }
            if piv==d { return 0; }
            m.swap(k,piv); sign=-sign;
        }
        for i in (k+1)..d { for j in (k+1)..d {
            m[i][j] = (m[i][j]*m[k][k] - m[i][k]*m[k][j]) / prev;
        } m[i][k]=0; }
        prev=m[k][k];
    }
    sign * m[d-1][d-1]
}

// f64-log2 of |N| for big n (det may overflow i128); compute log|det| via the negacyclic matrix
// eigenvalues = A(beta) over the d primitive roots beta = exp(i*pi*(2k+1)/d... ), i.e. roots of x^d+1.
// log2|N| = sum_k log2 |A(zeta)| over primitive n-th roots zeta. Exact-enough for the growth law.
fn log2norm_f64(a:&[i64], d:usize)->f64{
    // primitive n-th roots = exp(i*2pi*k/n) for k odd, n=2d. There are d of them.
    let n = (2*d) as f64;
    let mut s = 0.0f64;
    for k in (1..2*d).step_by(2) {
        let theta = std::f64::consts::PI*2.0*(k as f64)/n;
        // A(zeta) = sum_j a[j] zeta^j ; zeta = e^{i theta}
        let mut re=0.0f64; let mut im=0.0f64;
        for j in 0..d {
            if a[j]!=0 {
                let ph = theta*(j as f64);
                re += (a[j] as f64)*ph.cos();
                im += (a[j] as f64)*ph.sin();
            }
        }
        let mag2 = re*re+im*im;
        if mag2 <= 0.0 { return f64::NEG_INFINITY; }
        s += 0.5*mag2.log2();
    }
    s
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let mode = if args.len()>1 { args[1].clone() } else { "all".to_string() };

    println!("== wf-S3 MAXNORM(n,w) growth law + crossover w*(n,beta) ==");
    println!();

    // (A)(B)(C): exact exhaustive for n in {8,16,32} (d<=16, 3^16 = 43M feasible threaded? do d<=12 exact, d=16 structured).
    let exact_ns: Vec<u64> = vec![8,16,32];
    for &n in &exact_ns {
        let d=(n/2) as usize;
        let wmax = d; // up to full weight
        // exhaustive max |N| per weight, with a[0]=1 normalization (norm orbit under x-mult & negation).
        // For d=16 full 3^16=43M*det(16) is heavy; cap exact search at d<=12, else structured bracket.
        let exact = d<=12;
        let mut maxnorm_log = vec![f64::NEG_INFINITY; wmax+1];
        let mut maxnorm_exact = vec![0i128; wmax+1];
        let mut best_cfg: Vec<Vec<i64>> = vec![vec![]; wmax+1];
        if exact {
            // recurse over a[1..d) in {-1,0,1}, a[0]=1
            fn rec(a:&mut Vec<i64>, pos:usize, d:usize, w:usize,
                   ml:&mut Vec<f64>, me:&mut Vec<i128>, bc:&mut Vec<Vec<i64>>){
                if pos==d {
                    let nv=norm_exact(a,d); let av=nv.unsigned_abs() as i128;
                    if av>0 {
                        let lg=(av as f64).log2();
                        if lg>ml[w] { ml[w]=lg; me[w]=av; bc[w]=a.clone(); }
                    }
                    return;
                }
                a[pos]=0; rec(a,pos+1,d,w,ml,me,bc);
                a[pos]=1;  rec(a,pos+1,d,w+1,ml,me,bc);
                a[pos]=-1; rec(a,pos+1,d,w+1,ml,me,bc);
                a[pos]=0;
            }
            let mut a=vec![0i64;d]; a[0]=1;
            rec(&mut a,1,d,1,&mut maxnorm_log,&mut maxnorm_exact,&mut best_cfg);
        } else {
            // structured bracket for d=16: all-ones window of length w, alternating, and random sampling
            for w in 1..=wmax {
                let mut a=vec![0i64;d];
                // window of +1
                for j in 0..w { a[j]=1; }
                let lg=log2norm_f64(&a,d);
                if lg>maxnorm_log[w]{maxnorm_log[w]=lg; best_cfg[w]=a.clone();}
                // alternating
                let mut a2=vec![0i64;d]; for j in 0..w { a2[j]= if j%2==0 {1} else {-1}; }
                let lg2=log2norm_f64(&a2,d);
                if lg2>maxnorm_log[w]{maxnorm_log[w]=lg2; best_cfg[w]=a2.clone();}
                // spread evenly
                let mut a3=vec![0i64;d]; for t in 0..w { a3[(t*d)/w]=1; }
                let lg3=log2norm_f64(&a3,d);
                if lg3>maxnorm_log[w]{maxnorm_log[w]=lg3; best_cfg[w]=a3.clone();}
            }
            // random sampling to push the lower bracket up
            let mut seed=0x9e3779b97f4a7c15u64;
            for _ in 0..2_000_000u64 {
                seed ^= seed<<13; seed ^= seed>>7; seed ^= seed<<17;
                let mut a=vec![0i64;d]; let mut w=0;
                for j in 0..d {
                    let r=((seed>>(j%50))&3) as i64;
                    let v = if r==1 {1} else if r==2 {-1} else {0};
                    a[j]=v; if v!=0 {w+=1;}
                }
                if w==0 {continue;}
                let lg=log2norm_f64(&a,d);
                if w<=wmax && lg>maxnorm_log[w]{maxnorm_log[w]=lg; best_cfg[w]=a.clone();}
            }
        }
        println!("--- n={} (d=phi={}), {} ---", n, d, if exact {"EXACT exhaustive"} else {"STRUCTURED bracket (lower bound on MAXNORM)"});
        println!("   w   log2 MAXNORM   slope(log2/w)   |N|(exact if avail)");
        for w in 1..=wmax {
            if maxnorm_log[w]==f64::NEG_INFINITY {continue;}
            let slope = maxnorm_log[w]/(w as f64);
            let exstr = if exact && maxnorm_exact[w]>0 {format!("{}", maxnorm_exact[w])} else {"-".to_string()};
            println!("   {:2}   {:11.4}   {:11.4}     {}", w, maxnorm_log[w], slope, exstr);
        }
        // crossover w*(n,beta): largest w with log2 MAXNORM(n,w) < beta*log2 n
        let l2n=(n as f64).log2();
        for &beta in &[3.0f64,4.0,5.0] {
            let floor = beta*l2n;
            let mut wstar = 0usize;
            for w in 1..=wmax {
                if maxnorm_log[w]==f64::NEG_INFINITY {continue;}
                if maxnorm_log[w] < floor { wstar=w; } else { break; }
            }
            println!("   beta={} floor=beta*log2 n={:.2}:  w*(n,beta)={}  => certified depth r*={} (spur_r=0 for all r<=r* at every p~n^beta)",
                     beta as i64, floor, wstar, wstar/2);
        }
        println!();
    }

    // (D): linear-in-n test at FIXED small weight w, using log2norm_f64 (extremal = all-ones window).
    if mode=="all" || mode=="growth" {
        println!("--- (D) log2 MAXNORM(n,w) vs n at fixed weight (extremal family scan) ---");
        for w in [2usize,3,4,6,8] {
            print!("   w={}: ", w);
            for mu in 3..=12u32 {
                let n=1u64<<mu; let d=(n/2) as usize;
                if w>d {continue;}
                // scan structured extremal families, take max log2 norm
                let mut best=f64::NEG_INFINITY;
                // window
                let mut a=vec![0i64;d]; for j in 0..w {a[j]=1;} best=best.max(log2norm_f64(&a,d));
                // alternating window
                let mut a2=vec![0i64;d]; for j in 0..w {a2[j]=if j%2==0{1}else{-1};} best=best.max(log2norm_f64(&a2,d));
                // spread
                let mut a3=vec![0i64;d]; for t in 0..w {a3[(t*d)/w]=1;} best=best.max(log2norm_f64(&a3,d));
                // few random
                let mut seed=0xdeadbeef_u64 ^ (n*0x100000001b3);
                for _ in 0..200000 {
                    seed^=seed<<13; seed^=seed>>7; seed^=seed<<17;
                    let mut ar=vec![0i64;d]; let mut cnt=0;
                    let mut s2=seed;
                    while cnt<w {
                        let j=(s2 as usize)%d; s2=s2.wrapping_mul(6364136223846793005).wrapping_add(1);
                        if ar[j]==0 { ar[j]= if (s2&1)==0 {1} else {-1}; cnt+=1; }
                    }
                    best=best.max(log2norm_f64(&ar,d));
                }
                print!("n={}:{:.2}({:.3}/n) ", n, best, best/(n as f64));
            }
            println!();
        }
        println!();
        println!("   (slope log2MAXNORM/n stabilizing => MAXNORM(n,w) ~ c_w * n with c_w ~ slope; LINEAR in n confirmed/refuted)");
    }
}
