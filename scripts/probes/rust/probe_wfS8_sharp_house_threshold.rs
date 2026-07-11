// wf-S8: SHARPEN the house/resultant bound on |N(sigma_T)| to PUSH the no-spurious threshold.
//
// THE FRONTIER (from S3/S7): char-0 -> F_p transfer holds (PRIZE PROVEN unconditionally) for any
// n,p with  MAXNORM(n, 2r) < p,  where MAXNORM(n,w) = max over antipodal-free signed configs T of
// weight <= w of |N_{Q(zeta_n)/Q}(sigma_T)| = |det negacyclic matrix of {-1,0,1} coeff vec a|.
//
// The CRUDE "house" bound (S7) is |N(sigma_T)| <= w^{phi(n)} = w^{n/2} (each of the n/2 conjugates
// has modulus <= w). This gives the weight floor w >= p^{2/n}, which -> 1 at prize scale: useless.
//
// THE S8 QUESTION: how much SLACK is in the crude house bound? sigma_T is a SHORT sum of roots,
// NOT a generic length-w algebraic number. Most conjugates are FAR below w. The SHARP controlling
// quantity is the GEOMETRIC MEAN of conjugate moduli  GM(T) = |N(T)|^{2/n}  <=  w  (AM-GM / house).
// We measure the SHARP MAXNORM and its GM = MAXNORM^{2/n}, compare to the crude w, and compute the
// PUSHED threshold N0 = largest n with MAXNORM(n,2r) < p = n^beta at FIXED depth r.
//
// EMITS per (n,w): exact MAXNORM (log2), GM = MAXNORM^{2/phi}, crude house log2 = phi*log2(w),
// the SHARP/CRUDE log2-ratio, and -- at fixed depth r=w/2 -- whether MAXNORM < n^beta (PRIZE PROVEN).
//
// build: rustc -O probe_wfS8_sharp_house_threshold.rs -o /tmp/s8
// run:   /tmp/s8 <nmax_log2> <w> <beta>

fn norm_exact(a:&[i64], d:usize)->i128{
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
            m[i][j] = (m[i][j].wrapping_mul(m[k][k]) - m[i][k].wrapping_mul(m[k][j])) / prev;
        } m[i][k]=0; }
        prev=m[k][k];
    }
    sign * m[d-1][d-1]
}

// exhaustive max |N| over antipodal-free {-1,0,1} configs of weight <= w, deg<phi=d.
// antipodal-free: in the deg<phi=n/2 representation each basis root zeta^i (i<phi) is distinct and
// no zeta^i and -zeta^i=zeta^{i+phi} both occur, which is automatic since we only use i<phi.
// (the negacyclic det already encodes zeta^{phi}=-1, so a config supported on 0..phi-1 is a sum of
//  w distinct roots zeta^i, i<phi, with signs -- exactly an antipodal-free weight-w config.)
fn maxnorm(d:usize, w:usize)->i128{
    let mut a=vec![0i64;d];
    let mut best:i128=0;
    fn rec(a:&mut Vec<i64>, pos:usize, d:usize, left:usize, best:&mut i128){
        if left==0 || pos==d {
            let nv=norm_exact(a,d); let av=if nv<0 {-nv} else {nv};
            if av>*best {*best=av;}
            return;
        }
        // skip pos
        rec(a,pos+1,d,left,best);
        // place +1 / -1 at pos
        a[pos]=1; rec(a,pos+1,d,left-1,best);
        a[pos]=-1; rec(a,pos+1,d,left-1,best);
        a[pos]=0;
    }
    // fix a[0] = 1 by symmetry (config is determined up to global sign / rotation; we still scan all
    // positions for the absolute max but pin first nonzero to +1 to halve work).
    a[0]=1; rec(&mut a,1,d,w-1,&mut best);
    best
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let nmax_log2:u32 = if args.len()>1 { args[1].parse().unwrap() } else { 6 };
    let wfix:usize = if args.len()>2 { args[2].parse().unwrap() } else { 0 }; // 0 => sweep w
    let beta:f64 = if args.len()>3 { args[3].parse().unwrap() } else { 4.0 };

    println!("== wf-S8 sharp house bound vs crude w^(phi)  beta={} ==", beta);
    println!("{:>4} {:>4} {:>5} | {:>12} {:>9} | {:>12} {:>9} | {:>8} | {:>10}",
             "n","phi","w","MAXNORM_l2","GM=N^2/phi","crudeHouse","crude_w","sharp/crude","PRIZE? p=n^b");
    for mu in 3..=nmax_log2 {
        let n=1u64<<mu; let d=(n/2) as usize;
        if d>14 { println!("  n={} phi={} : skipped (exact det too wide for exhaustive)", n,d); continue; }
        let wlist:Vec<usize> = if wfix>0 { vec![wfix] } else { vec![2,4,6,8,(2*((beta*(n as f64).ln()).ceil() as usize)).max(2)] };
        for &w in &wlist {
            if w<2 || w>d { continue; }
            let mn = maxnorm(d,w);
            if mn==0 { continue; }
            let mnl2=(mn as f64).log2();
            let gm = (mn as f64).powf(2.0/(d as f64)); // |N|^{2/phi}*... actually N^{1/phi}; phi=d
            // careful: GM of conjugate moduli = |N|^{1/phi} = |N|^{1/d}
            let gm = (mn as f64).powf(1.0/(d as f64));
            let _=gm; let gm = (mn as f64).powf(1.0/(d as f64));
            let crude_house_l2 = (d as f64)*(w as f64).log2(); // log2(w^phi)
            let crude_w = w as f64;
            let ratio = mnl2/crude_house_l2;
            // prize: r = w/2 (depth), p = n^beta. proven if MAXNORM < n^beta i.e. mnl2 < beta*mu
            let floor_l2 = beta*(mu as f64);
            let proven = mnl2 < floor_l2;
            println!("{:>4} {:>4} {:>5} | {:>12.3} {:>9.4} | {:>12.3} {:>9.0} | {:>8.4} | {:>4} ({:.2}<{:.2})",
                     n,d,w, mnl2, gm, crude_house_l2, crude_w, ratio,
                     if proven {"YES"} else {"no "}, mnl2, floor_l2);
        }
    }
    println!("\n-- GM=N^{{1/phi}} is the SHARP per-conjugate house value (vs crude bound w). sharp/crude<1 = slack. --");
    println!("-- PRIZE column: at FIXED depth r=w/2, is MAXNORM(n,2r) < p=n^beta? (S3 good-prime certificate) --");
}
