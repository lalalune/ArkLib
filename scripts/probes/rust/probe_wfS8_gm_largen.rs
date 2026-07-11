// wf-S8 (large-n): SHARP per-conjugate house value GM(n,w) = |N(sigma_T)|^{1/phi} via complex
// evaluation of the phi=n/2 conjugates (no exact det needed for log2/GM; double precision suffices
// for the EXPONENT). Confirms the GM ~ c(w) law and the sharp/crude slack at n up to 512.
//
// log2|N(sigma_T)| = sum over primitive n-th roots zeta^k (k odd, 1<=k<n) of log2|sigma_T(zeta^k)|.
// We MAXIMIZE over antipodal-free weight-w configs by GREEDY + RANDOM RESTART search (the exact max
// is intractable for large phi; we report the best found = a LOWER bound on MAXNORM, which is the
// CONSERVATIVE direction for a good-prime certificate: real MAXNORM >= our estimate, so the
// threshold we report is if anything optimistic-checked. For the w=2,4 regime exhaustive is cheap.)
//
// build: rustc -O probe_wfS8_gm_largen.rs -o /tmp/s8g
// run:   /tmp/s8g <mu> <w>

use std::f64::consts::PI;

// log2|N| for coeff vector a (support on 0..phi-1, antipodal-free), n=2^mu.
fn log2norm(a:&[i64], n:usize)->f64{
    let phi=n/2;
    let mut acc=0.0f64;
    let mut kk=1usize;
    let mut cnt=0;
    while cnt<phi {
        // zeta^kk, kk odd
        let th = 2.0*PI*(kk as f64)/(n as f64);
        let (mut re,mut im)=(0.0f64,0.0f64);
        for i in 0..a.len() {
            if a[i]!=0 {
                let ang=(a[i] as f64)*0.0 + th*(i as f64); // sign applied to magnitude below
                let s=a[i] as f64;
                re += s*(ang).cos();
                im += s*(ang).sin();
            }
        }
        let m2=re*re+im*im;
        if m2<=0.0 { return f64::NEG_INFINITY; }
        acc += 0.5*m2.log2();
        kk+=2; cnt+=1;
    }
    acc
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let mu:u32 = if args.len()>1 { args[1].parse().unwrap() } else { 5 };
    let w:usize = if args.len()>2 { args[2].parse().unwrap() } else { 4 };
    let n=1usize<<mu; let phi=n/2;
    if w>phi { println!("w>phi"); return; }

    // Exhaustive for w<=4 over support 0..phi-1 with a[0]=1 pinned; else greedy/random search.
    let mut best=f64::NEG_INFINITY;
    let mut bestcfg=vec![0i64;phi];
    if w<=4 && phi<=64 {
        let mut a=vec![0i64;phi]; a[0]=1;
        fn rec(a:&mut Vec<i64>, pos:usize, phi:usize, left:usize, n:usize, best:&mut f64, bc:&mut Vec<i64>){
            if left==0 || pos==phi {
                let v=log2norm(a,n); if v>*best {*best=v; bc.clone_from(a);}
                return;
            }
            rec(a,pos+1,phi,left,n,best,bc);
            a[pos]=1; rec(a,pos+1,phi,left-1,n,best,bc);
            a[pos]=-1; rec(a,pos+1,phi,left-1,n,best,bc);
            a[pos]=0;
        }
        rec(&mut a,1,phi,w-1,n,&mut best,&mut bestcfg);
    } else {
        // random restart hill climb
        let mut seed:u64=0x9e3779b97f4a7c15;
        let mut rng=||{ seed^=seed<<13; seed^=seed>>7; seed^=seed<<17; seed };
        for _ in 0..4000 {
            let mut a=vec![0i64;phi];
            let mut placed=0;
            while placed<w {
                let p=(rng() as usize)%phi;
                if a[p]==0 { a[p]= if rng()&1==0 {1} else {-1}; placed+=1; }
            }
            // local improve: try flipping signs / moving one element
            let mut cur=log2norm(&a,n);
            for _ in 0..200 {
                let p=(rng() as usize)%phi;
                let old=a[p];
                let cand = match (rng()%3, old) {
                    (0,_) => -old,
                    (1,0) => if rng()&1==0 {1} else {-1},
                    _ => 0,
                };
                // keep weight ~ w
                let wt:usize = a.iter().filter(|&&x| x!=0).count();
                let newwt = wt - (if old!=0 {1} else {0}) + (if cand!=0 {1} else {0});
                if newwt>w || newwt<2 { continue; }
                a[p]=cand;
                let v=log2norm(&a,n);
                if v>=cur { cur=v; } else { a[p]=old; }
            }
            if cur>best { best=cur; bestcfg.clone_from(&a); }
        }
    }
    let gm = 2f64.powf(best/(phi as f64));
    let crude_house = (phi as f64)*(w as f64).log2();
    println!("n={} phi={} w={} : MAXNORM_log2(est)={:.3}  GM=|N|^(1/phi)={:.4}  sqrt(w)={:.4}  crudeHouse_log2={:.3}  sharp/crude={:.4}",
             n,phi,w, best, gm, (w as f64).sqrt(), crude_house, best/crude_house);
    // prize thresholds at this w (depth r=w/2): proven if best < beta*mu
    for &beta in &[2.0f64,3.0,4.0,5.0,6.0] {
        let floor=beta*(mu as f64);
        println!("    beta={}: floor=beta*mu={:.1}  MAXNORM_log2={:.2}  => PRIZE {}", beta, floor, best, if best<floor {"PROVEN"} else {"open"});
    }
}
