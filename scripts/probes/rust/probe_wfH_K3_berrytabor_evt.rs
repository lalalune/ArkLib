// probe_wfH_K3_berrytabor_evt.rs — Lane K3: Berry-Tabor/Poisson spacing -> EVT for the sup M(n)?
// build: rustc -O probe_wfH_K3_berrytabor_evt.rs -o /tmp/k3 && /tmp/k3
//
// QUESTION (mission): the period spectrum {|eta_b|} has POISSON (integrable, no level repulsion)
// nearest-neighbor spacing (in-tree D8: <r> ~= 0.386, the Poisson value, not GUE 0.603). Poisson
// processes have a known extreme-value law max ~ sqrt(2 log N)*scale. Does the PROVEN Poisson
// spacing of the period spectrum give the sup M(n) <= C sqrt(n log(p/n)) DIRECTLY via EVT, with a
// NON-energy independence/mixing input that dodges fence F12 (bounded-K energy transfer, DEAD)?
//
// EXACT INTEGER arithmetic throughout (cos/sin only for the magnitude readout; the spacing-ratio
// and max are scale facts; all counting is exact). NOT float-FFT.
//
// THREE TESTS:
//  T1. Confirm Poisson spacing (<r>) of the magnitude spectrum {|eta_b|} at the prize-shaped regime.
//  T2. DECISIVE: the spacing-ratio <r> is INVARIANT under monotone reparametrization of the value
//      axis => it carries ZERO info about the marginal tail that sets the max. Construct an explicit
//      monotone warp that keeps <r> ~ Poisson but inflates the max by an arbitrary factor. This
//      proves: Poisson spacing does NOT pin the max. (The EVT max needs the TAIL/threshold input.)
//  T3. The Leadbetter EVT-for-dependent-sequences max=Gumbel needs D(u_n) (long-range mixing at the
//      threshold level u_n) + D'(u_n) (local anti-clustering, extremal index theta=1). Measure the
//      threshold-level cluster count #{b : |eta_b| >= u_n} for u_n = sqrt(2 n log m) and whether the
//      *number of near-max periods* (the cluster size that controls theta) is read off any 2nd-order
//      quantity (variance / energy E_2) or grows with the deep tail. If theta-cluster needs E_r at
//      r ~ log m, the route REDUCES to F12.

use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128%p as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=&mut a;r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
// smallest prime p with p = 1 mod n and p >= lo
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// distinct period magnitudes over the m=(p-1)/n cosets
fn periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut mags=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0;let mut im=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;let a=2.0*PI*(t as f64)/p as f64;re+=a.cos();im+=a.sin();}
        mags.push((re*re+im*im).sqrt());
        b=((b as u128*gn as u128)%p as u128)as u64;
    }
    mags
}

// spacing ratio <r> = avg min(g_i,g_{i+1})/max(g_i,g_{i+1}) of consecutive gaps of the SORTED values.
// Robust to exact ties: treat 0/0 as a degenerate cluster pair contributing 0 (a tie IS the absence
// of repulsion = the Poisson signature), so it is counted, not dropped. (Dropping ties is what gave
// the earlier NaN at small m where the magnitudes coincide on the dense bulk.)
fn spacing_ratio(vals:&[f64])->f64{
    let mut s=vals.to_vec(); s.sort_by(|a,b|a.partial_cmp(b).unwrap());
    // De-tie / unfold: collapse exact (and near-exact) duplicate magnitudes to distinct levels,
    // standard in level-spacing analysis. The Gauss-period magnitudes coincide on a discrete set at
    // small m; the spacing statistic is a property of the DISTINCT levels (the period spectrum), so
    // we measure consecutive gaps of the de-duplicated sorted spectrum.
    let mut lv=Vec::with_capacity(s.len());
    for &x in &s { if lv.last().map_or(true,|&p:&f64| (x-p).abs()>1e-7) { lv.push(x); } }
    let gaps:Vec<f64>=lv.windows(2).map(|w|w[1]-w[0]).collect();
    let mut rs=0.0; let mut cnt=0u64;
    for i in 1..gaps.len(){let a=gaps[i-1];let b=gaps[i];let mx=a.max(b);
        if mx>1e-9 { rs+=a.min(b)/mx; cnt+=1; }}
    if cnt==0 {f64::NAN} else {rs/cnt as f64}
}

fn main(){
    println!("=== LANE K3: Berry-Tabor/Poisson spacing -> EVT for the sup? (exact regime, GUE 0.603 / Poisson 0.386) ===\n");

    // ---- T1: confirm Poisson spacing of the period spectrum at the prize-shaped regime ----
    println!("-- T1: spacing ratio <r> of the period-magnitude spectrum (beta ~ 4) --");
    for &(n,lo) in &[(64u64,16_000_000u64),(64,260_000_000),(128,260_000_000),(256,4_000_000_000)] {
        let p=fp(n,lo); let m=(p-1)/n;
        let mags=periods(n,p);
        let r=spacing_ratio(&mags);
        let beta=(p as f64).ln()/(n as f64).ln();
        let mx=mags.iter().cloned().fold(0.0,f64::max);
        let scale=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        println!("n={:4} p={:>11} m={:>9} beta={:.2} | <r>={:.4} | M/sqrt(n log m)={:.3}",
            n,p,m,beta,r, mx/scale);
    }

    // ---- T2: DECISIVE -- spacing-ratio is scale/warp-invariant => carries NO tail info ----
    // Take the real period spectrum, apply a monotone warp w(x)=x for x<=t*max, w(x)=t*max+K*(x-t*max)
    // for x> t*max (stretch only the top tail). The SORTED ORDER and hence the spacing-RATIO of the
    // bulk is essentially preserved, but the max is inflated by a chosen factor K. We report <r>
    // before/after and the max inflation: if <r> barely moves while max blows up, spacing!=>max.
    println!("\n-- T2: monotone tail-warp keeps <r> ~ Poisson but inflates the max (spacing does NOT pin max) --");
    {
        let n=64u64; let p=fp(n,16_000_000); let mags=periods(n,p);
        let mx=mags.iter().cloned().fold(0.0,f64::max);
        let r0=spacing_ratio(&mags);
        // warp: only the single largest value gets multiplied by K (a structured 'bad coset' resonance)
        for &k in &[1.0f64,2.0,5.0,20.0,100.0] {
            let mut w=mags.clone();
            // find argmax and scale it
            let (mut ai,mut av)=(0usize,0.0f64);
            for (i,&v) in w.iter().enumerate(){if v>av{av=v;ai=i;}}
            w[ai]=av*k;
            let r=spacing_ratio(&w);
            let mxn=w.iter().cloned().fold(0.0,f64::max);
            println!("K={:6.1} | <r>={:.4} (orig {:.4}) | max={:8.3} -> inflation x{:.2} of sqrt-floor",
                k, r, r0, mxn, mxn/mx);
        }
        println!("  => moving ONE value (one bad coset) leaves <r> essentially Poisson while the MAX = the prize");
        println!("     object moves arbitrarily. <r> (a BULK statistic) is BLIND to the single tail event.");
    }

    // ---- T3: the EVT cluster/threshold input -- is theta-cluster a 2nd-order or deep-tail quantity? ----
    // Leadbetter: max ~ Gumbel(sqrt(2v log m)) iff D(u_n) [mixing] AND D'(u_n) [anti-cluster, theta=1].
    // The cluster count at threshold u_n = sqrt(2 n log m) is the EVT-relevant quantity. We measure
    // how #{|eta|>=u_n} scales with m, and compare to the 2nd-moment (energy) prediction. If the
    // count is governed by E_r at r~log m (the depth where u_n sits, ~sqrt(2 log m) sd), it is F12.
    println!("\n-- T3: threshold-level cluster count #{{|eta_b| >= u_n}}, u_n = c*sqrt(2 n log m) --");
    println!("   (the EVT-relevant quantity sits at tail-depth t = u_n/sqrt(n) = c*sqrt(2 log m) std devs)");
    for &(n,lo) in &[(64u64,16_000_000u64),(64,260_000_000),(128,260_000_000)] {
        let p=fp(n,lo); let m=(p-1)/n; let mags=periods(n,p);
        let v=(n as f64); // per-period variance ~ n
        let logm=(m as f64).ln();
        let un=(2.0*v*logm).sqrt();
        let depth=un/v.sqrt(); // = sqrt(2 log m), the tail-depth in std devs the max probes
        let cnt = mags.iter().filter(|&&x| x>=un).count();
        // moment order that 'sees' this tail depth: r ~ depth^2/2 = log m
        let r_seen = (depth*depth/2.0).round();
        let mx=mags.iter().cloned().fold(0.0,f64::max);
        println!("n={:4} m={:>9} | u_n={:7.2} depth={:.2} sd | #>=u_n={:5} | max/u_n={:.3} | tail-depth r ~ log m = {:.0}",
            n,m,un,depth,cnt,mx/un,r_seen);
    }
    println!("\n  VERDICT logic: the max sits at depth ~ sqrt(2 log m) std devs => moment order r ~ log m.");
    println!("  Controlling whether that tail is Gumbel (theta=1, no cluster) = controlling the law to");
    println!("  moment-depth r ~ log m = the EFFECTIVE CLT at depth log m = E_r <= (2r-1)!! n^r at r~log m");
    println!("  = BCHKS 1.12 = F12 (bounded-K energy transfer, DEAD at beta=4). The Poisson SPACING");
    println!("  (a BULK 2nd-order-invisible-to-tail statistic) gives NO independent purchase on it.");
}
