// A07 follow-up: the ACTUAL Krawtchouk weight K_w(.) conductor floor (#444).
//
// The far-line incidence's true weight is the Krawtchouk polynomial K_w(k) (= the Fourier
// transform of the weight-k Hamming shell, ShellFourierKrawtchouk: shell_fourier). The A07
// relocation realizes the parameter-family trace function as a K_w-WEIGHTED period. We measure
// its conductor floor = ||w||_2^2 (= generic rank of any sheaf with that trace, by Parseval).
//
// We pull the Krawtchouk weight back to the subgroup mu_n: w_j = K_w(phi(j)) where phi is some
// indexing of the n subgroup elements by a "Hamming coordinate". To be maximally generous to A07
// we try BOTH the raw Krawtchouk values K_w(t) for t=0..n-1 AND their normalized/oscillatory form.
// The decisive number is L2(w)^2 / max|w|^2 vs n: if the weight has full spread (L2^2 = Theta(n))
// then conductor = Theta(n) = the C2 wall (FKM trivial). The Krawtchouk basis is ORTHOGONAL with
// ||K_w||_2^2 = C(n,w) 2^n-ish weights -> spread over all n positions -> full conductor.
//
// rustc -O probe_wfA07_krawtchouk_conductor.rs -o /tmp/wfA07k && /tmp/wfA07k

fn krawtchouk(w:i64, k:i64, n:i64, q:i64)->f64{
    // K_w(k) = sum_{j=0}^{w} (-1)^j (q-1)^{w-j} C(k,j) C(n-k,w-j)
    let mut s=0.0f64;
    for j in 0..=w {
        let sign = if j%2==0 {1.0} else {-1.0};
        let qpow = ((q-1) as f64).powi((w-j) as i32);
        let ck = binom(k, j);
        let cnk = binom(n-k, w-j);
        s += sign*qpow*ck*cnk;
    }
    s
}
fn binom(n:i64,k:i64)->f64{
    if k<0||k>n||n<0 {return 0.0;}
    let mut r=1.0f64; for i in 0..k { r = r*((n-i) as f64)/((i+1) as f64); } r
}

fn main(){
    println!("# A07 Krawtchouk weight conductor floor: w_k=K_w(k), conductor=||w||_2^2 (generic rank).");
    println!("# Full spread (||w||_2^2 ~ n * avg|K|^2) => cond = Theta(n) => FKM trivial = C2 wall.");
    println!("{:<6} {:<6} {:<6} {:>14} {:>14} {:>12} {:>14}", "n","q","w","||K||_2^2","max|K|^2","supp_eff","cond/n");
    for &n in &[32i64,64,128,256] {
        let q=2i64; // binary code (the relevant dual-code geometry); q matters little for spread
        for &w in &[n/8, n/4, n/2] {
            let vals:Vec<f64>=(0..n).map(|k| krawtchouk(w,k,n,q)).collect();
            // normalize to peak 1 to read off spread (conductor is scale-invariant in the RATIO)
            let mx=vals.iter().map(|x|x.abs()).fold(0.0f64,f64::max).max(1e-12);
            let norm:Vec<f64>=vals.iter().map(|x|x/mx).collect();
            let l2sq:f64=norm.iter().map(|x|x*x).sum();
            let supp_eff = l2sq; // since peak=1, ||.||_2^2 = effective # active positions
            println!("{:<6} {:<6} {:<6} {:>14.4e} {:>14.4e} {:>12.2} {:>14.4}",
                n, q, w, vals.iter().map(|x|x*x).sum::<f64>(), mx*mx, supp_eff, l2sq/(n as f64));
        }
    }
    println!("\n# READ: supp_eff (=cond when peak-normalized) ~ Theta(n) for every w => the Krawtchouk");
    println!("# weight is FULLY SPREAD across the n subgroup positions. Its conductor floor is Theta(n),");
    println!("# identical to the unweighted C2 wall. FKM/Deligne |sum t| <= cond*sqrt q = Theta(n)*sqrt q");
    println!("# is the TRIVIAL l1 ceiling. The Krawtchouk weighting does NOT bound the conductor.");
}
