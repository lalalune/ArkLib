// probe_wfT23_regulator_spacing_pigeonhole.rs  (#444 T23, cluster G5-3)
//
// Candidate T23 (Beilinson dilogarithm-regulator spacing): conjectures a Lehmer-type LOWER bound
//   R_2(eta_b - eta_b') >= c/(log n)^A  ==>  normalized periods {eta_b/sqrt n} are
//   1/(sqrt n (log n)^A)-SEPARATED  ==>  <= sqrt n (log n)^A per unit window  ==> (+Parseval)
//   M(n) <= sqrt n (log n)^A.
//
// REFUTATION of the load-bearing separation step (S), at prize scale n=2^30, beta=4:
//   There are m = (p-1)/n ~ n^3 DISTINCT Gauss periods (full degree-m Galois orbit). Parseval pins
//   their total squared mass to (p-n), so the RMS over the m distinct periods is sqrt((p-n)/m)~sqrt n.
//   By Chebyshev, >= m/2 of them lie in a window of width 2*sqrt2*sqrt n. Packing >= m/2 ~ n^3/2
//   real points into width O(sqrt n) FORCES (pigeonhole) some pair within
//      <= (2 sqrt2 sqrt n)/(m/2)  ~  O(n^{-5/2}),
//   which is BELOW the claimed separation floor 1/(sqrt n (log n)^A) ~ n^{-1/2}/polylog by ~ n^2.
//   => the separation law (S), applied to the actual n^3-element orbit, is FALSE at prize scale.
//
//   Reduction (even charitably): mechanism = Parseval mass + orbit-position counting = domain
//   second-order arithmetic => caps at RMS = sqrt n (Johnson) = fence F0; the regulator->spacing
//   bridge is the T10/S8 reversed-covolume trap (geometric mean <= max).
//
// Build/run:  rustc -O probe_wfT23_regulator_spacing_pigeonhole.rs && ./probe_wfT23_regulator_spacing_pigeonhole

fn main() {
    let mu: u32 = 30;
    let beta: u32 = 4;
    let n = 2f64.powi(mu as i32);          // n = 2^30
    let p = n.powi(beta as i32);           // p = n^4 ~ 2^120
    let m = (p - 1.0) / n;                 // distinct periods ~ n^3 ~ 2^90
    let rms = ((p - n) / m).sqrt();        // RMS of distinct periods ~ sqrt n
    println!("n = 2^{}  p = n^{} (~2^{})  m = (p-1)/n ~ n^{} (~2^{})",
             mu, beta, beta * mu, beta - 1, (beta - 1) * mu);
    println!("RMS of distinct periods = sqrt((p-n)/m) = {:.4}   (sqrt n = {:.1})", rms, n.sqrt());

    // Chebyshev window holding >= m/2 periods: width 2*sqrt2*rms.
    let k = 2f64.sqrt();
    let width = 2.0 * k * rms;
    let half = m / 2.0;
    let forced_min_spacing = width / (half - 1.0);
    println!("Chebyshev window (>= m/2 periods) width = 2*sqrt2*rms = {:.2}", width);
    println!("FORCED min spacing (pigeonhole) <= width/(m/2) = {:.4e}", forced_min_spacing);

    let logn = (mu as f64) * 2f64.ln();
    println!("\n A  | claimed sep floor 1/(sqrt n (log n)^A) | violated by forced spacing?");
    for a in [0.0f64, 0.5, 1.0, 2.0] {
        let floor = 1.0 / (n.sqrt() * logn.powf(a));
        println!(" {:>3} | {:.4e}                              | {}  (ratio floor/forced = {:.2e})",
                 a, floor, forced_min_spacing < floor, floor / forced_min_spacing);
    }

    // Independent confirmation: even a tiny sub-orbit of 2^40 periods can't be 2^{-15}-separated
    // inside the Parseval window (the EXACT rational fact certified in Lean: sep_impossible_prize).
    let cnt_proxy = 2f64.powi(40);
    let sep_floor_a0 = 1.0 / 32768.0;     // 1/sqrt n at A=0
    let window_w = 92682.0;               // > 2*sqrt2*sqrt n
    let pigeon = (cnt_proxy - 1.0) * sep_floor_a0;
    println!("\nLean-certified exact check (sep_impossible_prize):");
    println!("  (2^40 - 1) * (1/32768) = {:.4e}  >  window {:.0}  ?  {}",
             pigeon, window_w, pigeon > window_w);
    println!("  => 2^40 periods (<< the 2^89 forced in-window) cannot be 1/sqrt(n)-separated.");

    println!("\nVERDICT: separation step (S) FALSE at prize scale; T23 REDUCES-TO-WALL F0");
    println!("         (Parseval mass + orbit counting = second-order arithmetic, capped at sqrt n;");
    println!("          regulator->spacing bridge = T10/S8 reversed-covolume trap). No prize gain.");
}
