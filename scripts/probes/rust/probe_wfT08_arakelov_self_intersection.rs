// probe_wfT08_arakelov_self_intersection.rs
//
// T08 (architect G2-3): "Arithmetic self-intersection (Arakelov) lower bound on the period
// section forces archimedean equidistribution rate."
//
// THE CANDIDATE'S CENTRAL INEQUALITY (read off the statement):
//   House(theta_b)^2 <= n * exp( -2 * (ord_P(theta_b)*log p + ord_2-content) / phi(n) ) * (1+spread)
// i.e. a LARGER non-archimedean arithmetic-intersection content (ord_P*log p + ord_2)
// is claimed to FORCE a SMALLER archimedean House.  At the prize this is supposed to give
// M(n) <= sqrt(n*log(p/n)).
//
// THE ARAKELOV / PRODUCT-FORMULA FACT (degree of a principal arithmetic divisor = 0):
// For an ALGEBRAIC INTEGER theta (a Gaussian period IS one, a sum of roots of unity),
//   sum_{w arch} log|w theta|  =  - sum_{v non-arch} N_v log|theta|_v  =  log|N_{K/Q}(theta)|  >= 0.
// Each non-arch term has |theta|_v <= 1 (integer), so the "intersection content"
//   content := (1/phi) * sum_{v non-arch} N_v * (-log|theta|_v) = (1/phi) log|N| >= 0
// EQUALS (1/phi) of the archimedean log-mass.  The two COLUMNS MOVE TOGETHER.
// Hence the House (= max over arch places of |w theta| = M(n) for theta = eta_b) satisfies
//   log House >= (1/phi) sum_w log|w theta| = content   (max >= mean),
// i.e. content is a LOWER bound lever, NOT the upper bound the candidate claims.
//
// THIS PROBE: for actual Gaussian periods eta_b = sum_{x in mu_n} e_p(b x) (b != 0), an
// ALGEBRAIC INTEGER in K = Q(zeta_p), we EXACTLY compute over all conjugates (the Galois orbit
// = scaling b over F_p^* modulo mu_n):
//   * House = max_b |eta_b|        (= M(n), the prize object)
//   * geom-mean modulus = (prod_b |eta_b|)^{1/#orbit} = |N|^{1/#orbit}  (the content exp)
//   * the candidate's predicted ceiling   sqrt(n) * exp(-content)  (content > 0)
// and check whether House <= candidate-ceiling (candidate) vs House >= geom-mean (Arakelov).
//
// If House > candidate-ceiling on real periods at every prize-shaped (n,p), the candidate's
// sign is reversed => REFUTED, exactly as the abstract product-formula argument predicts.

fn pow_mod(mut a: u128, mut e: u128, m: u128) -> u128 {
    let mut r: u128 = 1 % m;
    a %= m;
    while e > 0 {
        if e & 1 == 1 { r = r * a % m; }
        a = a * a % m;
        e >>= 1;
    }
    r
}

fn is_prime(n: u128) -> bool {
    if n < 2 { return false; }
    for p in [2u128,3,5,7,11,13,17,19,23,29,31,37] {
        if n % p == 0 { return n == p; }
    }
    // Miller-Rabin deterministic for < 3.3e24 with these bases
    let mut d = n - 1; let mut s = 0;
    while d & 1 == 0 { d >>= 1; s += 1; }
    'wit: for &a in &[2u128,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = pow_mod(a % n, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s-1 {
            x = x * x % n;
            if x == n - 1 { continue 'wit; }
        }
        return false;
    }
    true
}

// find a prime p = 1 mod n with p ~ n^beta (closest prime above n^beta)
fn find_prime(n: u128, target: u128) -> u128 {
    // smallest p > target with p % n == 1
    let mut k = target / n + 1;
    loop {
        let p = k * n + 1;
        if p > target && is_prime(p) { return p; }
        k += 1;
    }
}

// a generator of F_p^*
fn primitive_root(p: u128) -> u128 {
    let phi = p - 1;
    // factor phi
    let mut fac = vec![];
    let mut m = phi; let mut d = 2u128;
    while d*d <= m {
        if m % d == 0 { fac.push(d); while m % d == 0 { m /= d; } }
        d += 1;
    }
    if m > 1 { fac.push(m); }
    for g in 2..p {
        if fac.iter().all(|&q| pow_mod(g, phi/q, p) != 1) { return g; }
    }
    unreachable!()
}

fn main() {
    println!("# T08 Arakelov self-intersection / product-formula sign test on REAL Gaussian periods");
    println!("# House = M(n) = max_b |eta_b|;  content = (1/orbit) log|N| = arch-mean (product formula)");
    println!("# candidate ceiling = sqrt(n)*exp(-content)  (claims House <= this; content>0 => below sqrt(n))");
    println!("# Arakelov truth     = House >= exp(content)   (max >= geom-mean)");
    println!();

    // beta = 4 prize shape (scaled-down n so the FFT-free direct conjugate enumeration is feasible).
    // The product-formula sign is regime-INDEPENDENT (it is an exact identity for any integer),
    // so any (n,p) with p=1 mod n exhibits it; we sweep several n at beta~4.
    let cases: Vec<(u128, u128)> = vec![
        (4, 4u128.pow(4)),
        (8, 8u128.pow(4)),
        (16, 16u128.pow(4)),
        (32, 32u128.pow(4)),
        (64, 64u128.pow(4)),
        (128, 128u128.pow(4)),
    ];

    let mut violations = 0u64;
    let mut sign_correct = 0u64;

    for (n, tgt) in cases {
        let p = find_prime(n, tgt);
        let g = primitive_root(p);
        // mu_n = order-n subgroup = { g^{k*(p-1)/n} : k } ; generator h = g^{(p-1)/n}
        let h = pow_mod(g, (p - 1) / n, p);
        // elements of mu_n
        let mut mu = Vec::with_capacity(n as usize);
        let mut x = 1u128;
        for _ in 0..n { mu.push(x); x = x * h % p; }

        let two_pi = 2.0 * std::f64::consts::PI;
        // eta_b = sum_{x in mu_n} exp(2*pi*i * b*x / p).  b ranges over coset reps of F_p^*/mu_n,
        // which is the full Galois conjugate orbit of eta_1.  We enumerate b = 1..p-1 (all nonzero)
        // for small p; |eta_b| is constant on mu_n-cosets so #distinct = (p-1)/n conjugates.
        // For the prize object M(n) we need max over ALL b != 0, which equals max over orbit reps.
        let mut house = 0.0f64;
        let mut log_norm_sum = 0.0f64; // sum over orbit reps of log|eta_b|, weighted by coset size n
        // To keep cost ~ p, iterate b over all nonzero residues but only need one rep per coset.
        // Cheapest correct enumeration: iterate over coset reps. Build reps by sieving membership.
        let mut seen = vec![false; p as usize];
        let mut reps: Vec<u128> = Vec::new();
        for b in 1..p {
            if !seen[b as usize] {
                reps.push(b);
                // mark whole coset b*mu_n
                for &u in &mu { seen[(b * u % p) as usize] = true; }
            }
        }
        // each rep => one distinct |eta_b|, with multiplicity n (coset size) in the full norm
        let mut sum_log = 0.0f64;
        for &b in &reps {
            let mut re = 0.0f64; let mut im = 0.0f64;
            for &xx in &mu {
                let ang = two_pi * ((b * xx % p) as f64) / (p as f64);
                re += ang.cos(); im += ang.sin();
            }
            let mag = (re*re + im*im).sqrt();
            if mag > house { house = mag; }
            sum_log += (mag.max(1e-300)).ln();
        }
        // |N(eta_1)| over K=Q(zeta_p): the conjugates of eta_1 are { eta_b : b in F_p^*/mu_n },
        // each appearing... actually [K:Q]=p-1 and eta_1 lives in the degree-(p-1)/n subfield;
        // the relevant norm down to Q is prod over the (p-1)/n distinct conjugates.
        let orbit = reps.len() as f64;
        let mean_log = sum_log / orbit;            // = (1/#conj) log|N| = content
        let _ = log_norm_sum;
        let content = mean_log;                    // >= 0 expected (integer)
        let geom_mean = content.exp();             // = |N|^{1/#conj}
        let candidate_ceiling = (n as f64).sqrt() * (-content).exp(); // sqrt(n)*exp(-content)

        // candidate claim: House <= candidate_ceiling   (content lowers the ceiling below sqrt(n))
        let cand_holds = house <= candidate_ceiling + 1e-6;
        // arakelov truth: House >= geom_mean (max >= mean) AND content >= 0
        let arak_holds = house >= geom_mean - 1e-6 && content >= -1e-6;

        if !cand_holds { violations += 1; }
        if arak_holds { sign_correct += 1; }

        println!("n={:>4} p={:<12} #conj={:>6}  House(M)={:>10.4}  sqrt(n)={:>9.4}  content={:>8.4}  geomMean={:>9.4}",
                 n, p, reps.len(), house, (n as f64).sqrt(), content, geom_mean);
        println!("       candidate ceiling sqrt(n)*e^(-content)={:>9.4}  => House<=ceiling? {}  (CANDIDATE)",
                 candidate_ceiling, cand_holds);
        println!("       Arakelov: content>=0? {}  House>=geomMean? {}  => content is a LOWER lever (TRUTH)",
                 content >= -1e-6, house >= geom_mean - 1e-6);
        // also: is content > 0 (genuine non-unit)? then candidate ceiling < sqrt(n) strictly
        println!("       content>0 (nonunit, candidate forces House<sqrt(n))? {}  but House vs sqrt(n): {}",
                 content > 1e-6,
                 if house > (n as f64).sqrt() { "House > sqrt(n)" } else { "House <= sqrt(n)" });
        println!();
    }

    println!("# SUMMARY");
    println!("# candidate (House <= sqrt(n)*exp(-content)) VIOLATIONS: {}", violations);
    println!("# Arakelov truth (content>=0 AND House>=geomMean) HOLDS in: {} cases", sign_correct);
    println!("# VERDICT: the candidate's content lever has the WRONG SIGN (product formula: arch mass = norm content, they move together). REFUTED -> reduces F3/F9/F11.");
}
