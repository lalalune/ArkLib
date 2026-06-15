# pg-rs — parallel far-line incidence engine (#407)
Computes delta* = (n-s*)/n for RS[mu_n,k] at the prize-scale prime (=char-0). Validated: delta*(mu_16,k=4)=9/16.
Run: cargo build --release && ./target/release/pg <n> <k>. Cost ~2^n (binding s*~n/2 at rho=1/4): n=28~24min,
n=32~9.6h, n>=36 infeasible. Exact formula found: delta* = 1/2 + (1/(2rho)-1)/n (budget=n).
