// mcadebug — audit ONE (u0,u1) direction at one t: print, for each gamma, whether mcaEvent holds,
// with the witness set A, the witnessing codeword's agreement, and the no-joint check made explicit.
// Cross-checks the mcadelta bad-count by hand. Usage: mcadebug <n> <k> <t> <e0> <e1> [mult=4] [maxgamma=40]
fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn big_prime(n:u64,mult:u32)->u64{let mut p=n.pow(mult);if p<1000{p=1000;}p+=(1+n-p%n)%n;loop{if p%n==1&&isprime(p){return p;}p+=n;}}
fn interp(idx:&[usize],mu:&[u64],z:&[u64],k:usize,p:u64)->Vec<u64>{
    let xs:Vec<u64>=idx.iter().map(|&i|mu[i]).collect();
    let ys:Vec<u64>=idx.iter().map(|&i|z[i]).collect();
    let mut coef=vec![0u64;k];
    for i in 0..k{let mut denom=1u64;for j in 0..k{if j!=i{denom=mulmod(denom,submod(xs[i],xs[j],p),p);}}
        let scale=mulmod(ys[i],invmod(denom,p),p);
        let mut np=vec![0u64;k];np[0]=1;let mut deg=0usize;
        for j in 0..k{if j!=i{let mut nn=vec![0u64;k];for t in 0..=deg{nn[t+1]=addmod(nn[t+1],np[t],p);nn[t]=addmod(nn[t],mulmod(np[t],submod(0,xs[j],p),p),p);}np=nn;deg+=1;}}
        for t in 0..k{coef[t]=addmod(coef[t],mulmod(scale,np[t],p),p);}}
    coef}
fn eval(c:&[u64],x:u64,p:u64)->u64{let mut r=0u64;for &v in c.iter().rev(){r=addmod(mulmod(r,x,p),v,p);}r}
fn agree_mask(c:&[u64],mu:&[u64],z:&[u64],p:u64)->u64{let mut m=0u64;for i in 0..mu.len(){if eval(c,mu[i],p)==z[i]{m|=1<<i;}}m}
fn next_comb(c:&mut [usize],n:usize)->bool{let s=c.len();let mut i=s;while i>0{i-=1;if c[i]!=i+n-s{c[i]+=1;for j in i+1..s{c[j]=c[j-1]+1;}return true;}}false}
fn codewords_agree_ge(z:&[u64],mu:&[u64],k:usize,p:u64,t:usize)->Vec<(Vec<u64>,u64)>{
    let n=mu.len();let mut seen=std::collections::HashSet::new();let mut out=vec![];
    let mut c:Vec<usize>=(0..k).collect();
    loop{let coef=interp(&c,mu,z,k,p);if !seen.contains(&coef){let m=agree_mask(&coef,mu,z,p);if (m.count_ones() as usize)>=t{out.push((coef.clone(),m));}seen.insert(coef);}if !next_comb(&mut c,n){break;}}
    out}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();let k:usize=a[2].parse().unwrap();let t:usize=a[3].parse().unwrap();
    let e0:usize=a[4].parse().unwrap();let e1:usize=a[5].parse().unwrap();
    let mult:u32=a.get(6).and_then(|x|x.parse().ok()).unwrap_or(4);
    let maxg:u64=a.get(7).and_then(|x|x.parse().ok()).unwrap_or(40);
    let p=big_prime(n as u64,mult);let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let u0:Vec<u64>=(0..n).map(|i|powmod(mu[i],e0 as u64,p)).collect();
    // u1: monomial x^e1, OR if MCA_E1B set, binomial x^e1 + x^{MCA_E1B} (NEAR direction probe).
    let e1b:Option<usize>=std::env::var("MCA_E1B").ok().and_then(|x|x.parse().ok());
    let u1:Vec<u64>=(0..n).map(|i|{
        let m=powmod(mu[i],e1 as u64,p);
        match e1b { Some(b)=>addmod(m,powmod(mu[i],b as u64,p),p), None=>m }
    }).collect();
    if let Some(b)=e1b { println!("(u1 = x^{} + x^{} binomial NEAR-probe)",e1,b); }
    // is u1 a codeword (deg<k)? is it far?
    let u1_is_cw = e1<k; let u0_is_cw = e0<k;
    println!("n={} k={} t={} p={} u0=x^{}(cw?{}) u1=x^{}(cw?{})",n,k,t,p,e0,u0_is_cw,e1,u1_is_cw);
    let joint_on=|amask:u64|->bool{
        let idx:Vec<usize>=(0..n).filter(|&i|amask&(1<<i)!=0).collect();
        if idx.len()<k {return true;}
        let v0=interp(&idx[0..k],&mu,&u0,k,p);for &i in &idx{if eval(&v0,mu[i],p)!=u0[i]{return false;}}
        let v1=interp(&idx[0..k],&mu,&u1,k,p);for &i in &idx{if eval(&v1,mu[i],p)!=u1[i]{return false;}}
        true};
    let mut bad=0u64; let mut total_explainable=0u64;
    for gamma in 0..maxg.min(p){
        let l:Vec<u64>=(0..n).map(|i|addmod(u0[i],mulmod(gamma,u1[i],p),p)).collect();
        let ws=codewords_agree_ge(&l,&mu,k,p,t);
        if ws.is_empty(){continue;}
        total_explainable+=1;
        let mut is_bad=false; let mut witmask=0u64;
        for (_w,am) in &ws{ if !joint_on(*am){is_bad=true;witmask=*am;break;} }
        if is_bad{
            bad+=1;
            let idx:Vec<usize>=(0..n).filter(|&i|witmask&(1<<i)!=0).collect();
            // show the joint check failure
            let v0=interp(&idx[0..k.min(idx.len())],&mu,&u0,k,p);
            let v0_agrees=idx.iter().all(|&i|eval(&v0,mu[i],p)==u0[i]);
            let v1=interp(&idx[0..k.min(idx.len())],&mu,&u1,k,p);
            let v1_agrees=idx.iter().all(|&i|eval(&v1,mu[i],p)==u1[i]);
            if gamma<12 {println!("  gamma={} BAD: |A|={} A={:?}  joint? v0_agreesAllA={} v1_agreesAllA={} (jointfail since one is false)",gamma,idx.len(),idx,v0_agrees,v1_agrees);}
        }
    }
    println!("=> over gamma in [0,{}): explainable={} BAD(mcaEvent)={}",maxg.min(p),total_explainable,bad);
}
