// orbitdecomp — for the worst MONOMIAL line x^aa + γ·x^b at each agreement size s, compute the
// bad-γ SET and decompose it under the dilation orbit law #bad = [0 bad] + (n/d)·O_P, d=gcd(aa-b,n).
// Answers lalalune's 08:46Z #444 "O_P=1 persistence" question with BINDING-rung data (their examples
// are shallow c=1 where O_P is large; this sweeps to the budget-crossing rung). VERIFIES the orbit
// structure (closure of bad set under mult by h^{aa-b}) rather than assuming the law. Lean: none.
// Usage: orbitdecomp <n> <k> [mult=4]
use std::collections::HashSet;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
#[inline] fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
#[inline] fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
#[inline] fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn gcd(mut a:u64,mut b:u64)->u64{while b!=0{let t=b;b=a%b;a=t;}a}
fn is_prime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn big_prime(n:u64,mult:u32)->u64{let mut p=n.pow(mult);if p<1000{p=1000;}p+=(1+n-p%n)%n;loop{if p%n==1&&is_prime(p){return p;}p+=n;}}
#[inline]
fn ddk_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->u64{
    let mut vs:[u64;72]=[0u64;72];
    for t in 0..=k{vs[t]=vals[t];}
    for j in 1..=k{for i in (j..=k).rev(){let inv=invd[idx[i]*n+idx[i-j]];vs[i]=mulmod(submod(vs[i],vs[i-1],p),inv,p);}}
    vs[k]
}
#[inline]
fn in_rs_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->bool{
    let s=idx.len(); if s<=k{return true;}
    for st in 0..(s-k){if ddk_idx(&vals[st..st+k+1],&idx[st..st+k+1],k,p,invd,n)!=0{return false;}}
    true
}
// returns the bad-γ set for line ev0 + γ·ev1 against RS[k] at agreement >= s
fn bad_set(n:usize,ev0:&[u64],ev1:&[u64],k:usize,p:u64,s:usize,invd:&[u64])->Option<HashSet<u64>>{
    let mut local:HashSet<u64>=HashSet::new();
    let mut comb:Vec<usize>=(0..s).collect();
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    loop{
        for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
        if in_rs_idx(&u1,&comb,k,p,invd,n){
            if in_rs_idx(&u0,&comb,k,p,invd,n){return None;} // γ-free agreement: incidence blows up, skip dir
        } else {
            let a0=ddk_idx(&u0,&comb,k,p,invd,n);let a1=ddk_idx(&u1,&comb,k,p,invd,n);
            if a1!=0{let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                if in_rs_idx(&full,&comb,k,p,invd,n){local.insert(gm);}}
        }
        let mut i=s;let mut adv=false;
        while i>0{i-=1;if comb[i]!=i+n-s{comb[i]+=1;for j in (i+1)..s{comb[j]=comb[j-1]+1;}adv=true;break;}}
        if !adv{break;}
    }
    Some(local)
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();let k:usize=a[2].parse().unwrap();
    let mult:u32=a.get(3).and_then(|x|x.parse().ok()).unwrap_or(4);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let mut powtab=vec![0u64;n*n];
    for e in 0..n{for i in 0..n{powtab[e*n+i]=powmod(mu[i],e as u64,p);}}
    let budget=n as u64;
    let ev_mono=|e:usize|->Vec<u64>{(0..n).map(|i|powtab[e*n+i]).collect()};
    println!("# n={} k={} p={} budget={}  (monomial line x^aa + γ·x^b, worst over aa,b per s)",n,k,p,budget);
    println!("# s  c  #bad   aa  b  d=gcd(aa-b,n)  n/d  0bad  O_P   closure  verdict");
    let mut binding_reported=false;
    for s in (k+1)..=(n-1){
        let c=s-k;
        // find worst monomial line over all (aa,b) pairs in [k,n)
        let mut best:Option<(usize,usize,HashSet<u64>)>=None;
        for aa in k..n{ for b in k..n{ if aa==b{continue;}
            let ev0=ev_mono(aa); let ev1=ev_mono(b);
            if let Some(set)=bad_set(n,&ev0,&ev1,k,p,s,&invd){
                let better = match &best{None=>true,Some((_,_,bs))=>set.len()>bs.len()};
                if better{best=Some((aa,b,set));}
            }
        }}
        let (aa,b,set)=match best{Some(x)=>x,None=>{println!("{:>3} {:>2}  (all dirs γ-free / blow-up)",s,c);continue;}};
        let nbad=set.len() as u64;
        let diff=((aa as i64)-(b as i64)).rem_euclid(n as i64) as u64;
        let d=gcd(diff,n as u64);
        let orb=(n as u64)/d;                 // orbit size = order of h^{aa-b}
        let zero_bad = set.contains(&0u64);
        let nonzero = nbad - if zero_bad{1}else{0};
        // VERIFY closure: nonzero bad set closed under mult by h^{aa-b}=mu[diff]
        let scale = mu[diff as usize];
        let mut closed=true;
        for &x in set.iter(){ if x==0{continue;} if !set.contains(&mulmod(x,scale,p)){closed=false;break;} }
        let op_ok = nonzero % orb == 0;
        let op = if op_ok { nonzero/orb } else { 0 };
        let verdict = if !closed {"CLOSURE-FAIL".to_string()}
                      else if !op_ok {"NONINT-OP".to_string()}
                      else { format!("#bad={} = {}+{}*{}", nbad, if zero_bad{1}else{0}, orb, op) };
        let binding = nbad<=budget && !binding_reported;
        if binding { binding_reported=true; }
        println!("{:>3} {:>2}  {:>5}  {:>2} {:>2}  {:>3}          {:>3}  {:>4}  {:>3}  {:>7}  {}{}",
            s,c,nbad,aa,b,d,orb,zero_bad,op,closed,verdict, if binding{"   <== BINDING RUNG (first #bad<=budget)"}else{""});
    }
}
