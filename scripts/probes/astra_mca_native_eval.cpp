// Exact native evaluation of the reviewed two-generator MCA construction.
// Default: bounded self-checks. Production arrays require --scan and an explicit
// memory allowance; no probabilistic inference is used to count distinct values.
// Mathematical source: docs/kb/astra_mca_twogen_lift_eval-2026-09-04.md.
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <limits>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
#ifdef __APPLE__
#include <mach/mach.h>
#include <sys/sysctl.h>
#else
#include <fstream>
#endif

using U = uint64_t;
using W = __uint128_t;
constexpr U PROD = U(1) << 30;
constexpr U MIB = U(1) << 20;
constexpr U P0 = (U(192) << 30) + 1, P2 = U(1) << 30;
constexpr U NINV = (U(192) << 30) - 1;
struct F { U a, b, c; };
constexpr F ZERO{0, 0, 0};
constexpr F ONE{188978561025ULL, 18446744073709551424ULL, 1073741823};
constexpr F R2{0, 6597069766672ULL, 36864};
bool eq(F x, F y) { return x.a == y.a && x.b == y.b && x.c == y.c; }
bool zero(F x) { return (x.a | x.b | x.c) == 0; }
bool canonical(F x) {
  return x.c < P2 || (x.c == P2 && x.b == 0 && x.a < P0);
}
F reduce_once(F z) {
  if (!canonical(z)) {
    U borrow = z.a < P0; z.a -= P0;
    U carry = z.b < borrow; z.b -= borrow; z.c -= P2 + carry;
  }
  return z;
}
F add(F x, F y) {
  W t = W(x.a) + y.a; F z{U(t), 0, 0};
  t = W(x.b) + y.b + U(t >> 64); z.b = U(t);
  z.c = x.c + y.c + U(t >> 64);
  return reduce_once(z);
}
F sub(F x, F y) {
  U b0 = x.a < y.a, a = x.a - y.a;
  W ys = W(y.b) + b0; U b1 = W(x.b) < ys, b = U(W(x.b) - ys);
  W zs = W(y.c) + b1; U borrow = W(x.c) < zs, c = U(W(x.c) - zs);
  if (borrow) {
    W t = W(a) + P0; a = U(t);
    t = W(b) + U(t >> 64); b = U(t); c += P2 + U(t >> 64);
  }
  return {a, b, c};
}
F neg(F x) { return sub(ZERO, x); }
// Three-limb Montgomery multiplication, R=2^192. P's middle limb is zero.
F mul(F x, F y) {
  U a[3] = {x.a, x.b, x.c}, b[3] = {y.a, y.b, y.c}, t[7] = {};
  for (int i = 0; i < 3; ++i) {
    U carry = 0;
    for (int j = 0; j < 3; ++j) {
      W v = W(a[i]) * b[j] + t[i+j] + carry;
      t[i+j] = U(v); carry = U(v >> 64);
    }
    int j = i+3;
    while (carry) { W v = W(t[j]) + carry; t[j++] = U(v); carry = U(v >> 64); }
  }
  constexpr U p[3] = {P0, 0, P2};
  for (int i = 0; i < 3; ++i) {
    U m = t[i] * NINV, carry = 0;
    for (int j = 0; j < 3; ++j) {
      W v = W(m) * p[j] + t[i+j] + carry;
      t[i+j] = U(v); carry = U(v >> 64);
    }
    int j = i+3;
    while (carry) { W v = W(t[j]) + carry; t[j++] = U(v); carry = U(v >> 64); }
  }
  return reduce_once({t[3], t[4], t[5]});
}
F from_u64(U n) { return mul({n, 0, 0}, R2); }
F ordinary(F x) { return mul(x, {1, 0, 0}); }
F power(F x, U n) {
  F r = ONE;
  while (n) { if (n & 1) r = mul(r, x); x = mul(x, x); n >>= 1; }
  return r;
}
F inverse(F x) {
  if (zero(x)) throw std::runtime_error("inverse of zero");
  constexpr U exponent[3] = {P0-2, 0, P2};
  F r = ONE;
  for (int j = 158; j >= 0; --j) {
    r = mul(r, r);
    if ((exponent[j/64] >> (j%64)) & 1) r = mul(r, x);
  }
  return r;
}
F divide(F x, F y) { return mul(x, inverse(y)); }
F decimal(const std::string &s) {
  F x = ZERO, ten = from_u64(10);
  for (char c : s) {
    if (c < '0' || c > '9') throw std::runtime_error("invalid decimal");
    x = add(mul(x, ten), from_u64(c-'0'));
  }
  return x;
}
std::string decimal_out(F x) {
  std::string s;
  while (!zero(x)) {
    U q[3], limbs[3] = {x.a, x.b, x.c}, rem = 0;
    for (int j = 2; j >= 0; --j) { W z = (W(rem) << 64) | limbs[j]; q[j] = U(z/10); rem = U(z%10); }
    s += char('0'+rem); x = {q[0], q[1], q[2]};
  }
  if (s.empty()) return "0";
  std::reverse(s.begin(), s.end()); return s;
}
struct Direction { F first, second; };
struct Value { bool finite; F gamma; }; // gamma is canonical, not Montgomery.
struct Incomplete : std::runtime_error { using std::runtime_error::runtime_error; };
U mix(U x) {
  x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 27; x *= 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}
U fingerprint(Value v) {
  if (!v.finite) return 0;
  return mix(v.gamma.a ^ mix(v.gamma.b ^ mix(v.gamma.c ^ 0x9e3779b97f4a7c15ULL)));
}
U key_for(Value v,unsigned bits=64) {
  return fingerprint(v) & (~U(0) << (64-bits));
}

struct Model {
  U n, m; unsigned terms;
  F omega, ii, inv_m, half_i, anchor_x, anchor_y;
  F num_a[14], num_b[14];
  std::array<Direction, 4> priv;
  explicit Model(U n_) : n(n_), m(n_/4), terms(0) {
    U p = 4;
    while (p < n && terms < 14) { p *= 4; ++terms; }
    if (n < 16 || n > PROD || p != n) throw std::runtime_error("n must be 4^r in [16,2^30]");
    F generator = decimal("303645430271030343624574566109998498685964493478");
    omega = power(generator, PROD/n);
    if (!eq(power(omega,n/2), neg(ONE)) || !eq(power(omega,n),ONE))
      throw std::runtime_error("root order failed");
    ii = power(omega,m); inv_m = inverse(from_u64(m));
    half_i = divide(ii,from_u64(2));
    F ca = sub(ONE,add(ii,ii)), cb = neg(add(ii,add(ii,ii)));
    for (unsigned j = 0; j < terms; ++j) {
      F d = from_u64(U(1) << (2*j)); num_a[j] = mul(d,ca); num_b[j] = mul(d,cb);
    }
    auto ax = regular_with_derivative(ONE), ay = regular_with_derivative(omega);
    anchor_x = ax.first; anchor_y = ay.first;
    if (eq(anchor_x,anchor_y)) throw std::runtime_error("deleted anchor rows coincide");
    F dx = add(ax.second,divide(from_u64(m),from_u64(4)));
    F dy = add(ay.second,divide(from_u64(m),mul(from_u64(4),omega)));
    F gap = sub(anchor_x,anchor_y), distance = sub(ONE,omega);
    priv = {{{ZERO,ONE},{gap,mul(distance,dx)},{mul(distance,dy),gap},{ONE,ZERO}}};
  }
  std::pair<F,F> regular_with_derivative(F x) const {
    F z = mul(omega,x), total = ZERO, derivative = ZERO;
    F half = inverse(from_u64(2));
    for (unsigned j = 0; j < terms; ++j) {
      F d = from_u64(U(1) << (2*j));
      F ia = inverse(sub(z,ii)), ib = inverse(add(z,ONE));
      total = add(total,mul(d,sub(mul(half,ib),mul(ii,ia))));
      F slope = sub(mul(ii,mul(ia,ia)),mul(half,mul(ib,ib)));
      derivative = add(derivative,mul(mul(d,d),mul(z,slope)));
      z = mul(z,z); z = mul(z,z);
    }
    return {mul(total,inv_m),divide(mul(derivative,inv_m),x)};
  }
  Direction at(U e, F x) const {
    if (e < 2 || e >= n) throw std::runtime_error("ordinary exponent out of range");
    F numerator, denominator;
    if ((e & 3) == 3) { numerator = ONE; denominator = ZERO; }
    else {
      F a = ZERO, b = ONE, z = mul(omega,x);
      for (unsigned j = 0; j < terms; ++j) {
        F term_n = add(mul(num_a[j],z),num_b[j]);
        F term_d = mul(sub(z,ii),add(z,ONE)); term_d = add(term_d,term_d);
        a = add(mul(a,term_d),mul(term_n,b)); b = mul(b,term_d);
        z = mul(z,z); z = mul(z,z);
      }
      if (zero(b)) throw std::runtime_error("unexpected ordinary pole");
      numerator = mul(a,inv_m); denominator = b;
      if ((e & 3) == 2) numerator = add(numerator,mul(half_i,b));
    }
    Direction row{mul(sub(numerator,mul(anchor_y,denominator)),sub(x,ONE)),
                  mul(sub(numerator,mul(anchor_x,denominator)),sub(x,omega))};
    if (zero(row.first) && zero(row.second)) throw std::runtime_error("zero residual direction");
    return row;
  }
  Direction slot(U s, F x) const { return s < 4 ? priv[s] : at(s-2,x); }
};

// A fixed chart g -> g+f: gamma=-first/(first+second). Poles are explicitly
// excluded from finite-event counts, even if several slots represent that pole.
void normalize(const std::vector<Direction>& rows, std::vector<Value>& values) {
  std::vector<F> prefixes(rows.size());
  F product = ONE;
  for (size_t j=0; j<rows.size(); ++j) {
    if(zero(rows[j].first) && zero(rows[j].second))throw std::runtime_error("zero residual in normalization");
    prefixes[j]=product; F d=add(rows[j].first,rows[j].second);
    if (!zero(d)) product=mul(product,d);
  }
  F back=inverse(product); values.resize(rows.size());
  for (size_t j=rows.size(); j-- > 0;) {
    F d=add(rows[j].first,rows[j].second);
    if (zero(d)) { values[j]={false,ZERO}; continue; }
    F inv=mul(back,prefixes[j]); back=mul(back,d);
    values[j]={true,ordinary(mul(neg(rows[j].first),inv))};
  }
}

U available_bytes() {
#ifdef __APPLE__
  vm_statistics64_data_t vm{}; mach_msg_type_number_t count=HOST_VM_INFO64_COUNT;
  mach_port_t host=mach_host_self(); vm_size_t page=0;
  kern_return_t a=host_page_size(host,&page);
  kern_return_t b=host_statistics64(host,HOST_VM_INFO64,reinterpret_cast<host_info64_t>(&vm),&count);
  mach_port_deallocate(mach_task_self(),host);
  if (a!=KERN_SUCCESS || b!=KERN_SUCCESS) throw std::runtime_error("cannot inspect available memory");
  // HOST_VM_INFO64 free_count already includes speculative_count. See Apple's
  // mach/vm_statistics.h and osfmk/kern/host.c. Do not add it a second time.
  // Deliberately exclude other file cache, anonymous and compressed pages.
  return U(vm.free_count)*page;
#else
  std::ifstream f("/proc/meminfo"); std::string key, unit; U value;
  while (f>>key>>value>>unit) if(key=="MemAvailable:") return value*1024;
  throw std::runtime_error("cannot inspect available memory");
#endif
}
void require_normal_pressure() {
#ifdef __APPLE__
  uint32_t level=0;size_t size=sizeof(level);
  if(sysctlbyname("kern.memorystatus_vm_pressure_level",&level,&size,nullptr,0)!=0 || size!=sizeof(level))
    throw Incomplete("cannot read macOS memory-pressure level");
  // This sysctl returns dispatch flags, not the internal enum: NORMAL=1.
  if(level!=1)throw Incomplete("macOS memory pressure is not NORMAL");
#endif
}
struct Totals { U slots=0, poles=0, checksum=0; double seconds=0; };
// Callback receives the slot number: private slots0..3, then exponent=slot-2.
template<class Callback>
Totals stream(const Model &model,U count,unsigned workers,Callback callback,bool memory_watch=false,U memory_floor=512*MIB) {
  constexpr U BLOCK=4096;
  if (count>model.n+2 || workers==0 || workers>18) throw std::runtime_error("invalid stream bounds");
  std::atomic<U> next{0},poles{0},checksum{0}; std::atomic<bool> stop{false};
  std::exception_ptr failure; std::mutex lock; std::vector<std::thread> threads;
  auto start=std::chrono::steady_clock::now();
  for(unsigned t=0;t<workers;++t) threads.emplace_back([&]{
    try {
      std::vector<Direction> rows; std::vector<Value> values; rows.reserve(BLOCK);
      while(!stop.load(std::memory_order_relaxed)) {
        U begin=next.fetch_add(BLOCK); if(begin>=count) break;
        if(memory_watch && begin%(BLOCK*256)==0) {
          require_normal_pressure();
          if(available_bytes()<memory_floor)
            throw Incomplete("available memory fell below scan floor; scan aborted");
        }
        U end=std::min(count,begin+BLOCK); rows.clear();
        U exponent=begin<4 ? 2 : begin-2; F x=power(model.omega,exponent);
        for(U s=begin;s<end;++s) {
          rows.push_back(model.slot(s,x));
          if(s>=4) x=mul(x,model.omega);
        }
        normalize(rows,values); U local_poles=0,local_hash=0;
        for(U s=begin;s<end;++s) {
          Value v=values[s-begin]; local_poles+=!v.finite;
          local_hash^=mix(fingerprint(v)^s); callback(s,v);
        }
        poles.fetch_add(local_poles);checksum.fetch_xor(local_hash);
      }
    } catch(...) { std::lock_guard<std::mutex> guard(lock); if(!failure) failure=std::current_exception(); stop=true; }
  });
  for(auto &thread:threads) thread.join();
  if(failure) std::rethrow_exception(failure);
  return {count,poles.load(),checksum.load(),std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()};
}
bool less_f(F a,F b) { return a.c!=b.c?a.c<b.c:a.b!=b.b?a.b<b.b:a.a<b.a; }
void arithmetic_check() {
  F last{sub(ZERO,ONE)}, one=ONE;
  if(!eq(mul(one,one),one) || !eq(add(last,one),ZERO) || !eq(mul(last,last),one))
    throw std::runtime_error("field edge check failed");
  U rng=0x123456789abcdefULL;
  for(unsigned j=0;j<1000;++j) {
    rng=mix(rng+j); F a=from_u64(rng); rng=mix(rng); F b=from_u64(rng);
    if(!eq(sub(add(a,b),b),a) || !eq(mul(a,add(b,ONE)),add(mul(a,b),a)))
      throw std::runtime_error("field identity failed");
  }
}
void small(U n) {
  Model model(n);std::vector<F> values;values.reserve(n+2);
  Totals t=stream(model,n+2,1,[&](U,Value v){if(v.finite)values.push_back(v.gamma);});
  std::sort(values.begin(),values.end(),less_f);
  U unique=std::unique(values.begin(),values.end(),eq)-values.begin();
  std::cout<<"{\"mode\":\"bounded_self_check\",\"n\":"<<n<<",\"slots\":"<<t.slots
    <<",\"chart_poles\":"<<t.poles<<",\"exact_distinct_finite_values\":"<<unique<<",\"seconds\":"<<t.seconds<<"}\n";
  if(unique!=n+2)throw std::runtime_error("small count changed");
}
struct Record {U key; F value;};
void scan(U n,unsigned workers,U allowance_mib,unsigned bits=64,bool bounded_test=false) {
  if(bounded_test && n>65536)throw std::runtime_error("test reserve restricted to n<=65536");
  if(allowance_mib>std::numeric_limits<U>::max()/MIB)throw std::runtime_error("array allowance overflow");
  Model model(n); U slots=n+2, bytes=slots*sizeof(U), allowance=allowance_mib*MIB;
  U available=available_bytes();
  U reserve=(bounded_test?64:4096)*MIB,memory_floor=(bounded_test?64:512)*MIB;
  if(bytes>allowance || available<bytes+reserve)
    throw Incomplete("scan memory gate failed: require array allowance and free_count >= array+reserve");
  require_normal_pressure();
  std::unique_ptr<U[]> keys(new U[slots]);
  Totals t=stream(model,slots,workers,[&](U s,Value v){keys[s]=key_for(v,bits);},true,memory_floor);
  require_normal_pressure();
  auto sort_start=std::chrono::steady_clock::now();std::sort(keys.get(),keys.get()+slots);
  require_normal_pressure();
  U unique=slots?1:0;std::vector<U> affected;constexpr U MAX_KEYS=1000000;
  for(U j=1;j<slots;++j) {
    if(keys[j]!=keys[j-1])++unique;
    else if(affected.empty() || affected.back()!=keys[j]) {
      if(affected.size()==MAX_KEYS)throw Incomplete("too many fingerprint ties for bounded resolution");
      affected.push_back(keys[j]);
    }
  }
  double sorting=std::chrono::duration<double>(std::chrono::steady_clock::now()-sort_start).count();
  U lower=unique-(t.poles?1:0),exact=0;bool resolved=false;
  // Distinct fingerprints are a deterministic lower bound. Only if insufficient,
  // revisit tied keys and compare full canonical field values, excluding poles.
  if(lower<n+1) {
    if(t.poles && !std::binary_search(affected.begin(),affected.end(),U(0))) {
      affected.push_back(0);std::sort(affected.begin(),affected.end());
    }
    constexpr U MAX_RECORDS=4000000;
    std::vector<Record> records;records.reserve(std::min<U>(slots,MAX_RECORDS));std::mutex mutex;
    stream(model,slots,workers,[&](U,Value v){
      if(!v.finite)return;U key=key_for(v,bits);
      if(!std::binary_search(affected.begin(),affected.end(),key))return;
      std::lock_guard<std::mutex> guard(mutex);
      if(records.size()==MAX_RECORDS)throw Incomplete("too many candidates for bounded exact resolution");
      records.push_back({key,v.gamma});
    },true,memory_floor);
    require_normal_pressure();
    std::sort(records.begin(),records.end(),[](const Record&a,const Record&b){return a.key!=b.key?a.key<b.key:less_f(a.value,b.value);});
    require_normal_pressure();
    U corrected=0;
    for(size_t j=0;j<records.size();++j)
      if(j==0 || records[j].key!=records[j-1].key || !eq(records[j].value,records[j-1].value))++corrected;
    exact=unique-affected.size()+corrected;lower=exact;resolved=true;
  }
  std::cout<<"{\"mode\":\"exact_fingerprint_scan\",\"n\":"<<n<<",\"slots\":"<<slots
    <<",\"array_bytes\":"<<bytes<<",\"available_bytes_before\":"<<available
    <<",\"chart_pole_slots\":"<<t.poles<<",\"distinct_keys\":"<<unique
    <<",\"finite_event_count_lower_bound\":"<<lower<<",\"exact_resolution_used\":"<<(resolved?"true":"false")
    <<",\"length_plus_one_met\":"<<(lower>=n+1?"true":"false")
    <<",\"production_budget_exceeded\":"<<(n==PROD && lower>=PROD+1?"true":"false")<<",\"evaluation_seconds\":"<<t.seconds
    <<",\"sort_seconds\":"<<sorting<<",\"checksum\":"<<t.checksum
    <<",\"scope\":\"native_finite_computation_not_Lean_proof\"}\n";
}

// Equal finite values have equal fingerprints and therefore always enter the
// same top-bit partition. Each pass streams the whole domain but retains only
// one partition. Capacity is an explicit bound, never a distribution assumption.
void partition_scan(U n,unsigned workers,U cap_bytes,unsigned bits=64,unsigned partition_bits=1,bool bounded_test=false) {
  if(partition_bits<1 || partition_bits>4)throw std::runtime_error("partition bits must be in1..4");
  if(bounded_test && n>65536)throw std::runtime_error("test reserve restricted to n<=65536");
  Model model(n);U slots=n+2,bytes=std::min(cap_bytes,slots*sizeof(U));
  if(bytes<sizeof(U))throw Incomplete("partition capacity is zero");
  U available=available_bytes();
  U reserve=bounded_test?64*MIB:std::max<U>(1024*MIB,bytes/2);
  U memory_floor=(bounded_test?64:512)*MIB;
  if(available<bytes+reserve)throw Incomplete("partition memory gate failed: require array+reserve conservative available");
  require_normal_pressure();
  U capacity=bytes/sizeof(U);std::unique_ptr<U[]> keys(new U[capacity]);
  U total=0,first_poles=0,first_checksum=0,resolution_passes=0;double evaluation=0,sorting=0;
  unsigned partitions=1u<<partition_bits;
  for(unsigned part=0;part<partitions;++part) {
    std::atomic<U> used{0};
    std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"evaluation_start\",\"slots\":"<<slots<<"}\n"<<std::flush;
    Totals t=stream(model,slots,workers,[&](U,Value v){
      if(!v.finite)return;U key=key_for(v,bits);if((key>>(64-partition_bits))!=part)return;
      U at=used.fetch_add(1);if(at>=capacity)throw Incomplete("partition capacity exceeded; no count certificate produced");
      keys[at]=key;
    },true,memory_floor);
    evaluation+=t.seconds;
    std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"evaluation_complete\",\"seconds\":"<<t.seconds<<",\"stored_slots\":"<<used.load()<<"}\n"<<std::flush;
    if(part==0){first_poles=t.poles;first_checksum=t.checksum;}
    else if(t.poles!=first_poles || t.checksum!=first_checksum)throw std::runtime_error("partition streams disagree");
    U length=used.load(),unique=length?1:0;std::vector<U> affected;
    std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"sort_start\",\"stored_slots\":"<<length<<"}\n"<<std::flush;
    require_normal_pressure();
    auto start=std::chrono::steady_clock::now();std::sort(keys.get(),keys.get()+length);
    require_normal_pressure();
    for(U j=1;j<length;++j) {
      if(keys[j]!=keys[j-1])++unique;
      else if(affected.empty() || affected.back()!=keys[j]) {
        if(affected.size()==1000000)throw Incomplete("too many partition tie keys for bounded resolution");
        affected.push_back(keys[j]);
      }
    }
    sorting+=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"sort_complete\",\"unique_keys\":"<<unique<<",\"tied_keys\":"<<affected.size()<<"}\n"<<std::flush;
    U corrected=unique;
    if(!affected.empty()) {
      constexpr U MAX_RECORDS=4000000;
      std::vector<Record> records;records.reserve(std::min<U>(length,MAX_RECORDS));std::mutex mutex;
      std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"exact_tie_resolution_start\"}\n"<<std::flush;
      Totals second=stream(model,slots,workers,[&](U,Value v){
        if(!v.finite)return;U key=key_for(v,bits);
        if(!std::binary_search(affected.begin(),affected.end(),key))return;
        std::lock_guard<std::mutex> guard(mutex);
        if(records.size()==MAX_RECORDS)throw Incomplete("partition exact-tie candidate capacity exceeded");
        records.push_back({key,v.gamma});
      },true,memory_floor);
      evaluation+=second.seconds;++resolution_passes;
      if(second.poles!=first_poles || second.checksum!=first_checksum)throw std::runtime_error("tie-resolution stream disagrees");
      require_normal_pressure();
      std::sort(records.begin(),records.end(),[](const Record&a,const Record&b){return a.key!=b.key?a.key<b.key:less_f(a.value,b.value);});
      require_normal_pressure();
      U distinct=0;
      for(size_t j=0;j<records.size();++j)
        if(j==0 || records[j].key!=records[j-1].key || !eq(records[j].value,records[j-1].value))++distinct;
      corrected=unique-affected.size()+distinct;
      std::cout<<"{\"mode\":\"partition_progress\",\"partition\":"<<part<<",\"phase\":\"exact_tie_resolution_complete\",\"candidate_records\":"<<records.size()<<"}\n"<<std::flush;
    }
    total+=corrected;
    std::cout<<"{\"mode\":\"partition_pass\",\"partition\":"<<part<<",\"stored_finite_slots\":"<<length
      <<",\"unique_fingerprints\":"<<unique<<",\"tied_keys\":"<<affected.size()
      <<",\"exact_finite_values_in_partition\":"<<corrected<<",\"complete_domain_certificate\":false}\n"<<std::flush;
  }
  std::cout<<"{\"mode\":\"partition_scan_complete\",\"n\":"<<n<<",\"slots\":"<<slots
    <<",\"array_bytes\":"<<bytes<<",\"available_bytes_before\":"<<available<<",\"hash_bits\":"<<bits
    <<",\"partition_bits\":"<<partition_bits<<",\"partition_count\":"<<partitions<<",\"reserve_bytes\":"<<reserve
    <<",\"chart_pole_slots\":"<<first_poles<<",\"exact_distinct_finite_values\":"<<total
    <<",\"finite_event_count_lower_bound\":"<<total<<",\"exact_resolution_passes\":"<<resolution_passes
    <<",\"length_plus_one_met\":"<<(total>=n+1?"true":"false")
    <<",\"production_budget_exceeded\":"<<(n==PROD && total>=PROD+1?"true":"false")
    <<",\"evaluation_seconds\":"<<evaluation<<",\"sort_seconds\":"<<sorting
    <<",\"checksum\":"<<first_checksum<<",\"scope\":\"native_finite_computation_not_Lean_proof\"}\n";
}
U number(const char*s){
  if(!s[0])throw std::runtime_error("empty number");
  for(const char*p=s;*p;++p)if(*p<'0' || *p>'9')throw std::runtime_error("invalid unsigned number");
  size_t end=0;U n=std::stoull(s,&end);if(s[end])throw std::runtime_error("invalid number");return n;
}
unsigned worker_number(const char*s){U n=number(s);if(n==0 || n>18)throw std::runtime_error("workers must be in1..18");return unsigned(n);}
int main(int argc,char**argv) {
  try {
    arithmetic_check();std::string mode=argc>1?argv[1]:"--self-check";
    if(mode=="--self-check") {for(U n:{16,64,256})small(n);return 0;}
    if(mode=="--memory") {std::cout<<"{\"available_bytes_conservative\":"<<available_bytes()<<"}\n";return 0;}
    if(mode=="--field-vectors") {
      U rng=0xc001d00d1234ULL;
      for(unsigned j=0;j<1000;++j) {
        auto sample=[&]{rng=mix(rng);U a=rng;rng=mix(rng);U b=rng;rng=mix(rng);return F{a,b,rng&((U(1)<<30)-1)};};
        F a=sample(),b=sample();
        std::cout<<decimal_out(a)<<' '<<decimal_out(b)<<' '<<decimal_out(mul(a,b))
          <<' '<<decimal_out(add(a,b))<<' '<<decimal_out(sub(a,b))<<'\n';
      }return 0;
    }
    if(mode=="--field-input") {
      std::string left,right;
      while(std::cin>>left>>right) {
        F am=decimal(left),bm=decimal(right),a=ordinary(am),b=ordinary(bm);
        std::cout<<decimal_out(mul(a,b))<<' '<<decimal_out(add(a,b))<<' '<<decimal_out(sub(a,b))
          <<' '<<(zero(am)?"zero":decimal_out(ordinary(inverse(am))))<<'\n';
      }return 0;
    }
    if(mode=="--normalize-input") {
      std::string first,second;std::vector<Direction> rows;
      while(std::cin>>first>>second) {
        if(rows.size()==10000)throw std::runtime_error("normalization test capped at10000 rows");
        rows.push_back({decimal(first),decimal(second)});
      }
      std::vector<Value> values;normalize(rows,values);
      for(Value v:values)std::cout<<(v.finite?decimal_out(v.gamma):"pole")<<'\n';return 0;
    }
    if(mode=="--emit" && argc==6) {
      U n=number(argv[2]),start=number(argv[3]),count=number(argv[4]),step=number(argv[5]);Model model(n);
      if(count>1000000 || !step || start>=n || (count && count-1>(n-1-start)/step))throw std::runtime_error("bounded emit range invalid");
      for(U j=0;j<count;++j) {
        U e=start+j*step;std::vector<Direction> rows;
        if(e<2)rows={model.priv[e*2],model.priv[e*2+1]};else rows={model.at(e,power(model.omega,e))};
        std::vector<Value> values;normalize(rows,values);
        for(size_t q=0;q<values.size();++q)std::cout<<"{\"exponent\":"<<e<<",\"private_slot\":"<<(e<2?int(q):-1)
          <<",\"gamma\":"<<(values[q].finite?"\""+decimal_out(values[q].gamma)+"\"":"null")<<"}\n";
      }return 0;
    }
    if(mode=="--emit-slots" && argc==5) {
      U n=number(argv[2]),count=number(argv[3]);unsigned workers=worker_number(argv[4]);Model model(n);std::mutex lock;
      if(count>10000)throw std::runtime_error("bounded slot output capped at10000");
      stream(model,count,workers,[&](U s,Value v){
        std::lock_guard<std::mutex> guard(lock);
        std::cout<<"{\"slot\":"<<s<<",\"gamma\":"<<(v.finite?"\""+decimal_out(v.gamma)+"\"":"null")<<"}\n";
      });return 0;
    }
    if(mode=="--benchmark" && argc==5) {
      U n=number(argv[2]),count=number(argv[3]);unsigned workers=worker_number(argv[4]);Model model(n);
      if(count>4000000)throw std::runtime_error("benchmark capped at4million slots");
      Totals t=stream(model,std::min(n+2,count),workers,[](U,Value){});
      std::cout<<"{\"mode\":\"bounded_evaluation_benchmark\",\"n\":"<<n<<",\"slots\":"<<t.slots
        <<",\"workers\":"<<workers<<",\"seconds\":"<<t.seconds<<",\"slots_per_second\":"<<t.slots/t.seconds
        <<",\"chart_poles\":"<<t.poles<<",\"checksum\":"<<t.checksum<<"}\n";return 0;
    }
    if(mode=="--benchmark-partition" && argc==5) {
      U n=number(argv[2]),count=number(argv[3]);unsigned workers=worker_number(argv[4]);Model model(n);
      if(count>4000000 || count>n+2)throw std::runtime_error("partition benchmark capped at4million valid slots");
      std::unique_ptr<U[]> keys(new U[count]);std::atomic<U> used{0};
      Totals t=stream(model,count,workers,[&](U,Value v){if(v.finite){U key=fingerprint(v);if(!(key>>63))keys[used.fetch_add(1)]=key;}});
      auto start=std::chrono::steady_clock::now();U length=used.load();std::sort(keys.get(),keys.get()+length);
      double sorting=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
      std::cout<<"{\"mode\":\"bounded_partition_benchmark\",\"n\":"<<n<<",\"slots\":"<<count
        <<",\"workers\":"<<workers<<",\"evaluation_seconds\":"<<t.seconds<<",\"sort_seconds\":"<<sorting
        <<",\"stored_slots\":"<<length<<",\"array_bytes\":"<<count*sizeof(U)<<",\"checksum\":"<<t.checksum<<"}\n";return 0;
    }
    if(mode=="--scan" && argc==5) {scan(number(argv[2]),worker_number(argv[3]),number(argv[4]));return 0;}
    if(mode=="--scan-test" && argc==4) {
      U n=number(argv[2]),bits=number(argv[3]);if(n>65536 || bits<1 || bits>64)throw std::runtime_error("invalid bounded hash test");
      scan(n,2,1,unsigned(bits),true);return 0;
    }
    if(mode=="--partition-scan" && (argc==5 || argc==6)) {
      U cap=number(argv[4]);if(cap>std::numeric_limits<U>::max()/MIB)throw std::runtime_error("partition capacity overflow");
      U pb=argc==6?number(argv[5]):1;if(pb<1 || pb>4)throw std::runtime_error("partition bits must be in1..4");
      partition_scan(number(argv[2]),worker_number(argv[3]),cap*MIB,64,unsigned(pb));return 0;
    }
    if(mode=="--partition-test" && (argc==5 || argc==6)) {
      U n=number(argv[2]),bits=number(argv[3]),cap=number(argv[4]);
      if(n>65536 || bits<1 || bits>64 || cap>MIB)throw std::runtime_error("invalid bounded partition test");
      U pb=argc==6?number(argv[5]):1;if(pb<1 || pb>4)throw std::runtime_error("partition bits must be in1..4");
      partition_scan(n,2,cap,unsigned(bits),unsigned(pb),true);return 0;
    }
    std::cerr<<"Usage: --self-check | --memory | --field-vectors | --field-input | --normalize-input | --emit N START COUNT STEP | --emit-slots N COUNT THREADS | --benchmark N SLOTS THREADS | --scan N THREADS MAX_ARRAY_MIB | --partition-scan N THREADS CAP_MIB [PARTITION_BITS] | --scan-test N HASH_BITS | --partition-test N HASH_BITS CAP_BYTES [PARTITION_BITS]\n";return 2;
  }catch(const Incomplete&e){std::cerr<<"INCOMPLETE: "<<e.what()<<'\n';return 3;}
  catch(const std::bad_alloc&){std::cerr<<"INCOMPLETE: allocation failed\n";return 3;}
  catch(const std::exception&e){std::cerr<<"FAIL: "<<e.what()<<'\n';return 1;}
}
