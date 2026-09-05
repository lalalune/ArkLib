// Exact factor-partition experiment, NOT a Lean or ProtocolClaim certificate.
// This strengthens only the rectangle R<=12,V<=48,Z<=3000. Outside it, the
// existing source closure is used. The full original root and ledger remain.
// Reproduction and independent checks: astra_companion_atom_audit.py.

#include <cstdint>
#include <vector>
struct Source;
namespace AstraAtomPartition {
void setup(const std::vector<Source>&);
void begin_slope(int);
void visit(int,int,int,__int128_t&);
}
#define ASTRA_PHASE_SETUP(sources) AstraAtomPartition::setup(sources)
#define ASTRA_PHASE_SLOPE_BEGIN(r) AstraAtomPartition::begin_slope(r)
#define ASTRA_PHASE_CAP_VISIT(r,v,z,cap) AstraAtomPartition::visit(r,v,z,cap)
#define main phase_evaluator_main
#include "astra_companion_phases.cpp"
#undef main
#undef ASTRA_PHASE_SETUP
#undef ASTRA_PHASE_SLOPE_BEGIN
#undef ASTRA_PHASE_CAP_VISIT
#include <memory>
#include <random>

namespace AstraAtomPartition {
struct Piece { int lo,hi; Integer slope,intercept; };

std::vector<Piece> segments(const std::vector<std::uint64_t>& values) {
  std::vector<Piece> result;
  int last=int(values.size())-1;
  for(int lo=0;lo<=last;) {
    int hi=lo; Integer slope=0;
    if(hi<last) {
      slope=Integer(values[hi+1])-values[hi]; ++hi;
      while(hi<last&&Integer(values[hi+1])-values[hi]==slope) ++hi;
    }
    result.push_back({lo,hi,slope,Integer(values[lo])-slope*lo});
    lo=hi+1;
  }
  return result;
}

// max_{k in [lo,hi], k<=z} (rest[z-k] + slope*k + intercept).
// The sliding window works for negative slopes and downward jumps too.
void convolve(const std::uint64_t* rest,std::uint64_t* target,int last,
              const Piece& p,std::vector<int>& queue) {
  int head=0,tail=0;
  auto value=[&](int i){return Integer(rest[i])-p.slope*i;};
  for(int z=p.lo;z<=last;++z) {
    int next=z-p.lo; Integer val=value(next);
    while(tail>head&&value(queue[tail-1])<=val) --tail;
    queue[tail++]=next;
    while(head<tail&&queue[head]<z-p.hi) ++head;
    assert(head<tail);
    Integer candidate=p.slope*z+p.intercept+value(queue[head]);
    assert(candidate>=0&&candidate<(Integer(1)<<64));
    if(candidate>target[z]) target[z]=std::uint64_t(candidate);
  }
}

void self_test() {
  std::mt19937 random(6804);
  for(int trial=0;trial<1000;++trial) {
    int last=int(random()%40);
    std::vector<std::uint64_t> atom(last+1),rest(last+1),actual(last+1),expected(last+1);
    std::vector<int> queue(last+1);
    for(int z=0;z<=last;++z) {
      atom[z]=random()%1000000; rest[z]=random()%1000000;
      actual[z]=expected[z]=random()%1000000;
    }
    auto parts=segments(atom);
    std::vector<int> visits(last+1);
    for(const auto& p:parts) {
      for(int z=p.lo;z<=p.hi;++z) {
        assert(p.slope*z+p.intercept==atom[z]); ++visits[z];
      }
      convolve(rest.data(),actual.data(),last,p,queue);
    }
    for(int z=0;z<=last;++z) {
      assert(visits[z]==1);
      for(int k=0;k<=z;++k) expected[z]=std::max(expected[z],rest[z-k]+atom[k]);
      assert(actual[z]==expected[z]);
    }
  }
  std::cout<<"ATOM_CONVOLUTION_SELF_TEST 1000 exact_cases_passed\n";
}

struct Partition {
  static constexpr int R=12,V=48,Z=3000;
  std::vector<std::uint64_t> table;
  std::vector<std::vector<Piece>> pieces;
  std::uint64_t convolutions=0,improved=0;
  Integer singleton=0,point_before=0,point_after=0;
  std::size_t at(int r,int v,int z) const {
    return (std::size_t(r)*(V+1)+v)*(Z+1)+z;
  }
  explicit Partition(const std::vector<Source>& sources)
      :table(std::size_t(R+1)*(V+1)*(Z+1)),pieces((R+1)*(V+1)) {
    std::vector<std::uint64_t> values(Z+1);
    for(int r=1;r<=R;++r) for(int v=0;v<=V;++v) {
      std::vector<int> thresholds;
      for(const auto& s:sources) thresholds.push_back(route_threshold(s,r,v,Z+r+v));
      for(int z=0;z<=Z;++z) {
        Integer cap=ordinary_cost(r,v,z);
        for(int i=0;i<int(sources.size());++i) if(z>=thresholds[i])
          cap=std::min(cap,evaluate(sources[i].potential,r,v,z));
        assert(cap>=0&&cap<(Integer(1)<<64));
        values[z]=std::uint64_t(cap); table[at(r,v,z)]=values[z];
      }
      if(r==10&&v==37) singleton=values[2317];
      pieces[r*(V+1)+v]=segments(values);
    }
  }
  void begin(int r) {
    if(r>R) return;
    std::vector<int> queue(Z+1);
    // A family with at least two positive-slope factors has one factor
    // with slope <=r/2. Its complement has strictly smaller slope and has
    // already received its final cap. Singletons initialize this layer.
    for(int a=1;a<=r/2;++a) for(int v=0;v<=V;++v) for(int av=0;av<=v;++av) {
      const auto* rest=&table[at(r-a,v-av,0)]; auto* target=&table[at(r,v,0)];
      for(const auto& p:pieces[a*(V+1)+av]) {
        ++convolutions; convolve(rest,target,Z,p,queue);
      }
    }
  }
  void observe(int r,int v,int z,Integer& cap) {
    if(r>R||v>V||z>Z) return;
    auto& value=table[at(r,v,z)]; Integer before=cap;
    if(value<cap) ++improved;
    cap=std::min(cap,Integer(value)); value=std::uint64_t(cap);
    if(r==10&&v==37&&z==2317) {point_before=before; point_after=cap;}
  }
};
std::unique_ptr<Partition> partition;
void setup(const std::vector<Source>& sources) {partition=std::make_unique<Partition>(sources);}
void begin_slope(int r) {partition->begin(r);}
void visit(int r,int v,int z,Integer& cap) {partition->observe(r,v,z,cap);}
}

int main(int argc,char** argv) {
  if(argc==2&&std::string(argv[1])=="self-test") {AstraAtomPartition::self_test(); return 0;}
  if(argc<2||std::string(argv[1])!="candidate-closure") {
    std::cerr<<"atom experiment requires candidate-closure mode\n";
    return 1;
  }
  int result=phase_evaluator_main(argc,argv);
  if(result) return result;
  const auto& p=*AstraAtomPartition::partition;
  std::cout<<"ATOM_PARTITION rectangle 12 48 3000 convolutions "<<p.convolutions
      <<" improved_cells "<<p.improved<<" singleton "<<decimal(p.singleton)
      <<" point_before "<<decimal(p.point_before)<<" point_after "<<decimal(p.point_after)<<"\n";
  std::cout<<"RESEARCH_PARTITION_RECURRENCE_ONLY; NO_PROTOCOL_PROOF\n";
  return 0;
}
