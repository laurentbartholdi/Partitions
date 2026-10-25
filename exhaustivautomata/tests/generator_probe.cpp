#include <cassert>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sstream>
#include "ExhaustiveDFAGenerator.hpp"
#include "DFAAutomaton.hpp"
#include "MultiInitialDFAGenerator.hpp"
#include "UniqueLanguageFilter.hpp"

using namespace regal;

typedef DFAAutomaton<int,char> DFA;

static void checkPartialMinimality(){
  Alphabet<char> alphabet;
  alphabet.insert('a');
  alphabet.insert('b');
  MooreAlgorithm<int,char,DFA> moore;
  DFA a(2,alphabet);
  a.addState(); a.addState();
  a.setStateAsInitial(0,true);
  a.setStateAsFinal(0,true);
  a.setStateAsFinal(1,true);
  a.addTransition(0,1,'a');
  // All states final, but their right languages are {epsilon,a} and {epsilon}.
  assert(moore.isMinimalPartial(&a));
  a.addTransition(1,1,'a');
  assert(!moore.isMinimalPartial(&a)); // Both right languages are a*.
  a.setStateAsFinal(1,false);
  assert(!moore.isMinimalPartial(&a)); // State 1 has empty right language.
  assert(!a.isFinal(-1));
  assert(!a.isInitial(-1));
  assert(a.getArrivalState(-1,'a')==-1);
  a.addTransition(0,-1,'a');
  assert(a.getArrivalState(0,'a')==-1);
  bool caught=false;
  try {a.addTransition(-1,0,'a');} catch(...) {caught=true;}
  assert(caught);
  caught=false;
  try {a.setStateAsFinal(-1,true);} catch(...) {caught=true;}
  assert(caught);
  DFA empty(1,alphabet);
  empty.addState();
  assert(moore.isMinimalPartial(&empty));
  empty.addTransition(0,0,'a');
  assert(!moore.isMinimalPartial(&empty)); // Canonical empty language omits edges.
  empty.setStateAsFinal(0,true);
  assert(moore.isMinimalPartial(&empty));
  // Reuse the same minimizer across sizes and repeated no-final-state cuts.
  a.setStateAsFinal(0,false);
  for(int i=0;i<3;i++)assert(!moore.isMinimal(&a));
  a.setStateAsFinal(1,true);
  a.addTransition(0,1,'b');
  assert(moore.isMinimalPartial(&a));

  // Distinct right languages are not enough to prevent duplicate union languages.
  a.setStateAsInitial(1,true);
  a.setStateAsFinal(0,true);
  a.addTransition(0,0,'a'); a.addTransition(0,0,'b');
  a.addTransition(1,-1,'a'); a.addTransition(1,-1,'b');
  assert(moore.isMinimalPartial(&a)); // Sigma* and {epsilon} are distinct.
  DFA universal(1,alphabet);
  universal.addState();
  universal.setStateAsInitial(0,true);
  universal.setStateAsFinal(0,true);
  universal.addTransition(0,0,'a'); universal.addTransition(0,0,'b');
  typedef UniqueLanguageFilter<int,char,DFA> Filter;
  assert(Filter::key(&a)==Filter::key(&universal));
  Filter filter;
  assert(filter.insert(&a));
  assert(!filter.insert(&universal));
  a.setStateAsInitial(0,false);
  assert(Filter::key(&a)!=Filter::key(&universal));
}

int main(int argc,char ** argv){
  assert(argc>=2&&argc<=4);
  // Invalid transition checks print diagnostics, so keep them out of raw output.
  std::streambuf * saved=std::cout.rdbuf();
  std::ostringstream diagnostics;
  std::cout.rdbuf(diagnostics.rdbuf());
  checkPartialMinimality();
  std::cout.rdbuf(saved);
  const int n=std::atoi(argv[1]);
  bool partial=false,multi=false;
  for(int i=2;i<argc;i++){
    if(std::strcmp(argv[i],"--partial")==0)partial=true;
    else if(std::strcmp(argv[i],"--multi-initial")==0)multi=true;
    else assert(false);
  }
  Alphabet<char> alphabet;
  alphabet.insert('a'); alphabet.insert('b');
  AbstractExhaustiveGenerator<DFA> * generator;
  if(multi)generator=new MultiInitialDFAGenerator<int,char,DFA>(n,alphabet,partial);
  else generator=new ExhaustiveDFAGenerator<int,char,DFA>(n,alphabet,partial);
  DFA * first=generator->first();
  generator->next();
  assert(first==generator->first());
  long count=0;
  for(DFA * a=generator->first();a!=generator->end();a=generator->next()){
    assert(a==first); // Enumeration reuses the automaton rather than materializing a list.
    std::cout<<*a<<std::endl;
    ++count;
  }
  std::cout<<count<<std::endl;
  if(multi)assert(generator->next()==generator->end());
  delete generator;
}
