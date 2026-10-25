#include <iostream>
#include <cerrno>
#include <climits>
#include <cstring>
#include <cstdlib>
#include "../include/ExhaustiveDFAGenerator.hpp"
#include "../include/DFAAutomaton.hpp"
#include "../include/DotConverter.hpp"
#include "../include/Alphabet.hpp"



#include "../include/MooreAlgorithm.hpp"
#include "../include/MultiInitialDFAGenerator.hpp"
#include "../include/UniqueLanguageFilter.hpp"


using namespace std;
using namespace regal;

bool isSink(DFAAutomaton<int,char> * a, int state){
  if(a->isFinal(state))
    return false;
  //The sink state has two loops labelled by 'a' and 'b'
  if(a->getArrivalState(state,'a') != state || a->getArrivalState(state,'b') != state)
    return false;
  return true;
}


bool startsWithAnA(DFAAutomaton<int,char> * a){
  int sink = a->getArrivalState(0,'b');
  //Initial State cannot be final
  if(a->isFinal(0))
    return false;
  //Initiale state cannot contain loops
  if(sink == 0 || a->getArrivalState(0,'a') == 0)
    return false;
  return isSink(a,sink);
}

//A final state cannot have an incoming transition labelled by 'a'
bool endsWithB(DFAAutomaton<int,char> * a){
  bool at_least_one_b = false;
  for(int i = 0; i < a->getSize(); i++){
    if(a->isFinal(a->getArrivalState(i,'a')))
      return false;
    if(a->isFinal(a->getArrivalState(i,'b')))
      at_least_one_b = true;
  }
  return at_least_one_b;
}

int main(int argc, char ** argv){
  bool partial=false,multiInitial=false;
  bool valid=argc>=2;
  for(int i=2;i<argc;i++){
    if(std::strcmp(argv[i],"--partial")==0&&!partial)partial=true;
    else if(std::strcmp(argv[i],"--multi-initial")==0&&!multiInitial)multiInitial=true;
    else valid=false;
  }
  if(!valid){
    std::cerr<<"Use: ./dfa max-size [--partial] [--multi-initial]"<<std::endl;
    return 1;
  }
  char * end;
  errno=0;
  const long parsedSize=std::strtol(argv[1],&end,10);
  if(errno||end==argv[1]||*end!='\0'||parsedSize<=0||parsedSize>(INT_MAX-1)/2){
    std::cerr<<"Maximum size must be a positive integer (at most "<<(INT_MAX-1)/2<<")."<<std::endl;
    return 1;
  }
  const int maxSize=static_cast<int>(parsedSize);
  Alphabet<char> alpha;
  alpha.insert('a');
  alpha.insert('b');
  DFAAutomaton<int,char> * a;
  MooreAlgorithm<int,char,DFAAutomaton<int,char> > ma;
  typedef DFAAutomaton<int,char> Automaton;
  // Keep one exact language filter across all sizes and both generator modes.
  UniqueLanguageFilter<int,char,Automaton> languages;
  DotConverter dc("dfa.dot");

  for(int size=1;size<=maxSize;size++){
    AbstractExhaustiveGenerator<Automaton> * ag;
    if(multiInitial)ag=new MultiInitialDFAGenerator<int,char,Automaton>(size,alpha,partial);
    else ag=new ExhaustiveDFAGenerator<int,char,Automaton>(size,alpha,partial);
    for(a=ag->first();a!=ag->end();a=ag->next()){
      if(partial?ma.isMinimalPartial(a):ma.isMinimal(a)){
        if(!languages.insert(a))continue;
        cout<<*a<<endl;
      }
    }
    delete ag;
  }
  return 0;
}
