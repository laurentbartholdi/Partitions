#ifndef MULTI_INITIAL_DFA_GENERATOR_HPP
#define MULTI_INITIAL_DFA_GENERATOR_HPP

#include <algorithm>
#include <vector>
#include "AbstractExhaustiveGenerator.hpp"
#include "AbstractAutomaton.hpp"

namespace regal{

  /**
     Enumerate reachable deterministic transition graphs with a nonempty set of
     initial states, up to isomorphism. The initial states are numbered first;
     other states are numbered in order of breadth-first discovery. Trying all
     orders of the initial states makes the canonicality test exhaustive even
     when no individual initial state reaches the whole automaton.
     Only the current table, traversal workspace and result are retained.
  */
  template<typename StateLabel_t,typename Sigma,class Automaton_t>
  class MultiInitialDFAGenerator: public AbstractExhaustiveGenerator<Automaton_t>{
    Automaton_t * result;
    int n,k,roots,position,firstTarget;
    std::vector<Sigma> letters;
    std::vector<int> table,discovered,permutation,order,renamed;
    std::vector<char> final;
    bool finished;

    bool nextTable(){
      const int length=n*k;
      while(roots<=n){
        while(position>=0){
          if(position==length){
            --position;
            if(discovered[length]==n)return true;
            continue;
          }
          const int known=discovered[position];
          const int lastTarget=known<n?known:n-1;
          if(position/k>=known||++table[position]>lastTarget){
            table[position]=firstTarget-1;
            --position;
            continue;
          }
          const int nextKnown=known+(table[position]==known?1:0);
          if(n-nextKnown>length-position-1)continue;
          discovered[position+1]=nextKnown;
          ++position;
          if(position<length)table[position]=firstTarget-1;
        }
        ++roots;
        position=0;
        discovered[0]=roots;
        std::fill(table.begin(),table.end(),firstTarget-1);
      }
      return false;
    }

    // Compare the table first and final flags second under each root ordering.
    // If withFinal is false, reject entire noncanonical transition graphs before
    // enumerating their final sets. Ties are resolved after finalization.
    bool canonical(bool withFinal){
      permutation.resize(roots);
      for(int i=0;i<roots;i++)permutation[i]=i;
      while(std::next_permutation(permutation.begin(),permutation.end())){
        std::fill(renamed.begin(),renamed.end(),-1);
        int known=roots;
        for(int i=0;i<roots;i++){
          order[i]=permutation[i];
          renamed[order[i]]=i;
        }
        int comparison=0;
        for(int i=0;i<n&&comparison==0;i++){
          for(int a=0;a<k;a++){
            const int target=table[order[i]*k+a];
            if(target!=-1&&renamed[target]==-1){
              renamed[target]=known;
              order[known++]=target;
            }
            const int image=target==-1?-1:renamed[target];
            if(image!=table[i*k+a]){
              comparison=image<table[i*k+a]?-1:1;
              break;
            }
          }
        }
        if(comparison<0)return false;
        if(comparison==0&&withFinal){
          for(int i=0;i<n;i++)
            if(final[order[i]]!=final[i]){
              if(final[order[i]]<final[i])return false;
              break;
            }
        }
      }
      return true;
    }

    bool nextFinal(){
      for(int i=n-1;i>=0;i--){
        final[i]=!final[i];
        if(final[i])return true;
      }
      return false;
    }

    void installTable(){
      for(int i=0;i<n;i++){
        const StateLabel_t state=result->getRealValue(i);
        result->setStateAsInitial(state,i<roots);
        for(int a=0;a<k;a++)
          result->addTransition(state,result->getRealValue(table[i*k+a]),letters[a]);
      }
    }

    Automaton_t * installFinal(){
      for(int i=0;i<n;i++)result->setStateAsFinal(result->getRealValue(i),final[i]!=0);
      return result;
    }

  public:
    MultiInitialDFAGenerator(int size,const Alphabet<Sigma> & alphabet,bool partial=false):
      result(NULL),n(size),k(alphabet.getSize()),roots(1),position(0),
      firstTarget(partial?-1:0),finished(true){
      if(n<=0||k<=0)throw InvalidStateException();
      Alphabet<Sigma> copy=alphabet;
      std::list<Sigma> list=copy.getList();
      letters.assign(list.begin(),list.end());
      table.resize(n*k);
      discovered.resize(n*k+1);
      order.resize(n);
      renamed.resize(n);
      final.resize(n);
      result=new Automaton_t(n,alphabet);
      for(int i=0;i<n;i++)result->addState();
    }

    virtual ~MultiInitialDFAGenerator(){delete result;}

    Automaton_t * first(){
      roots=1;
      position=0;
      discovered[0]=roots;
      std::fill(table.begin(),table.end(),firstTarget-1);
      std::fill(final.begin(),final.end(),0);
      finished=false;
      while(nextTable())
        if(canonical(false)){
          installTable();
          return installFinal();
        }
      finished=true;
      return NULL;
    }

    Automaton_t * next(){
      if(finished)return NULL;
      while(true){
        while(nextFinal())
          if(canonical(true))return installFinal();
        while(nextTable())
          if(canonical(false)){
            installTable();
            return installFinal(); // The all-nonfinal set is always canonical.
          }
        finished=true;
        return NULL;
      }
    }

    Automaton_t * end(){return NULL;}

  private:
    MultiInitialDFAGenerator(const MultiInitialDFAGenerator &);
    MultiInitialDFAGenerator & operator=(const MultiInitialDFAGenerator &);
  };
}
#endif
