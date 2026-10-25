#ifndef UNIQUE_LANGUAGE_FILTER_HPP
#define UNIQUE_LANGUAGE_FILTER_HPP

#include <map>
#include <set>
#include <vector>
#include "Alphabet.hpp"

namespace regal{

  /**
     Exact language deduplication for deterministic transitions and arbitrarily
     many initial states. Determinize the initial subset (including an empty
     rejecting sink if reachable), minimize, then number the quotient by BFS.
     Equal integer vectors mean equal languages, with no hash collisions.
     The alphabet order must be the same for every call to a filter instance.
  */
  template<typename StateLabel_t,typename Sigma,class Automaton_t>
  class UniqueLanguageFilter{
    std::set<std::vector<int> > seen;

  public:
    static std::vector<int> key(Automaton_t * automaton){
      const int n=automaton->getSize();
      Alphabet<Sigma> alphabet=automaton->getAlphabet();
      std::list<Sigma> list=alphabet.getList();
      std::vector<Sigma> letters(list.begin(),list.end());
      const int k=static_cast<int>(letters.size());
      std::vector<int> initial;
      for(int i=0;i<n;i++)
        if(automaton->isInitial(automaton->getRealValue(i)))initial.push_back(i);

      std::map<std::vector<int>,int> index;
      std::vector<std::vector<int> > subsets;
      std::vector<std::vector<int> > transitions;
      std::vector<int> finals;
      index[initial]=0;
      subsets.push_back(initial);
      for(size_t current=0;current<subsets.size();current++){
        // Inserting a new subset may reallocate subsets, so retain a copy.
        const std::vector<int> subset=subsets[current];
        bool accepting=false;
        for(size_t i=0;i<subset.size();i++)
          if(automaton->isFinal(automaton->getRealValue(subset[i])))accepting=true;
        finals.push_back(accepting?1:0);
        std::vector<int> row(k);
        for(int a=0;a<k;a++){
          std::vector<char> reached(n,0);
          for(size_t i=0;i<subset.size();i++){
            const int target=automaton->getArrivalNumericalState(subset[i],letters[a]);
            if(target!=-1)reached[target]=1;
          }
          std::vector<int> next;
          for(int i=0;i<n;i++)if(reached[i])next.push_back(i);
          typename std::map<std::vector<int>,int>::iterator found=index.find(next);
          if(found==index.end()){
            const int id=static_cast<int>(subsets.size());
            index[next]=id;
            subsets.push_back(next);
            row[a]=id;
          }
          else row[a]=found->second;
        }
        transitions.push_back(row);
      }

      // Refinement of the complete subset DFA, independent of Moore's treatment
      // of undefined edges in the original partial automaton.
      const int count=static_cast<int>(subsets.size());
      std::vector<int> classes=finals;
      while(true){
        std::map<std::vector<int>,int> groups;
        std::vector<int> refined(count);
        for(int i=0;i<count;i++){
          std::vector<int> signature;
          signature.push_back(classes[i]);
          for(int a=0;a<k;a++)signature.push_back(classes[transitions[i][a]]);
          const int nextId=static_cast<int>(groups.size());
          refined[i]=groups.insert(std::make_pair(signature,nextId)).first->second;
        }
        if(refined==classes)break;
        classes.swap(refined);
      }

      std::vector<int> representative(count,-1),renamed(count,-1),order;
      for(int i=0;i<count;i++)
        if(representative[classes[i]]==-1)representative[classes[i]]=i;
      renamed[classes[0]]=0;
      order.push_back(classes[0]);
      std::vector<int> result;
      result.push_back(k);
      for(size_t i=0;i<order.size();i++){
        const int state=representative[order[i]];
        result.push_back(finals[state]);
        for(int a=0;a<k;a++){
          const int target=classes[transitions[state][a]];
          if(renamed[target]==-1){
            renamed[target]=static_cast<int>(order.size());
            order.push_back(target);
          }
          result.push_back(renamed[target]);
        }
      }
      return result;
    }

    bool insert(Automaton_t * automaton){return seen.insert(key(automaton)).second;}
  };
}
#endif
