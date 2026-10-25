// DFAAutomaton.hpp: this file is part of the REGAL project.
//
// REGAL : Random and Exhaustive Generators for Automata - Library
//
// Copyright (C) 2007 Julien DAVID.
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// The complete GNU General Public Licence Notice can be found as the
// `COPYING' file in the root directory.
//
//
#ifndef DFAAUTOMATON
#define DFAAUTOMATON

#include <list>
#include <iterator>
#include "AbstractAutomaton.hpp"
#include "VerboseOption.hpp"
#include "Pair.hpp"

using namespace std;

namespace regal{

  struct AutomatonLimitSizeExcedeedException : public std::exception {};
  
  template<typename StateLabel_t,typename Sigma>
  class DFAAutomaton: public AbstractAutomaton<StateLabel_t, Sigma> {
  private:
    int maxSize; /*!< max number of states in the automaton */
    //int number; /*!< actual number of states in the automaton */
    int languageSize; /*!< alphabet size */
    int ** data; /*!< matrix of transitions */
    bool * finalStates; /*!< Tabular that indicates if a state is final */
    bool * initialStates; /*!< Tabular that indicates if a state is initial */
  
    
    /**
     Export the DFA into a graphical format
     @param cc is the converter (can be a DoTConverter, GasteXConverter)...
    */
    void exportFormat(Converter * cc){
      char nameBuffer[32],name2Buffer[32],wordBuffer[32];
      char * name=nameBuffer;
      char * name2=name2Buffer;
      char * word=wordBuffer;
      int c,w,c2;
      std::list<Sigma> listT=this->alphabet.getList();
      typename std::list<Sigma>::iterator l;
      cc->beginAutomaton(165,(maxSize/5)*33);
      
      for(c=0;c<getSize();c++){
	snprintf(name,sizeof(nameBuffer),"%d",c);
	cc->draw_node(name,(c%5)*20,-(c/5)*33,isInitial(c),isFinal(c));
      }
    
      for(c=0;c<getSize();c++){
	//for(w=0;w<languageSize;w++){
	for(l=listT.begin();l!=listT.end();l++){  
	  w=this->alphabet.getNumericalValue(*l);
	  c2=data[c][w];
	  if(c2!=undefinedTransition()){
	    snprintf(name,sizeof(nameBuffer),"%d",c);
	    snprintf(name2,sizeof(name2Buffer),"%d",c2);
	    snprintf(word,sizeof(wordBuffer),"%c",*l);
	    cc->draw_edge(name,name2,word);
	  }
	}
      }
      cc->endAutomaton();
    }
    
  public:
    /**
       This function returns a label for a new state and reallocate memory
       if it's necessary.
       @param value isn't used in this specification
       @Return the state added in the automaton
    */
    int createState(const int & value=0){
      if(this->stateNumber<=maxSize)
	return this->stateNumber++;
      
      cout<<"This Automaton has a fixed number of states"<<endl;
      throw new AutomatonLimitSizeExcedeedException();
    }  

    /**
       This function descreases the number of definied states.
       Since the automaton is defined as a matrix, it doesn't 
       reduces the memory space used by the automaton
    */
    void deleteLastState(){
      this->undefineLastState();
    }
    

    
    Pair<int,int> createState(const Pair<int,int> & value){
      if(this->stateNumber<maxSize){
	this->stateNumber++;
	return value;
      }
      cout<<"This Automaton has a fixed number of states"<<endl;
      throw new AutomatonLimitSizeExcedeedException();
    }

    


    /**
       Returns the value associated to an undefined transition
       according to the type of the states
       @Return the value associated to an undefined transition
    */
    StateLabel_t undefinedTransition() const{
      return -1;
    }    

        
    /**
       Returns the actual size of the automaton
       @Return the actual size of the automaton
    */
    int getSize(){return this->stateNumber;}
    
    /**
       Returns q, with p-->w-->q
       @param start is the starting state
       @param word is the label on the transition coming out from start
       @Return q, with p-->w-->q
    */
    StateLabel_t getArrivalState(const StateLabel_t & start,const Sigma & word){
      if(start==undefinedTransition())return undefinedTransition();
      const int index=this->getIntegerValue(start);
      if(index<0||index>=this->stateNumber)throw InvalidStateException();
      return this->getRealValue(data[index][this->alphabet.getNumericalValue(word)]);
    }
    
    /**
       Returns q, with p-->w-->q
       @param start is the starting state
       @param word is the label on the transition coming out from start
       @Return q, with p-->w-->q
    */
    int getArrivalNumericalState(const int & start,const Sigma & word){
      return data[start][this->alphabet.getNumericalValue(word)];
    }
    
    /**
       Adds a transtition between start and end.
       @param start is the state where the transition comes from.
       @param end is the state pointed by the transition
       @param value is the label associated to the transition.
    */
    void addTransition(const StateLabel_t& start,const StateLabel_t& end,
		       const Sigma & value){
      const int from=this->getIntegerValue(start);
      const bool undefined=end==undefinedTransition();
      const int to=undefined?-1:this->getIntegerValue(end);
      const int letter=this->alphabet.getNumericalValue(value);
      if(from>=0&&from<this->stateNumber&&(undefined||(to>=0&&to<this->stateNumber))
	 &&letter>=0&&letter<languageSize)
	data[from][letter]=to;
      else{
	cout<<"Automaton Max Size : "<<maxSize<<" Size : "<<this->stateNumber<<", tried values : "<<this->getIntegerValue(start)<<" "<<this->getIntegerValue(end)<<" ";
	cout<<this->alphabet.getNumericalValue(value)<<endl;
	throw new InvalidStateException();
      }
    }

   
    
    
    /**
       Checks if a state is Final
       @param s1 is the state we want to verify
       @Return true if s1 is final, false otherwise
    */
    bool isFinal(const StateLabel_t & sl){
      if(this->getIntegerValue(sl)>=0&&this->getIntegerValue(sl)<this->stateNumber&&finalStates[this->getIntegerValue(sl)]==true)
	return true;
      return false;
    }

    /**
       Checks if a state is initial
       @param s1 is the state we want to verify
       @Return true if s1 is initial, false otherwise
    */
    bool isInitial(const StateLabel_t & sl){
      if(this->getIntegerValue(sl)>=0&&this->getIntegerValue(sl)<this->stateNumber&&initialStates[this->getIntegerValue(sl)]==true)
	return true;
      return false;
    }
    
    /**
       Set a state as final
       @param s1 is the state to parameter
    */
    void setStateAsFinal(const StateLabel_t & sl,const bool & value){
      if(this->getIntegerValue(sl)>=0&&this->getIntegerValue(sl)<this->stateNumber)
	finalStates[this->getIntegerValue(sl)]=value;
      else
	throw new InvalidStateException();
    }
    
    /**
       Set a state as initial
       @param s1 is the state to parameter
    */
    void setStateAsInitial(const StateLabel_t & sl,const bool & value){
      if(this->getIntegerValue(sl)>=0&&this->getIntegerValue(sl)<this->stateNumber){
	initialStates[this->getIntegerValue(sl)]=value;
      }
      else
	throw new InvalidStateException();
    }
    
    
    /**
       Translate a DFA into gasteX file format, in order 
       to have a graphical view of the object.
       @param gc is the object which generate gasteX code.
    */
    void toGasteX(GasteXConverter * gc){
      exportFormat(gc);
    }
    
    
    /**
       Convert the current automaton into a DOT file 
       @param F is the file where the DOT format automaton will be saved
    */
    void toDOT(DotConverter * dc){
      exportFormat(dc);
    }
    
    
    friend ostream& operator<<(ostream& o,const DFAAutomaton<int,char> & a);
    friend ostream& operator<<(ostream& o,const DFAAutomaton<Pair<int,int> ,char> & a);
    
    /**
       Creates a DFAAutomaton.
       @param sSize is the maximal number of states in the automaton. (Actually max-1 since
       we let the possibility to complete the automaton 
       @param a is the alphabet
    */
    DFAAutomaton(const int& sSize,const Alphabet<Sigma> & a):AbstractAutomaton<StateLabel_t,Sigma>::AbstractAutomaton(a){
      int i,j;
      maxSize=sSize;
      languageSize=a.getSize();
            
      data= new int*[maxSize+1];
      finalStates= new bool[maxSize+1];
      initialStates= new bool[maxSize+1];
      
      for(i=0;i<(maxSize+1);i++){
	data[i]=new int[languageSize];
	for(j=0;j<languageSize;j++)
	  data[i][j]=undefinedTransition();
	finalStates[i]=false;
	initialStates[i]=false;
      }
      verbose("Creation of an DFAAutomaton");
      
    }
    /**
       Destroy the current DFAAutomaton
    */
    virtual ~DFAAutomaton(){
      int i;
      for(i=0;i<(maxSize+1);i++)
	delete [] data[i];
      delete [] data;
      delete [] finalStates;
      delete [] initialStates;
      verbose("Destruction of an DFAAutomaton");
    }
  };

  /**
     Print a DFA automaton
     @param o is the stream in which we add the DFA's description
     @param a is the DFA we want to print
     @Return the modified stream 
  */
  ostream& operator<<(ostream& o,const DFAAutomaton<int,char> & a){
    int i,j;
    o<<a.stateNumber;
    for(i=0;i<a.stateNumber;i++) {
      if (a.initialStates[i]) o<< " i" << i;
      if (a.finalStates[i]) o<< " f" << i;
    }
    for(i=0;i<a.stateNumber;i++)
      for(j=0;j<a.languageSize;j++)
    	  if(a.data[i][j]!=a.undefinedTransition())
	    o<<" "<<i<<char('a'+j)<<a.data[i][j];
    return o;
  }
  
  /**
     Print a DFA automaton
     @param o is the stream in which we add the DFA's description
     @param a is the DFA we want to print
     @Return the modified stream 
  */
  ostream& operator<<(ostream& o,const DFAAutomaton<Pair<int,int> ,char> & a){
    int i,j;
    Pair<int,int> p;
    o<<endl<<"----------"<<endl;
    o<<"Automaton"<<endl;
    o<<"MaxSize = "<<a.maxSize<<endl;
    o<<"Language Size = "<<a.languageSize<<endl<<endl;
    o<<"   ";
    std::list<char> listT=a.getAlphabet().getList();
    for(std::list<char>::iterator l=listT.begin();l!=listT.end();l++)
      o<<"  "<<*l;
    o<<"    Initial    Final";
    o<<endl<<endl;
    for(i=0;i<a.stateNumber;i++){
      o<<i<<"  ";
      for(j=0;j<a.languageSize;j++){
	p=a.data[i][j];
	if(p.first==a.undefinedTransition())
	  cout<<"        "<<a.undefinedTransition();
	else
	  o<<"  "<<p;
      }
      o<<"    "<<a.initialStates[i]<<"          "<<a.finalStates[i];
      o<<endl;
    }
    o<<endl<<"----------"<<endl;
    return o;
  }

}

#endif
