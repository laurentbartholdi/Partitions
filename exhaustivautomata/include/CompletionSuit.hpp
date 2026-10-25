// CompletionSuit.hpp: this file is part of the REGAL project.
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
#ifndef COMPLETIONSUIT
#define COMPLETIONSUIT


#include "AbstractSuit.hpp"
#include "CatalanSuit.hpp"

namespace regal{
  
  class CompletionSuit: public AbstractSuit{
  private:
    int modifiedPosition;/*!< Indicates the position of the first modified value */
    CatalanSuit * catalanSuit; /*!< CatalanSuit to complete */
    int firstValue; /*!< Zero encodes an undefined transition; states start at one. */
  public:
    
    
    int * first();
    int * next();
    
    int getModifiedPosition(){return modifiedPosition;}
    
    /**
       Creates a CompletioSuit
       @param cs CatalanSuit to complete
       @param allowUndefined allow zero (an undefined transition) in the completion
    */
    CompletionSuit(CatalanSuit * cs,bool allowUndefined=false):AbstractSuit::AbstractSuit(cs->getSize()){
      catalanSuit=cs;
      firstValue=allowUndefined?0:1;
      modifiedPosition=0;
      verbose("Creation of a CompletionSuit");
    }
    
    /**
       Destroy a CompletionSuit   
    */
    virtual ~CompletionSuit(){
      verbose("Destruction of a CompletionSuit");
    }
  };

}


#endif
