/***********************************************************************************************
Copyright (c) 2013, Martin Suda
Max-Planck-Institut für Informatik, Saarbrücken, Germany

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "Translate.h"

#include "bb.h"
#include "output.h"

#include "Common.h"

#include <sstream>
#include <string>
#include <cassert>

using namespace std;

static int encodeActions(bool print, FILE* outfile) {
  int numcl = 0;
  int actvar = gnum_relevant_facts+1;

  for (Action* a = gactions; a; a = a->next) { 
    // preconds    
    for (int i = 0; i < numPreconds(a); i++) {
      if (print) {
        fprintf(outfile,"%d %d 0\n",-actvar,getPrecond(a,i)+1);
      }
      numcl++;
    }
    // adds       
    for (int i = 0; i < numAdds(a); i++) {
      if (print) {
        fprintf(outfile,"%d %d 0\n",-actvar,(gnum_relevant_facts+gnum_actions+getAdd(a,i)+1));
      }
      numcl++;
    }
    // dels
    for (int i = 0; i < numDels(a); i++) {
      if (print) {
        fprintf(outfile,"%d %d 0\n",-actvar,-(gnum_relevant_facts+gnum_actions+getDel(a,i)+1));
      }
      numcl++;
    }
    actvar++;
  }      
  
  return numcl;
}

static bool actionPreservesFact(Action* a, int fact) {
  for (int i = 0; i < numAdds(a); i++)
    if (getAdd(a,i) == fact)
      return false;
      
  for (int i = 0; i < numDels(a); i++)
    if (getDel(a,i) == fact)
      return false;
      
  return true;
}

static int sequentialEncoding(bool print, FILE* outfile) {  
  int numcl = 0;  
  int actvar;
  
  // at least one
  if (print) {
    actvar = gnum_relevant_facts+1;
    for (int i = 0; i < gnum_actions; i++)
      fprintf(outfile,"%d ",actvar++);
    fprintf(outfile,"0\n");        
  }
  numcl++;

  // precond and effect
  numcl += encodeActions(print,outfile);
  
  // classical frame   
  actvar = gnum_relevant_facts+1;
  for (Action* a = gactions; a; a = a->next) {          
    for (int i = 0; i < gnum_relevant_facts; i++)
      if (actionPreservesFact(a,i)) {
        if (print) {
          fprintf(outfile,"%d %d %d 0\n",-actvar,-(i+1),(gnum_relevant_facts+gnum_actions+i+1));
          fprintf(outfile,"%d %d %d 0\n",-actvar,(i+1),-(gnum_relevant_facts+gnum_actions+i+1));
        }
        numcl += 2;
      }    
    actvar++;
  }
  
  return numcl;
}

static bool actionDeletesPreOrAdd(Action *a, Action *b) {
  for (int i = 0; i < numDels(a); i++) {
    for (int j = 0; j < numPreconds(b); j++)
      if (getDel(a,i) == getPrecond(b,j))
        return true;
  
    for (int j = 0; j < numAdds(b); j++)
      if (getDel(a,i) == getAdd(b,j))
        return true;
  }
     
  return false;
}

static int parallelEncoding(bool print, FILE* outfile) {
  int numcl = 0;
   
  // at most one (mutex)
  int actvara = gnum_relevant_facts+1;
  for (Action* a = gactions; a; a = a->next) {
    int actvarb = actvara+1;
    for (Action* b = a->next; b; b = b->next) {
      if (actionDeletesPreOrAdd(a,b) || actionDeletesPreOrAdd(b,a)) {
        if (print)
          fprintf(outfile,"%d %d 0\n",-actvara,-actvarb);        
        numcl++;
      }
      actvarb++;
    }    
    actvara++;
  }
    
  // precond and effect
  numcl += encodeActions(print,outfile);

  // explanatory frame
  for (int i = 0; i < gnum_relevant_facts; i++) {
    if (print) {
      int actvar;
      // added
      fprintf(outfile,"%d %d ",(i+1),-(gnum_relevant_facts+gnum_actions+i+1));
      actvar = gnum_relevant_facts+1;
      for (Action* a = gactions; a; a = a->next) {
        for (int j = 0; j < numAdds(a); j++)
          if (getAdd(a,j) == i) {
            fprintf(outfile,"%d ",actvar);
            break;
          }
            
        actvar++;
      }
      fprintf(outfile,"0\n");
      
      // deleted
      fprintf(outfile,"%d %d ",-(i+1),(gnum_relevant_facts+gnum_actions+i+1));
      actvar = gnum_relevant_facts+1;
      for (Action* a = gactions; a; a = a->next) {
        for (int j = 0; j < numDels(a); j++)
          if (getDel(a,j) == i) {
            fprintf(outfile,"%d ",actvar);
            break;
          }            
        actvar++;
      }
      fprintf(outfile,"0\n");    
    }
    numcl += 2;
  }
   
  return numcl;
}

void translate_Translate(FILE* outfile, BoolState& start_state, Clause& target_condition) {
  int varidx = 0;

  for (; varidx < gnum_relevant_facts; varidx++) {
    fprintf(outfile,"c FACT %d ",varidx+1);
    print_FactToFile(varidx,outfile);
    fprintf(outfile,"\n");
  }

  for (Action* a = gactions; a; a = a->next) { 
    fprintf(outfile,"c ACTION %d ", varidx++ +1);
    printAction(outfile,a);
  }    
  fprintf(outfile,"c START\n");

  // pass on a hint that it is sufficient to decide on the action variables, i.e. the state variables are implied and should not be explicitly decided upon
  fprintf(outfile,"c implied %d %d\n",1,gnum_relevant_facts+1);  // low value included, high value excluded
  
  // initial condition
  fprintf(outfile,"i cnf %d %d\n",gnum_relevant_facts+gnum_actions,gnum_relevant_facts);
  for (size_t i = 0; i < start_state.size(); i++)
    fprintf(outfile,"%d 0\n",start_state[i] ? (int)(i+1) : (int) -(i+1));   
  
  // goal condition
  fprintf(outfile,"g cnf %d %zu\n",gnum_relevant_facts+gnum_actions,target_condition.size());
  for (size_t i = 0; i < target_condition.size(); i++)
    fprintf(outfile,"%zu 0\n",target_condition[i]+1);
  
  if (gcmd_line.just_translate == 1) {
    int numcl = sequentialEncoding(false,0);
    fprintf(outfile,"t cnf %d %d\n",2*(gnum_relevant_facts+gnum_actions),numcl);
    sequentialEncoding(true,outfile);
  } else {
    int numcl = parallelEncoding(false,0);
    fprintf(outfile,"t cnf %d %d\n",2*(gnum_relevant_facts+gnum_actions),numcl);
    parallelEncoding(true,outfile);
  }
  
  if (gcmd_line.gen_invariant) {
    // do the forward invariant even in forward dir (backward invariant is useless for planning benchmarks)
    bool extra_flip; 
    if ((extra_flip = !gcmd_line.reverse)) {// assiment intended!
      gcmd_line.reverse = 1; // will force forward invariant computation 

      // hack the (already above properly used) target condition to the clauses false in the initial state
      target_condition.clear();
      for (size_t i = 0; i < start_state.size(); i++ ) 
        if (!start_state[i])
          target_condition.push_back(i);      
    }
   
    invariant_Init(target_condition);
    
    fprintf(outfile,"u cnf %d %zu\n",gnum_relevant_facts+gnum_actions,invariant_Size());
    
    const char* maybe_minus = extra_flip ? "-" : "";
    
    while (invariant_CurrentValid()) {
      BinClause& bcl = invariant_Current();
                    
      if (bcl.l1 == bcl.l2)
        fprintf(outfile,"%s%d 0\n",maybe_minus,bcl.l1+1);
      else 
        fprintf(outfile,"%s%d %s%d 0\n",maybe_minus,bcl.l1+1,maybe_minus,bcl.l2+1);
        
      invariant_Next();
    }
    invariant_Done();
  }
}

void translate_DumpGrounded(BoolState& start_state, Clause& target_condition) {
  FILE* out_file;
          
  // the domain file    
  {
    stringstream filename;
    filename << "operator" << gcmd_line.just_dumpgrounded << ".pddl";
    out_file = fopen(filename.str().c_str(),"w");
  }
  fprintf(out_file,"(define (domain %s-GND)\n",gdomain_name);
  fprintf(out_file,"(:predicates\n");
  
  fprintf(out_file,"\t(dummy)\n"); // to prevent the initial state from being empty
  
  for (int i = 0; i < gnum_relevant_facts; i++) {
    fprintf(out_file,"\t");
    print_GroundedFactToFile(i,out_file);
    fprintf(out_file,"\n");
  }
  fprintf(out_file,")\n");    

  for (Action* a = gactions; a; a = a->next) {
    fprintf(out_file,"(:action ");
    printGroundedAction(out_file,a);
    
    if (numPreconds(a) > 0) {      
      fprintf(out_file,"\t:precondition (and ");
      for (int i = 0; i < numPreconds(a); i++) {
        print_GroundedFactToFile(getPrecond(a,i),out_file);
        fprintf(out_file," ");
      }       
      fprintf(out_file,")\n");
    }
    
    if (numAdds(a) + numDels(a) > 0) {
      fprintf(out_file,"\t:effect (and ");
      for (int i = 0; i < numAdds(a); i++) {
        print_GroundedFactToFile(getAdd(a,i),out_file);
        fprintf(out_file," ");
      }
      for (int i = 0; i < numDels(a); i++) {
        fprintf(out_file,"(not ");
        print_GroundedFactToFile(getDel(a,i),out_file);
        fprintf(out_file,") ");
      }
      fprintf(out_file,")\n");
    }
    
    fprintf(out_file,")\n");
  }

  fprintf(out_file,")\n");
  fclose(out_file);

  // the problem file
  {
    stringstream filename;
    filename << "facts" << gcmd_line.just_dumpgrounded << ".pddl";
    out_file = fopen(filename.str().c_str(),"w");
  }    
  fprintf(out_file,"(define (problem %s-GND)\n",gproblem_name);
  fprintf(out_file,"(:domain %s-GND)\n",gdomain_name);

  fprintf(out_file,"(:init\n");
  
  fprintf(out_file,"\t(dummy)\n"); // to prevent the initial state from being empty
  
  for (size_t i = 0; i < start_state.size(); i++) {      
    if (start_state[i]) {    
      fprintf(out_file,"\t");
      print_GroundedFactToFile(i,out_file);
      fprintf(out_file,"\n");
    }
  }
  fprintf(out_file,")\n");   
  
  fprintf(out_file,"(:goal (and\n");  
  for (size_t i = 0; i < target_condition.size(); i++) {           
    fprintf(out_file,"\t");
    print_GroundedFactToFile(target_condition[i],out_file);
    fprintf(out_file,"\n");      
  }
  fprintf(out_file,"))\n");

  fprintf(out_file,")\n");            
  fclose(out_file);
}