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

#include "bb.h"
#include "output.h"

#include "Common.h"
#include "Translate.h"
#include "Invariant.h"

#include <unistd.h>

#include <cassert>
#include <signal.h>

#include <cstring>
#include <climits>
#include <cerrno>

#include <list>
#include <algorithm>
#include <string>

using namespace std;

/* refcounted wrapper for storing layer clauses */
struct ClauseBox {
  Clause data;
  
  size_t refcnt;
  size_t from, to;
  
  ClauseBox(Clause const& cl, size_t f) : data(cl), refcnt(0), from(f), to(f) {}
  
  ClauseBox* inc() { refcnt++; return this; }
  void dec() { if (!(--refcnt)) delete this;}
  
  bool validAt(size_t idx) {
    return (from >= idx && idx >= to);
  }
  
  void kickedFrom(size_t idx) {
    to = idx+1;
  }
  
  void extendedTo(size_t idx) {
    from = idx;
  }  
};

typedef vector<ClauseBox*> Clauses;

static void pruneInvalid(Clauses &layer, size_t layer_idx) {
  size_t j = 0;
  for (size_t i = 0; i < layer.size(); i++)
    if (layer[i]->validAt(layer_idx))
      layer[j++] = layer[i];
    else {
      // printf("Clause no longer valid in layer %zu: ",layer_idx); printClauseNice(layer[i]->data);                
      layer[i]->dec();
    }
  layer.resize(j);    
}

struct Obligation {
  size_t depth;
  BoolState state;
    
  Obligation* parent;
  Action *action;
  
  Obligation(Obligation* p, Action* a) : parent(p), action(a) {}
};

typedef list<Obligation*> Obligations;

// Helper class to store more than one clause in a continuous vector
// it works like a "stream" where we always record the clause's size and then its literals
struct ClauseBuffer {
  vector<size_t> clauses;  
  size_t num_clauses;
  Action* action;
  
  ClauseBuffer() : num_clauses(0) {}  
  
  void clear() {  
    num_clauses = 0;
    clauses.clear();
  }
};

// Helper class to store more than one binary (or unary) clause in a continuous vector
struct BinClauseBuffer {   
  void pushClause(Clause& cl) {
    assert(cl.size());
    assert(cl.size() <= 2);
    if (cl.size() == 1) {
      data.push_back(cl[0]);
      data.push_back(cl[0]);
    } else {
      data.push_back(cl[0]);
      data.push_back(cl[1]);
    }         
  }
  
  void pushClause(BinClause& cl) {
    data.push_back(cl.l1);
    data.push_back(cl.l2);
  }
  
  void loadClause(size_t idx, Clause& cl) {
    idx *= 2;
    assert(idx < data.size());
    cl.clear();
    cl.push_back(data[idx]);
    if (data[idx] != data[idx+1])
      cl.push_back(data[idx+1]);  
  }

  size_t size() {
    return data.size() >> 1;
  }
  
  void swap(BinClauseBuffer& other) {
    data.swap(other.data);
  }
  
  void reserve(size_t sz) {
    data.reserve(sz << 1);
  }
  
  void clear() {
    data.clear();
  }
  
  void swapClauses(size_t idx1, size_t idx2) {
    // printf("idx1 = %zu, idx2 = %zu, size = %zu\n",idx1,idx2,data.size());
  
    idx1 *= 2;
    assert(idx1 < data.size());
    idx2 *= 2;
    assert(idx2 < data.size());
    
    size_t tmp;
    
    tmp = data[idx1];
    data[idx1] = data[idx2];
    data[idx2] = tmp;
    
    tmp = data[idx1+1];
    data[idx1+1] = data[idx2+1];
    data[idx2+1] = tmp;    
  }
  
  void killByLast(size_t idx) {
    idx *= 2;
    assert(idx < data.size());
    
    swapClauses((idx >> 1),(data.size() >> 1) -1);
    data.resize(data.size()-2);          
  }
  
  private:
  vector<size_t> data;
  //stores (data.size() / 2) many binary (or unary) clauses
  //unary clauses are represented by repeating the same literal twice   
};


struct SolvingContext {
  size_t phase;

  size_t sigsize;
  BoolState start_state;
  
  // intialized only when (gcmd_line.minimize > 1)
  BoolState goal_lits;   // true if the lit should be true in the goal state; used for efficient inductive minimization
  
  BinClauseBuffer invariant;  
  
  // clause sitting primarily here:
  vector< Clauses > layers_delta;     // size == phase+1, i.e. phase is a valid index into the last layer  
  // clauses coming here from weaker layers:
  // REMARK: clauses in layers_deriv could have been invalidated externally - any traversal should check for that
  vector< Clauses > layers_deriv;     // size == phase+1, i.e. phase is a valid index into the last layer  
  
  vector< Obligations > obligations;  // size == phase
  Obligations obl_grave;
  
  // statistics
  size_t oblig_processed;  
  size_t oblig_sat;  
  size_t oblig_side;
  size_t oblig_unsat;
  size_t oblig_subsumed;  
  size_t oblig_killed;
  
  size_t cla_derived;
  size_t cla_second;
  size_t cla_subsumed;
  size_t cla_pushed;
  
  size_t minim_attempted;
  size_t minim_litkilled;
  
  float time_extend_sat;
  float time_extend_uns;
  float time_pushing;
  float time_postprocessing;
  
  size_t path_min_layer;       // this one is for statistics
  size_t least_affected_layer; // this one is for speeding up clause propagation (otherwise more or less the same!)
  
  SolvingContext() : phase(0), sigsize(0),
                     oblig_processed(0), oblig_sat(0), oblig_side(0), oblig_unsat(0), oblig_subsumed(0), oblig_killed(0),
                     cla_derived(0), cla_second(0), cla_subsumed(0), cla_pushed(0),
                     minim_attempted(0), minim_litkilled(0),
                     time_extend_sat(0.0), time_extend_uns(0.0), time_pushing(0.0), time_postprocessing(0.0),
                     path_min_layer(1),
                     least_affected_layer(1)
  {
  
  }
  
  ~SolvingContext() {    
    printGOStat(); 
  
    // clauses
    for (size_t i = 0; i < layers_delta.size(); i++) {
      for (size_t j = 0; j < layers_delta[i].size(); j++)
        layers_delta[i][j]->dec();
      for (size_t j = 0; j < layers_deriv[i].size(); j++)
        layers_deriv[i][j]->dec();        
    }
        
    // obligations
    for (size_t i = 0; i < obligations.size(); i++)
      for (Obligations::iterator j = obligations[i].begin(); j != obligations[i].end(); ++j)           
        delete *j;
        
    // and the grave
    for (Obligations::iterator j = obl_grave.begin(); j != obl_grave.end(); ++j)           
      delete *j;    
  }
  
  void printStat(bool between_phases = true) {             
    // Obligations
    {
      printf("\nObligations:\n");
      printf("\t%zu processed,\n",oblig_processed);      
      printf("\t%zu extended,\n",oblig_sat);
      printf("\t%zu sidestepped,\n",oblig_side);  
      printf("\t%zu blocked,\n",oblig_unsat);
      if (gcmd_line.obl_subsumption == 2)
        printf("\t%zu subsumed (%zu extra killed).\n",oblig_subsumed,oblig_killed);      
      else
        printf("\t%zu subsumed.\n",oblig_subsumed);      
      if (gcmd_line.obl_survive == 2 || gcmd_line.obl_subsumption == 2)
        printf("\n\t%zu obligations in the grave.\n",obl_grave.size());
            
      // The following are reset after the timing report:
      // oblig_processed = 0;
      // oblig_sat = 0;      
      // oblig_side = 0;
      // oblig_unsat = 0;           
      
      oblig_subsumed = 0;
      oblig_killed = 0;
    }   
    
    // Clauses
    {
      size_t cla_kept = 0;
      size_t cla_lensum = 0;
      
      for (size_t i = 1; i < layers_delta.size(); i++) 
        for (size_t j = 0; j < layers_delta[i].size(); j++) {
          cla_kept++;
          cla_lensum += layers_delta[i][j]->data.size();
        }
          
      printf("\nClauses:\n");      
      printf("\t%zu derived,\n",cla_derived);
      printf("\t%zu subsumed,\n",cla_subsumed);
      printf("\t%zu pushed,\n",cla_pushed);      
      printf("\t%zu kept (average size %f lits ).\n",cla_kept,cla_lensum*(1.0/cla_kept));

      cla_derived = 0;
      cla_second = 0;
      cla_subsumed = 0;
      cla_pushed = 0;
    }
            
    // Minimization (if applicable)
    if (gcmd_line.minimize) {
      printf("\nMinimization success rate: %f lits per attempt.\n",minim_litkilled*(1.0/minim_attempted));
      minim_attempted = 0;
      minim_litkilled = 0;                        
    }
    
    // Model if (between_phases)    
    
    // Layer
    {  
      printf("\nLayers: ");      
      assert(layers_delta.size() == layers_deriv.size());
      for (size_t i = 0; i < layers_delta.size(); i++) {            
        size_t layer_lensum = 0;
        for (size_t j = 0; j < layers_delta[i].size(); j++)          
          layer_lensum += layers_delta[i][j]->data.size();          
        
        pruneInvalid(layers_deriv[i],i);
        printf("%zu+%zu",layers_delta[i].size(),layers_deriv[i].size());        
                                  
        if (layers_delta[i].size())
          printf(" s%zu",layer_lensum/layers_delta[i].size());          
        else 
          printf(" s-");          
        
        if (i < layers_delta.size()-1)
          printf(" | ");
        else
          printf("\n");        
      }        
    }
        
    // Timing
    {
      printf("\nTiming:\n");
      printf("\t%fs spent extending (%f calls per second),\n",time_extend_sat+time_extend_uns,oblig_processed/(time_extend_sat+time_extend_uns));
      printf("\t%fs SAT (%f calls per second),\n",time_extend_sat,(oblig_sat+oblig_side)/time_extend_sat);
      printf("\t%fs UNS (%f calls per second),\n",time_extend_uns,oblig_unsat/time_extend_uns);
      printf("\t%fs spent pushing.\n",time_pushing);
      if (gcmd_line.postprocess && !between_phases) 
        printf("\t%fs spent postprocessing the plan.\n",time_postprocessing);                
                   
      time_extend_sat = 0.0;
      time_extend_uns = 0.0;
      time_pushing = 0.0;
      oblig_processed = 0;      
      oblig_sat = 0;  
      oblig_side = 0;
      oblig_unsat = 0;           
    }

    printf("\n"); fflush(stdout);        
  }
  
  void printLayers() {
    for (size_t i = 0; i < layers_delta.size(); i++) {            
      printf("Layer %zu:\n",i);
      for (size_t j = 0; j < layers_delta[i].size(); j++)          
        printClauseNice(layers_delta[i][j]->data);
    } 
  }
  
  void printGOStat() {
    /*
    printLayers();
    */
    /*
    for (size_t i = 0; i < layers_delta.size(); i++) {
      printf("Layer %zu:\n",i);
      for (size_t j = 0; j < layers_delta[i].size(); j++)          
        printClauseNice(layers_delta[i][j]->data);
    
      if (i > 0)
        for (size_t j = 0; j < layers_delta[i].size(); j++) {
          bool found = false;
          for (size_t k = 0; k < layers_delta[i-1].size(); k++) 
            if (subsumes(layers_delta[i-1][k]->data,layers_delta[i][j]->data)) {
              found = true;
              break;
            }
          if (!found) {        
            printf("In layer %zu, following clause not subsumed in prev layer: ",i); printClauseNice(layers_delta[i][j]->data);
          }
        }        
    }  
    */
    
    if (phase > 0) {
      printf("\nGame over during phase %zu\n",phase);      
      printStat(false);
    }
    
    { // Global timing 
      times( &gend );
      printf("\nPDR took: %7.2f seconds overall.\n\n",( float ) ( ( gend.tms_utime - gstart.tms_utime + gend.tms_stime - gstart.tms_stime  ) / 100.0 ));                           
    }    
  }   
  
  void randomPermutation(vector<size_t> & vec, size_t size) {
    vec.clear();
    for (size_t i = 0; i < size; i++)
      vec.push_back(i);
               
    for (size_t i = size-1; i > 0; i--) {
      size_t idx = rand() % (i+1);
      size_t tmp = vec[idx];
      vec[idx] = vec[i];
      vec[i] = tmp;                   
    } 
  }   
  
  bool isLayerState(size_t layer_idx, BoolState const& state) {
    for (size_t i = 0; i < layers_delta[layer_idx].size(); i++)
      if (clauseUnsatisfied(layers_delta[layer_idx][i]->data,state))
        return false;
        
    // is this neccessary?
    for (size_t i = 0; i < layers_deriv[layer_idx].size(); i++)
      if (clauseUnsatisfied(layers_deriv[layer_idx][i]->data,state))
        return false;
    
    return true;
  }
  
  // extend temporaries:
  vector<Action *>     actions; // actions dumped into vector for random access
  
  size_t      used_buffer_size;
  vector<ClauseBuffer> buffers; // for every interesting action a list (in a form of a buffer) of potential contributions to the final clause
  
  vector< vector<size_t> > action_ords; //action order separately for each layer_idx
  
  vector<size_t>   buffer_ord;  // indices to traverse buffers in specific order
  
  BoolState false_precond_lits; // false preconditions of the current action
  BoolState      working_state; // the currently considered potential next state
  
  vector<size_t>       lit_ord; // for traversing literals of the output clause in a specific order
  Clause            inv_clause; // temporary storage for current invariant clause
  
  vector<size_t> false_clauses; // indices to layers_delta[layer_idx] pointing to clauses unsat in state
  
  // extend output:  
  Action*           extend_action_out;
    
  Clause            extend_clause_out;  // may return more than one   
  
  vector<int>       reason_histogram;
  static const size_t  histogram_size = 10; 
  
  struct CompareBufferSizes {
    vector<ClauseBuffer> & buffers;
    bool operator() (size_t i,size_t j) { return (buffers[i].num_clauses < buffers[j].num_clauses); }
    CompareBufferSizes(vector<ClauseBuffer> & buffs) : buffers(buffs) {}
  };   
  
  struct CompareActionScores {
    vector<Action *> & actions;
    bool operator() (size_t i,size_t j) { return (actions[i]->score < actions[j]->score); }
    CompareActionScores(vector<Action *> & acts) : actions(acts) {}
  };
  
  char extend(size_t layer_idx, BoolState const & state, bool pushTest, bool chat = false) {           
    // will be set to a non-null action before returning result > 0  
    extend_action_out = NULL;
            
    //printf("Extend into %zu:\n",layer_idx);
    //printState(state);    
    
    /*
     false clauses are those which the current state doesn't satisfy
     it is typically much smaller set than the whole layers_delta[layer_idx]
     
     it pays off to focus on false clauses first
     > for the positive case, we only look at the other clauses (which the action could have made false due to a delete effect)
       when the action looks plausible (all precondintions are true in current and all false_clauses true in the successor)
     > for the negative case (if the default quickreason is on) only plausible actions seek reasons
       among the other clauses
       
     the "side" trick (the default resched = 2) returns an action as if it was a proper successor if it satisfies some false_clauses and does not undo validity any other clause
    */
    false_clauses.clear();
    for (size_t i = 0; i < layers_delta[layer_idx].size(); i++)
      if (clauseUnsatisfied(layers_delta[layer_idx][i]->data,state)) {
        // printf("False clause %zu: ",false_clauses.size()); printClauseNice(layers_delta[layer_idx][i]->data);
        false_clauses.push_back(i);
      }
    
    // printf("Extending state into %zu; number of false clauses %zu\n",layer_idx,false_clauses.size());    
    // printf("The state:\n"); printStateHash(state);
    
    assert(false_clauses.size() > 0); // there is always a false clause, otherwise <state> could already sit in layer_idx-th layer
    // moreover, there is never a false clause from layers_deriv nor in invariant (that has been already checked "above")
    
    // for implementing "side"
    Action *best_action = 0;
    int best_false_after = (int)false_clauses.size(); // must improve to qualify    
    
    // records preconditions of the current action 
    // used to skip reasons from false clauses "subsumed" by a failed precond reason
    // at the same time such a clause is still considerd false with respect to "side" and its counting
    false_precond_lits.clear();
    false_precond_lits.resize(state.size(),false);    
    
    // for recording reasons of "interesting" actions
    // interesting action is an action the reason set of which is not "SUBSUMED" by the reason set of NOOP (e.g. it must make at least one false_clase true)
    // we don't need to record reasons of non-interesting actions (this tends to speedup subsequent overall-reason computation and minimization)
    used_buffer_size = 0;
    
    assert(layer_idx < action_ords.size());    
    vector<size_t> & actions_ord = action_ords[layer_idx];    

    for (size_t act_idx = 0; act_idx < actions_ord.size(); act_idx++) {
      size_t action_idx = actions_ord[act_idx];
      Action *a = actions[action_idx];
      
      bool plausible = true;         // as far as we see it, it could be applied and would yield a good successor (satisfying all the clauses it should)
      bool interesting = false;      // satisfies at least one false clause -> keep the reason set for it
      a->interesting = 0;
      
      // for "side"
      bool failed_precond = false;   // know explicitly whether a side condition failed
      int false_after = 0;           // count the number of false_clauses false in the successor      
      bool can_do_side;              
      bool just_because_side;        
      
      // give me a buffer for the current action
      ClauseBuffer & buffer = buffers[used_buffer_size++];
      buffer.clear();
      buffer.action = a;

      // printf("--- Trying action %zu:",act_idx); printAction(stdout,a);      
      
      // start preparing the successor state
      working_state.clear();
      for (size_t i = 0; i < state.size(); i++)
        working_state.push_back(state[i]);      
            
      // adding 
      bool useless = true;
      for (int i = 0; i < numAdds(a); i++) {
        int add = getAdd(a,i);
        working_state[add] = true;
        
        if (!state[add])
          useless = false;
      }
      
      // useless action cannot help reaching the goal from here
      if (useless) {
        used_buffer_size--; // the current buffer will get overwritten in the next round         
        a->score = INT_MAX; // syst2 had "(int)false_clauses.size();" here instead (not to discriminate the "here useless" too much), but it wasn't that successful
        continue;
      }
                  
      // test preconditions
      size_t failed_preconds = 0;
      for (int i = 0; i < numPreconds(a); i++) {
        int precond = getPrecond(a,i);
        if (!state[precond]) {
          
          //printf("Failed precond: ");
          //print_ft_name(precond); 
          //printf("\n");          
        
          if (pushTest)
            goto next_action_1;
            
          plausible = false;
          failed_precond = true;
          
          // record the reason
          buffer.num_clauses++;
          buffer.clauses.push_back(1);
          buffer.clauses.push_back(precond);
                              
          failed_preconds++;
          
          false_precond_lits[precond] = true;
        }
      }
      // if (chat) printf("%zuF  ",failed_preconds);
                           
      // deleting
      for (int i = 0; i < numDels(a); i++) {
        int del = getDel(a,i);
        working_state[del] = false;
      }                 
      
      { // first check the false clauses
        size_t failed_cnt = 0;
      
        for (size_t i = 0; i < false_clauses.size(); i++) {
          Clause &cl = layers_delta[layer_idx][false_clauses[i]]->data;
          
          if (!clauseUnsatisfied(cl,working_state))
            continue;
          
          failed_cnt++;
 
          //printf("Failed false clause %zu\n",i);
          if (pushTest)
            goto next_action_1;
 
          if (!clauseUnsatisfied(cl,false_precond_lits)) { // a better reason has been recorded already
            assert(!plausible);
            continue;
          }
          
          // we have a false clause 
          plausible = false;          
          false_after++;
          
          // all literals get recorded          
          buffer.num_clauses++;                      
          buffer.clauses.push_back(cl.size());  
          for (size_t j = 0; j < cl.size(); j++)
            buffer.clauses.push_back(cl[j]);        
        }

        if (failed_cnt < false_clauses.size()) {          
          interesting = true;
          a->interesting = 1;
          //printf("Interesting action: "); printAction(stdout,a);
        } else {
          used_buffer_size--; // the current buffer will get overwritten in the next round (the reasons are boring; effectively subsumed by those of NOOP)                    
        }
      }
      
      if (plausible)
        a->score = INT_MAX; // if we ever get to use the score, it will mean this action breaks something below and so can never be used successfully in this context
      else
        a->score = (int)buffer.num_clauses;
           
      can_do_side = (gcmd_line.resched == 2) && !failed_precond && (false_after < best_false_after);
      just_because_side = false;            
            
      if ( plausible ||                                         // normally, only if the action still seems ok, we perform the full test
          (gcmd_line.quick_reason == 0) ||                      // unless we don't want the quickreason trick (seems to harm on UNSAT problems)
          (interesting && gcmd_line.quick_reason == 2) ||       // something in the middle (experimental)
          (just_because_side = true, can_do_side) ) {           // or if we still need to check whether "side" is an option ...
          
        pruneInvalid(layers_deriv[layer_idx],layer_idx);
        
        size_t layers_delta_size = layers_delta[layer_idx].size();
        size_t layers_deriv_size = layers_deriv[layer_idx].size();
        size_t invariant_size    = invariant.size();
        size_t false_clause_idx  = 0;
                       
        for (size_t i = 0; i < layers_delta_size + layers_deriv_size + invariant_size; i++) {
          // bool in_delta = false;
          // bool in_deriv = false;
          // bool in_inv   = false;
        
          Clause* p_cl;
          if (i < layers_delta_size) {
            // TODO: testing whether the test shouldn't be rather skipped
            if (false_clause_idx < false_clauses.size() && i == false_clauses[false_clause_idx]) {
              false_clause_idx++;
              continue; // we had this one already
            }
            p_cl = &layers_delta[layer_idx][i]->data;
            // in_delta = true;
          } else if (i - layers_delta_size < layers_deriv_size) {
            p_cl = &layers_deriv[layer_idx][i-layers_delta_size]->data;
            // in_deriv = true;
          } else {
            invariant.loadClause(i - layers_delta_size - layers_deriv_size,inv_clause);
            p_cl = &inv_clause;
            // in_inv = true;
          }
          Clause &cl = *p_cl;

          if (!clauseUnsatisfied(cl,working_state))
            continue; // next clause
          
          can_do_side = false;
          if (just_because_side)
            break;
     
          //printf("Failed clause: "); printClauseNice(cl);
          if (pushTest)
            goto next_action_1;

          if (!clauseUnsatisfied(cl,false_precond_lits)) { // a better reason has been recorded already
            assert(!plausible);
            continue;
          }
          
          // we have a false clause 
          plausible = false;
          
          // all preserved negative literals get recorded
          {
            buffer.num_clauses++;
            size_t new_cl_size = 0;
            size_t new_cl_idx = buffer.clauses.size();
            buffer.clauses.push_back(0);  // will update when we know the real size
            for (size_t j = 0; j < cl.size(); j++)
              if (!state[cl[j]]) { // was already false, so was preserved; the others were deleted explicitly so cannot be part of the reason clause
                new_cl_size++;
                buffer.clauses.push_back(cl[j]);
                
                //print_ft_name(cl[j]); printf(" ");
              }
            buffer.clauses[new_cl_idx] = new_cl_size; 
          }

          //printf("\n");                   
        }
        
        //if (chat) printf(" R: %zu\n",buffer.num_clauses);
      }   
      
      // all clauses sat in new state
      if (plausible) {
        // printf("SAT\n"); 
      
        if (pushTest)
          return 1;
      
        // there is a room for heuristics when picking just one next state        
        // printf("Succesfully going forward!\n");      
        extend_action_out = a;
        
        // syst3: bring the successful action to front
        for (size_t i = act_idx; i > 0; i--)
          actions_ord[i] = actions_ord[i-1];
        actions_ord[0] = action_idx;         
              
        // printAction(stdout,extend_action_out);
        return 1;
      }
                  
      if (can_do_side &&
         isLayerState(layer_idx+1,working_state)) { /* since layers_deriv are sumbsumption reduced, 
                                                    there is still a risk the successors does not satisfy all the layer clauses of its parent */                             
        // printf("Improved best to %d with state:\n",false_after);
        // printStateHash(working_state);      
      
        best_false_after = false_after;
        best_action = a;
      }
      
      next_action_1: 
      // cleanup for the action
      for (int i = 0; i < numPreconds(a); i++) 
        false_precond_lits[getPrecond(a,i)] = false;            
    }
    
    // all actions checked here !!!         
    if (pushTest)
      return 0;      
    
    // finishing the "side" trick
    if (gcmd_line.resched == 2 && best_action != 0) {      
      extend_action_out = best_action;
      // printf("SIDE (%d)\n",best_false_after);
      // printAction(stdout,extend_action_out);
      return 2;
    }
    
    //printf("UNSAT\n");
    
    // the contribution from "no-op" = clauses from current layer false in the given state
    { 
      ClauseBuffer & buffer = buffers[used_buffer_size++];
      buffer.clear();
      buffer.action = NULL;
      
      for (size_t i = 0; i < false_clauses.size(); i++) {
        Clause &cl = layers_delta[layer_idx][false_clauses[i]]->data;
        buffer.num_clauses++;
        buffer.clauses.push_back(cl.size());
        for (size_t j = 0; j < cl.size(); j++)
          buffer.clauses.push_back(cl[j]);
      }
    }
    
    // update the order for next time
    stable_sort(actions_ord.begin(),actions_ord.end(),CompareActionScores(actions)); // low score is better
    
    /*
    printf("Uptaded actions_ord for idx %zu:\n",layer_idx);
    for (size_t act_idx = 0; act_idx < actions_ord.size(); act_idx++) {
      size_t action_idx = actions_ord[act_idx];
      Action *a = actions[action_idx];
      printf("Score: %d for ",a->score);
      printAction(stdout,a);
    }
    */
    
    // just for fun - histogram of the number of reasons per action
    /*
    {
      reason_histogram.clear();
      reason_histogram.resize(histogram_size,0);
      
      for (size_t i = 0; i < used_buffer_size; i++) {
        ClauseBuffer & buffer = buffers[i];
        assert(buffer.num_clauses > 0);    
        if (buffer.num_clauses <= histogram_size) {
          reason_histogram[buffer.num_clauses-1]++;
        }        
      }
      
      for (size_t i = 0; i < histogram_size; i++)
        printf("%3d, ",reason_histogram[i]);
      printf(" histogram for idx %zu\n",layer_idx);
    }
    */
    
    // prepare the conflict clause -- abusing the workingstate for that (to represent the union being built)
    working_state.clear();
    working_state.resize(sigsize,false);
    
    // resize buffer ord and sort it based on buffer sizes
    randomPermutation(buffer_ord,used_buffer_size);   // TODO: could skip the random and use identity permutation instead (no big deal, would it speed up?)
    sort(buffer_ord.begin(),buffer_ord.end(),CompareBufferSizes(buffers)); //start with small buffers            
    
    for (size_t act_idx = 0; act_idx < buffer_ord.size(); act_idx++) {
      ClauseBuffer & buffer = buffers[buffer_ord[act_idx]];      
      assert(buffer.num_clauses > 0);      
      
      /*
      printf("%zu contributions of action %zu: ",buffer.num_clauses,buffer_ord[act_idx]);
      if (buffer.action)
        printAction(stdout,buffer.action);
      else
        printf("(NOOP)\n");
      */
      
      size_t best_adds = sigsize+1;
      size_t best_idx = 0;
      
      size_t i = 0;
      size_t sz = 0;
      while (i < buffer.clauses.size()) {
        sz = buffer.clauses[i];
        
        size_t curbase = i;
        size_t curadds = 0;
        
        while (i++,sz--) {
          /*
          print_ft_name(buffer.clauses[i]);
          printf(" ");          
          */
          
          if (!working_state[buffer.clauses[i]])
            curadds++;
        }
        /*
        printf("\n");        
        */
        if (curadds < best_adds) {
          best_adds = curadds;
          best_idx = curbase;
        }        
        
        if (best_adds == 0) // no further improvement possible
          break;
      }
      
      assert(best_adds <= sigsize);
      // if (chat) printf("- best adds %zu\n",best_adds);
        
      // apply the best guy
      {
        i = best_idx;
        sz = buffer.clauses[i];
        while (i++,sz--)
          working_state[buffer.clauses[i]] = true;                                   
      }
    }
      
    /*
    if (chat) {
      size_t sz = 0;
      for (size_t i = 0; i < working_state.size(); i++)
        if (working_state[i])
          sz++;
      printf("Final size %zu\n",sz);
    }
    */
      
    /*
    printf("Derived clause ");
    printState(working_state);          
    */
    
    if (gcmd_line.minimize) {
      minim_attempted++;      
    
      // printf("Minimizing:\n");
      randomPermutation(lit_ord,sigsize); // TODO: could have better minimization heuristics (like avoiding the first action's reason first)
      
      int goal_lits_remaining = 0;
      if (gcmd_line.minimize > 1) {
        for (size_t i = 0; i < sigsize; i++)
          if (goal_lits[i] && working_state[i])
            goal_lits_remaining++;
      }
      
      bool removed_something;
      do {
        removed_something = false;
      
        for (size_t lit_idx = 0; lit_idx < sigsize; lit_idx++) {
          if (working_state[lit_ord[lit_idx]]) { // could remove this guy
            size_t saved = lit_ord[lit_idx];
            working_state[saved] = false;
            if (goal_lits[saved])
              goal_lits_remaining--;
            
            // check if we still "fit in" with the contributions
            for (size_t act_idx = 0; act_idx < buffer_ord.size(); act_idx++) {
              ClauseBuffer & buffer = buffers[buffer_ord[act_idx]];      
              size_t i = 0;
              size_t sz = 0;              
            
              if (goal_lits_remaining) {       // can apply the inductive argument
                assert(gcmd_line.minimize > 1);
                
                // can try the inductive reason first
                if (buffer.action) {
                  for (int i = 0; i < numAdds(buffer.action); i++) {
                    int add = getAdd(buffer.action,i);
                    if (working_state[add])
                      goto all_the_standard_reasons_to_try;
                  }
                } else { // the NOOP action itself is never a problem, but it represents all the non-interesting actions which need to be tried, and why not try them now?
                  for (Action* a = gactions; a; a = a->next) 
                    if (!a->interesting)
                      for (int i = 0; i < numAdds(a); i++) {
                        int add = getAdd(a,i);
                        if (working_state[add])
                          goto all_the_standard_reasons_to_try;
                      }
                }
                
                // either NOOP, which always succeds inductively, or the action cannot make our current clause true anyway
                goto next_action_2;
              }
              
              all_the_standard_reasons_to_try: ;              

              while (i < buffer.clauses.size()) {
                sz = buffer.clauses[i++];
                while (sz) {
                  if (!working_state[buffer.clauses[i]])
                    break;
                  i++, sz--;
                }
                if (sz)
                  i += sz;
                else
                  goto next_action_2; // the current is OK
              }
              
              /*
              printf("Kept "); print_ft_name(saved); printf(" also because of "); 
              if (buffer.action)
                printAction(stdout,buffer.action);
              else
                printf("(NOOP)\n");
              */
              
              // none of them is good enough - put the literal back
              working_state[saved] = true;
              if (goal_lits[saved])
                goal_lits_remaining++;
              goto next_literal;
              
              next_action_2: ;
            }
          
            // good riddance :)
            removed_something = true;
            minim_litkilled++;
          }
          
          next_literal: ;
        }
      } while (gcmd_line.minimize > 2 && removed_something);
            
      /*
      printf("Minimized to   ");
      printState(working_state);      
      */
      
      /*
      if (chat) {
        size_t sz = 0;
        for (size_t i = 0; i < working_state.size(); i++)
          if (working_state[i])
            sz++;
        printf("Minimized to %zu\n",sz);
      }
      */
    }      
        
    extend_clause_out.clear();
    for (size_t i = 0; i < working_state.size(); i++)
      if (working_state[i])
        extend_clause_out.push_back(i);    
    
    return 0;
  }
  
  bool pruneLayerByClause(Clause const & cl, Clauses& layer, size_t idx, bool testForWeak, ClauseBox*& same_clause) {    
    bool strong = true;    
    same_clause = 0;
    
    // what happens in the cycle:
    // 1. some clauses in layer may be invalid and should be deleted
    // 2. among the rest, some may get subsumed and deleted
    // 3. if the subsumed clause is equal to current, it is removed (but still alive) and returned as same_clause
    // 3. if testForWeak, cl itself can get subsumed
    // in any case we need to finish iterating to properly copy the rest of clauses and shrink the layer
        
    size_t j = 0;
    for (size_t i = 0; i < layer.size(); i++) {
      if (!layer[i]->validAt(idx)) {               
        layer[i]->dec();
        continue;
      }
      if (strong && !same_clause) {
        if (subsumes(cl,layer[i]->data)) {
          if (cl.size() == layer[i]->data.size()) {            
            //printf("same clause discovered in %zu\n",idx);
                      
            same_clause = layer[i];
          } else {
            //printf("subsumes clause in %zu: ",idx); printClauseNice(layer[i]->data);
          
            layer[i]->kickedFrom(idx);
            layer[i]->dec();
            cla_subsumed++;           
          }
          continue;       // removed from layer
          
        } else if (testForWeak && subsumes(layer[i]->data,cl))
          strong = false;
      }
      layer[j++] = layer[i]; //kept                       
    }
    layer.resize(j);
    return strong;
  }                     
    
  size_t insertClauseIntoLayers(Clause const & cl, size_t idx) {       
    // printf("inserting into layer %zu: ",idx); printClauseNice(cl);
    
    ClauseBox* clbox = 0;
    
    // first its own layer (without obl_subsumption the clause may be too weak already in its own layer)
    if (!pruneLayerByClause(cl,layers_delta[idx],idx,!gcmd_line.obl_subsumption,clbox)) {
      //printf("Subsumed in its own layer!\n");
      return 0;
    }
    if (clbox) {
      //printf("Already present in its own layer!\n");
      layers_delta[idx].push_back(clbox);
      return 0;    
    }
    if (!pruneLayerByClause(cl,layers_deriv[idx],idx,!gcmd_line.obl_subsumption,clbox)) {    
      // could this happen at all ?
      // printf("Expelled from its own layer!\n");
      return 0;
    }
    if (clbox) {
      // could this happen at all ?
      // printf("Already present behind its own layer!\n");
      layers_deriv[idx].push_back(clbox);
      return 0;
    }
                 
    assert(idx > 0);
    size_t i;
    for (i = idx-1; i > 0; i--) {
      if (!gcmd_line.cla_subsumption) // we just use the fact that i was set to idx-1
        break;
    
      if (!pruneLayerByClause(cl,layers_delta[i],i,true,clbox))
        break;
        
      if (layers_delta[i].size() == 0) {
        if (clbox) // was removed from layers_delta[i], but there was no dec() in pruneLayerByClause
          clbox->dec();
        return i;
      }
      
      if (clbox) {
        // printf("Already present in %zu\n",i);
        clbox->extendedTo(idx);
        layers_delta[idx].push_back(clbox->inc());
        layers_deriv[i].push_back(clbox); // no inc() here, there was no dec() in pruneLayerByClause either
        
        for (size_t j = idx-1; j > i; j--)
          layers_deriv[j].push_back(clbox->inc());
        
        return 0;
      }        
    }
    
    // printf("Too weak in %zu\n",i); //(including the case when i == 0, now)
        
    // creating box and putting where necessary
    clbox = new ClauseBox(cl,idx);
    clbox->to = i+1;
    layers_delta[idx].push_back(clbox->inc());    
    for (size_t j = idx-1; j > i; j--)
      layers_deriv[j].push_back(clbox->inc());
      
    return 0;
  }

  void processAndPrintSolution(FILE* outfile,Obligation* obl) {    
    vector< pair<Action*,size_t> > plan;    

    // extract the plan 
    while (obl->parent) {
      plan.push_back(make_pair(obl->action,0));
      obl = obl->parent;
    }
    reverse(plan.begin(), plan.end());
          
    if (gcmd_line.postprocess) { // Action Elimination (Nakhost & Mueller 2010)
      times(&start);
                  
      BoolState s = start_state, t;
      size_t i = 0;
      while (i < plan.size()) {
        plan[i].second = i+1; // mark a_i
        t = s;                // a_i skipped
        for (size_t j = i+1; j < plan.size(); j++ ) {
          if (actionApplicable(t,plan[j].first))
            applyActionEffects(t,plan[j].first);
          else
            plan[j].second = i+1; // mark a_j
        }
        
        if (isLayerState(0,t)) {  // goal satisfied         
          // remove marked
          size_t k = i;  // will be overwritten
          for (size_t j = i+1; j < plan.size(); j++) {
            if (plan[j].second != i+1) // unmarked stays
              plan[k++] = plan[j];
          }
          plan.resize(k);                                    
        } else {
          applyActionEffects(s,plan[i].first);
          i++;
        }
        
        // NOTICE: no action is marked by i+1 at this moment
      }      
      printf("Reduced to %zu actions.\n",plan.size());
      
      times(&end);
      TIME( time_postprocessing );
    }
    
    // printing
    int idx, delta;
    if (!gcmd_line.reverse) {
      idx = 0;
      delta = 1;
    } else {
      idx = plan.size()-1;
      delta = -1;
    }
    for (size_t i = 0; i < plan.size(); i++) {    
      fprintf(outfile,"%zu:   ",i);
      printAction(outfile,plan[idx].first);
      idx += delta;
    }
  }  
  
  bool processObligations() {
    assert(phase);
    
    assert(gcmd_line.resched < 2 || gcmd_line.oblig_prior_stack); 
    /* "side" is a bit weird. 
        We don't guarantee that a state will not generate the same side next time it is considered.
        This may lead to problems with "oblig_prior_queue" as exemplified on the WOODWORKING domain.
        
        Initial obligation A "sides" to give a better "B",
        then A is considered again and sides B again
        then B is considered and sides a better C,
        then we need to deal with A again
        then we need to deal with A again 
        ... 
       
        BLEE %)
    */
    
    size_t obl_top = phase-1;  
    for(;;) {      
      assert(obligations[0].size() <= 1 || gcmd_line.resched > 1); // The first stack is always trivial, unless we do sidestepping
    
      while (obl_top < phase && obligations[obl_top].size() == 0)
        obl_top++;
        
      if (obl_top == phase) {
        if (!gcmd_line.obl_survive) { 
          // free obligations and next phases starts from scratch
          while (!obligations[phase].empty()) {
            delete obligations[phase].back();
            obligations[phase].pop_back();
          }
        }
                         
        return false;
      }
      
      Obligation* obl;
      if (gcmd_line.oblig_prior_stack) {   // stack-wise handling of obligations favours long plans in a certain sense
        obl = obligations[obl_top].back();
        obligations[obl_top].pop_back();           
      } else {
        obl = obligations[obl_top].front();
        obligations[obl_top].pop_front();           
      }
      
      // printf("Handling obligation with depth %zu and state of size %zu\n",obl->depth,obl->state.size());
      oblig_processed++;
      
      if (obl_top < path_min_layer)
        path_min_layer = obl_top;
      
      if (obl_top+1 < least_affected_layer)
        least_affected_layer = obl_top+1;
        
      times(&start);
      
      char res;      
      if ((res = extend(obl_top,obl->state,false))) { 
        times(&end);
        TIME( time_extend_sat );
      
        if (res > 1) {
          oblig_side++;          
        } else {
          oblig_sat++;          
        }        
      
        // the parent goes back
        if (gcmd_line.obl_survive < 2) /* gcmd_line.obl_survive == 2 is incomplete! */
          obligations[obl_top].push_back(obl);
        else  
          obl_grave.push_back(obl);          
      
        // going forward     
        assert(extend_action_out != NULL);
        {
          Obligation* new_obl = new Obligation(obl,extend_action_out);
          new_obl->depth = obl->depth+1;
          new_obl->state = obl->state;
          applyActionEffects(new_obl->state,extend_action_out);
                    
          //printf("Extended by action "); printAction(stdout,extend_action_out);          
              
          if (res > 1) { // sidestep
            obligations[obl_top].push_back(new_obl);    
          } else {
            if (obl_top == 0) {
              printf("SAT: plan of length %zu found\n",new_obl->depth);
              
              string filename;
              filename += gcmd_line.path;
              filename += gcmd_line.fct_file_name;
              filename += ".soln";
                         
              FILE* outfile = fopen(filename.c_str(),"w");              
              if (!outfile)
                printf("%s\n",strerror(errno));              
              else {
                processAndPrintSolution(outfile,new_obl);
                fclose(outfile);
              }
              
              delete new_obl;         
              return true;
            }
          
            obligations[obl_top-1].push_back(new_obl);
          }        
        }
        
        if (res > 1) 
          ;
        else
          obl_top--; // going forward with the new guy(s)
             
      } else {
        oblig_unsat++;        
        
        times(&end);
        TIME( time_extend_uns );
      
        {
          cla_derived++;
          
          size_t empty_layer = insertClauseIntoLayers(extend_clause_out,obl_top+1);
          
          if (empty_layer) {
            if (gcmd_line.obl_survive < 2)
              printf("UNSAT: repetition detected!\nDelta-layer %zu emptied by subsumption!\n",empty_layer);
            else
              printf("UNRESOLVED: repetition detected under incompete setup!\nDelta-layer %zu emptied by subsumption!\n",empty_layer);
            delete obl;          
            return true;
          }            
        
          // obligation subsumption
          if (gcmd_line.obl_subsumption == 2 && obl_top+1 == phase) { // we put them to the grave when they go "off the rim"
            
            for (Obligations::iterator it = obligations[obl_top].begin(); it != obligations[obl_top].end(); ) {
              Obligation* tmp_obl = *it;
              if (clauseUnsatisfied(extend_clause_out,tmp_obl->state)) {
                it = obligations[obl_top].erase(it);
                obl_grave.push_back(tmp_obl); // cannot delete directly, they may by part of the future plan
                oblig_killed++;
              } else {
                ++it;
              }
            }
          } else if (gcmd_line.obl_subsumption) {
            for (Obligations::iterator it = obligations[obl_top].begin(); it != obligations[obl_top].end(); ) {
              Obligation* tmp_obl = *it;
              if (clauseUnsatisfied(extend_clause_out,tmp_obl->state)) {
                it = obligations[obl_top].erase(it);
                obligations[obl_top+1].push_back(tmp_obl);
                oblig_subsumed++;
              } else {
                ++it;
              }
            }
          }
        }
                   
        //rescheduling
        if (gcmd_line.resched)
          obligations[obl_top+1].push_back(obl);
        else 
          delete obl;
      }
    }  
  }
  
  BoolState pushState;
  
  bool clausePushing() {
    // printf("clausePushing\n");
    
    assert(layers_delta.size() == phase+2);     
    for (size_t idx = least_affected_layer; idx <= phase; idx++) {
      size_t j = 0;
      for (size_t i = 0; i < layers_delta[idx].size(); i++) {
        ClauseBox* clbox = layers_delta[idx][i];
        
        // TODO: swapping trick that always temporarily makes i-th clause the first one could speed up pushing (fast fail in extend for each stupid action)
        // yes, but since the_clause goes to false_clases anyway the only way to speed it up would be to force false_clase = { the_clause } (only true when clause subsumption is on)
        // the saving is then not per every action, but only once per call to extend - seems not to pay off
        
        pushState.clear();
        pushState.resize(sigsize,true);
        for (size_t n = 0; n < clbox->data.size(); n++)
          pushState[clbox->data[n]] = false;
        
        // printf("Trying clause from layer %zu: ",idx); printClauseNice(clbox->data);
        
        if (extend(idx,pushState,true)) { // SAT -> not pushed
          layers_delta[idx][j++] = clbox;
        } else {       
          // printf("Pushing clause from layer %zu: ",idx); printClauseNice(clbox->data);
          cla_pushed++;
          
          ClauseBox* dummy = 0; 
          
          bool res = pruneLayerByClause(clbox->data,layers_delta[idx+1],idx+1,false,dummy);          
          assert(res && !dummy);
          
          // TODO: why not prune in deriv as well? could it not be harmfull, to keep them there? Think:
          /*
          size_t before = cla_subsumed;          
          res = pruneLayerByClause(clbox->data,layers_deriv[idx+1],idx+1,false,dummy);          
          assert(res && !dummy);          
          if (cla_subsumed > before)
            printf("Subsumed in deriv!\n");
          */
          
          layers_deriv[idx].push_back(clbox); // inheriting the refcount point from layers_delta[idx] from where we remove it
          clbox->extendedTo(idx+1);
          layers_delta[idx+1].push_back(clbox->inc());

          // obl_subsumption is obligatory in pushing when obl_survive, otherwise we could later violate `false_clauses.size() > 0' in extend...
          assert(!gcmd_line.obl_survive || gcmd_line.obl_subsumption); 
                    
          if (gcmd_line.obl_subsumption) {            
            for (Obligations::iterator it = obligations[idx].begin(); it != obligations[idx].end(); ) {
              assert(idx == phase); // as we currently only call pushing between phases, only the obligations[phase] are possibly non-empty and that only in survive mode
              Obligation* tmp_obl = *it;
              if (clauseUnsatisfied(clbox->data,tmp_obl->state)) {
                it = obligations[idx].erase(it);
                obligations[idx+1].push_back(tmp_obl);
                oblig_subsumed++;
              } else {
                ++it;
              }
            }
          }          
        }
      }
      layers_delta[idx].resize(j);
    
      if (layers_delta[idx].size() == 0) {
        if (gcmd_line.obl_survive < 2)
          printf("UNSAT: repetition detected!\nDelta-layer %zu emptied by pushing!\n",idx);
        else
          printf("UNRESOLVED: repetition detected under incompete setup!\nDelta-layer %zu emptied by pushing!\n",idx);
          
        return true;
      }
    }
    
    least_affected_layer = phase+1; 
    // we are at the end of a phase so least_affected_layer will be equal to the new value of phase next time clausePushing is called (unless explicitly decremented)
    
    return false;
  }

  bool stateNotModel(BoolState& s, Clauses& layer) {
    for (size_t i = 0; i < layer.size(); i++)
      if (clauseUnsatisfied(layer[i]->data,s))
        return true;
    return false;
  }
  
  bool stateNotOfInvariant(BoolState& s) {
    Clause cur_clause;
    for (size_t i = 0; i < invariant.size(); i++) {
      invariant.loadClause(i,cur_clause);
      if (clauseUnsatisfied(cur_clause,s))
        return true;
    }     
    return false;
  }  
  
  void solve() {  
    times( &gstart );
    
    assert(sigsize > 0);
    assert(start_state.size() == sigsize);

    assert(layers_delta.size() == 1);  // already filled by caller
    assert(layers_deriv.size() == 0);
    layers_deriv.push_back(Clauses()); // catch up with layers_delta
       
    assert(obligations.size() == 0);
    obligations.push_back(Obligations()); // for keeping them all alive until the end of the phase
          
    //printf("Loading %d actions.\n",gnum_actions);    
    
    // temporaries needed for extending state
    actions.reserve(gnum_actions);
    for (Action* a = gactions; a; a = a->next) {
      // printf("Checking action "); printAction(stdout,a);
      actions.push_back(a);
    }
    buffers.resize(gnum_actions+1, ClauseBuffer()); // the last guy represents the "no-op" that ensures monotonicity                 
     
    // extend one more step - to be ready for phase 1
    layers_delta.push_back(Clauses());
    layers_deriv.push_back(Clauses());
    obligations.push_back(Obligations());
        
    action_ords.push_back(vector<size_t>());
    randomPermutation(action_ords.back(),gnum_actions);    
           
    if (stateNotOfInvariant(start_state)) {
      printf("UNSAT: initial state doesn't satisfy the backward invariant!\n");
      return;
    }   
        
    for (phase = 1 ;; phase++) {    
      if (gcmd_line.pphase == 1)
        printf("Phase %zu\n",phase);        
    
      if (gcmd_line.phaselim && (int)phase > gcmd_line.phaselim) {
        printf("UNRESOLVED: Phase limit reached!\n");        
        return;
      }
      
      bool reinsert_initial = (!gcmd_line.obl_survive || !gcmd_line.resched || phase == 1 || gcmd_line.obl_subsumption == 2);
      bool result = false;
      
      if (reinsert_initial && (gcmd_line.cla_subsumption == 2) && stateNotModel(start_state,layers_delta[phase])) {
        if (gcmd_line.pphase == 1)
            printf("Skipped - initial state doesn't satisfy pushed clauses!\n");      
      } else {
        if (reinsert_initial) {
          Obligation* obl = new Obligation(NULL,NULL); // the initial guy has no parents
          obl->depth = 0;
          obl->state = start_state;
          obligations[phase-1].push_front(obl); // so that it is picked last with oblig_prior_stack+obl_survive+obl_subsumption=2        
        }
        result = processObligations();
      }
      if (gcmd_line.pphase == 2) {
        for (size_t i = 0; i < phase; i++)
          if (i < path_min_layer)
            printf(".");
          else
            printf("*");
        printf("\n");

        path_min_layer = phase+1;
      }
      
      if (result)
        return;
      
      // extending for the next phase, so that pushing can fill the new layer
      layers_delta.push_back(Clauses());
      layers_deriv.push_back(Clauses());
      obligations.push_back(Obligations());
      
      action_ords.push_back(vector<size_t>());
      randomPermutation(action_ords.back(),gnum_actions);
      
      if (gcmd_line.cla_subsumption == 2) { // clause pushing
        times(&start);
        bool done = clausePushing();
        times(&end);
        TIME( time_pushing );
        
        if (done)
          return;        
      }

      if (gcmd_line.pphase == 1) {
        printStat();
        /*
        printf("Layers: ----------------------------- \n");
        printLayers();
        printf("------------------------------------- \n");
        */
      }
    }  
  }  
} context;

static void SIGINT_exit(int signum) {
  printf("*** INTERRUPTED ***\n");    
  context.printGOStat();
  fflush(stdout);  
  _exit(1);
}

void normalizeActions() { // "first delete then add" is the official semantics!
  vector<int> playground;
  playground.resize(gnum_relevant_facts,0);
  int mark = 1;
  
  size_t modified_actions = 0;
  size_t dropped_actions = 0;
  Action** me_ptr = &gactions;
  
  for (Action* a = gactions; a; a = a->next) {
    // printf("Checking action "); printAction(stdout,a);
    
    bool modified = false;
    int i,j;
    
    // del := del \ add
    for (i = 0; i < a->num_adds; i++)
      playground[a->adds[i]] = mark;            
    for (i = 0, j = 0; i < a->num_dels; i++) 
      if (playground[a->dels[i]] == mark) {
        //drop him
        modified = true;      
      } else {
        //keep him
        a->dels[j++] = a->dels[i];
      }
    a->num_dels = j;
    
    mark++;    
    
    // add := add \ pre
    for (i = 0; i < a->num_preconds; i++)
      playground[a->preconds[i]] = mark;            
    for (i = 0, j = 0; i < a->num_adds; i++) 
      if (playground[a->adds[i]] == mark) {
        //drop him
        modified = true;
      } else {
        //keep him
        a->adds[j++] = a->adds[i];
      }       
    
    if (j == 0) {
      *me_ptr = a->next;
      
      // TODO: release a (but first update me_ptr and don't drive the cycle by a anymore!)
      
      // printf("Dropped!\n");
      
      gnum_actions--;
      dropped_actions++;
    } else {
      a->num_adds = j;
      me_ptr = &a->next;
    }
       
    if (modified)
      modified_actions++;
      
    mark++;    
  }
  
  printf("\nNormalized actions: modified %zu and dropped %zu.\n",modified_actions,dropped_actions);
}

int main(int argc, char** argv)
{
  main_orig(argc,argv); 

  normalizeActions();    
     
  BoolState initial_state, start_state;
  Clause target_condition; // abusing clause structure, imposing conjunctive semantics
  
  initial_state.resize(gnum_relevant_facts,false);
  for (int i = 0; i < ginitial_state.num_F; i++ ) 
    initial_state[ginitial_state.F[i]] = true;
      
  bool sat_in_initial = true;
  for (int i = 0; i < ggoal_state.num_F; i++ )
    if (!initial_state[ggoal_state.F[i]]) {
      sat_in_initial = false;
      break;
    }
  
  if (sat_in_initial) {
    printf("Initial state satisfies the goal.\nPlan is trivial!\n");
    exit(0);
  }
      
  // start state
  if (!gcmd_line.reverse) {
    start_state = initial_state;
                    
    for (int i = 0; i < ggoal_state.num_F; i++ )
      target_condition.push_back(ggoal_state.F[i]);      
  } else {
    // reverse has start_state with goal instead of init and flipped polarity
    start_state.resize(gnum_relevant_facts,true);
    for (int i = 0; i < ggoal_state.num_F; i++) 
      start_state[ggoal_state.F[i]] = false;
                 
    //in target_condition are unit clauses corresponding to false initial lits    
    for (size_t i = 0; i < initial_state.size(); i++ ) 
      if (!initial_state[i])
        target_condition.push_back(i);                  
  }
  
  if (gcmd_line.just_translate) {            
    printf("\nTranslating problem with operator file %s and fact file %s.\n",gcmd_line.ops_file_name,gcmd_line.fct_file_name);           
        
    translate_Translate(stdout,start_state,target_condition);
        
    fflush(stdout);
    _exit(0);
  }
  
  if (gcmd_line.just_dumpgrounded) {
    translate_DumpGrounded(start_state,target_condition);
    
    fflush(stdout);
    _exit(0);
  } 
  
  // register the handler
  signal(SIGINT, SIGINT_exit);
  
  // initilize context
  {
    Clause temp_clause;
    context.layers_delta.push_back(Clauses());    
    Clauses& target_layer = context.layers_delta[0];     
    
    //signature
    context.sigsize = gnum_relevant_facts;
    
    //start
    context.start_state = start_state;       
    
    //goal - putting into layers and also into goal_lits for fast random access with induction
    context.goal_lits.resize(gnum_relevant_facts,false);    
    
    for (size_t i = 0; i < target_condition.size(); i++ ) {
      temp_clause.clear();
      temp_clause.push_back(target_condition[i]);                
      ClauseBox* clbox = new ClauseBox(temp_clause,0);     
      target_layer.push_back(clbox->inc());    
      
      if (gcmd_line.minimize > 1)
        context.goal_lits[target_condition[i]] = true;       
    }
    
    // invariant
    if (gcmd_line.gen_invariant) {
      float time_invariant = 0.0;
      printf("\nGenerating invariant ...\n");
    
      times(&start);
      invariant_Init(target_condition);
      times(&end);
      TIME( time_invariant );
             
      size_t bincl = 0;
      size_t unitcl = 0;
      context.invariant.reserve(invariant_Size());           
      
      while (invariant_CurrentValid()) {
        BinClause& bcl = invariant_Current();
                      
        if (bcl.l1 == bcl.l2)
          unitcl++;
        else 
          bincl++;
        context.invariant.pushClause(bcl);         

        /*
        print_ft_name(bcl.l1);
        if (bcl.l1 != bcl.l2) {
          printf(" ");
          print_ft_name(bcl.l2);
        }
        printf("\n");          
        */
        
        invariant_Next();
      }
      invariant_Done();
       
      printf("\tderived %zu binclauses and %zu units,\n",bincl,unitcl);
      printf("\ttook %fs.\n\n",time_invariant);
    }
  }
  
  printf("\n--- Starting PDR --- \n");
  
  context.solve();
  
  return 0;
}
