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

#include "Invariant.h"
#include <cassert>

#include <vector>
#include <list>

const char FL_NONE = 0;
const char FL_PRE  = 1;
const char FL_ADD  = 2;
const char FL_DEL  = 4;

using namespace std;

struct ClBox {
  int other_lit;
  ClBox *next;
  ClBox **next_at_prev;
  ClBox *other;
  
  ClBox(int lit) : other_lit(lit), next(0), next_at_prev(0), other(0) {}
  
  void integrate(ClBox** holder) {  // like insert
    assert(holder);
    next = *holder;
    *holder = this;
    next_at_prev = holder;
    if (next) {
      assert(next->next_at_prev == holder);
      next->next_at_prev = &next;
    }    
  }    
    
  void disintegrate() {             // like remove 
    assert(next_at_prev);
    assert(*next_at_prev == this);
    *next_at_prev = next;
    if (next) {
      assert(next->next_at_prev == &next);      
      next->next_at_prev = next_at_prev;
    }
  }
  
};

vector<char> playground;
vector< ClBox* > clauses;

int cl_cnt;

size_t idx;
BinClause result;

static bool unit(int i) {
  return (clauses[i] && !clauses[i]->other);
}

static void loadA(Action* a) {
  for (int i = 0; i < numPreconds(a); i++) 
    playground[getPrecond(a,i)] |= FL_PRE;
    
  for (int i = 0; i < numAdds(a); i++) 
    playground[getAdd(a,i)] |= FL_ADD;
    
  for (int i = 0; i < numDels(a); i++) 
    playground[getDel(a,i)] |= FL_DEL;
}

static void unloadA(Action* a) {
  for (int i = 0; i < numPreconds(a); i++) 
    playground[getPrecond(a,i)] = FL_NONE;
    
  for (int i = 0; i < numAdds(a); i++) 
    playground[getAdd(a,i)] = FL_NONE;
    
  for (int i = 0; i < numDels(a); i++) 
    playground[getDel(a,i)] = FL_NONE;
}

static bool isPre(int idx) {
  return (playground[idx] & FL_PRE) != FL_NONE;
}

static bool isAdd(int idx) {
  return (playground[idx] & FL_ADD) != FL_NONE;
}

static bool isDel(int idx) {
  return (playground[idx] & FL_DEL) != FL_NONE;
}

void invariant_Init(Clause& goal_condition) {
  cl_cnt = 0;

  playground.clear();
  playground.resize(gnum_relevant_facts,FL_NONE);
    
  clauses.clear();
  //fixed size from now on -- reallocate would kill us!
  clauses.resize(gnum_relevant_facts,0);
    
  for (size_t i = 0; i < goal_condition.size(); i++) {
    int cond = goal_condition[i];
    if (!clauses[cond]) { //insert each unit only once
      ClBox *unit = new ClBox(cond);
      unit->integrate(&clauses[cond]);
      
      // printf("Created unit %d\n",(int)cond);
      
      cl_cnt++;
    }
  }

  bool modified;
  do {
    modified = false;
    
    // a fixedpoint is finally reach iff:
    // for all clauses $c$ and all actions $a$. 
    // $(pre_a \cap c = \emptyset \land add_a \cap c \neq \emptyset --> 
    //            \exists d . d \subseteq ((c \setminus add_a) \cup del_a)$
    
    // we can assume actions normalized: pre_a \cap add_a = \emptyset \land del_a \cap add_a = \emptyset
    
    for (Action* a = gactions; a; a = a->next) {
      loadA(a);
    
      // printAction(stdout,a); 
    
      for (int i = 0; i < numAdds(a); i++) {
        int c_lit = getAdd(a,i);
        ClBox* c = clauses[c_lit];
        
        while (c) {
          int c_other_lit = c->other_lit;
        
          // printf("lit = %d, other = %d\n",c_lit,c_other_lit);
        
          if (isPre(c_other_lit)) { // NOT (pre_a \cap c = \emptyset)
            c = c->next;
            continue;
          }

          if (isAdd(c_other_lit)) // (c \setminus add_a) = emptyset
            c_other_lit = -1;     // do not ``pair up'' via c_other_lit
        
          // search for a clause d
          bool found = false;               
          for (int j = 0; j < numDels(a); j++) {
            ClBox* d = clauses[getDel(a,j)];
            
            while (d) {
              if (isDel(d->other_lit)) // CANNOT KILL ANY CLAUSE: \exists d. d \subseteq del_a
                goto next_action;      // also work for unit(d)
            
              if (c_other_lit == d->other_lit) {
                found = true;
                goto d_iter_finished;
              }
              
              d = d->next;
            }
          }
        
          d_iter_finished:
          if (!found) { // action a says: clause c must be killed
            modified = true;
          
            ClBox *dead = c;
            c = c->next;      // move fwd with c
                                    
            if (dead->other) {            
              // printf("Killing binay %d,%d\n",c_lit,dead->other_lit);            
            
              dead->other->disintegrate();                         
              delete dead->other;              
              
            } else { // a unit dies
              // printf("Killing unit %d\n",c_lit);
            
              for (int j = 0; j < gnum_relevant_facts; j++) {                
                if (j != c_lit && !unit(j)) {
                  cl_cnt++;
                  ClBox* lit1 = new ClBox(j);
                  ClBox* lit2 = new ClBox(c_lit);

                  lit1->other = lit2;
                  lit2->other = lit1;
                  
                  lit1->integrate(&clauses[c_lit]);
                  lit2->integrate(&clauses[j]);                                                    
                  
                  // printf("Creating binary %d,%d\n",c_lit,j);
                }
              }
            }
          
            // disconnect next prev
            dead->disintegrate();            
            delete dead;
            
            cl_cnt--;
          } else
            c = c->next;      // move fwd with c
        }
      }

      next_action: 
      unloadA(a);
    }      
    
    // printf("%d\n",cl_cnt);
    
  } while (modified);  
 
  playground.clear();
    
  idx = 0;
  invariant_Next();   
}

size_t invariant_Size() {
  return cl_cnt;
} 

bool invariant_CurrentValid() {
  return result.l1 >= 0;
}

const BinClause& invariant_Current() {
  return result;
}

void invariant_Next() {
  while ((idx < clauses.size()) && (!clauses[idx]))
    idx++;
    
  if (idx < clauses.size()) {
    ClBox *dead = clauses[idx];
      
    result.l1 = idx;
    result.l2 = dead->other_lit;
    
    if (dead->other) {
      dead->other->disintegrate();
      delete dead->other;
    }
    
    dead->disintegrate();
    delete dead;
    
  } else {
    result.l1 = -1;
    result.l2 = -1;
  }
}

void invariant_Done() {
  // clean up
}
