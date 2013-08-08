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
#include <map>
#include <queue>
#include <stack>

using namespace std;

struct Todo {
  int clause;
  Action* act;   // NULL means all
  int witness;   // -1 means undef
  Todo(int cl) : clause(cl), act(NULL), witness(-1) {}
  Todo(int cl, Action* a, int wi) : clause(cl), act(a), witness(wi) {}
};

struct BinClauseImpl : BinClause {   
  vector<Todo> watched;
};

typedef map<int,BinClauseImpl> Clauses;

// global temporaries
int playground_mark;
vector<int> playground;

/* returns true if the clause should die; if it lives but just with other's support, the supporter is informed */
static bool checkClause(Clauses& clauses,           /* all the currently living clauses*/
                        Clauses::iterator it,       /* a ptr to the clause to be rechecked */
                        Action* act,                /* against this action */
                        Clauses::iterator hint) {   /* start checking against other clauses from here */
                        
  BinClauseImpl& cl = it->second;
                        
  // 1 - if preconds intersect with clause   
  for (int i = 0; i < numPreconds(act); i++)
    if (getPrecond(act,i) == cl.l1 || getPrecond(act,i) == cl.l2)
      return false;
  
  playground_mark++;
  playground[cl.l1] = playground_mark;
  playground[cl.l2] = playground_mark;
  
  // 2 - if adds don't intersect with clause
  bool saves = false;
  for (int i = 0; i < numAdds(act); i++)
    if (getAdd(act,i) == cl.l1 || getAdd(act,i) == cl.l2) {
      playground[getAdd(act,i)] = 0;
      saves = true;
      // don't break, leave a chance to cancel out the other as well
    }
    
  if (!saves)
    return false;
                       
  // 3 - mark the delete effects
  for (int i = 0; i < numDels(act); i++)
    playground[getDel(act,i)] = playground_mark;  
  
  // 4 - traverse all the clauses 
  while (hint != clauses.end()) {
    BinClauseImpl& other_cl = hint->second;
  
    if (playground[other_cl.l1] == playground_mark && playground[other_cl.l2] == playground_mark) { // this one is false
      other_cl.watched.push_back(Todo(it->first,act,hint->first));      
      return false;
    }
    ++hint;
  }
  
  return true;                     
}

Clauses           *p_clauses;  // global guy to store the result
Clauses::iterator implicit_it; // and an iterator therein

void invariant_Init(Clause& goal_condition) {     
  playground_mark = 0; 
  playground.clear();
  playground.resize(gnum_relevant_facts,0);
        
  int last_clause = 0;
  p_clauses = new Clauses();
  Clauses& clauses = *p_clauses;
  vector<bool> units;
  stack<Todo> stack;   
  
  units.resize(gnum_relevant_facts,false);
  for (size_t i = 0; i < goal_condition.size(); i++)
    if (!units[goal_condition[i]]) {
      last_clause++;
      BinClauseImpl &cl = clauses[last_clause];
      cl.l1 = cl.l2 = goal_condition[i];
      units[goal_condition[i]] = true;
      stack.push(Todo(last_clause));
    }
  
  while (!stack.empty()) {
    Todo t = stack.top(); stack.pop();
    
    // printf("%zu - clauses (%d last_clause), %zu - requests on the stack\n",clauses.size(),last_clause,stack.size());
    
    Clauses::iterator it = clauses.find(t.clause);
    if (it == clauses.end())  // the clause has been deleted in the meantime
      continue;
    
    bool dying = false;
    if (t.act == NULL) {
      for (Action* a = gactions; a; a = a->next) {      
        dying = checkClause(clauses, it, a, clauses.begin());        
        if (dying)
          break;
      }      
    } else
      dying = checkClause(clauses, it, t.act, clauses.upper_bound(t.witness));
    
    if (dying) {
      BinClauseImpl& cl = it->second;
      
      // enqueue watched guys
      for (size_t i = 0; i < cl.watched.size(); i++)
        stack.push(cl.watched[i]);
    
      if (cl.l1 == cl.l2) { //unit clause - replacing it by binary ones
        assert(units[cl.l1]);
        
        for (int i = 0; i < gnum_relevant_facts; i++) 
          if (!units[i]) {
            last_clause++;
            BinClauseImpl &new_cl = clauses[last_clause];              
            new_cl.l1 = cl.l1;
            new_cl.l2 = i;
            stack.push(Todo(last_clause));
          }

        units[cl.l1] = false; // a trick to set it only here so the we don't generate the "binary" clause containing this unit's literal twice
      }
                       
      // kill it
      clauses.erase(it);      
    }       
  }   
     
  playground.clear();
  implicit_it = clauses.begin();
}

size_t invariant_Size() {
  return p_clauses->size();
} 

bool invariant_CurrentValid() {
  return (implicit_it != p_clauses->end());
}

BinClause& invariant_Current() {
  return implicit_it->second;
}

void invariant_Next() {
  ++implicit_it;
}

void invariant_Done() {
  delete p_clauses;
}
