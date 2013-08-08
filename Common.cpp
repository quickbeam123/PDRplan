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

#include "Common.h"

#include "bb.h"
#include "output.h"

#include <cassert>

using namespace std;

int numPreconds(Action* a) {
    if (!gcmd_line.reverse) 
      return a->num_preconds;
    else
      return a->num_dels;
  }
  
int getPrecond(Action* a, int i) {
  if (!gcmd_line.reverse) 
    return a->preconds[i];
  else
    return a->dels[i];
}

int numAdds(Action* a) {  
  return a->num_adds;  
}

int getAdd(Action* a, int i) {
  return a->adds[i];  
}

int numDels(Action* a) {
  if (!gcmd_line.reverse) 
    return a->num_dels;
  else
    return a->num_preconds;
}

int getDel(Action* a, int i) {
  if (!gcmd_line.reverse) 
    return a->dels[i];
  else
    return a->preconds[i];
}

bool clauseUnsatisfied(Clause const &cl, BoolState const &st) {
  for (size_t i = 0; i < cl.size(); i++)
    if (st[cl[i]])
      return false;
      
  return true;
}

bool subsumes(Clause const &c1, Clause const &c2) { 
  if (c1.size() > c2.size())
    return false;

  size_t j = 0;
  for (size_t i = 0; i < c1.size(); i++) {    
    while (j < c2.size() && c2[j] < c1[i])
      j++;
    if (j == c2.size())
      return false;
    if (c1[i] != c2[j])
      return false;
    j++;
  }

  return true;
}

void applyActionEffects(BoolState &state, Action* a) {
  for (int i = 0; i < a->num_adds; i++)
    state[a->adds[i]] = true;
  for (int i = 0; i < numDels(a); i++)
    state[getDel(a,i)] = false;  
}

void printClause(Clause const & clause) {
  for (size_t i = 0; i < clause.size(); i++)
    printf("%zu, ",clause[i]);
  printf("\n");    
}

void printClauseNice(Clause const & clause) {
  for (size_t i = 0; i < clause.size(); i++) {
    print_ft_name(clause[i]);
    printf(" ");
  }
  printf("\n"); 
}

void printClauseAsState(Clause const & clause) {
  assert(clause.size());
  size_t curidx = 0;
  size_t curlit = clause[curidx++];

  for (size_t i = 0; i < (size_t)gnum_relevant_facts; i++) {
    if (i == curlit) {
      printf("*");
      if (curidx < clause.size())
        curlit = clause[curidx++];
      else
        curlit = gnum_relevant_facts;
    } else 
      printf("-");
  }
  printf("\n"); 
}

void printState(BoolState const & state) {
  for (size_t i = 0; i < state.size(); i++)
    if (state[i]) {
      print_ft_name(i);
      printf(" ");
    }
  printf("\n"); 
}

void printStateHash(BoolState const & state) {
  int tick = 0;
  char cur = 0;
  char last = 0;
  int cnt = 0;
  for (size_t i = 0; i < state.size(); i++) {
    cur ^= (bool)state[i];    
    if (++tick == 4) {  // from 0 to 16
      cur = 'a' + cur;
      if (cur == last) 
        cnt++;
      else {
        last = cur;
        printf("%d%c",cnt,cur);
        cnt = 0;
      }          
      tick = 0;
      cur = 0;
    } else {
      cur <<= 1;
    }
  }
  printf("%d%c\n",cnt,'a'+cur);
}

void printAction(FILE* outfile, Action* a) {
  Operator *o = goperators[a->op];
  fprintf(outfile,"(%s",o->name);
  for (int  i = 0; i < o->num_vars; i++ )
    fprintf(outfile," %s",gconstants[a->inst_table[i]]);
  fprintf(outfile,")\n");  
}

void printGroundedAction(FILE* outfile, Action* a) {
  Operator *o = goperators[a->op];
  fprintf(outfile,"%s",o->name);
  for (int  i = 0; i < o->num_vars; i++ )
    fprintf(outfile,"-%s",gconstants[a->inst_table[i]]);
  fprintf(outfile,"\n");  
}
