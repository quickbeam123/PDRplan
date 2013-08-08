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

#ifndef Common_h
#define Common_h

#include "bb.h"
#include <cstdio>

#include <vector>

typedef std::vector<bool> BoolState;
typedef std::vector<size_t> Clause; // only positive clauses -- implemented as a vector of their atom indices

int numPreconds(Action* a);
int getPrecond(Action* a, int i);
int numAdds(Action* a);
int getAdd(Action* a, int i);
int numDels(Action* a);
int getDel(Action* a, int i);

bool subsumes(Clause const &c1, Clause const &c2); // assumed sorted
bool clauseUnsatisfied(Clause const &cl, BoolState const &st);
void applyActionEffects(BoolState &state, Action* a);

void printClause(Clause const & clause);
void printClauseNice(Clause const & clause);
void printClauseAsState(Clause const & clause);
void printState(BoolState const & state);
void printStateHash(BoolState const & state);

void printAction(FILE* outfile, Action* a);
void printGroundedAction(FILE* outfile, Action* a);

#endif