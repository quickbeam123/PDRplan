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

#ifndef Invariant_h
#define Invariant_h

#include "Common.h"

struct BinClause {
  int l1,l2;   // l1 == l2 simulates a unary clause   
};

void invariant_Init(Clause& goal_condition);    /* prepares the invariant, setting an implicit iterator to its first clause */

size_t invariant_Size();                        /* Number of clauses in the invariant */
bool invariant_CurrentValid();                  /* does the implicit iterator correspond to a real value ? */
const BinClause& invariant_Current();                 /* retrieve the value of the implicit itetator */
void invariant_Next();                          /* move the implicit iterator one step fwd*/

void invariant_Done();                          /* release the module's data strucutures */

#endif