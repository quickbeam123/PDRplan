
/* A Bison parser, made by GNU Bison 2.4.1.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C
   
      Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.4.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 0

/* Substitute the variable and function names.  */
#define yyparse         ops_pddlparse
#define yylex           ops_pddllex
#define yyerror         ops_pddlerror
#define yylval          ops_pddllval
#define yychar          ops_pddlchar
#define yydebug         ops_pddldebug
#define yynerrs         ops_pddlnerrs


/* Copy the first part of user declarations.  */

/* Line 189 of yacc.c  */
#line 1 "scan-ops_pddl.y"

#ifdef YYDEBUG
  extern int yydebug=1;
#endif


#include <stdio.h>
#include <string.h> 
#include "bb.h"
#include "memory.h"
#include "parse.h"


#ifndef SCAN_ERR
#define SCAN_ERR
#define DOMDEF_EXPECTED            0
#define DOMAIN_EXPECTED            1
#define DOMNAME_EXPECTED           2
#define LBRACKET_EXPECTED          3
#define RBRACKET_EXPECTED          4
#define DOMDEFS_EXPECTED           5
#define REQUIREM_EXPECTED          6
#define TYPEDLIST_EXPECTED         7
#define LITERAL_EXPECTED           8
#define PRECONDDEF_UNCORRECT       9
#define TYPEDEF_EXPECTED          10
#define CONSTLIST_EXPECTED        11
#define PREDDEF_EXPECTED          12 
#define NAME_EXPECTED             13
#define VARIABLE_EXPECTED         14
#define ACTIONFUNCTOR_EXPECTED    15
#define ATOM_FORMULA_EXPECTED     16
#define EFFECT_DEF_EXPECTED       17
#define NEG_FORMULA_EXPECTED      18
#define NOT_SUPPORTED             19
#define ACTION                    20
#endif


#define NAME_STR "name\0"
#define VARIABLE_STR "variable\0"
#define STANDARD_TYPE "OBJECT\0"
 

static char *serrmsg[] = {
  "domain definition expected",
  "'domain' expected",
  "domain name expected",
  "'(' expected",
  "')' expected",
  "additional domain definitions expected",
  "requirements (e.g. ':STRIPS') expected",
  "typed list of <%s> expected",
  "literal expected",
  "uncorrect precondition definition",
  "type definition expected",
  "list of constants expected",
  "predicate definition expected",
  "<name> expected",
  "<variable> expected",
  "action functor expected",
  "atomic formula expected",
  "effect definition expected",
  "negated atomic formula expected",
  "requirement %s not supported by this IPP version",  
  "action definition is not correct",
  NULL
};


void opserr( int errno, char *par );


static int sact_err;
static char *sact_err_par = NULL;
static PlOperator *scur_op = NULL;
static Bool sis_negated = FALSE;


int supported( char *str )

{

  int i;
  char * sup[] = { ":STRIPS", ":NEGATION", ":EQUALITY",":TYPING", 
		   ":CONDITIONAL-EFFECTS", ":DISJUNCTIVE-PRECONDITIONS", 
		   ":EXISTENTIAL-PRECONDITIONS", ":UNIVERSAL-PRECONDITIONS", 
		   ":QUANTIFIED-PRECONDITIONS", ":ADL",
		   NULL };     

  for (i=0; NULL != sup[i]; i++) {
    if ( SAME == strcmp(sup[i], str) ) {
      return TRUE;
    }
  }
  
  return FALSE;

}



/* Line 189 of yacc.c  */
#line 184 "scan-ops_pddl.tab.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     DEFINE_TOK = 258,
     DOMAIN_TOK = 259,
     REQUIREMENTS_TOK = 260,
     TYPES_TOK = 261,
     EITHER_TOK = 262,
     CONSTANTS_TOK = 263,
     PREDICATES_TOK = 264,
     ACTION_TOK = 265,
     VARS_TOK = 266,
     CONTEXT_TOK = 267,
     IMPLIES_TOK = 268,
     PRECONDITION_TOK = 269,
     PARAMETERS_TOK = 270,
     EFFECT_TOK = 271,
     AND_TOK = 272,
     NOT_TOK = 273,
     WHEN_TOK = 274,
     FORALL_TOK = 275,
     IMPLY_TOK = 276,
     OR_TOK = 277,
     EXISTS_TOK = 278,
     EQUAL_TOK = 279,
     NAME = 280,
     VARIABLE = 281,
     TYPE = 282,
     OPEN_PAREN = 283,
     CLOSE_PAREN = 284
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 214 of yacc.c  */
#line 107 "scan-ops_pddl.y"


  char string[MAX_LENGTH];
  char *pstring;
  PlNode *pPlNode;
  FactList *pFactList;
  TokenList *pTokenList;




/* Line 214 of yacc.c  */
#line 261 "scan-ops_pddl.tab.c"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


/* Copy the second part of user declarations.  */


/* Line 264 of yacc.c  */
#line 273 "scan-ops_pddl.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   126

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  30
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  39
/* YYNRULES -- Number of rules.  */
#define YYNRULES  73
/* YYNRULES -- Number of states.  */
#define YYNSTATES  156

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   284

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint8 yyprhs[] =
{
       0,     0,     3,     4,     7,     8,    14,    19,    21,    24,
      27,    30,    33,    36,    37,    43,    44,    45,    52,    53,
      54,    62,    63,    64,    68,    69,    75,    76,    82,    83,
      84,    93,    94,    99,   100,   106,   107,   112,   113,   118,
     120,   125,   130,   135,   141,   149,   157,   158,   161,   163,
     168,   173,   181,   187,   188,   191,   196,   198,   203,   204,
     207,   209,   211,   213,   216,   218,   220,   221,   227,   231,
     234,   235,   241,   245
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      31,     0,    -1,    -1,    32,    33,    -1,    -1,    28,     3,
      35,    34,    36,    -1,    28,     4,    25,    29,    -1,    29,
      -1,    41,    36,    -1,    48,    36,    -1,    46,    36,    -1,
      50,    36,    -1,    37,    36,    -1,    -1,    28,     9,    39,
      38,    29,    -1,    -1,    -1,    28,    25,    68,    29,    40,
      39,    -1,    -1,    -1,    28,     5,    42,    25,    43,    44,
      29,    -1,    -1,    -1,    25,    45,    44,    -1,    -1,    28,
       6,    47,    67,    29,    -1,    -1,    28,     8,    49,    67,
      29,    -1,    -1,    -1,    28,    10,    51,    25,    52,    53,
      54,    29,    -1,    -1,    15,    28,    68,    29,    -1,    -1,
      11,    28,    68,    29,    54,    -1,    -1,    14,    57,    55,
      54,    -1,    -1,    16,    59,    56,    54,    -1,    61,    -1,
      28,    17,    58,    29,    -1,    28,    22,    58,    29,    -1,
      28,    18,    57,    29,    -1,    28,    21,    57,    57,    29,
      -1,    28,    23,    28,    68,    29,    57,    29,    -1,    28,
      20,    28,    68,    29,    57,    29,    -1,    -1,    57,    58,
      -1,    61,    -1,    28,    17,    60,    29,    -1,    28,    18,
      59,    29,    -1,    28,    20,    28,    68,    29,    59,    29,
      -1,    28,    19,    57,    59,    29,    -1,    -1,    59,    60,
      -1,    28,    18,    62,    29,    -1,    62,    -1,    28,    66,
      63,    29,    -1,    -1,    64,    63,    -1,    25,    -1,    26,
      -1,    25,    -1,    25,    65,    -1,    25,    -1,    24,    -1,
      -1,    25,     7,    65,    29,    67,    -1,    25,    27,    67,
      -1,    25,    67,    -1,    -1,    26,     7,    65,    29,    68,
      -1,    26,    27,    68,    -1,    26,    68,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   163,   163,   163,   174,   173,   190,   200,   202,   204,
     206,   208,   210,   217,   216,   226,   229,   228,   268,   272,
     267,   283,   287,   286,   300,   299,   314,   313,   329,   333,
     328,   347,   351,   364,   367,   386,   385,   392,   391,   406,
     419,   425,   431,   437,   447,   489,   531,   535,   549,   562,
     568,   574,   611,   630,   634,   646,   652,   661,   673,   675,
     686,   692,   702,   709,   720,   726,   737,   739,   799,   811,
     835,   837,   896,   908
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "DEFINE_TOK", "DOMAIN_TOK",
  "REQUIREMENTS_TOK", "TYPES_TOK", "EITHER_TOK", "CONSTANTS_TOK",
  "PREDICATES_TOK", "ACTION_TOK", "VARS_TOK", "CONTEXT_TOK", "IMPLIES_TOK",
  "PRECONDITION_TOK", "PARAMETERS_TOK", "EFFECT_TOK", "AND_TOK", "NOT_TOK",
  "WHEN_TOK", "FORALL_TOK", "IMPLY_TOK", "OR_TOK", "EXISTS_TOK",
  "EQUAL_TOK", "NAME", "VARIABLE", "TYPE", "OPEN_PAREN", "CLOSE_PAREN",
  "$accept", "file", "$@1", "domain_definition", "$@2", "domain_name",
  "optional_domain_defs", "predicates_def", "$@3", "predicates_list",
  "$@4", "require_def", "$@5", "$@6", "require_key_star", "$@7",
  "types_def", "$@8", "constants_def", "$@9", "action_def", "$@10", "$@11",
  "param_def", "action_def_body", "$@12", "$@13", "adl_goal_description",
  "adl_goal_description_star", "adl_effect", "adl_effect_star",
  "literal_term", "atomic_formula_term", "term_star", "term", "name_plus",
  "predicate", "typed_list_name", "typed_list_variable", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    30,    32,    31,    34,    33,    35,    36,    36,    36,
      36,    36,    36,    38,    37,    39,    40,    39,    42,    43,
      41,    44,    45,    44,    47,    46,    49,    48,    51,    52,
      50,    53,    53,    54,    54,    55,    54,    56,    54,    57,
      57,    57,    57,    57,    57,    57,    58,    58,    59,    59,
      59,    59,    59,    60,    60,    61,    61,    62,    63,    63,
      64,    64,    65,    65,    66,    66,    67,    67,    67,    67,
      68,    68,    68,    68
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     2,     0,     5,     4,     1,     2,     2,
       2,     2,     2,     0,     5,     0,     0,     6,     0,     0,
       7,     0,     0,     3,     0,     5,     0,     5,     0,     0,
       8,     0,     4,     0,     5,     0,     4,     0,     4,     1,
       4,     4,     4,     5,     7,     7,     0,     2,     1,     4,
       4,     7,     5,     0,     2,     4,     1,     4,     0,     2,
       1,     1,     1,     2,     1,     1,     0,     5,     3,     2,
       0,     5,     3,     2
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       2,     0,     0,     1,     0,     3,     0,     0,     4,     0,
       0,     0,     0,     7,     5,     0,     0,     0,     0,     0,
       6,    18,    24,    26,    15,    28,    12,     8,    10,     9,
      11,     0,    66,    66,     0,    13,     0,    19,    66,     0,
       0,    70,     0,    29,    21,     0,    66,    69,    25,    27,
      70,     0,    14,    31,    22,     0,    62,     0,    68,     0,
      70,    73,    16,     0,    33,    21,    20,    63,    66,     0,
      72,    15,    70,     0,     0,     0,     0,    23,    67,    70,
      17,     0,    70,     0,    35,    39,    56,     0,    37,    48,
      30,    71,    32,     0,    46,     0,     0,     0,    46,     0,
      65,    64,    58,    33,    53,     0,     0,     0,    33,    33,
      46,     0,     0,     0,    70,     0,     0,    70,    60,    61,
       0,    58,    36,    53,     0,     0,     0,    70,    38,    34,
      47,    40,    42,    55,     0,     0,    41,     0,    57,    59,
      54,    49,    50,     0,     0,     0,    43,     0,    52,     0,
       0,     0,     0,    45,    44,    51
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
      -1,     1,     2,     5,    10,     8,    14,    15,    42,    35,
      71,    16,    31,    44,    55,    65,    17,    32,    18,    33,
      19,    36,    53,    64,    76,   103,   108,   110,   111,   123,
     124,    85,    86,   120,   121,    57,   102,    39,    51
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -96
static const yytype_int8 yypact[] =
{
     -96,    11,   -12,   -96,    23,   -96,     8,    43,   -96,    25,
      -1,    19,    51,   -96,   -96,    -1,    -1,    -1,    -1,    -1,
     -96,   -96,   -96,   -96,    26,   -96,   -96,   -96,   -96,   -96,
     -96,    33,    37,    37,    38,   -96,    49,   -96,    -4,    22,
      53,    54,    55,   -96,    66,    67,    37,   -96,   -96,   -96,
      -2,    64,   -96,    79,   -96,    68,    67,    69,   -96,    67,
      54,   -96,   -96,    72,    65,    66,   -96,   -96,    37,    70,
     -96,    26,    54,    73,    74,    75,    76,   -96,   -96,    54,
     -96,    77,    54,    48,   -96,   -96,   -96,    21,   -96,   -96,
     -96,   -96,   -96,    78,    74,    74,    80,    74,    74,    81,
     -96,   -96,    17,    65,    75,    75,    74,    82,    65,    65,
      74,    83,    84,    85,    54,    74,    86,    54,   -96,   -96,
      87,    17,   -96,    75,    88,    89,    75,    54,   -96,   -96,
     -96,   -96,   -96,   -96,    90,    91,   -96,    92,   -96,   -96,
     -96,   -96,   -96,    93,    94,    74,   -96,    74,   -96,    75,
      95,    96,    97,   -96,   -96,   -96
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -96,   -96,   -96,   -96,   -96,   -96,    71,   -96,   -96,    24,
     -96,   -96,   -96,   -96,    31,   -96,   -96,   -96,   -96,   -96,
     -96,   -96,   -96,   -96,   -95,   -96,   -96,   -62,   -92,   -71,
     -19,   -74,   -86,   -10,   -96,   -39,   -96,   -31,   -50
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      61,    89,    40,    45,    88,    59,   116,    47,   122,   113,
      70,     3,    84,   128,   129,    58,     4,    67,   130,   113,
      69,    38,    81,    46,    50,    60,     6,    12,    13,    91,
      89,    89,    93,   112,   125,   115,     7,    78,   104,   105,
     106,   107,   118,   119,   126,   100,   101,     9,    20,    89,
      11,    48,    89,   135,    34,   143,    21,    22,    37,    23,
      24,    25,    38,    41,   134,    94,    95,   137,    96,    97,
      98,    99,   100,   101,    43,    89,    73,   144,   152,    74,
      50,    75,    49,   150,    52,   151,    26,    27,    28,    29,
      30,    54,    56,    62,    63,    80,    77,    66,    68,    79,
      72,    82,    83,    87,   140,    90,    92,   109,   114,   117,
     127,   139,   131,   132,   133,   136,   138,   141,   142,   145,
     146,   147,   148,   149,   153,   154,   155
};

static const yytype_uint8 yycheck[] =
{
      50,    75,    33,     7,    75,     7,    98,    38,   103,    95,
      60,     0,    74,   108,   109,    46,    28,    56,   110,   105,
      59,    25,    72,    27,    26,    27,     3,    28,    29,    79,
     104,   105,    82,    95,   105,    97,    28,    68,    17,    18,
      19,    20,    25,    26,   106,    24,    25,     4,    29,   123,
      25,    29,   126,   115,    28,   126,     5,     6,    25,     8,
       9,    10,    25,    25,   114,    17,    18,   117,    20,    21,
      22,    23,    24,    25,    25,   149,    11,   127,   149,    14,
      26,    16,    29,   145,    29,   147,    15,    16,    17,    18,
      19,    25,    25,    29,    15,    71,    65,    29,    29,    29,
      28,    28,    28,    28,   123,    29,    29,    29,    28,    28,
      28,   121,    29,    29,    29,    29,    29,    29,    29,    29,
      29,    29,    29,    29,    29,    29,    29
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    31,    32,     0,    28,    33,     3,    28,    35,     4,
      34,    25,    28,    29,    36,    37,    41,    46,    48,    50,
      29,     5,     6,     8,     9,    10,    36,    36,    36,    36,
      36,    42,    47,    49,    28,    39,    51,    25,    25,    67,
      67,    25,    38,    25,    43,     7,    27,    67,    29,    29,
      26,    68,    29,    52,    25,    44,    25,    65,    67,     7,
      27,    68,    29,    15,    53,    45,    29,    65,    29,    65,
      68,    40,    28,    11,    14,    16,    54,    44,    67,    29,
      39,    68,    28,    28,    57,    61,    62,    28,    59,    61,
      29,    68,    29,    68,    17,    18,    20,    21,    22,    23,
      24,    25,    66,    55,    17,    18,    19,    20,    56,    29,
      57,    58,    57,    62,    28,    57,    58,    28,    25,    26,
      63,    64,    54,    59,    60,    59,    57,    28,    54,    54,
      58,    29,    29,    29,    68,    57,    29,    68,    29,    63,
      60,    29,    29,    59,    68,    29,    29,    29,    29,    29,
      57,    57,    59,    29,    29,    29
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}

/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*-------------------------.
| yyparse or yypush_parse.  |
`-------------------------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{


    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:

/* Line 1455 of yacc.c  */
#line 163 "scan-ops_pddl.y"
    { 
  opserr( DOMDEF_EXPECTED, NULL ); 
;}
    break;

  case 4:

/* Line 1455 of yacc.c  */
#line 174 "scan-ops_pddl.y"
    { 
  /* initialize typetree 
   */
  gglobal_type_tree_list = new_type_tree_list( STANDARD_TYPE );
;}
    break;

  case 5:

/* Line 1455 of yacc.c  */
#line 180 "scan-ops_pddl.y"
    {
  if ( gcmd_line.display_info >= 1 ) {
    printf("\ndomain '%s' defined\n", gdomain_name);
  }
;}
    break;

  case 6:

/* Line 1455 of yacc.c  */
#line 191 "scan-ops_pddl.y"
    { 
  gdomain_name = new_Token( strlen((yyvsp[(3) - (4)].string))+1 );
  strcpy( gdomain_name, (yyvsp[(3) - (4)].string));
;}
    break;

  case 13:

/* Line 1455 of yacc.c  */
#line 217 "scan-ops_pddl.y"
    {
;}
    break;

  case 14:

/* Line 1455 of yacc.c  */
#line 220 "scan-ops_pddl.y"
    { 
;}
    break;

  case 15:

/* Line 1455 of yacc.c  */
#line 226 "scan-ops_pddl.y"
    {;}
    break;

  case 16:

/* Line 1455 of yacc.c  */
#line 229 "scan-ops_pddl.y"
    {

  FactList *fl, *fl1;
  TokenList *tl, *tl1;

  if ( gpredicates_and_types ) {
    fl = gpredicates_and_types;
    while ( fl->next ) {
      fl = fl->next;
    }
    fl->next = new_FactList();
    fl = fl->next;
  } else {
    fl = new_FactList();
    gpredicates_and_types = fl;
  }
  tl = new_TokenList();
  fl->item = tl;
  tl->item = new_Token( strlen( (yyvsp[(2) - (4)].string) ) + 1);
  strcpy( tl->item, (yyvsp[(2) - (4)].string) );
  fl1 = (yyvsp[(3) - (4)].pFactList);
  while ( fl1 ) {
    tl1 = new_TokenList();
    tl->next = tl1;
    tl = tl1;
    tl1->item = new_Token( strlen( fl1->item->next->item ) + 1 );
    strcpy( tl1->item, fl1->item->next->item );
    fl1 = fl1->next;
  }
  free_FactList( (yyvsp[(3) - (4)].pFactList) );

;}
    break;

  case 18:

/* Line 1455 of yacc.c  */
#line 268 "scan-ops_pddl.y"
    { 
  opserr( REQUIREM_EXPECTED, NULL ); 
;}
    break;

  case 19:

/* Line 1455 of yacc.c  */
#line 272 "scan-ops_pddl.y"
    { 
  if ( !supported( (yyvsp[(4) - (4)].string) ) ) {
    opserr( NOT_SUPPORTED, (yyvsp[(4) - (4)].string) );
    yyerror();
  }
;}
    break;

  case 22:

/* Line 1455 of yacc.c  */
#line 287 "scan-ops_pddl.y"
    { 
  if ( !supported( (yyvsp[(1) - (1)].string) ) ) {
    opserr( NOT_SUPPORTED, (yyvsp[(1) - (1)].string) );
    yyerror();
  }
;}
    break;

  case 24:

/* Line 1455 of yacc.c  */
#line 300 "scan-ops_pddl.y"
    { 
  opserr( TYPEDEF_EXPECTED, NULL ); 
;}
    break;

  case 25:

/* Line 1455 of yacc.c  */
#line 304 "scan-ops_pddl.y"
    { 
  add_to_type_tree( (yyvsp[(4) - (5)].pFactList), main_type_tree() );
  free_FactList( (yyvsp[(4) - (5)].pFactList) );
;}
    break;

  case 26:

/* Line 1455 of yacc.c  */
#line 314 "scan-ops_pddl.y"
    { 
  opserr( CONSTLIST_EXPECTED, NULL ); 
;}
    break;

  case 27:

/* Line 1455 of yacc.c  */
#line 318 "scan-ops_pddl.y"
    { 
  gorig_constant_list = (yyvsp[(4) - (5)].pFactList);
;}
    break;

  case 28:

/* Line 1455 of yacc.c  */
#line 329 "scan-ops_pddl.y"
    { 
  opserr( ACTION, NULL ); 
;}
    break;

  case 29:

/* Line 1455 of yacc.c  */
#line 333 "scan-ops_pddl.y"
    { 
  scur_op = new_PlOperator( (yyvsp[(4) - (4)].string) );
;}
    break;

  case 30:

/* Line 1455 of yacc.c  */
#line 337 "scan-ops_pddl.y"
    {
  scur_op->next = gloaded_ops;
  gloaded_ops = scur_op; 
;}
    break;

  case 31:

/* Line 1455 of yacc.c  */
#line 347 "scan-ops_pddl.y"
    { 
  scur_op->params = NULL; 
;}
    break;

  case 32:

/* Line 1455 of yacc.c  */
#line 352 "scan-ops_pddl.y"
    {
  FactList *f;
  scur_op->params = (yyvsp[(3) - (4)].pFactList);
  for (f = scur_op->params; f; f = f->next) {
    /* to be able to distinguish params from :VARS 
     */
    scur_op->number_of_real_params++;
  }
;}
    break;

  case 34:

/* Line 1455 of yacc.c  */
#line 368 "scan-ops_pddl.y"
    {
  FactList *f = NULL;

  /* add vars as parameters 
   */
  if ( scur_op->params ) {
    for( f = scur_op->params; f->next; f = f->next ) {
      /* empty, get to the end of list 
       */
    }
    f->next = (yyvsp[(3) - (5)].pFactList);
    f = f->next;
  } else {
    scur_op->params = (yyvsp[(3) - (5)].pFactList);
  }
;}
    break;

  case 35:

/* Line 1455 of yacc.c  */
#line 386 "scan-ops_pddl.y"
    { 
  scur_op->preconds = (yyvsp[(2) - (2)].pPlNode); 
;}
    break;

  case 37:

/* Line 1455 of yacc.c  */
#line 392 "scan-ops_pddl.y"
    { 
  scur_op->effects = (yyvsp[(2) - (2)].pPlNode); 
;}
    break;

  case 39:

/* Line 1455 of yacc.c  */
#line 407 "scan-ops_pddl.y"
    { 
  if ( sis_negated ) {
    (yyval.pPlNode) = new_PlNode(NOT);
    (yyval.pPlNode)->sons = new_PlNode(ATOM);
    (yyval.pPlNode)->sons->atom = (yyvsp[(1) - (1)].pTokenList);
    sis_negated = FALSE;
  } else {
    (yyval.pPlNode) = new_PlNode(ATOM);
    (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
  }
;}
    break;

  case 40:

/* Line 1455 of yacc.c  */
#line 420 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(AND);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 41:

/* Line 1455 of yacc.c  */
#line 426 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(OR);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 42:

/* Line 1455 of yacc.c  */
#line 432 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(NOT);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 43:

/* Line 1455 of yacc.c  */
#line 438 "scan-ops_pddl.y"
    { 
  PlNode *np = new_PlNode(NOT);
  np->sons = (yyvsp[(3) - (5)].pPlNode);
  np->next = (yyvsp[(4) - (5)].pPlNode);

  (yyval.pPlNode) = new_PlNode(OR);
  (yyval.pPlNode)->sons = np;
;}
    break;

  case 44:

/* Line 1455 of yacc.c  */
#line 450 "scan-ops_pddl.y"
    { 
  /* The typed_list_variable returns a FactList with two-item TokenLists, 
   * the first item is the variable and the second item its type.
   * We now have to split off this FactList into a PlNode for each 
   * variable-type TokenList. 
   */
  FactList *tl = (yyvsp[(4) - (7)].pFactList), *t1;
  PlNode *pln1;
  PlNode *pln2;

  pln1 = new_PlNode(EX);
  pln1->atom = tl->item;
  (yyval.pPlNode) = pln1;

  t1 = tl;
  /* every loop gives us one quantor with one variable and its type 
   */
  while ( t1->next ) {
    t1 = t1->next;

    pln2 = new_PlNode(EX);
    pln2->atom = t1->item;
    /* append the next quantor to the sons of the previous node 
     */
    pln1->sons = pln2;
    pln1 = pln2;
  }
  pln1->sons = (yyvsp[(6) - (7)].pPlNode);

  t1 = tl->next;
  while ( TRUE ) {
    free ( tl );
    if ( !t1 ) break;
    tl = t1;
    t1 = tl->next;
  }

;}
    break;

  case 45:

/* Line 1455 of yacc.c  */
#line 492 "scan-ops_pddl.y"
    { 
  /* This will be handled exactly like the ex-quantor case, s.a. 
   */
  FactList *tl = (yyvsp[(4) - (7)].pFactList), *t1;
  PlNode *pln1;
  PlNode *pln2;
  
  pln1 = new_PlNode(ALL);
  pln1->atom = tl->item;
  (yyval.pPlNode) = pln1;

  t1 = tl;
  /* every loop gives us one quantor with one variable and its type 
   */
  while ( t1->next ) {
    t1 = t1->next;
      
    pln2 = new_PlNode(ALL);
    pln2->atom = t1->item;
    pln1->sons = pln2;
    pln1 = pln2;
  }
  pln1->sons = (yyvsp[(6) - (7)].pPlNode);

  t1 = tl->next;
  while ( TRUE ) {
    free ( tl );
    if ( !t1 ) break;
    tl = t1;
    t1 = tl->next;
  }

;}
    break;

  case 46:

/* Line 1455 of yacc.c  */
#line 531 "scan-ops_pddl.y"
    {
  (yyval.pPlNode) = NULL;
;}
    break;

  case 47:

/* Line 1455 of yacc.c  */
#line 536 "scan-ops_pddl.y"
    {
  (yyvsp[(1) - (2)].pPlNode)->next = (yyvsp[(2) - (2)].pPlNode);
  (yyval.pPlNode) = (yyvsp[(1) - (2)].pPlNode);
;}
    break;

  case 48:

/* Line 1455 of yacc.c  */
#line 550 "scan-ops_pddl.y"
    { 
  if ( sis_negated ) {
    (yyval.pPlNode) = new_PlNode(NOT);
    (yyval.pPlNode)->sons = new_PlNode(ATOM);
    (yyval.pPlNode)->sons->atom = (yyvsp[(1) - (1)].pTokenList);
    sis_negated = FALSE;
  } else {
    (yyval.pPlNode) = new_PlNode(ATOM);
    (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
  }
;}
    break;

  case 49:

/* Line 1455 of yacc.c  */
#line 563 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(AND);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 50:

/* Line 1455 of yacc.c  */
#line 569 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(NOT);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 51:

/* Line 1455 of yacc.c  */
#line 577 "scan-ops_pddl.y"
    { 
  /* This will be handled exactly like quantors in the goals part, s.o. 
   */
  FactList *fl = (yyvsp[(4) - (7)].pFactList), *f1;
  PlNode *pln1;
  PlNode *pln2;
  
  pln1 = new_PlNode(ALL);
  pln1->atom = fl->item;
  (yyval.pPlNode) = pln1;

  f1 = fl;
  /* every loop gives us one quantor with one variable and its type 
   */
  while ( f1->next ) {
    f1 = f1->next;
    
    pln2 = new_PlNode(ALL);
    pln2->atom = f1->item;
    pln1->sons = pln2;
    pln1 = pln2;
  }
  pln1->sons = (yyvsp[(6) - (7)].pPlNode);

  f1 = fl->next;
  while ( TRUE ) {
    free( fl );
    if ( !f1 ) break;
    fl = f1;
    f1 = fl->next;
  }

;}
    break;

  case 52:

/* Line 1455 of yacc.c  */
#line 612 "scan-ops_pddl.y"
    {
  /* This will be conditional effects in FF representation, but here
   * a formula like (WHEN p q) will be saved as:
   *  [WHEN]
   *  [sons]
   *   /  \
   * [p]  [q]
   * That means, the first son is p, and the second one is q. 
   */
  (yyval.pPlNode) = new_PlNode(WHEN);
  (yyvsp[(3) - (5)].pPlNode)->next = (yyvsp[(4) - (5)].pPlNode);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (5)].pPlNode);
;}
    break;

  case 53:

/* Line 1455 of yacc.c  */
#line 630 "scan-ops_pddl.y"
    { 
  (yyval.pPlNode) = NULL; 
;}
    break;

  case 54:

/* Line 1455 of yacc.c  */
#line 635 "scan-ops_pddl.y"
    {
  (yyvsp[(1) - (2)].pPlNode)->next = (yyvsp[(2) - (2)].pPlNode);
  (yyval.pPlNode) = (yyvsp[(1) - (2)].pPlNode);
;}
    break;

  case 55:

/* Line 1455 of yacc.c  */
#line 647 "scan-ops_pddl.y"
    { 
  (yyval.pTokenList) = (yyvsp[(3) - (4)].pTokenList);
  sis_negated = TRUE;
;}
    break;

  case 56:

/* Line 1455 of yacc.c  */
#line 653 "scan-ops_pddl.y"
    {
  (yyval.pTokenList) = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 57:

/* Line 1455 of yacc.c  */
#line 662 "scan-ops_pddl.y"
    { 
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(2) - (4)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(3) - (4)].pTokenList);
;}
    break;

  case 58:

/* Line 1455 of yacc.c  */
#line 673 "scan-ops_pddl.y"
    { (yyval.pTokenList) = NULL; ;}
    break;

  case 59:

/* Line 1455 of yacc.c  */
#line 676 "scan-ops_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(1) - (2)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(2) - (2)].pTokenList);
;}
    break;

  case 60:

/* Line 1455 of yacc.c  */
#line 687 "scan-ops_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy( (yyval.pstring), (yyvsp[(1) - (1)].string) );
;}
    break;

  case 61:

/* Line 1455 of yacc.c  */
#line 693 "scan-ops_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy( (yyval.pstring), (yyvsp[(1) - (1)].string) );
;}
    break;

  case 62:

/* Line 1455 of yacc.c  */
#line 703 "scan-ops_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy( (yyval.pTokenList)->item, (yyvsp[(1) - (1)].string) );
;}
    break;

  case 63:

/* Line 1455 of yacc.c  */
#line 710 "scan-ops_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = new_Token( strlen((yyvsp[(1) - (2)].string))+1 );
  strcpy( (yyval.pTokenList)->item, (yyvsp[(1) - (2)].string) );
  (yyval.pTokenList)->next = (yyvsp[(2) - (2)].pTokenList);
;}
    break;

  case 64:

/* Line 1455 of yacc.c  */
#line 721 "scan-ops_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy( (yyval.pstring), (yyvsp[(1) - (1)].string) );
;}
    break;

  case 65:

/* Line 1455 of yacc.c  */
#line 727 "scan-ops_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen(EQ_STR)+1 );
  strcpy( (yyval.pstring), EQ_STR );
;}
    break;

  case 66:

/* Line 1455 of yacc.c  */
#line 737 "scan-ops_pddl.y"
    { (yyval.pFactList) = NULL; ;}
    break;

  case 67:

/* Line 1455 of yacc.c  */
#line 740 "scan-ops_pddl.y"
    { /* this is a very, very special case... it may mean that
   * a. a parameter has one of the types in name_plus
   * b. a type is subtype of one of the following types in name_plus 
   * => for both possibilities we use the same solution:
   * build a new type name: either_name1_name2_..._namen and check
   * if a type with this name already exists. If so then NAME has this type,
   * if not then build a new type, include it in the type tree and
   * return NAME with the new type 
   * The new artificial type is not a subtype of OBJECT because its own
   * elements must already be instances of a subtype of OBJECT 
   */
  char *s;
  TokenList *t, *t1;
  type_tree tt;
  type_tree_list rootl, *st;
  
  s = new_Token( MAX_LENGTH );
  strcpy( s, EITHER_STR );
  for ( t = (yyvsp[(3) - (5)].pTokenList); t; t = t->next ) {
    strcat( s, CONNECTOR );
    strcat( s, t->item );
  }
  tt = NULL;
  for ( rootl = gglobal_type_tree_list; rootl; rootl = rootl->next ) {
    if ((tt = find_branch( s, rootl->item))) break;
  }
  if ( !tt ) {/* the type doesn't exist yet, so build it */
    rootl = new_type_tree_list( s );
    rootl->next = gglobal_type_tree_list;
    st = &(rootl->item->sub_types);
    for ( t = (yyvsp[(3) - (5)].pTokenList); t; t = t->next ) {
      if ((tt = find_branch( t->item, main_type_tree()))) {
	*st = new_type_tree_list( NULL );
	(*st)->item = tt;
	st = &((*st)->next);
      }
    }  
  }

  t = (yyvsp[(3) - (5)].pTokenList);
  while ( t ) {
    t1 = t->next;
    free( t->item );
    free( t );
    t = t1;
  }

  /* now do the simple stuff: return a name with a (quite complicated)
   * type 
   */
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (5)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (5)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  (yyval.pFactList)->item->next->item = s;
  (yyval.pFactList)->next = (yyvsp[(5) - (5)].pFactList);
;}
    break;

  case 68:

/* Line 1455 of yacc.c  */
#line 800 "scan-ops_pddl.y"
    {
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (3)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (3)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  (yyval.pFactList)->item->next->item = new_Token( strlen((yyvsp[(2) - (3)].string))+1 );
  strcpy( (yyval.pFactList)->item->next->item, (yyvsp[(2) - (3)].string) );
  (yyval.pFactList)->next = (yyvsp[(3) - (3)].pFactList);
;}
    break;

  case 69:

/* Line 1455 of yacc.c  */
#line 812 "scan-ops_pddl.y"
    {
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (2)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (2)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  if ( (yyvsp[(2) - (2)].pFactList) ) {/* another element (already typed) is following */
    char *s = (yyvsp[(2) - (2)].pFactList)->item->next->item;
    (yyval.pFactList)->item->next->item = new_Token(strlen(s) + 1);
    strcpy( (yyval.pFactList)->item->next->item, s ); /* same type as the next one */
    (yyval.pFactList)->next = (yyvsp[(2) - (2)].pFactList);
  } else {/* no further element - it must be an untyped list */
    (yyval.pFactList)->item->next->item = new_Token( strlen(STANDARD_TYPE)+1 );
    strcpy( (yyval.pFactList)->item->next->item, STANDARD_TYPE );
    (yyval.pFactList)->next = (yyvsp[(2) - (2)].pFactList);
  }
;}
    break;

  case 70:

/* Line 1455 of yacc.c  */
#line 835 "scan-ops_pddl.y"
    { (yyval.pFactList) = NULL; ;}
    break;

  case 71:

/* Line 1455 of yacc.c  */
#line 838 "scan-ops_pddl.y"
    { /* this is a very, very special case... it may mean that
   * a parameter has one of the types in name_plus
   * => build a new type name: either_name1_name2_..._namen and check
   * if a type with this name already exists. If so then NAME has this type,
   * if not then build a new type, include it in the type tree and
   * return NAME with the new type 
   * The new artificial type is not a subtype of OBJECT because its own
   * elements must already be instances of a subtype of OBJECT 
   */
  char *s;
  TokenList *t, *t1;
  type_tree tt;
  type_tree_list rootl, *st;
  
  s = new_Token( MAX_LENGTH );
  strcpy( s, EITHER_STR );
  for ( t = (yyvsp[(3) - (5)].pTokenList); t; t = t->next ) {
    strcat( s, CONNECTOR );
    strcat( s, t->item );
  }
  tt = NULL;
  for ( rootl = gglobal_type_tree_list; rootl; rootl = rootl->next ) {
    if ((tt = find_branch( s, rootl->item))) break;
  }
  if ( !tt ) {/* the type doesn't exist yet, so build it */
    rootl = new_type_tree_list( s );
    rootl->next = gglobal_type_tree_list;
    st = &(rootl->item->sub_types);
    for ( t = (yyvsp[(3) - (5)].pTokenList); t; t = t->next ) {
      if ((tt = find_branch( t->item, main_type_tree()))) {
	*st = new_type_tree_list( NULL );
	(*st)->item = tt;
	st = &((*st)->next);
      }
    }  
    gglobal_type_tree_list = rootl;
  }

  t = (yyvsp[(3) - (5)].pTokenList);
  while ( t ) {
    t1 = t->next;
    free( t->item );
    free( t );
    t = t1;
  }

  /* now do the simple stuff: return a name with a (quite complicated)
   * type 
   */
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (5)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (5)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  (yyval.pFactList)->item->next->item = s;
  (yyval.pFactList)->next = (yyvsp[(5) - (5)].pFactList);
;}
    break;

  case 72:

/* Line 1455 of yacc.c  */
#line 897 "scan-ops_pddl.y"
    {
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (3)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (3)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  (yyval.pFactList)->item->next->item = new_Token( strlen((yyvsp[(2) - (3)].string))+1 );
  strcpy( (yyval.pFactList)->item->next->item, (yyvsp[(2) - (3)].string) );
  (yyval.pFactList)->next = (yyvsp[(3) - (3)].pFactList);
;}
    break;

  case 73:

/* Line 1455 of yacc.c  */
#line 909 "scan-ops_pddl.y"
    {
  (yyval.pFactList) = new_FactList();
  (yyval.pFactList)->item = new_TokenList();
  (yyval.pFactList)->item->item = new_Token( strlen((yyvsp[(1) - (2)].string))+1 );
  strcpy( (yyval.pFactList)->item->item, (yyvsp[(1) - (2)].string) );
  (yyval.pFactList)->item->next = new_TokenList();
  if ( (yyvsp[(2) - (2)].pFactList) ) {/* another element (already typed) is following */
    char *s = (yyvsp[(2) - (2)].pFactList)->item->next->item;
    int l = strlen( s );
    (yyval.pFactList)->item->next->item = new_Token( l+1 );
    strcpy( (yyval.pFactList)->item->next->item, s ); /* same type as the next one */
    (yyval.pFactList)->next = (yyvsp[(2) - (2)].pFactList);
  } else {/* no further element - it must be an untyped list */
    (yyval.pFactList)->item->next->item = new_Token( strlen(STANDARD_TYPE)+1 );
    strcpy( (yyval.pFactList)->item->next->item, STANDARD_TYPE );
    (yyval.pFactList)->next = (yyvsp[(2) - (2)].pFactList);
  }
;}
    break;



/* Line 1455 of yacc.c  */
#line 2466 "scan-ops_pddl.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



/* Line 1675 of yacc.c  */
#line 929 "scan-ops_pddl.y"

#include "lex.ops_pddl.c"


/**********************************************************************
 * Functions
 **********************************************************************/

/* 
 * call	bison -pops -bscan-ops scan-ops.y
 */

void opserr( int errno, char *par )

{

  sact_err = errno;

  if ( sact_err_par ) {
    free(sact_err_par);
  }
  if ( par ) {
    sact_err_par = new_Token(strlen(par)+1);
    strcpy(sact_err_par, par);
  } else {
    sact_err_par = NULL;
  }

}
  


int yyerror( char *msg )

{

  fflush(stdout);
  fprintf(stderr, "\n%s: syntax error in line %d, '%s':\n", 
	  gact_filename, lineno, yytext);

  if ( NULL != sact_err_par ) {
    fprintf(stderr, "%s %s\n", serrmsg[sact_err], sact_err_par);
  } else {
    fprintf(stderr, "%s\n", serrmsg[sact_err]);
  }

  exit( 1 );

}



void load_ops_file( char *filename )

{

  FILE * fp;/* pointer to input files */
  char tmp[MAX_LENGTH] = "";

  /* open operator file 
   */
  if( ( fp = fopen( filename, "r" ) ) == NULL ) {
    sprintf(tmp, "\nff: can't find operator file: %s\n\n", filename );
    perror(tmp);
    exit( 1 );
  }

  gact_filename = filename;
  lineno = 1; 
  yyin = fp;

  yyparse();

  fclose( fp );/* and close file again */

}

