%{
#include <stdio.h>
#include "etree.h"
#include "pred.h"
#include "func.h"
#include "lit.h"

static struct etree *et;
void yyerror(char* msg)
{
        fprintf(stderr, "Error: %s\n", msg);
}
%}

%locations

%token PROP IMPL OR AND NOT EQU LE FUNC EOL
%union {
	int ival;
	struct etree *tval;
	char *sval;
}

%start main
%right IMPL
%right OR
%right AND
%nonassoc NOT

%type <ival> PROP
%type <sval> FUNC
%type <ival> func
%type <ival> func_arg
%type <tval> expr
%error-verbose
/*%define parse.lac full*/
%%
main: expr EOL {et = $1;};

expr
	: PROP
	{
		$$ = etree_mknode(T_PROP, lit_make(0, prop_new($1)), NULL, NULL);
	}
	| '(' expr ')'
	{
		$$ = $2;
	}
	| expr IMPL expr
	{
		$$ = etree_mknode(T_IMPL, lit_make(0, 0), $1, $3);
	}
	| expr AND expr
	{
		$$ = etree_mknode(T_AND, lit_make(0, 0), $1, $3);
	}
	| expr OR expr
	{
		$$ = etree_mknode(T_OR, lit_make(0, 0), $1, $3);
	}
	| NOT expr
	{
		$$ = etree_mknode(T_NOT, lit_make(0, 0), $2, NULL);
	}
	| func EQU func
	{
		$$ = etree_mknode(T_PROP, lit_make(0, pred_new(P_EQU, $1, $3)), NULL, NULL);
	}
	| func LE func
	{
		$$ = etree_mknode(T_PROP, lit_make(0, pred_new(P_LE, $1, $3)), NULL, NULL);
	}
	;

func
	: FUNC
	{
		int type = func_info_new($1, 0);
		$$ = func_new(type, -1, -1);
		free($1);
	}
	| FUNC '(' func_arg ')'
	{
		int type = func_info_new($1, ($3>>16) == -1 ? 1 : 2);
		$$ = func_new(type, $3 & 0xffff, $3 >> 16);
		free($1);
	}
	;

func_arg
	: func
	{
		$$ = $1 | (-1 << 16);
	}
	| func ',' func
	{
		$$ = $1 | ($3 << 16);
	}
%%
struct etree *parse()
{
	int ret;
//	yydebug = 1;
	ret = yyparse();
	if(ret)
		return NULL;
	else
		return et;
}
