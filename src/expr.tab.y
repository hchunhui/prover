%{
#include <stdio.h>
#include "etree.h"
#include "pred.h"
#include "func.h"

static struct etree *et;
void yyerror(char* msg)
{
        fprintf(stderr, "Error: %s\n", msg);
}
%}

%locations

%token PROP IMPL OR AND NOT EQU FUNC EOL
%union {
	int ival;
	struct etree *tval;
}

%start main
%right IMPL
%right OR
%right AND
%nonassoc NOT

%type <ival> PROP
%type <ival> FUNC
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
		$$ = etree_mknode(T_PROP, 1+prop_new($1), NULL, NULL);
	}
	| '(' expr ')'
	{
		$$ = $2;
	}
	| expr IMPL expr
	{
		$$ = etree_mknode(T_IMPL, 0, $1, $3);
	}
	| expr AND expr
	{
		$$ = etree_mknode(T_AND, 0, $1, $3);
	}
	| expr OR expr
	{
		$$ = etree_mknode(T_OR, 0, $1, $3);
	}
	| NOT expr
	{
		$$ = etree_mknode(T_NOT, 0, $2, NULL);
	}
	| func EQU func
	{
		$$ = etree_mknode(T_PROP, 1+pred_new(P_EQU, $1, $3), NULL, NULL);
	}
	;

func
	: FUNC
	{
		$$ = func_new($1, -1, -1);
	}
	| FUNC '(' func_arg ')'
	{
		$$ = func_new($1, $3 & 0xffff, $3 >> 16);
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
