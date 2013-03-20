%{
#include <stdio.h>
#include "etree.h"

static struct etree *et;
void yyerror(char* msg)
{
        fprintf(stderr, "Error: %s\n", msg);
}
%}

%locations

%token PROP IMPL OR AND NOT EOL
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
%type <tval> expr
%error-verbose
/*%define parse.lac full*/
%%
main: expr EOL {et = $1;};

expr
	: PROP
	{
		$$ = etree_mknode(T_PROP, $1, NULL, NULL);
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
	;
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
