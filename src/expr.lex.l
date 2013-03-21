%{
#include <stdio.h>
#include <stdlib.h>
#include "expr.tab.h"

int yycolumn = 0;

#define YY_USER_ACTION yylloc.first_line = yylloc.last_line = yylineno; \
    yylloc.first_column = yycolumn; yylloc.last_column = yycolumn+yyleng-1; \
    yycolumn += yyleng;
%}

%option yylineno

%%
\/\*[^\*]*\*(([^\*\/][^\*]*)?\*)*\/ {  }

A[0-9]+			{
	int val;
	sscanf(yytext, "A%d", &val);
	if(val == 0 || val > 64)
		exit(1);
	yylval.ival = val;
	return(PROP);
}
x[0-9]+			{
	int val;
	sscanf(yytext, "x%d", &val);
	if(val == 0 || val > 64)
	       exit(1);
	yylval.ival = val;
	return(VAR);
}
"~"			{ return(NOT); }
"/\\"			{ return(AND); }
"\\/"			{ return(OR); }
"->"			{ return(IMPL); }
"("			{ return('('); }
")"			{ return(')'); }
"="			{ return(EQU); }

[ \v\f]			{  }
\t			{ yycolumn += 8 - yycolumn%8; }
[\n\r]			{ yycolumn = 0;return EOL;}
.			{ fprintf(stderr, "unmatched: %s\n", yytext); return 1; }

%%

int yywrap(void)
{
	return 1;
}
