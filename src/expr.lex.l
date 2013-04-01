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
c[0-9]+			{
	int val;
	sscanf(yytext, "c%d", &val);
	if(val >= 4)
	       exit(1);
	yylval.ival = val;
	return(FUNC);
}
f[0-9]+			{
	int val;
	sscanf(yytext, "f%d", &val);
	if(val >= 4)
	       exit(1);
	yylval.ival = 4 + val;
	return(FUNC);
}
g[0-9]+			{
	int val;
	sscanf(yytext, "g%d", &val);
	if(val >= 4)
	       exit(1);
	yylval.ival = 8 + val;
	return(FUNC);
}

"~"			{ return(NOT); }
"/\\"			{ return(AND); }
"\\/"			{ return(OR); }
"->"			{ return(IMPL); }
"("			{ return('('); }
")"			{ return(')'); }
"="			{ return(EQU); }
","			{ return(','); }

[ \v\f]			{  }
\t			{ yycolumn += 8 - yycolumn%8; }
[\n\r]			{ yycolumn = 0;return EOL;}
.			{ fprintf(stderr, "unmatched: %s\n", yytext); return 1; }

%%

int yywrap(void)
{
	return 1;
}
