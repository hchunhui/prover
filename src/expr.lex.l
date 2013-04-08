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
[a-z][a-z0-9]*|\+|\.		{
	yylval.sval = strdup(yytext);
	return(FUNC);
}

\-?[0-9]+		{
	char num[16];
	strcpy(num, "@");
	strcat(num, yytext);
	yylval.sval = strdup(num);
	return(FUNC);
}

"~"			{ return(NOT); }
"/\\"			{ return(AND); }
"\\/"			{ return(OR); }
"->"			{ return(IMPL); }
"("			{ return('('); }
")"			{ return(')'); }
"="			{ return(EQU); }
"<="			{ return(LE); }
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
