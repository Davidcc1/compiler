/*************************************************************************** 
Scanner for the Simple language 
Author: Anthony A. Aaby
Modified by: Jordi Planes 
Modified again by: David Castillo
***************************************************************************/ 

%option nounput
%option noinput

%{ 
/*========================================================================= 
C-libraries and Token definitions 
=========================================================================*/ 
#include <string.h> /* for strdup */ 
#include <stdlib.h> /* for atoi */ 
#include "senzillc.tab.h" /* for token definitions and yylval */ 

int i ;
char * buff;
int num_line = 1;

#define MAX_INCLUDE_DEPTH 10
YY_BUFFER_STATE include_stack[MAX_INCLUDE_DEPTH];
int include_stack_ptr = 0;

%} 

%x incl
%x string
/*========================================================================= 
TOKEN Definitions 
=========================================================================*/ 
DIGIT [0-9] 
ID [a-z][a-z0-9]* 

/*========================================================================= 
REGULAR EXPRESSIONS defining the tokens for the Simple language 
=========================================================================*/ 
%% 

include BEGIN(incl);
goes: {return GO;}
main { return MAIN; }
":=" { return(ASSGNOP); } 
{DIGIT}+ { yylval.intval = atoi( yytext ); 
return(NUMBER); } 
string { return STR; }
do { return(DO); } 
else { return(ELSE); } 
end { return(END); } 
fi { return(FI); } 
if { return(IF); } 
in { return(IN); } 
function { return(FUNCTION);}
procedure { return(PROCEDURE);}
integer { return(INTEGER); } 
let { return(LET); } 
read { return(READ); } 
skip { return(SKIP); } 
then { return(THEN); } 
while { return(WHILE); } 
write { return(WRITE); }
\" 					{BEGIN(string); i = 0; buff = malloc(sizeof(char)*(1024));}

\#.+  
{ID} { yylval.id = (char *) strdup(yytext); return(IDENTIFIER); } 

<string>[^\\"\n] 	{strcat(buff,yytext); i = i + yyleng;}
<string>\n			{buff[i++] = '\n';}
<string>\"			{yylval.str = strdup(buff); BEGIN 0; return LABEL; }

<incl>[ \t]* 
<incl>[^ \t\n]+ { 
	if ( include_stack_ptr >= MAX_INCLUDE_DEPTH ){
	 	fprintf( stderr, "Includes nested too deeply" );
	 	exit( 1 );
	}
 	include_stack[include_stack_ptr++] =
 	YY_CURRENT_BUFFER;
 	yyin = fopen( yytext, "r" );
 	if ( ! yyin )
 		printf("error");
 	yy_switch_to_buffer(
 	yy_create_buffer( yyin, YY_BUF_SIZE ) );
 	BEGIN(INITIAL);
}
<<EOF>> {
	 	if ( --include_stack_ptr < 0 ){
	 		yyterminate();
	 	}else{
	 	yy_delete_buffer( YY_CURRENT_BUFFER );
	 	yy_switch_to_buffer(include_stack[include_stack_ptr] );
	 	}
 }


\n      num_line++;
[ \t]+ /* eat up whitespace */ 
. { return(yytext[0]);} 

%% 

int yywrap(void){ 
   return 1; 
} 

/************************** End Scanner File *****************************/ 

