%{
/*************************************************************************
Compiler for the Simple language
Author: Anthony A. Aaby
Modified by: Jordi Planes
Modified again by: David Castillo
***************************************************************************/
/*=========================================================================
C Libraries, Symbol Table, Code Generator & other C code
=========================================================================*/
#include <stdio.h> /* For I/O */
#include <stdlib.h> /* For malloc here and in symbol table */
#include <string.h> /* For strcmp in symbol table */
#include "ST.h" /* Symbol Table */
#include "SM.h" /* Stack Machine */
#include "CG.h" /* Code Generator */

#define YYDEBUG 1 /* For Debugging */

int yyerror(char *);
int yylex();

int errors; /* Error Count */
/*-------------------------------------------------------------------------
The following support backpatching
-------------------------------------------------------------------------*/
struct lbs /* Labels for data, if and while */
{
  int for_goto;
  int for_jmp_false;
};

struct lbs * newlblrec() /* Allocate space for the labels */
{
   return (struct lbs *) malloc(sizeof(struct lbs));
}

/*-------------------------------------------------------------------------
Install identifier & check if previously defined.
-------------------------------------------------------------------------*/
void install ( char *sym_name, int length )
{
  symrec *s = getsym (sym_name);
  if (s == 0)
    s = putsym (sym_name, length);
  else {
    char message[ 100 ];
    sprintf( message, "%s is already defined\n", sym_name );
    yyerror( message );
  }
}

void install2 ( char *sym_name, int length )
{
  symrec *s = getsym (sym_name);
  if (s == 0)
    s = putsym2 (sym_name, length);
  else {
    char message[ 100 ];
    sprintf( message, "%s is already defined\n", sym_name );
    yyerror( message );
  }
}

/*-------------------------------------------------------------------------
If identifier is defined, generate code
-------------------------------------------------------------------------*/
int context_check( char *sym_name )
{
  symrec *identifier = getsym( sym_name );
  return identifier->offset;
}

/*=========================================================================
SEMANTIC RECORDS
=========================================================================*/
//%type <str> sexpr

%}

%union /* semrec - The Semantic Records */
 {
   int intval; /* Integer values */
   char *id; /* Identifiers */
   char *str;
   struct lbs *lbls; /* For backpatching */
};

/*=========================================================================
TOKENS
=========================================================================*/

%token <intval> NUMBER /* Simple integer */
%token <id> IDENTIFIER /* Simple identifier */
%token <str> LABEL
%token <lbls> IF WHILE PROCEDURE /* For backpatching labels */
%token SKIP THEN ELSE FI DO END DOT FUNCTION
%token INTEGER READ WRITE LET IN
%token ASSGNOP LPAREN RPAREN STR MAIN GO


/*=========================================================================
OPERATOR PRECEDENCE
=========================================================================*/
%left '-' '+'
%left '*' '/'
%right '^'

/*=========================================================================
GRAMMAR RULES for the Simple language
=========================================================================*/

%%

program :   GO {reserve_loc();}
	    declarations { gen_code( DATA, data_location() ); }
	    functions
	    MAIN '{' {back_patch(0,GOTO,gen_label());} 
            commands { gen_code( HALT, 0 ); YYACCEPT; }
	    '}'
	    | declarations { gen_code( DATA, data_location() ); }
	    commands { gen_code( HALT, 0 ); YYACCEPT; }
            
;

functions: /*empty*/
          | function functions
;

function:   PROCEDURE IDENTIFIER '(' declaration ')' '{'
            { 	$1 = (struct lbs *) newlblrec(); install2($2,1); }
            commands
            '}' { gen_code( RET, 0); }
	    | error {yyerrok;}
;

declarations : declaration '.'
	| declarations declaration '.'
;

declaration : /* empty */
    | INTEGER id_seq IDENTIFIER { install( $3 , 1); }
    | INTEGER id_seq IDENTIFIER '[' NUMBER ']' { install($3,$5);}
    | FUNCTION IDENTIFIER '(' id_seq ')' ':' INTEGER  {}

;

id_seq : /* empty */

    | id_seq IDENTIFIER ',' { install( $2, 1); }
    | id_seq IDENTIFIER '[' NUMBER ']' ',' { install($2,$4); }
    | FUNCTION IDENTIFIER '(' id_seq ')' ':' INTEGER ',' {}
;

commands : /* empty */
    | commands command ';'
;

command : SKIP
   | READ IDENTIFIER { gen_code( READ_INT, context_check( $2 ) ); }
   | WRITE exp { gen_code( WRITE_INT, 0 ); }
   | IDENTIFIER ASSGNOP exp { gen_code( STORE, context_check( $1 ) ); }
   | IDENTIFIER '[' exp ']' ASSGNOP exp { gen_code( LD_INT, context_check( $1 )); gen_code( STORE_SUB, 0 ); }
   | IF bool_exp { $1 = (struct lbs *) newlblrec(); $1->for_jmp_false = reserve_loc(); }
   THEN commands { $1->for_goto = reserve_loc(); } ELSE {
     back_patch( $1->for_jmp_false, JMP_FALSE, gen_label() );
   } commands FI { back_patch( $1->for_goto, GOTO, gen_label() ); }
   | WHILE { $1 = (struct lbs *) newlblrec(); $1->for_goto = gen_label(); }
   bool_exp { $1->for_jmp_false = reserve_loc(); } DO commands END { gen_code( GOTO, $1->for_goto );
   back_patch( $1->for_jmp_false, JMP_FALSE, gen_label() ); }
   | IDENTIFIER '(' ')' { gen_code( CALL , context_check( $1 ) ); }


;

bool_exp : exp '<' exp { gen_code( LT, 0 ); }
   | exp '=' exp { gen_code( EQ, 0 ); }
   | exp '>' exp { gen_code( GT, 0 ); }
;

exp :/*empty*/
	|NUMBER { gen_code( LD_INT, $1 ); }
   	| IDENTIFIER { gen_code( LD_VAR, context_check( $1 ) ); }
   	| IDENTIFIER '[' exp ']' { gen_code( LD_INT, context_check( $1 )); gen_code( LD_SUB, 0);}
   	| exp '+' exp { gen_code( ADD, 0 ); }
   	| exp '-' exp { gen_code( SUB, 0 ); }
   	| exp '*' exp { gen_code( MULT, 0 ); }
   	| exp '/' exp { gen_code( DIV, 0 ); }
   	| exp '^' exp { gen_code( PWR, 0 ); }
   	| '(' exp ')'
   	| IDENTIFIER '(' exp ')' { gen_code( CALL , context_check( $1 ) ); }
;

%%

extern struct instruction code[ MAX_MEMORY ];

/*=========================================================================
MAIN
=========================================================================*/
int main( int argc, char *argv[] )
{
  extern FILE *yyin;
  if ( argc < 3 ) {
    printf("usage <input-file> <output-file>\n");
    return -1;
  }
  yyin = fopen( argv[1], "r" );
  //yydebug = 1;
  errors = 0;
  printf("Senzill Compiler\n");
  yyparse ();
  printf ( "Parse Completed\n" );
  if ( errors == 0 )
    {
      //print_code ();
      //fetch_execute_cycle();
      write_bytecode( argv[2] );
    }
  return 0;
}

/*=========================================================================
YYERROR
=========================================================================*/
extern int num_line;
int yyerror ( char *s ) /* Called by yyparse on error */
{
  errors++;
  printf ("%s in line: %d\n", s, num_line);
  return 0;
}
/**************************** End Grammar File ***************************/
