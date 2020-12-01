grammar Retreet;                         

prog 
      : (function)+ 
      | (relation)+
      ;                                  

relation
      : 'unfused' ':' INT '->' 'fused' ':' INT
      ;

id
      : IDENTIFIER
      ;

function 
      : main 
      | func
      ;

main 
      : 'main' '(' id ')''{' stmt+ '}'
      ;

func 
      : id '(' param_list ')' '{' stmt+ '}'
      ;               

param_list 
      : id   // loc variable
      | id param_tail   // loc & int variables
      ;

param_tail
      : ',' id param_tail   // int variable
      | // empty
      ;
           
stmt 
      : block_withid
      | if_stmt
      | '[' block_withid ':' block_withid ']' // parallel
      ;

block_withid
      : block '//' INT
      //| if_stmt_withid '//' INT
      ;
     
block 
      : call
      | assgn_list
      | single_if_stmt
      ;

call 
      : id '(' arg_list ')' ';'
      ;

arg_list
      : lexpr arg_list_tail
      ;

arg_list_tail
      : ',' aexpr arg_list_tail
      | // empty
      ;

assgn_list
      : assgn+
      ;

assgn 
      : field '=' aexpr ';'
      | id '=' aexpr ';'
      | 'return' ';'
      ;

single_if_stmt
      : 'if' '(' bexpr ')' '{' assgn_list '}'
      ;

if_stmt 
      :if_part else_part;

if_part 
      : 'if' '(' bexpr ')' '{' stmt+ '}'
      ;

else_part 
      : 'else' '{' stmt+ '}'
      | // empty
      ;

lexpr 
      : id
      | lexpr '.' dir
      ;

dir
      : 'left'
      | 'right'
      | 'next'
      ;

aexpr 
      : INT
      | id
      | field
      | aexpr aop aexpr
      ;

aop
      : '+'
      | '-'
      ;

field
      : lexpr '.' id
      ;

bexpr
      : lit bexpr_suffix
      ;

bexpr_suffix
      : '&&' lit bexpr_suffix
      | '||' lit bexpr_suffix
      | // empty
      ;

lit
      : '!' basic_cond
      | basic_cond
      ;

basic_cond
      : aexpr compop aexpr
      | lexpr eqop 'nil'
      | 'true'
      | 'false'
      ;

compop
      : '>'
      | '<'
      | '>='
      | '<='
      | eqop
      ;

eqop
      : '=='
      | '!='
      ;

WHITESPACE
      : ( ' ' | '\t' | '\r' | '\n' )+ -> skip
      ;

KEYWORD
      : 'main'
      | 'if'
      | 'else'
      | 'nil'
      | 'return'
      | 'left'
      | 'right'
      | 'next'
      | 'true'
      | 'false'
      ;

IDENTIFIER 
      : [a-zA-Z]+
      ;

INT
      : [0-9]+
      ;
