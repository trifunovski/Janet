%{
  open Syntax
  open Parseterm
%}

%token <string> VAR PROP
%token DOT LAMBDA LOLLI TENPAIR WITHPAIR UNIT STAR ONE LPAREN RPAREN COMMA COLON EOF EOL LETTEN LETAPP LETFST LETSND BE IN TENSOR OR WITH INL INR LESS GREATER CASE OF ARROW

%start typEXP termEXP ctxtmEXP
%type <Syntax.Typ.t> typEXP
%type <Parseterm.pr> termEXP
%type <string> var
%type <(string * Syntax.TermVar.t * Syntax.Typ.t) list> ctxtmEXP

%%

typ:  LPAREN typ TENSOR typ RPAREN { Typ.Tensor ($2 , $4) }
    | LPAREN typ OR typ RPAREN { Typ.Or ($2 , $4) }
    | LPAREN typ WITH typ RPAREN { Typ.With ($2 , $4) }
    | ONE { Typ.One }
    | LPAREN typ LOLLI typ RPAREN { Typ.Lolli ($2 , $4) }
    | PROP { Typ.Prop ($1) }
;

typEXP: typ EOL { $1 }
      | typ EOF { $1 }
;


var: VAR { $1 }
;


ctxtm: var COLON typ { ($1 , (TermVar.newT $1) , $3) }
;

ctxtmEXP: ctxtm COMMA ctxtmEXP { $1 :: $3 }
        | ctxtm EOL { [$1] }
        | ctxtm EOF { [$1] }
        | EOL { [] }
        | EOF { [] }
;

term:
    | var { PVar $1 }
    | LPAREN term TENSOR term RPAREN { (PTenPair ($2 , $4)) }
    | LESS term COMMA term GREATER { (PWithPair ($2 , $4)) }
    | CASE var OF INL LPAREN var RPAREN ARROW term COMMA INR LPAREN var RPAREN ARROW term
        { (PCase ($2 , ($6 , $9) , ($13 , $16)))}
    | LETTEN term BE var IN term { (PLetten ($2 , $4 , $6)) }
    | LETAPP term BE var IN term { (PLetapp ($2 , $4 , $6)) }
    | LETFST term BE var IN term { (PLetfst ($2 , $4 , $6)) }
    | LETSND term BE var IN term { (PLetsnd ($2 , $4 , $6)) }
    | LPAREN term term RPAREN { (PApp ($2 , $3)) }
    | STAR { (PStar) }
    | INL LPAREN term RPAREN { (PInl ($3)) }
    | INR LPAREN term RPAREN { (PInr ($3)) }
    | LAMBDA var COLON typ DOT term { (PLam (($2 , $4) , $6))}
;

termEXP: term EOL { $1 }
    |    term EOF { $1 }
;
