%{
  open Termvar
  open Syntax
  open Parseterm
%}

%token <string> VAR PROP
%token DOT LAMBDA LOLLI TENPAIR WITHPAIR LETMV UNIT STAR LETONE ONE LPAREN RPAREN COMMA COLON EOF EOL LETTEN LETAPP LETFST LETSND BE IN TENSOR OR WITH INL INR LESS GREATER CASE OF ARROW

%start typEXP termEXP ctxtmEXP
%type <Syntax.Typ.t> typEXP
%type <Parseterm.pr> termEXP
%type <string> var
%type <(string * Termvar.TermVar.t * Syntax.Typ.t) list> ctxtmEXP

%%

typ:  typ TENSOR typ  { Typ.Tensor ($1 , $3) }
    | typ OR typ  { Typ.Or ($1 , $3) }
    | typ WITH typ  { Typ.With ($1 , $3) }
    | ONE { Typ.One }
    | typ LOLLI typ { Typ.Lolli ($1 , $3) }
    | PROP { Typ.Prop ($1) }
    | LPAREN typ RPAREN { $2 }
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
    | LETTEN term BE term IN term { (PLetten ($2 , $4 , $6)) }
    | LETAPP var BE term IN term { (PLetapp ($2 , $4 , $6)) }
    | LETFST term BE term IN term { (PLetfst ($2 , $4 , $6)) }
    | LETSND term BE term IN term { (PLetsnd ($2 , $4 , $6)) }
    | LETMV var BE term IN term { (PLetmv ($2 , $4, $6)) }
    | LETONE term BE term IN term { (PLetone ($2 , $4 , $6))}
    | LPAREN term term RPAREN { (PApp ($2 , $3)) }
    | STAR { (PStar) }
    | INL LPAREN term RPAREN { (PInl ($3)) }
    | INR LPAREN term RPAREN { (PInr ($3)) }
    | LAMBDA var COLON typ DOT term { (PLam (($2 , $4) , $6))}
;

termEXP: term EOL { $1 }
    |    term EOF { $1 }
;
