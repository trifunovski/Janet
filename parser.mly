%{
  open Syntax
%}

%token <string> VAR PROP
%token DOT LAMBDA LOLLI TENPAIR WITHPAIR UNIT STAR TOP ONE LPAREN RPAREN COMMA COLON EOF EOL LETTEN LETAPP LETFST LETSND BE IN TENSOR OR WITH INL INR LESS GREATER CASE OF ARROW

%start typEXP termEXP ctxtmEXP
%type <Syntax.Typ.t> typEXP
%type <Syntax.Term.pr> termEXP
%type <string> var
%type <(string * Syntax.TermVar.t * Syntax.Typ.t) list> ctxtmEXP

%%

typ:  LPAREN typ TENSOR typ RPAREN { Typ.Tensor ($2 , $4) }
    | LPAREN typ OR typ RPAREN { Typ.Or ($2 , $4) }
    | LPAREN typ WITH typ RPAREN { Typ.With ($2 , $4) }
    | ONE { Typ.One }
    | TOP { Typ.Top }
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
    | var { Term.PVar $1 }
    | LPAREN term TENSOR term RPAREN { (Term.PTenPair ($2 , $4)) }
    | LESS term COMMA term GREATER { (Term.PWithPair ($2 , $4)) }
    | CASE var OF INL LPAREN var RPAREN ARROW term COMMA INR LPAREN var RPAREN ARROW term
        { (Term.PCase ($2 , ($6 , $9) , ($13 , $16)))}
    | LETTEN term BE var IN term { (Term.PLetten ($2 , $4 , $6)) }
    | LETAPP term BE var IN term { (Term.PLetapp ($2 , $4 , $6)) }
    | LETFST term BE var IN term { (Term.PLetfst ($2 , $4 , $6)) }
    | LETSND term BE var IN term { (Term.PLetsnd ($2 , $4 , $6)) }
    | LPAREN term term RPAREN { (Term.PApp ($2 , $3)) }
    | LESS GREATER { (Term.PUnit) }
    | STAR { (Term.PStar) }
    | INL LPAREN term RPAREN { (Term.PInl ($3)) }
    | INR LPAREN term RPAREN { (Term.PInr ($3)) }
    | LAMBDA var COLON typ DOT term { (Term.PLam (($2 , $4) , $6))}
;

termEXP: term EOL { $1 }
    |    term EOF { $1 }
;
