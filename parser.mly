%{
  open Syntax
%}

%token <string> VAR PROP
%token DOT LAMBDA LOLLI TENPAIR WITHPAIR UNIT STAR TOP ONE LPAREN RPAREN COMMA COLON EOF EOL LET BE IN TENSOR OR WITH INL INR LESS GREATER CASE OF ARROW

%start typEXP termEXP ctxtmEXP
%type <Typ.t> typEXP
%type <Term.t> termEXP
%type <TermVar.t> var
%type <TermVar.t * Typ.t> ctxtmEXP

%%

typ:  typ TENSOR typ { Typ.Tensor ($1 , $3) }
    | typ OR typ { Typ.Or ($1 , $3) }
    | typ WITH typ { Typ.With ($1 , $3) }
    | ONE { Typ.One }
    | TOP { Typ.Top }
    | typ LOLLI typ { Typ.Lolli ($1 , $3) }
    | PROP { Typ.Prop ($1) }
;

typEXP: typ EOL { $1 }
      | typ EOF { $1 }
;


var: VAR { (TermVar.newT $1) }
;

ctxtm: var COLON typ { ($1 , $3) }
;

ctxtmEXP: ctxtm EOL { $1 }
        | ctxtm EOF { $1 }
;

term:
    | var {  Term.into (Term.Var $1) }
    | LPAREN term TENSOR term RPAREN { Term.into (Term.TenPair ($2 , $4)) }
    | LESS term COMMA term GREATER { Term.into (Term.WithPair ($2 , $4)) }
    | CASE term OF INL LPAREN var RPAREN ARROW term COMMA INR LPAREN var RPAREN ARROW term
        { Term.into (Term.Case ($2 , ($6 , $9) , ($13 , $16)))}
    | LET term BE term IN term { Term.into (Term.Let ($2 , $4 , $6)) }

    | LPAREN term term RPAREN { Term.into (Term.App ($2 , $3)) }
    | LESS GREATER { Term.into (Term.Unit) }
    | STAR { Term.into (Term.Star) }
    | INL LPAREN term RPAREN LPAREN typ RPAREN { Term.into (Term.Inl ($6 , $3)) }
    | INR LPAREN term RPAREN LPAREN typ RPAREN { Term.into (Term.Inr ($6 , $3)) }
    | LAMBDA var COLON typ DOT term { Term.into (Term.Lam (($2 , $4) , $6))}
;

termEXP: term EOL { $1 }
    |    term EOF { $1 }
;
