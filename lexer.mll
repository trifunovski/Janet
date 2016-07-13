{
  open Parser
  exception Eof
}

let digit = ['0'-'9']
let id = ['a'-'z']['a'-'z' '0'-'9']*
let prop = ['A'-'Z']['A'-'Z']*
let ws = ['\t' ' ']

rule exp_token = parse
  | "let" { LET }
  | "case" { CASE }
  | "T" { TOP }
  | "1" { UNIT }
  | "=>" { ARROW }
  | "of" { OF }
  | "<" { LESS }
  | ">" { GREATER }
  | "inl" { INL }
  | "inr" { INR }
  | "in" { IN }
  | "be" { BE }
  | ":" { COLON }
  | "," { COMMA }
  | "." { DOT }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "*" { STAR }
  | "&" { WITH }
  | "+" { OR }
  | "X" { TENSOR}
  | "<>" { UNIT }
  | "-o" { LOLLI }
  | "//" { LAMBDA }
  | id as var { VAR var }
  | prop as p { PROP p }
  | ws { exp_token lexbuf }
  | "\n" { EOL }
  | eof { EOF }
