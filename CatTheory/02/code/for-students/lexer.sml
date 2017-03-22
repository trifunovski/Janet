signature LEXER =
sig
    datatype token =
        LET
      | BE
      | IN
      | END
      | LPAREN
      | RPAREN
      | SEMICOLON
      | PLUS
      | CAT
      | NUMBER of int
      | STRING of string
      | VAR of string

    exception Error of string

    val lex : (char * char list) Stream.stream -> (token * char list) Stream.stream

    val tokenToString : token -> string
end;  (* signature LEXER *)


structure Lexer :> LEXER =
struct

    structure S = Stream

    exception Error of string

    datatype token =
        LET
      | BE
      | IN
      | END
      | LPAREN
      | RPAREN
      | SEMICOLON
      | PLUS
      | CAT
      | NUMBER of int
      | STRING of string
      | VAR of string

    fun next s =
        case S.force s of
            S.Nil => raise Error "Unexpected end of stream"
          | S.Cons result => result
   
    fun isNum (c) = Char.isDigit (c)
    fun isAlpha (c) = Char.contains "_'" c orelse Char.isDigit (c)
                      orelse Char.isLower (c) orelse Char.isUpper (c)

    fun keywords ("let") = LET
      | keywords ("be") = BE
      | keywords ("in") = IN
      | keywords ("end") = END
      | keywords v = VAR(v)

    fun lexAlpha (s, v, l) =
        let val ((c,_), s') = next s
        in if isAlpha (c) then lexAlpha (s', c::v, l)
                          else ((keywords(implode(rev(v))), l), s)
        end

    fun lexNum (s, k, l) =
        let val ((c,_), s') = next s
        in if isNum (c) then lexNum (s', 10*k + (ord c - ord #"0"), l)
                        else ((NUMBER(k), l), s)
        end

    fun lexString (s, t, l) =
	let val ((c,_), s') = next s
	in if c = #"\"" then ((STRING(implode(rev(t))), l), s')
	   else lexString (s', c::t, l)
	end

    fun token ((#"(",l), s) = ((LPAREN,l), s)
      | token ((#")",l), s) = ((RPAREN,l), s)
      | token ((#";",l), s) = ((SEMICOLON,l), s)
      | token ((#"+",l), s) = ((PLUS,l), s)
      | token ((#"^",l), s) = ((CAT,l), s)
      | token ((#"\"",l), s) = lexString(s, [], l)
      | token ((c,l), s) =
             if isNum c then lexNum (s, ord c - ord #"0", l)
             else if isAlpha c then lexAlpha (s, [c], l)
             else raise Error ("Illegal character at `" ^
                               concat (map Char.toString l) ^ "'")

    and lex s =
        S.delay (fn () => lex' (S.force s))

    (* process characters, skipping whitespace *)
    and lex' S.Nil = S.Nil
      | lex' (S.Cons ((#" ",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\r",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\t",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\v",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\n",_), s)) = lex' (S.force s)
      | lex' (S.Cons r) =
            let val (t, s) = token r
            in S.Cons (t, lex s) end

    fun tokenToString t = 
        case t of
            LET => "LET"
          | BE => "BE"
          | IN => "IN"
          | END => "END"
          | LPAREN => "LPAREN"
          | RPAREN => "RPAREN"
          | SEMICOLON => "SEMICOLON"
          | PLUS => "PLUS"
          | CAT => "CAT"
          | NUMBER k => "NUMBER(" ^ Int.toString k ^ ")"
          | STRING s => "STRING(\"" ^ s ^ "\")"
          | VAR v => "VAR(" ^ v ^ ")"

end;  (* structure Lexer *)
