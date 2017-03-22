signature PARSE =
sig
  type exp

  val parse : (Lexer.token * char list) Stream.stream -> exp Stream.stream

  exception Error of string
end;  (* signature PARSE *)

functor ParseFun(structure E : EXP)
	:> PARSE where type exp = E.exp =
struct

    type exp = E.exp
    
    structure S = Stream
    open E
    open Lexer

    exception Error of string

    (* 
       The concrete grammar parsed by this module is as follows:

       program ::= exp0 SEMICOLON

       exp0    ::= exp0 PLUS expinf | exp0 CAT expinf | expinf
       expinf  ::= LPAREN exp0 RPAREN
                |  NUMBER(k)
                |  STRING(s)
                |  VAR(s)
                |  LET VAR(s) BE exp0 IN exp0 END
    *)
       
    (* next s = (x,s'), where x is the head of s, s' the tail of s
       raises Error if stream is empty
    *)
    fun next s =
        case S.force s
          of S.Nil => raise Error "Unexpected end of stream"
           | S.Cons result => result

    fun expected s msg =
        let val ((_, l), _) = next s
        in raise Error ("Expected " ^ msg ^ " at `" ^
                        concat (map Char.toString l) ^ "'") end

    fun require s token =
            let val ((t,l), s') = next s
            in if t = token then s'
               else expected s (Lexer.tokenToString token ^ " token")
            end

    fun program s =
            let val (e, s) = exp0 ((fn x => raise Error ("Free variable `" ^ x ^ "'")), s)
                val s = require s SEMICOLON
            in (e, s) end

    and exp0 (g, s) =
            let val (e, s) = expinf (g, s)
            in exp0' (e, g, s) end
    and exp0' (e, g, s) =
            case next s
              of ((PLUS,_), s) =>
                     let val (e', s) = expinf (g, s)
                     in exp0' (hide (Plus(e, e')), g, s) end
               | ((CAT,_), s) =>
                     let val (e', s) = expinf (g, s)
                     in exp0' (hide (Cat(e, e')), g, s) end
               | _ => (e, s)

    and expinf (g, s) = case next s
         of ((LPAREN,_), s) => let val (e, s) = exp0 (g, s)
                               val s = require s RPAREN
                           in (e, s) end
          | ((NUMBER(k),_), s) => (hide (Num(k)), s)
          | ((STRING(t),_), s) => (hide (Str(t)), s)
          | ((VAR(x),_), s) => (hide (Var(g x)), s)
          | ((LET,_), s) => let val (x, s) = var s
                                val s = require s BE
                                val (e1, s) = exp0 (g, s)
                                val s = require s IN
				val g' = extend(g, x)
                                val (e2, s) = exp0 (g', s)
                                val s = require s END
                            in (hide (Let(e1, g' x, e2)), s) end
          | _ => expected s "an expression"

    and extend (g, x) = let val v = N.new x in (fn y => if x = y then v else g y) end

    and var s = case next s
         of ((VAR(x),_), s) => (x, s)
          | _ => expected s "a variable name"

    (* Exported parsing function *)
          
    fun parse s = S.delay (fn () =>
            case S.force s
              of S.Nil => S.Nil
               | S.Cons _ => let val (e, s) = program s
                             in S.Cons(e, parse s) end)

end;  (* functor ParseFun *)
