signature PRINT =
sig
  type exp

  (* print an expression *)
  val expToString : exp -> string
end

functor PrintFun(structure E : EXP)
        :> PRINT where type exp = E.exp =
struct

  type exp = E.exp

  open E

  fun exp0 (tab, e) = case show e
       of Plus(e1, e2) =>
              exp0 (tab, e1) ^ " + " ^ expinf (tab, e2)
	| Cat(e1, e2) =>
	      exp0 (tab, e1) ^ " ^ " ^ expinf (tab, e2)
	| _ => expinf (tab, e)

  and expinf (tab, e) = case show e
       of Num(k) => Int.toString k
	| Str(s) => "\"" ^ s ^ "\""
        | Var(x) => N.toString x
        | Let(e1, x, e2) =>
              let val tab' = tab ^ "    "
              in "let " ^ N.toString x ^ " be " ^ exp0 (tab, e1) ^ " in" ^
                 tab' ^ exp0 (tab', e2) ^
                 tab ^ "end" end
        | _ => "(" ^ exp0 (tab, e) ^ ")"

  fun expToString t = exp0 ("\n", t)

end;  (* functor PrintFun *)
