
structure NamedExp :> EXP = 
struct

    structure N = Name

    datatype exp1 = 
	Var of N.name
      | Num of int
      | Str of string
      | Plus of exp1 * exp1
      | Cat of exp1 * exp1
      | Let of exp1 * N.name * exp1

    (* in this implementation, exp is just exp1 *)
    type exp = exp1

    (* hide doesn't need to do anything *)
    fun hide e = e;

    fun show e = raise Fail "unimplemented"

end
