
signature EXP = 
sig

    structure N : NAME

    (* real type of expressions *)
    type exp;

    (* for pattern matching, we expose an exp one level as a datatype *)
    datatype exp1 = 
	Var of N.name
      | Num of int
      | Str of string
      | Plus of exp * exp
      | Cat of exp * exp
      | Let of exp * N.name * exp

    (* invariant: any name you get back from show is fresh *)
    val show : exp -> exp1
    val hide : exp1 -> exp
	
end
    
